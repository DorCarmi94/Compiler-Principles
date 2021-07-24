(* 
   This module contains code to generate the low-level implementation of
   parts of the standard library procedures.
   The module works by defining a hierarchy of templates, which call each other
   to form complete routines. See the inline comments below for more information
   on the templates and the individual routines.

   Note that the implementation below contain no error handling or correctness-checking
   of any kind. This is because we will not test your compilers on invalid input.
   However, adding correctness-checking and error handling *as general templates* would be
   rather simple.
 *)
module type PRIMS = sig
  val procs : string;;
end

module Prims : PRIMS = struct
  (* This is the most basic routine template. It takes a body and label name, and
     creates the standard x86-64 bit routine form.
     All other templates and routine-generation functions depend on this template. *)
  let make_routine label body =
    label ^ ":
       push rbp
       mov rbp, rsp 
       " ^ body ^ "
         pop rbp
         ret";;

  (* Many of the low-level stdlib procedures are predicate procedures, which perform 
     some kind of comparison, and then return one of the constants sob_true or sob_false.
     Since this pattern repeats so often, we have a template that takes a body, and a type
     of condition to test for jump, and generates an assembly snippet that evaluated the body,
     and return true or false, depending on the type of condition. *)
  let return_boolean jcc body =
    body ^ "
      " ^ jcc ^ " .true
       mov rax, SOB_FALSE_ADDRESS
       jmp .return
       .true:
       mov rax, SOB_TRUE_ADDRESS
       .return:";;

  (* 
     Many of the predicates just test some kind of equality (or, equivalently, if the 
     zero flag is set), so this is an auxiliary function dedicated to equality-testing predicates. 
     Note how we make use of currying here.
   *)
  let return_boolean_eq = return_boolean "je";;
  
  (* 
     Almost all of the stdlib function take 1 or more arguments. Since all of the variadic procedures
     are implemented in the high-level scheme library code (found in stdlib.scm), we only have to deal
     with 1,2 or 3 arguments.
     These helper functions inject instructions to get parameter values off the stack and into registers
     to work with.
     The argument register assignment follows the x86 64bit Unix ABI, because there needs to be *some*
     kind of consistency, so why not just use the standard ABI.
     See page 22 in https://raw.githubusercontent.com/wiki/hjl-tools/x86-psABI/x86-64-psABI-1.0.pdf
   *)
  let make_unary label body = make_routine label ("mov rsi, PVAR(0)\n\t" ^ body);;
  let make_binary label body = make_unary label ("mov rdi, PVAR(1)\n\t" ^ body);;
  let make_tertiary label body = make_binary label ("mov rdx, PVAR(2)\n\t" ^ body);;

  (* All of the type queries in scheme (e.g., null?, pair?, char?, etc.) are equality predicates
     that are implemented by comparing the first byte pointed to by PVAR(0) to the relevant type tag.
     so the only unique bits of each of these predicates are the name of the routine (i.e., the label), 
     and the type tag we expect to find.
     The implementation of the type-queries generator is slightly more complex, since a template and a label
     name aren't enough: we need to generate a routine for every (label * type_tag) pair (e.g., the routine 
     `is_boolean` should test for the T_BOOL type tag).
     We have a list of pairs, associating each predicate label with the correct type tag, and map the templating 
     function over this list. Note that the query template function makes use of some of the other templating 
     functions defined above: `make_unary` (predicates take only one argument) and `return_boolean_eq` (since 
     these are equality-testing predicates).
   *)
  let type_queries =
    let queries_to_types = [
        "boolean", "T_BOOL"; "flonum", "T_FLOAT"; "rational", "T_RATIONAL"; "pair", "T_PAIR";
        "null", "T_NIL"; "char", "T_CHAR"; "string", "T_STRING"; "symbol", "T_SYMBOL";
        "procedure", "T_CLOSURE"
      ] in
    let single_query name type_tag =
      make_unary (name ^ "?")
        (return_boolean_eq ("mov sil, byte [rsi]\n\tcmp sil, " ^ type_tag)) in
    String.concat "\n\n" (List.map (fun (a, b) -> single_query a b) queries_to_types);;

  (* The arithmetic operation implementation is multi-tiered:
     - The low-level implementations of all operations are binary, e.g. (+ 1 2 3) and (+ 1) are not 
       supported in the low-level implementation.
     - The low-level implementations only support same-type operations, e.g. (+ 1 2.5) is not supported
       in the low-level implementation. This means each operation has two low-level implementations, one
       for floating-point operands, and one for fractional operands.
     - Each pair of low-level operation implementations is wrapped by a dispatcher which decides which 
       of the two implementations to call (by probing the types of the operands).
     - The high-level implementations (see stdlib.scm) make use of a high-level dispatcher, that is in charge
       of performing type conversions as necessary to satisfy the pre-conditions of the low-level implementations.
     
     Operations on floating-point operands:
     -------------------------------------
     The implementations of binary floating point arithmetic operations contain almost identical code. The
     differences are the name (label) of the routines, and the arithmetic instruction applied to 
     the two arguments. Other than that, they are all the same: binary routines which load the values
     pointed at by PVAR(0) and PVAR(1) into SSE2 registers, compute the operation, create a new sob_float
     on the heap with the result, and store the address of the sob_float in rax as the return value.
     This allows us to easily abstract this code into a template that requires a label name and its matching
     arithmetic instruction (which are paired up in the op_map).

     Operations on fractional operands:
     ----------------------------------
     The addition and multiplication operations on rational numbers are similar to each other: both load 2 arguments,
     both deconstruct the arguments into numerator and denominator, both allocate a sob_rational to store the result
     on the heap, and both move the address of this sob_rational into rax as the return value. The only differences 
     are the routine name (label), and the implementation of the arithmetic operation itself.
     This allows us to easily abstract this code into a template that requires a label name and its matching
     arithmetic instruction (which are paired up in the op_map).
     
     Unlike in the case of floating point arithmetic, rational division is treated differently, and is implemented by
     using the identity (a/b) / (c/d) == (a/b) * (d/c).
     This is done by inverting the second arg (in PVAR(1)) and tail-calling fraction multiplication (`jmp mul`).

     Comparators:
     ------------
     While the implementation of the Comparators is slightly more complex, since they make use of `return_boolean`,
     the idea is the same as the arithmetic operators.
     A couple of things to note:
     - `eq.flt` can collapse to a bitwise comparison (like in the case of integers in C), while `eq.rat` involves
       comparing the numerator and denominator separately, due to our fraction representation using 128 bits
       and not 64 bits.
     - `lt.flt` does not handle NaN, +inf and -inf correctly. This allows us to use `return_boolean jl` for both the
       floating-point and the fraction cases. For a fully correct implementation, `lt.flt` should make use of
       `return_boolean jb` instead (see https://www.felixcloutier.com/x86/ucomisd for more information).
   *)
  let numeric_ops =
    let numeric_op name flt_body rat_body body_wrapper =      
      make_binary name
        (body_wrapper
           ("mov dl, byte [rsi]
             cmp dl, T_FLOAT
	     jne ." ^ name ^ "_rat
             " ^ flt_body ^ "
             jmp .op_return
          ." ^ name ^ "_rat:
             " ^ rat_body ^ "
          .op_return:")) in      
    let arith_map = [
        "MAKE_RATIONAL(rax, rdx, rdi)
         mov PVAR(1), rax
         pop rbp
         jmp mul", "divsd", "div";
        
        "imul rsi, rdi
	 imul rcx, rdx", "mulsd", "mul";
        
        "imul rsi, rdx
	 imul rdi, rcx
	 add rsi, rdi
	 imul rcx, rdx", "addsd", "add";
      ] in
    let arith name flt_op rat_op =
      numeric_op name
        ("FLOAT_VAL rsi, rsi 
          movq xmm0, rsi
          FLOAT_VAL rdi, rdi 
          movq xmm1, rdi
	  " ^ flt_op ^ " xmm0, xmm1
          movq rsi, xmm0
          MAKE_FLOAT(rax, rsi)")
        ("DENOMINATOR rcx, rsi
	  DENOMINATOR rdx, rdi
	  NUMERATOR rsi, rsi
	  NUMERATOR rdi, rdi
          " ^ rat_op ^ "
          MAKE_RATIONAL(rax, rsi, rcx)") in
    let comp_map = [
        (* = *)
        return_boolean_eq,
        "NUMERATOR rcx, rsi
	 NUMERATOR rdx, rdi
	 cmp rcx, rdx
	 jne .false
	 DENOMINATOR rcx, rsi
	 DENOMINATOR rdx, rdi
	 cmp rcx, rdx
         .false:",
        "FLOAT_VAL rsi, rsi
	 FLOAT_VAL rdi, rdi
	 cmp rsi, rdi", "eq";

        (* < *)
        return_boolean "jl",
        "DENOMINATOR rcx, rsi
	 DENOMINATOR rdx, rdi
	 NUMERATOR rsi, rsi
	 NUMERATOR rdi, rdi
	 imul rsi, rdx
	 imul rdi, rcx
	 cmp rsi, rdi",
        "FLOAT_VAL rsi, rsi
	 movq xmm0, rsi
	 FLOAT_VAL rdi, rdi
	 movq xmm1, rdi
	 ucomisd xmm0, xmm1", "lt";
      ] in
    let comparator comp_wrapper name flt_body rat_body = numeric_op name flt_body rat_body comp_wrapper in
    (String.concat "\n\n" (List.map (fun (a, b, c) -> arith c b a (fun x -> x)) arith_map)) ^
      "\n\n" ^
        (String.concat "\n\n" (List.map (fun (a, b, c, d) -> comparator a d c b) comp_map));;


  (* The following set of operations contain fewer similarities, to the degree that it doesn't seem that 
     creating more fine-grained templates for them is beneficial. However, since they all make use of
     some of the other templates, it is beneficial to organize them in a structure that enables
     a uniform mapping operation to join them all into the final string.*)
  let misc_ops =
    let misc_parts = [
        (* string ops *)
        "STRING_LENGTH rsi, rsi
         MAKE_RATIONAL(rax, rsi, 1)", make_unary, "string_length";
        
        "STRING_ELEMENTS rsi, rsi
         NUMERATOR rdi, rdi
         add rsi, rdi
         mov sil, byte [rsi]
         MAKE_CHAR(rax, sil)", make_binary, "string_ref";
        
        "STRING_ELEMENTS rsi, rsi
         NUMERATOR rdi, rdi
         add rsi, rdi
         CHAR_VAL rax, rdx
         mov byte [rsi], al
         mov rax, SOB_VOID_ADDRESS", make_tertiary, "string_set";
        
        "NUMERATOR rsi, rsi
         CHAR_VAL rdi, rdi
         and rdi, 255
         MAKE_STRING rax, rsi, dil", make_binary, "make_string";
        
        "SYMBOL_VAL rsi, rsi
	 STRING_LENGTH rcx, rsi
	 STRING_ELEMENTS rdi, rsi
	 push rcx
	 push rdi
	 mov dil, byte [rdi]
	 MAKE_CHAR(rax, dil)
	 push rax
	 MAKE_RATIONAL(rax, rcx, 1)
	 push rax
	 push 2
	 push SOB_NIL_ADDRESS
	 call make_string
	 add rsp, 4*8
	 STRING_ELEMENTS rsi, rax   
	 pop rdi
	 pop rcx
	 cmp rcx, 0
	 je .end
         .loop:
	 lea r8, [rdi+rcx]
	 lea r9, [rsi+rcx]
	 mov bl, byte [r8]
	 mov byte [r9], bl
	 loop .loop
         .end:", make_unary, "symbol_to_string";

        (* the identity predicate (i.e., address equality) *)
        (return_boolean_eq "cmp rsi, rdi"), make_binary, "eq?";

        (* type conversions *)
        "CHAR_VAL rsi, rsi
	 and rsi, 255
	 MAKE_RATIONAL(rax, rsi, 1)", make_unary, "char_to_integer";

        "NUMERATOR rsi, rsi
	 and rsi, 255
	 MAKE_CHAR(rax, sil)", make_unary, "integer_to_char";

        "DENOMINATOR rdi, rsi
	 NUMERATOR rsi, rsi 
	 cvtsi2sd xmm0, rsi
	 cvtsi2sd xmm1, rdi
	 divsd xmm0, xmm1
	 movq rsi, xmm0
	 MAKE_FLOAT(rax, rsi)", make_unary, "exact_to_inexact";

        "NUMERATOR rsi, rsi
	 mov rdi, 1
	 MAKE_RATIONAL(rax, rsi, rdi)", make_unary, "numerator";

        "DENOMINATOR rsi, rsi
	 mov rdi, 1
	 MAKE_RATIONAL(rax, rsi, rdi)", make_unary, "denominator";

        (* GCD *)
        "xor rdx, rdx
	 NUMERATOR rax, rsi
         NUMERATOR rdi, rdi
       .loop:
	 and rdi, rdi
	 jz .end_loop
	 xor rdx, rdx 
	 div rdi
	 mov rax, rdi
	 mov rdi, rdx
	 jmp .loop	
       .end_loop:
	 mov rdx, rax
         MAKE_RATIONAL(rax, rdx, 1)", make_binary, "gcd";  
      ] in
    String.concat "\n\n" (List.map (fun (a, b, c) -> (b c a)) misc_parts);;


  let dorAndIdo=
    (*cons*)
    let cons=
      (*(make_binary label body)*)
      let label = "cons" in
      let body=
      "
        MAKE_PAIR (rax,rsi,rdi)\n
      "
      in (make_binary label body) 
    in
  
    let car=
      let label ="car" in
      let body=
        "
        CAR rax,rsi
        "
      in (make_unary label body)
    in
    let cdr=
      let label ="cdr" in
      let body=
        "
        CDR rax,rsi
        "
      in (make_unary label body)
    in
    let set_car=
      let label= "set_car" in
      let body=
        "
        mov rcx,rsi
        mov qword[rdi+TYPE_SIZE], rcx
        mov rax, SOB_VOID_ADDRESS
        " in
        (make_binary label body)
    in 
    let set_cdr=
      let label= "set_cdr" in
      let body=
        "
        mov rcx,rsi
        mov qword[rdi+TYPE_SIZE+WORD_SIZE], rcx
        mov rax, SOB_VOID_ADDRESS
        " in
        (make_binary label body)
  in



    let apply=
      let label="apply" in
      let body=
      "
      push rbp
      mov rbp, rsp 

apply_settingTheRBXtoTheList:
      push SOB_NIL_ADDRESS
      mov rbx, PARAM_COUNT
      sub rbx, 1; get to the last param
      add rbx, 4
      shl rbx, 3
      add rbx, rbp
apply_nowRBXpointsToList:

      ;rbx points to the list (last param)
      mov rcx,0
      mov rdi, qword[rbx]
      apply_LoopOverExtractListToStack:
      cmp rdi, SOB_NIL_ADDRESS
      je apply_EndOfLoopOverExtractListToStack
      CAR rsi, rdi
      push rsi
      CDR rsi,rdi
      mov rdi, rsi
      inc rcx
      jmp apply_LoopOverExtractListToStack

      apply_EndOfLoopOverExtractListToStack:


      ;update param count
      mov rax, PARAM_COUNT ; rax will hold forever paramcount
      mov rsi, qword [rbp+3*WORD_SIZE]
      add rsi, rcx
      sub rsi,2
      mov qword [rbp+3*WORD_SIZE], rsi
apply_afterUpdatePramaCount:

      mov rbx, rbp
      sub rbx, 2*WORD_SIZE
      mov rdx, rbp
      shl rcx,3
      sub rdx, 1*WORD_SIZE ; was 2 but count too much
      sub rdx, rcx
      shr rcx, 3 ;back to number of params in list 


      shr rcx, 1 ; for ido's algorithm

      apply_SwitchParamsOrderLoop:
      cmp rcx,0
      je apply_EndOfSwitchParamsOrderLoop
      mov rsi, qword [rbx]
      mov rdi, qword [rdx]
      mov qword[rdx], rsi
      mov qword[rbx], rdi
      dec rcx
      jmp apply_SwitchParamsOrderLoop

      apply_EndOfSwitchParamsOrderLoop:
      mov rcx, rax ; rax has the paramcount
      sub rcx,2

      mov rbx,0 ; for ido
      mov rbx, rax ; rax has the paramcount
      sub rbx,2
      add rbx, 4
      shl rbx,3
      add rbx, rbp
      
      apply_LoopForPushTheRestRegularArgs:
      cmp rcx,0
      je apply_EndOfLoopForPushTheRestRegularArgs
      mov rsi, qword[rbx]
      sub rbx, WORD_SIZE
      push rsi
      dec rcx
      jmp apply_LoopForPushTheRestRegularArgs

      apply_EndOfLoopForPushTheRestRegularArgs:
      push PARAM_COUNT

      mov rcx, qword[rbp+4*WORD_SIZE] ; mov rax the function clousre

      CLOSURE_ENV rbx,rcx
      push rbx ; push env
      CLOSURE_CODE rbx,rcx ; rbx has the address of the function we need to jump to, body inspector
      mov r8, rbx ; rdi has the address of the function we need to jump to, hot body

      
      mov rsi, qword[rbp+WORD_SIZE]
      push rsi ; push the ret address

      ;lets go get the old rbp
      mov rsi, qword[rbp] ; now rsi has old rbp
      push rsi ; push the old rbp

      apply_nowTheStackIsReady:
      apply_ApplicTPCode:

;switch the registes to fit with applic tp code




mov rcx, PARAM_COUNT ; now rcx has m
mov rsi, rcx
;as remembered rax holds the n from the beginning
mov rdi, rax; now rdi holds also n
; don't use fucking rsi!!!!!

add rax,5

add rcx,5
add rcx,1


mov rbx, 1 ; rbx is i

apply_ShiftLoop2:

cmp rbx, rcx
je apply_EndOfShiftLoop2

dec rax
haha1:
mov rdx, rbp
haha2:
shl rbx, 3
haha3:
sub rdx,rbx
haha4:
push qword [rdx]
haha5:
shr rbx, 3
haha6:

mov rdx,rbp
haha7:
shl rax, 3
haha8:
add rdx,rax
haha9:
pop qword [rdx]
haha10:
shr rax, 3

inc rbx
jmp apply_ShiftLoop2

apply_EndOfShiftLoop2:

;fix rbp and rsp


apply_checkMeeeeee:
mov rbx, rsi
add rbx, 5
shl rbx, 3


mov rcx, rsi ;assuming that rcx has m
shl rsi, 3
shl rcx, 3
shl rdi, 3

mov rdx, rsp
add rdx, 4*WORD_SIZE

add rdx, rsi
add rdx, WORD_SIZE ; magic
add rdx, 4*WORD_SIZE
add rdx, rdi
;assuming that rdx has the pointer to the top
apply_NOWRDXINTHETOP:

;assuming that we have magic
sub rdx, rcx
sub rdx, 4*WORD_SIZE
;now rdx points to oldrbp
apply_NOWRDXISOLDRBP:

mov rsp, rdx ;
mov rbp, rdx ;


apply_checkMeeeeee222:

pop rbp
jmp r8
      
      " in (label^":\n"^body)
  in String.concat "\n\n" [cons;car;cdr; set_car;set_cdr;apply];;
  
  (* This is the interface of the module. It constructs a large x86 64-bit string using the routines
     defined above. The main compiler pipline code (in compiler.ml) calls into this module to get the
     string of primitive procedures. *)
  let procs = String.concat "\n\n" [type_queries ; numeric_ops; misc_ops;dorAndIdo];;
end;;
