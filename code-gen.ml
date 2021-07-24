#use "semantic-analyser.ml";;
#use "exprs-to-string.ml"

(*Sexpr equality*)

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Fraction (n1, d1)), Number(Fraction (n2, d2)) -> n1 = n2 && d1 = d2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | _ -> false;;

let rec constant_eq e1 e2 =
    match e1, e2 with
    | Const Void, Const Void -> true
    | Const Void, Const (Sexpr(s1))-> false
    | Const (Sexpr(s1)), Const Void-> false
    | Const (Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
    | _ -> false;;

let rec constant_eq_tag e1 e2 =
      match e1, e2 with
      | Const' Void, Const' Void -> true
      | Const' Void, Const' (Sexpr(s1))-> false
      | Const' (Sexpr(s1)), Const' Void-> false
      | Const' (Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
      | _ -> false;;




exception X_Yalla_Party;;
exception X_not_a_string;;
exception X_Constant_not_in_table1;;
exception X_Constant_not_in_table2 of string;;
exception X_Constant_not_in_table3;;
exception X_double_void_in_consts_tbl;;
exception X_Var_not_in_fvars;;
exception X_no_match_for_putting_const_in_tbl of string;;
(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> int -> string*int



  (*
  Our function*)
  val extractString : 'a * 'b -> 'a 
  val extractInt : 'a * 'b -> 'b
end;;






module Code_Gen : CODE_GEN = struct


  (*****General*****)


  let rec append l1 l2 =
    match l1 with
    | h::t -> h :: append t l2
    | [] -> l2;;

  
(*****Consts******)
let rec getAllConstsFromOneSExp ast=
match ast with
  | Const'(c)-> [c]
  | Var'(VarParam(v,_))-> []
  | Var'(VarBound(v,_,_))-> []
  | Var'(VarFree(v))->[]
  | Box'(v)-> []
  | BoxGet' (v)-> []
  | BoxSet'(v,e)->(getConstFromOneExp e)
  | If'(tst,dit,dif)->(append (append (getConstFromOneExp tst) (getConstFromOneExp dit)) (getConstFromOneExp dif))
  | Seq'(explst)->(getListConsts explst)
  | Set'(v,e)-> (getConstFromOneExp e)
  | Def'(v,e)-> (getConstFromOneExp e)
  | Or'(explst)-> (getListConsts explst)
  | LambdaSimple'(strLst,exp)-> (getConstFromOneExp exp)
  | LambdaOpt'(strLst,str,exp)->(getConstFromOneExp exp)
  | Applic'(exp, explst)->  (append (getConstFromOneExp exp) (getListConsts explst))
  | ApplicTP'(exp, explst)-> (append (getConstFromOneExp exp) (getListConsts explst))

and getListConsts explst=
  let maped= (List.map (fun x-> (getConstFromOneExp x)) explst) in
  let flatMap= List.flatten maped in
  flatMap

and getConstFromOneExp ast=
match ast with
|Const'(Void)->[Void]
|Const'(Sexpr(sexp))-> (getAllConstsFromOneSExp ast)
|exp->(getAllConstsFromOneSExp exp) ;;



let rec getMeAllConsts asts lst= (*for each scheme expression*)
match asts with
|[]-> lst
|(x::y)-> (getMeAllConsts y (append lst (getAllConstsFromOneSExp x)));;


let rec deleteAllAccurencesConsts expToDelete oldLst newLst=
match oldLst with
|[]-> newLst
|(c1::rst)->  if ((constant_eq (Const(c1)) (Const(expToDelete)))=true)
                          then (deleteAllAccurencesConsts expToDelete rst newLst)
                          else (deleteAllAccurencesConsts expToDelete rst (append newLst [c1]));;

let rec removeConstsDuplicates constsList=
match constsList with
|[]-> []
|(c1::[])-> [c1]
|(c1::rst)-> (append [c1] (removeConstsDuplicates (deleteAllAccurencesConsts c1 rst [])));;


let rec checkOneConstForBasicDup c1 basicList=
match basicList with
|[]-> [c1]
|(x::y)-> if ((constant_eq (Const(c1)) (Const(x)))=true) then [] else (checkOneConstForBasicDup c1 y);;

let rec removeBasicsFromConstsList constsList newConstsList basicList=
match constsList with
|[]-> newConstsList
|(c1::rst)-> (removeBasicsFromConstsList rst (append newConstsList (checkOneConstForBasicDup c1 basicList)) basicList);;

let rec expandSingleSexp c1=
match c1 with
|Symbol(s)-> [Sexpr(String(s));Sexpr(Symbol(s))]
|Pair(x1,rst)->(append (append (expandSingleSexp x1) (expandSingleSexp rst)) [Sexpr(Pair(x1,rst))])
|els-> [Sexpr(els)]

and expandSingleConst c1=
match c1 with
|Void-> [Void]
|Sexpr(sexp)->expandSingleSexp(sexp);;

let rec expandCosnts cosntsList=
match cosntsList with
|[]-> []
|(c1::rst)-> (append (expandSingleConst c1) (expandCosnts rst));;

let getNewIndexSexp sexp index=
match sexp with
| Bool(b1)-> (index + 2)
| Nil-> (index + 1)
| Number(n1)->  (
                  match n1 with
                  |Fraction(r1,r2)-> (index+17)
                  |Float(f1)-> (index+9)
                )
| Char(c1)-> (index + 2)
| String(str1)-> ((String.length str1) + 9 + index)
| Symbol(sym1)-> (index + 9)
| Pair (x,y)-> (index+17);;

let getNewIndexConst const index=
match const with
|Void-> raise X_Constant_not_in_table1
|Sexpr(exp)-> (getNewIndexSexp exp index);;




let string_to_ascii_list str =
  let chars = string_to_list str in
  let asciis = List.map Char.code chars in
  let ascii_strs = List.map (Printf.sprintf "%d") asciis in
  (String.concat ", " ascii_strs);;



let rec getConstExpInTbl const_exp constsTbl=
  match constsTbl with
  |[]-> raise (X_Constant_not_in_table2 (string_from_expr' (Const'(const_exp))))
  |((exp1,(ind,titl))::y)-> if(constant_eq (Const(exp1)) (Const(const_exp))) then ind else (getConstExpInTbl const_exp y);;


  let makeOurLiteralString charLstString index=
  "
  db T_STRING
  dq (end_str"^(string_of_int index)^" - str"^(string_of_int index)^")
  
  str"^(string_of_int index)^":
  db "^charLstString^"\n
  end_str"^(string_of_int index)^":
  ";;


let createOneTbl3Tuple sexp index tblListSoFar=
match sexp with
|Sexpr(String(str))-> (sexp, (index, (makeOurLiteralString (string_to_ascii_list str) index)))                 
|Sexpr(Number(Float(f)))-> (sexp,(index, (Printf.sprintf "MAKE_LITERAL_FLOAT (%f)" f)))
|Sexpr(Number(Fraction(n1,n2)))-> (sexp, (index,((Printf.sprintf "MAKE_LITERAL_RATIONAL (%d,%d)") n1 n2)  ))
|Sexpr(Char(ch))-> (sexp,(index, (Printf.sprintf "MAKE_LITERAL_CHAR(%d)" (Char.code ch))))
|Sexpr(Pair(car,cdr))-> (sexp, (index, (Printf.sprintf "MAKE_LITERAL_PAIR (const_tbl+%d, const_tbl+%d)" (getConstExpInTbl (Sexpr(car)) tblListSoFar) (getConstExpInTbl (Sexpr(cdr)) tblListSoFar))))
|Sexpr(Symbol(sym))-> (sexp,(index, (Printf.sprintf "MAKE_LITERAL_SYMBOL(const_tbl+%d)" (getConstExpInTbl (Sexpr(String(sym))) tblListSoFar))))
|els-> raise (X_no_match_for_putting_const_in_tbl "");;





let rec createTblFromExpandConstsSet constsLst tblLst index=
match constsLst with
|[]-> tblLst
|(x::y)-> (createTblFromExpandConstsSet y (append tblLst [(createOneTbl3Tuple x index tblLst)]) (getNewIndexConst x index));;


let make_consts_tbl2 asts=
(*Table of constants*)
  [ 
    (Void,                                (0, "db T_VOID"));
    ((Sexpr Nil),                         (1, "db T_NIL"));
    ((Sexpr (Bool false)),                (2, "db T_BOOL,0"));
    ((Sexpr (Bool true)),                 (4, "db T_BOOL,1"))
  ];;


let printMyConstsTbl=
print_string ""

(*make_consts_tbl [Semantics.run_semantics (List.hd (tag_parse_expressions (read_sexprs "'a")))];;*)

let make_consts_tbl asts = 
let basicList=[Void;Sexpr(Nil) ;Sexpr(Bool(false));Sexpr(Bool(true))] in (*List of Constants*)
let basicConsts= (*Table of constants*)
  [ 
    (Void,                    (0, "db T_VOID"));
    ((Sexpr Nil),             (1, "db T_NIL"));
    ((Sexpr (Bool false)),    (2, "db T_BOOL,0"));
    ((Sexpr (Bool true)),     (4, "db T_BOOL,1"))
  ] in 
  

let allConstsFromAsts=(getMeAllConsts asts []) in (*List of constatns-> remove the "Const" from the expr*)
(*List.map (fun(x)-> (print_string ((string_from_constant x)^"\n"))) allConstsFromAsts;*)
(*print_string "\n";*)
let allConstsFromAstsSet= (removeConstsDuplicates allConstsFromAsts) in (*Set of Void\Sexprs*)
(*List.map (fun(x)-> (print_string ((string_from_constant x)^"\n"))) allConstsFromAstsSet;*)
(*print_string "\n";*)
let expandConstsFromAsts= (expandCosnts allConstsFromAstsSet) in
(*List.map (fun(x)-> (print_string ((string_from_constant x)^"\n"))) expandConstsFromAsts;*)
(*print_string "\n";*)
let expandConstsFromAstNoBasics= (removeBasicsFromConstsList expandConstsFromAsts [] basicList) in
(*List.map (fun(x)-> (print_string ((string_from_constant x)^"\n"))) expandConstsFromAstNoBasics;*)
(*print_string "\n";*)
let expandConstsFromAstsSet= (removeConstsDuplicates expandConstsFromAstNoBasics) in

(*(print_string ((string_from_constant x)^"\n"))*)
(*List.map (fun(x)-> (print_string ((string_from_constant x)^"\n"))) expandConstsFromAstsSet;*)
let constsTblFromCode= (createTblFromExpandConstsSet expandConstsFromAstsSet basicConsts 6) (*4 because of the basic consts comming before*) in
(*List.map (fun(const ,(number,str))-> (print_string (Printf.sprintf "%s , (%d, %s)" (string_from_constant const) number str))) constsTblFromCode; (***Debug-> use print!!****)*)
(*print_string (string_of_int (List.length constsTblFromCode));*)
constsTblFromCode;; 




(***********Fvars***********)
let rec assignIndexesAndMakeFvarsLines fvars_lst fvars_tbl startIndex=
  match fvars_lst with
  |[]-> fvars_tbl
  |(x::y)-> (assignIndexesAndMakeFvarsLines y (append fvars_tbl [(x,startIndex)]) (startIndex+1));;

  

  let rec getMeAllFvarsFromOneExp exp lst=
  
  match exp with
  | Const'(c)-> lst
  | Var'(VarParam(v,_))-> lst
  | Var'(VarBound(v,_,_))-> lst
  | Var'(VarFree(v))->(append lst [v])
  | Box'(v)-> (getMeAllFvarsFromOneExp (Var'(v)) lst)
  | BoxGet' (v)-> (getMeAllFvarsFromOneExp (Var'(v)) lst)
  | BoxSet'(v,e)->(append lst (append (getMeAllFvarsFromOneExp (Var'(v)) []) (getMeAllFvarsFromOneExp e []))) 
  | If'(tst,dit,dif)->(append lst (append (getMeAllFvarsFromOneExp tst []) (append (getMeAllFvarsFromOneExp dit []) (getMeAllFvarsFromOneExp dif []))))
  | Seq'(explst)-> (append lst (getListfVars explst))
  | Set'(v,e)-> (append lst (append (getMeAllFvarsFromOneExp (Var'(v)) []) (getMeAllFvarsFromOneExp e []))) 
  | Def'(v,e)-> (append lst (append (getMeAllFvarsFromOneExp (Var'(v)) []) (getMeAllFvarsFromOneExp e []))) 
  | Or'(explst)-> (append lst (getListfVars explst))
  | LambdaSimple'(strLst,exp)-> (append lst (getMeAllFvarsFromOneExp exp []))
  | LambdaOpt'(strLst,str,exp)->(append lst (getMeAllFvarsFromOneExp exp []))
  | Applic'(exp, explst)-> (append lst (append (getMeAllFvarsFromOneExp exp []) (getListfVars explst)))
  | ApplicTP'(exp, explst)-> (append lst (append (getMeAllFvarsFromOneExp exp []) (getListfVars explst)))

  and getListfVars explst=
  let maped= (List.map (fun x-> (getMeAllFvarsFromOneExp x [])) explst) in
  let flatMap= List.flatten maped in
  flatMap;;
  

let rec getMeAllFvars asts lst=
match asts with
|[]-> (List.flatten lst)
|(x::y)-> (getMeAllFvars y (append lst [getMeAllFvarsFromOneExp x []]));;


let rec deleteAllAccurences nameToDelet oldLst newLst=
match oldLst with
|[]-> newLst
|((name1,index1)::rst)->  if (name1=nameToDelet)
                          then (deleteAllAccurences nameToDelet rst newLst)
                          else (deleteAllAccurences nameToDelet rst (append [(name1,index1)] newLst));;

let rec reduceDupsFvars fvarsTbl=
match fvarsTbl with
|[]-> []
|((name1,index1)::[])-> [(name1,index1)]
|((name1,index1)::rst)-> (append [(name1,index1)] (reduceDupsFvars (deleteAllAccurences name1 rst [])));;

(*#fvars*)
let make_fvars_tbl asts = 
  let primitiveFvars= [


                        "cons"
                        ;"car"
                        ;"cdr"
                        ;"set-car!"
                        ;"set-cdr!"
                        ;"apply"
                        ;"boolean?"
                        ; "flonum?"
                        ; "rational?"
                        ; "pair?"
                        ; "null?"
                        ; "char?"
                        ; "string?"
                        ; "procedure?"
                        ; "symbol?"
                        ;
                        (* String procedures *)
                        "string-length"
                        ; "string-ref"
                        ; "string-set!"
                        ; "make-string"
                        ; "symbol->string"
                        ;
                        (* Type conversions *)
                        "char->integer"
                        ; "integer->char"
                        ; "exact->inexact"
                        ;
                        (* Identity test *)
                        "eq?"
                        ;
                        (* Arithmetic ops *)
                        "+"
                        ; "*"
                        ; "/"
                        ; "="
                        ; "<"
                        ;
                        (* Additional rational numebr ops *)
                        "numerator"
                        ; "denominator"
                        ; "gcd"
                      ] in

  let primitivesInTbl= (assignIndexesAndMakeFvarsLines primitiveFvars [] 0) in
  let fvarsFromCode= (getMeAllFvars asts []) in
  let fvarsTblFromCode= (assignIndexesAndMakeFvarsLines fvarsFromCode [] (List.length primitivesInTbl)) in
  let fvarsFromCodeNoDups= (reduceDupsFvars fvarsTblFromCode ) in
  let primitivsAndCodeFvars= (append primitivesInTbl fvarsFromCodeNoDups) in
  (reduceDupsFvars primitivsAndCodeFvars)

    



(***Code generate**)

let extractString couple=
match couple with
|(str,num)-> str
|_-> raise X_not_a_string;;

let extractInt couple=
match couple with
|(str,num)-> num
|_-> raise X_not_a_string;;  

let rec getConstFromTbl con constsTbl=
match constsTbl with
|[]-> raise X_Constant_not_in_table3
|((cnst, (num, str))::rst) -> if (constant_eq_tag (Const'(cnst)) (Const'(con))) then num else (getConstFromTbl con rst);;

 
let rec lableInFVarTable fvars var=
match fvars with
|[]-> raise X_Var_not_in_fvars
|((v,num)::rst)-> if (v=var) then (string_of_int (num*8)) else (lableInFVarTable rst var);;

let rec our_generate consts fvars e index depthIndex=
  match e with
  
  |Var'(VarParam(_,minor))-> ((";Var'(VarParam()) \n mov rax, qword [rbp + 8 * (4+" ^ (string_of_int minor) ^")] \n"),index)
  |Const'(c)-> ((";Const\n mov rax, const_tbl+" ^ (string_of_int (getConstFromTbl c consts)) ^"\n"),index)
  |Set'(VarParam(_,minor), epsilon)->   ((fun (coup)-> ((
                                                        ";Set'(VarParam)\n" ^
                                                        (extractString coup)^
                                                        "mov qword [rbp + 8 * (4 +" ^ 
                                                        (string_of_int minor) ^
                                                        ")], rax \n"^
                                                        "mov rax, SOB_VOID_ADDRESS\n"), (extractInt coup))) (our_generate consts fvars epsilon index depthIndex))
  |Var'(VarBound(_,major,minor))->  ((";Var'(VarBound)\n "^
                                      "mov rax, qword [rbp+8*2]\n"^
                                    "mov rax, qword [rax+8*"^
                                    (string_of_int major)^
                                    "]\n"^
                                    "mov rax, qword [rax+8*"^
                                    (string_of_int minor)^
                                    "]\n"),index)
  |Set'(VarBound (_, major, minor),epsilon)->
                                    ((fun (coup)-> ((
                                        ";Set'(VarBound)\n"^
                                        (extractString coup)^
                                        "mov rbx, qword [rbp+8*2]"^
                                        "mov rbx, qword [rbx+8*"^
                                        (string_of_int major)^
                                        "]\n"^
                                        "mov qword [rbx + 8 *"^
                                        (string_of_int minor)^
                                        "], rax\n"^
                                        "mov rax, SOB_VOID_ADDRESS\n
                                        ;-----------------------EndOfSet----------\n"
                                        ), (extractInt coup))) (our_generate consts fvars epsilon index depthIndex))
  |Var'(VarFree(v))-> ((";Var'(VarFree) \n mov rax, [fvar_tbl+ " ^ (lableInFVarTable fvars v) ^"] \n"),index)
  |Set'(VarFree(v), epsilon)->  ((fun(coup)-> ((
                                    ";Set'(VarFree)\n"^
                                    (extractString coup)^
                                    "mov qword [fvar_tbl+"^ (lableInFVarTable fvars v) ^
                                    "], rax \n "^
                                    "mov rax, SOB_VOID_ADDRESS\n
                                    ;-----------------------EndOfSet----------\n"
                                          ), (extractInt coup))) (our_generate consts fvars epsilon index depthIndex))
  | Seq'(lst)-> (handleSeq lst index consts fvars ";Seq'\n" depthIndex)
  | Or' (lst)-> (handleOr lst (index+1) consts fvars ";Or'\n" index depthIndex)
  | If'(tst,dit,dif)->(handleIf tst dit dif (index+1) fvars consts index index depthIndex)
  | Def' (VarFree(v),exp)-> ((fun(coup)-> ((
                                    ";Def\n"^
                                    (extractString coup)^
                                    "mov qword [fvar_tbl+"^ (lableInFVarTable fvars v) ^
                                    "], rax \n "^
                                    "mov rax, SOB_VOID_ADDRESS
                                    ;-----------------------EndOfDef----------\n
                                    "
                                          ), (extractInt coup))) (our_generate consts fvars exp index depthIndex))
  | LambdaSimple' (args,bdy)-> (handleLambdaSimple args bdy consts fvars index depthIndex)
  | Applic'(operator,operands)->(handleApplic operator operands consts fvars index depthIndex)
  | Box'(var)->   ((fun(coup)->
                    (
                      ";Box(var)
                      mov rbx, SOB_NIL_ADDRESS
                      push rbx\n"^
                      (extractString coup)^
                    "      
                      push rax
                      

                      push 2
                      mov rax, [fvar_tbl+ "^ (lableInFVarTable fvars "cons")^"] 

                      CLOSURE_ENV rbx,rax
                      push rbx
                      CLOSURE_CODE rbx,rax
                      call rbx

                      add rsp, 8 ; pop env
                      pop rbx ; pop arg count
                      shl rbx,3 ;rbx=rbx*8
                      add rsp, rbx; pop args
                      ;-----------------------EndOfBox----------\n
                    "),(extractInt coup))
                    (our_generate consts fvars (Var'(var)) index depthIndex))
    
  |BoxGet'(var)-> ((fun(coup)->
                    ((";BoxGet\n
                    "^
                    (extractString coup)^
                    "
                      push rax
                      push 1
                      mov rax, [fvar_tbl+ "^ (lableInFVarTable fvars "car")^"] 

                      CLOSURE_ENV rbx,rax
                      push rbx
                      CLOSURE_CODE rbx,rax
                      call rbx

                      add rsp, 8 ; pop env
                      pop rbx ; pop arg count
                      shl rbx,3 ;rbx=rbx*8
                      add rsp, rbx; pop args
                      ;-----------------------EndOfBoxGet----------\n
                    "),(extractInt coup)))
                    (our_generate consts fvars (Var'(var)) index depthIndex))
  |BoxSet'(var,exp)->(
                        (fun(coup_var)->
                          (fun(coup_exp)->
                          ((
                          ";BoxSet\n                          
                          
                          "^
                          (extractString coup_var)^
                          "
                            push rax ; push Var address
                          "
                          ^(extractString coup_exp)^
                          "
                            push rax ; push exp

                            push 2
                            mov rax, [fvar_tbl+ "^ (lableInFVarTable fvars "set-car!")^"] 

                            CLOSURE_ENV rbx,rax
                            push rbx
                            CLOSURE_CODE rbx,rax
                            call rbx

                            add rsp, 8 ; pop env
                            pop rbx ; pop arg count
                            shl rbx,3 ;rbx=rbx*8
                            add rsp, rbx; pop args
                            ;-----------------------EndOfSet----------\n
                          "),(extractInt coup_exp)))
                          (our_generate consts fvars exp (extractInt coup_var) depthIndex)
                      )(our_generate consts fvars (Var'(var)) index depthIndex))

  |LambdaOpt'(args,str,bdy)->(handleLambdaOpt args bdy consts fvars index depthIndex)
  |ApplicTP'(operator, operands)-> (handleApplicTP operator operands consts fvars index depthIndex)

  |_-> raise X_Yalla_Party

(*
and handleCreateBox var consts fvars index depthIndex=
let theVar= (extractString (our_generate var consts fvars index depthIndex))
*)



and handleApplicTP operator operands consts fvars index depthIndex=
let pushMagic= "push SOB_NIL_ADDRESS\n" in
let operandsHandle= (handleOperands operands consts fvars index depthIndex "") in
let operandsString= (extractString operandsHandle) in
let afterOperandsString= 
" 
      push "^ (string_of_int (List.length operands))^"\n
" in
let convertProc=(our_generate consts fvars operator (extractInt operandsHandle) depthIndex) in
let procString= (extractString convertProc) in
let indexAfterProc= (extractInt convertProc) in
let afterProcString=
"

CLOSURE_ENV rbx,rax
push rbx ; push env
CLOSURE_CODE rbx,rax ; rbx has the address of the function we need to jump to, body inspector
mov rdi, rbx ; rdi has the address of the function we need to jump to, hot body

mov rsi, qword[rbp+WORD_SIZE]
push rsi ; push the ret address


;lets go get the old rbp
mov rsi, qword[rbp] ; now rsi has old rbp
push rsi ; push the old rbp



mov rax, PARAM_COUNT ; rax is n
mov r8, rax
add rax,5
mov rcx,"^(string_of_int (List.length operands))^" ; rcx is m
add rcx,5
add rcx,1

mov rbx, 1 ; rbx is i
ShiftLoop"^(string_of_int indexAfterProc)^":\n
cmp rbx, rcx
je EndOfShiftLoop"^(string_of_int indexAfterProc)^"\n
dec rax

mov rdx, rbp
shl rbx, 3
sub rdx,rbx
push qword [rdx]
shr rbx, 3


mov rdx,rbp
shl rax, 3
add rdx,rax
pop qword [rdx]
shr rax, 3

inc rbx
jmp ShiftLoop"^(string_of_int indexAfterProc)^"\n
EndOfShiftLoop"^(string_of_int indexAfterProc)^":\n

add r8,5
shl r8,3
add rsp, r8 ; 0= n
add rbp, r8 ; 0= n 

pop rbp
jmp rdi ; jump to the body of the new function
;-----------------------ApplicTP----------\n
" in
let allApplicCode= ";ApplicTP\n"^pushMagic ^operandsString^afterOperandsString^procString^afterProcString in
(allApplicCode, (indexAfterProc+1))




and handleLambdaOpt args bdy cosntsTbl fvars index depthIndex=
let beforeBody= 
"
    ;LambdOpt
    ;
    ;
    ;
    ;
    ;bdy: "^(string_from_expr' bdy)^"\n
    ;args: "^(String.concat "," args)^"\n
    ;
    ;
    ;

    ;Allocate the ExtEnv (the size of which is known statically and is 1 + |Env|)
    mov rbx, " ^ (string_of_int (depthIndex+1))^"\n
    shl rbx,3 ;multiply by word size
    MALLOC rbx,rbx
    ;rbx= pointer to Major Vector
    mov rsi,0
    mov rdi,1
    mov rcx, [rbp+2*WORD_SIZE] ; rcx points to env vector
    
    ;First for loop
    ExtEnvLoop"^(string_of_int index)^":\n
    cmp rsi, "^(string_of_int depthIndex)^"\n
    je EndOfExtEnvLoop"^(string_of_int index)^"\n
    shl rsi,3
    shl rdi,3
    mov rdx, [rcx+rsi]
    mov qword [rbx+rdi], rdx
    shr rsi,3
    shr rdi,3
    inc rdi
    inc rsi
    jmp ExtEnvLoop"^(string_of_int index)^"\n
    EndOfExtEnvLoop"^(string_of_int index)^":\n

    ;Allocate ExtEnv[0] to point to a vector where to store the parameters
    mov rcx, PARAM_COUNT
    shl rcx, 3
    MALLOC rcx, rcx
    mov qword[rbx+0],rcx

    ;Second for copy the parameters off the stack
    mov rdi,0
    CopyParametersLoop"^(string_of_int index)^":\n
    cmp rdi, PARAM_COUNT
    je EndCopyParametersLoop"^(string_of_int index)^"\n
    mov rdx,[rbp+(4+rdi)*WORD_SIZE]
    mov qword[rcx+rdi],rdx
    inc rdi
    jmp CopyParametersLoop"^(string_of_int index)^"\n
    EndCopyParametersLoop"^(string_of_int index)^":\n

    ;Allocate the closure object
    MAKE_CLOSURE (rax,rbx,lambda_body"^(string_of_int index)^" )\n
    jmp Lcont"^(string_of_int index)^"\n
" in
let coup= (our_generate cosntsTbl fvars bdy (index +1) (depthIndex+1)) in
let indexAfterCalcBody= (extractInt coup) in
let fixStackOperands=
"
mov rbx, "^(string_of_int (List.length args))^"\n
mov rcx, PARAM_COUNT
cmp rcx,rbx
jg ClassicHandleLambdaOpt"^(string_of_int index)^"\n
;Case: ParamCount= argCount
jmp EndOfFixLambdaOptOperands"^(string_of_int index)^"\n

ClassicHandleLambdaOpt"^(string_of_int index)^":\n
;fix rdx to point to the bottom of the frame
mov rdx, rbp
add rdx, 4*WORD_SIZE ; skip old rbp,ret,env,paramCount
mov rsi, PARAM_COUNT
shl rsi,3
add rdx,rsi
sub rdx, WORD_SIZE

;rcx has param count
sub rcx, "^(string_of_int (List.length args))^"\n
;rcx has the number of loop iterations

mov rbx, 0
mov rsi, SOB_NIL_ADDRESS ; init the loop


LoopForHandleOptClassic"^(string_of_int index)^":\n
cmp rbx,rcx
je EndOfLoopForHandleOptClassic"^(string_of_int index)^"\n
shl rbx,3         ; multiply by word size
mov rax,rdx
sub rax,rbx
mov rdi,qword[rax]
mov rax, rsi; rax has the old pair


push rax
push rbx
push rcx
push rdx
push rdi

MAKE_PAIR (rsi, rdi, rax)

pop rdi
pop rdx
pop rcx
pop rbx
pop rax



;rsi has the new pair
shr rbx,3         ;back to be counters
inc rbx
jmp LoopForHandleOptClassic"^(string_of_int index)^"\n





EndOfLoopForHandleOptClassic"^(string_of_int index)^":\n
mov rbx, rbp
mov rdx, PARAM_COUNT
mov rax, PARAM_COUNT
sub rdx,1 ; always 1, keep the last one for the list
shl rdx,3
add rbx, 4*WORD_SIZE ; skip oldRbp, ret, env, count
add rbx, rdx ; rbx= rbp+4*WordSize+ParamCount-1 => the last param on the stack


mov qword[rbx],rsi

mov rcx,"^(string_of_int (List.length args))^"\n
add rcx,4   ; always: oldRbp, ret,env,count

mov rbx,rbp
add rbx,4*8          ; always: oldRbp, ret,env,count
mov rdx, PARAM_COUNT ; 
shl rdx,3
add rbx,rdx  ; rbx= rbp+ WordSize*ParamCount
sub rbx, WORD_SIZE*2 ; 2 always, for the magic and last position => gets to the last param on stack   

mov rdi,rbp
add rdi,4*8          ; always: oldRbp, ret,env,count
add rdi,"^(string_of_int (List.length args))^"*8 ; number of args, from ocaml
sub rdi,1*8 ; always, to get to the right one

loopLoop"^(string_of_int index)^":
cmp rcx,0
je endLoopLoop"^(string_of_int index)^"
mov rsi, [rdi]
mov qword[rbx],rsi
sub rbx,WORD_SIZE
sub rdi,WORD_SIZE
dec rcx
jmp loopLoop"^(string_of_int index)^"
endLoopLoop"^(string_of_int index)^":

sub rax,"^(string_of_int (1+(List.length args)))^" ; rax saved PARAM_COUNT, now rax= PARAM_COUNT-3: where 3 is (args.length+1) from ocaml
shl rax,3
add rbp, rax
add rsp, rax

mov qword[rbp+3*WORD_SIZE],"^(string_of_int (1+(List.length args)))^" ; depends on code ; from ocaml
EndOfFixLambdaOptOperands"^(string_of_int index)^":
" in
let bodyString= (extractString coup) in
let indexAfterBody= (extractInt coup) in
let afterParty= 
"
      lambda_body"^(string_of_int index)^":\n
        push rbp
        mov rbp,rsp\n"^
        fixStackOperands^
        bodyString^"
        leave
        ret
      Lcont"^(string_of_int index)^":\n
      ;-----------------------EndOfLambdaOpt"^(string_of_int index)^"----------\n
" in
let allCodeToReturn= beforeBody ^ afterParty in
(allCodeToReturn,(indexAfterBody))


and handleLambdaSimple args bdy cosntsTbl fvars index depthIndex=
let beforeBody= 
"
    ;LambdaSimple\n
    ;
    ;
    ;
    ;
    ;bdy: "^(string_from_expr' bdy)^"\n
    ;args: "^(String.concat "," args)^"\n
    ;
    ;
    ;
        

    ;Allocate the ExtEnv (the size of which is known statically and is 1 + |Env|)

    mov rbx, " ^ (string_of_int (depthIndex+1))^"\n
    shl rbx,3 ;multiply by word size
    MALLOC rbx,rbx
    ;rbx= pointer to Major Vector
    mov r10,rbx
    mov rsi,0
    mov rdi,1
    mov rcx, [rbp+2*WORD_SIZE] ; rcx points to env vector
    cmp rcx, SOB_NIL_ADDRESS
    je globalEnvCopy"^(string_of_int index)^"\n
    


    ;First for loop
    ExtEnvLoop"^(string_of_int index)^":\n
    cmp rsi, "^(string_of_int depthIndex)^"\n
    je EndOfExtEnvLoop"^(string_of_int index)^"\n
    shl rsi,3
    shl rdi,3
    mov rdx, [rcx+rsi]
    mov qword [rbx+rdi], rdx
    shr rsi,3
    shr rdi,3
    inc rdi
    inc rsi
    jmp ExtEnvLoop"^(string_of_int index)^"\n
    EndOfExtEnvLoop"^(string_of_int index)^":\n

    ;Allocate ExtEnv[0] to point to a vector where to store the parameters
    mov rcx, PARAM_COUNT
    shl rcx, 3
    MALLOC rcx, rcx
    mov qword[rbx+0],rcx
    mov r11,qword[rbx]

    ;Second for copy the parameters off the stack
    mov rdi,0
    CopyParametersLoop"^(string_of_int index)^":\n
    cmp rdi, PARAM_COUNT
    je EndCopyParametersLoop"^(string_of_int index)^"\n
    mov rdx,[rbp+(4+rdi)*WORD_SIZE]
    mov qword[rcx+(rdi*WORD_SIZE)],rdx
    inc rdi
    jmp CopyParametersLoop"^(string_of_int index)^"\n
    EndCopyParametersLoop"^(string_of_int index)^":\n
    jmp Allocation"^(string_of_int index)^"\n


    globalEnvCopy"^(string_of_int index)^":\n
    mov qword[rbx],0


    Allocation"^(string_of_int index)^":
    ;Allocate the closure object
    mov r11, qword[rbx]
    MAKE_CLOSURE (rax,rbx,lambda_body"^(string_of_int index)^" )\n
    jmp Lcont"^(string_of_int index)^"\n
" in
let coup= (our_generate cosntsTbl fvars bdy (index +1) (depthIndex+1)) in
let bodyString= (extractString coup) in
let newTitleIndex= (extractInt coup) in
let afterParty= 
"
      lambda_body"^(string_of_int index)^":\n
        push rbp
        mov rbp,rsp\n"^
        bodyString^"
        leave
        ret
      Lcont"^(string_of_int index)^":\n
      ;-----------------------EndOfLambdaSimple"^(string_of_int index)^"----------\n
" in
let allCodeToReturn= beforeBody ^ afterParty in
(allCodeToReturn,newTitleIndex)

and handleApplic operator operands consts fvars index depthIndex=
let pushMagic= "push SOB_NIL_ADDRESS\n" in
let operandsHandle= (handleOperands operands consts fvars index depthIndex "") in
let operandsString= (extractString operandsHandle) in
let afterOperandsString= 
" 
      push "^ (string_of_int (List.length operands))^"\n
" in
let convertProc=(our_generate consts fvars operator (extractInt operandsHandle) depthIndex) in
let procString= (extractString convertProc) in
let afterProcString=
"
CLOSURE_ENV rbx,rax
push rbx
CLOSURE_CODE rbx,rax
call rbx
" in
let afterCallProc=
"
add rsp, 8 ; pop env
pop rbx ; pop arg count
shl rbx,3 ;rbx=rbx*8
add rsp, rbx; pop args
add rsp,8 ; pop out magic
" in
let allApplicCode= ";Applic\n"^pushMagic ^operandsString^afterOperandsString^procString^afterProcString^afterCallProc^";-----------------------EndOfApplic"^(string_of_int index)^"----------\n" in
(allApplicCode, (extractInt convertProc))

and handleOperands operands consts fvars index depthIndex allStr=
match operands with
|[]-> (allStr, index)
|(exp::rst)-> (
              (fun (coup)->
                (handleOperands rst consts fvars (extractInt coup) depthIndex ( ((extractString coup)^"push rax\n")^allStr))
              )(our_generate consts fvars exp index depthIndex)
              )


and handleSeq lst index consts fvars str deindex=
match lst with
|[]-> (str,index)
|(x::y)-> ((fun (coup)-> (handleSeq y (extractInt coup) consts fvars (str^(extractString coup)) deindex)) (our_generate consts fvars x index deindex))

and handleOr lst indexAferLabels consts fvars str originalIndexForLables deindex=
match lst with
|[]-> ((str^"\nLexit"^(string_of_int originalIndexForLables))^":\n",indexAferLabels)
|(x::y)-> ((fun (coup)-> (handleOr
                          y 
                          (extractInt coup) 
                          consts 
                          fvars 
                          (
                            str^(extractString coup)^
                            "cmp rax, SOB_FALSE_ADDRESS\n"^
                            "jne Lexit"^(string_of_int originalIndexForLables) ^" \n"                             
                          )
                          originalIndexForLables
                          deindex
                          )) (our_generate consts fvars x indexAferLabels deindex))


and handleIf tst dit dif index fvars constsTbl exitIndex elseIndex deindex=
(
  (fun (coup2)->
    (fun(coup3)-> 
      (fun (coup4)->
        (
          ((extractString coup2)^
          (extractString coup3)^
          (extractString coup4),(extractInt coup4))
        )
      )
      (handleDif dif fvars constsTbl exitIndex elseIndex (extractInt coup3) deindex)        
    )
    (handleDit dit fvars constsTbl exitIndex elseIndex (extractInt coup2) deindex)
  )
  (handleTst tst fvars constsTbl exitIndex elseIndex index deindex)
)

and handleTst tst fvars constsTbl exitIndex elseIndex index deindex=
( (fun (coup)-> 
      (((extractString coup)^
      "cmp rax, SOB_FALSE_ADDRESS\n"
      ^"je Lelse"^(string_of_int elseIndex)^"\n"),
      ((extractInt coup) + 1))
  )
(our_generate constsTbl fvars tst index deindex))

and handleDit dit fvars constsTbl exitIndex elseIndex index deindex=
( (fun (coup)-> 
      (((extractString coup)^
      "jmp Lexit"^(string_of_int exitIndex)^"\n"),
      ((extractInt coup) + 1))
  )
(our_generate constsTbl fvars dit index deindex))


and handleDif dif fvars constsTbl exitIndex elseIndex index deindex=
( (fun (coup)-> 
  
    (("Lelse"^(string_of_int elseIndex)^":\n"^
    (extractString coup)^
    "Lexit" ^(string_of_int exitIndex) ^":\n"),
    ((extractInt coup) + 1))
  )
(our_generate constsTbl fvars dif index deindex));;


(***Final***)
let generate consts fvars e index= 
      (our_generate consts fvars e index 0);;

end;;

