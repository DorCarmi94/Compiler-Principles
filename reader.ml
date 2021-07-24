
#use "pc.ml";;
open PC;;
exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
exception X_idodo1;;
exception X_idodo2;;
exception X_idodo33;;
exception X_idodo4;;
exception X_this_should_not_happen;;
exception X_I_am_here;;

 

type number =
  | Fraction of int * int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr;;

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

  
  let rec append l1 l2 =
    match l1 with
    | h::t -> h :: append t l2
    | [] -> l2;;
  
module Reader: sig
  (*Signatures*)
  val read_sexprs : string -> sexpr list

end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;


let rec debugPrint string=
match string with
|[]->let ddd= Printf.printf("\n") in ""
|(x::y)-> let dd= (Printf.printf "%c" x) in (debugPrint y);;



(*Tokens:*)

(*Basics*)
let digit = range '0' '9';;


(*Boolean*)


(*TODO: check about warning*)
let idodo_sulamit=char '#';;
let idodo_truesFalesString=one_of "tTfF";;
let idodo_bool= caten idodo_sulamit idodo_truesFalesString;;
let parse_bool= pack idodo_bool (  fun (a, b) -> match b with
                                  | 't' -> Bool(true)
                                  | 'T' -> Bool(true)
                                  | 'f' -> Bool(false)
                                  | 'F' -> Bool(false)
                                  |_-> raise X_idodo1);;


let emptyString= word_ci "j";;
let parse_nada=
pack emptyString (fun(lst)-> Nil);;

(*Char prefix*)
let idodo_slash= char '\092';;

let idodo_charPrefix=caten idodo_sulamit idodo_slash;;

(*Visible simple char*)
let idodo_vis_chars= range '!' '~';;



(*NamedChar*)

let idodo_NamedChar_newLine = pack (word_ci "newline") (fun (x)-> (char_of_int 10));;

let idodo_NamedChar_nul     = pack (word_ci "nul"     ) (fun (x) -> (char_of_int 0))    ;;
let idodo_NamedChar_page    = pack (word_ci "page"    ) (fun (x) -> (char_of_int 12))    ;;
let idodo_NamedChar_return  = pack (word_ci "return"  ) (fun (x) -> (char_of_int 13))    ;;
let idodo_NamedChar_space   = pack (word_ci "space"   ) (fun (x) -> (char_of_int 32))    ;;
let idodo_NamedChar_tab     = pack (word_ci "tab"     ) (fun (x) -> (char_of_int 9))    ;;

let idodo_NamedChar= disj_list [ idodo_NamedChar_newLine;
                                    idodo_NamedChar_nul;
                                    idodo_NamedChar_page;  
                                    idodo_NamedChar_return;
                                    idodo_NamedChar_space ;
                                    idodo_NamedChar_tab ];;  


(*Char*)

let parse_char= pack (caten idodo_charPrefix
                      (disj 
                        idodo_NamedChar  
                        idodo_vis_chars
                      )) (fun (a,b)-> Char b);;



(*SymbolCharNoDot*)
let idodo_Mysigns= one_of "!$^*_-=+<>?/:";;
let idodo_SymbolLetters= range_ci 'a' 'z';;
let idodo_packSymbolLetters= pack idodo_SymbolLetters (fun (c)-> (lowercase_ascii c));;

let idodo_symbolCharNotDot= disj_list   [ digit;
                                          idodo_packSymbolLetters;
                                          idodo_Mysigns];;

(*SymbolChar*)
let idodo_dot= char '.';;
let parseSymbolChar = disj_list         [ idodo_dot;
                                          idodo_symbolCharNotDot];;





(*Symbol*)

let parseSymbol_first = disj 
                      
    (pack (caten parseSymbolChar (plus parseSymbolChar)) (fun (a,b)-> a::b))       
    (pack idodo_symbolCharNotDot (fun (x) -> x::[]));;

let parse_symbol= pack parseSymbol_first (fun (x)-> match x with
|[]-> raise X_idodo2
|s->Symbol((list_to_string s)));;

                    

(*Numbers*)
(*Fraction*)
let digitSeq= plus digit;; 
let plusMinus= disj (char '-') (char '+');;
let fractionSeq= caten (
                  caten (
                    caten (
                      maybe plusMinus) 
                    digitSeq) 
                    (char '/')) 
                    digitSeq;;

let rec gcd a b =
  if b=0 then a else gcd b (a mod b);;

let parse_fraction= pack fractionSeq (fun (((sign, nume), slash), denum) -> 
  let mone= (int_of_string (list_to_string nume)) in
  let mehane= (int_of_string (list_to_string denum)) in
  let gcdFact= gcd mone mehane in
  match sign with
  |None-> Fraction (mone/gcdFact,mehane/gcdFact)
  |Some si-> if si='-' then Fraction ((-1 * (mone/gcdFact)), (mehane/gcdFact)) else Fraction ((1 * (mone/gcdFact)), (mehane/gcdFact))
  );;

  

(*Float*)
let floatSeq= caten (
                  caten (
                    caten (
                      maybe plusMinus) 
                    digitSeq) 
                    (char '.')) 
                    digitSeq;;


let idodo_float_less1 lst= 
List.fold_right
(fun op sum -> sum/.10.0 +. (float_of_int ((int_of_char op)-(int_of_char '0')))) lst 0.0;;
                  
let idodo_float_pack lst=
(idodo_float_less1 lst) /. 10.0;;


let parse_float= pack floatSeq (fun (((sign, inte), dot), esroni) -> 
  let shalem= (float_of_int(int_of_string (list_to_string inte))) in
  let shever= (idodo_float_pack esroni) in
  match sign with
  |None-> Float (shalem+.shever)
  |Some si-> if si='-' then Float (-1.0 *. (shalem +.shever)) else Float (shalem+.shever)
  );;


(*Integer*)
(*Fraction*)
let integerSeq= caten (maybe plusMinus) digitSeq;;

let parse_integer= pack integerSeq (fun (sign, num) -> 
  let newNum= (int_of_string (list_to_string num)) in
  match sign with
  |None-> Fraction (newNum,1)
  |Some si-> if si='-' then Fraction ((-1 * newNum),1) else Fraction ((1 * newNum), 1)
  );;

  

(*Scietific*)

let rec recursiveExponent sum n=
match n with
|0.0 -> sum
|x-> (recursiveExponent (sum *. 10.0) (x -. 1.0));;

let idodo_scientific_integer= caten 
                                (caten 
                                  integerSeq (char_ci 'e')) 
                              integerSeq;;

let idodo_scientific_float= caten 
                              (caten 
                                floatSeq (char_ci 'e')) 
                            integerSeq;;
let checkFirstSignForIntSci newNum newExpo minusOne sign2=
match sign2 with 
|None-> Float (minusOne *. ((float_of_int newNum) *. (recursiveExponent 1.0 (float_of_int newExpo))))
|Some expSi-> if (expSi='-' && newExpo!=0) then Float (minusOne *.  ((float_of_int newNum) *.    (1.0 /. (recursiveExponent 1.0 (float_of_int newExpo)))))
                            else Float (minusOne *. ((float_of_int newNum) *. (recursiveExponent 1.0 (float_of_int newExpo))));;

let checkFirstSignForFltSci newFloatNum newExpo minusOne sign2=
                            match sign2 with 
                            |None-> Float (minusOne *. (newFloatNum *. (recursiveExponent 1.0 (float_of_int newExpo))))
                            |Some expSi-> if (expSi='-' && newExpo!=0) then Float  (minusOne *.  (newFloatNum *.    (1.0 /. (recursiveExponent 1.0 (float_of_int newExpo)))))
                                          else Float  (minusOne *. (newFloatNum *. (recursiveExponent 1.0 (float_of_int newExpo))));;


let parseSci_integer= pack idodo_scientific_integer 
    (fun (((sign1, firstNum), expoSign), (sign2, theExpo))->
      let newNum= (int_of_string (list_to_string firstNum)) in
      let newExpo= (int_of_string (list_to_string theExpo)) in
      match sign1 with
      |None-> (checkFirstSignForIntSci newNum newExpo 1.0 sign2)
      |Some si-> if si='-' then (checkFirstSignForIntSci newNum newExpo (-1.0) sign2) else (checkFirstSignForIntSci newNum newExpo 1.0 sign2)
      );; 


let parseSci_float= pack idodo_scientific_float 
      (fun (((((sign1, inte), dot), esroni), expoSign), (sign2, theExpo))->
        let shalem= (float_of_int(int_of_string (list_to_string inte))) in
        let shever= (idodo_float_pack esroni) in
        let newFloatNum= (shalem +.shever) in
        let newExpo= (int_of_string (list_to_string theExpo)) in
        match sign1 with
        |None-> (checkFirstSignForFltSci newFloatNum newExpo 1.0 sign2)
        |Some si-> if si='-' then (checkFirstSignForFltSci newFloatNum newExpo (-1.0) sign2) else (checkFirstSignForFltSci newFloatNum newExpo 1.0 sign2)
        );; 



let parse_Scientific= disj parseSci_float parseSci_integer;;


(*Number*)
let fractionToNumber= pack parse_fraction (fun x-> Number(x));;
let floatToNumber= pack parse_float (fun x-> Number(x));;
let integerToNumber= pack parse_integer (fun x-> Number(x));;
let scientificToNumber = pack parse_Scientific (fun x -> Number(x));;
let parse_number_pre= disj_list [scientificToNumber; fractionToNumber; floatToNumber; integerToNumber ];;
let parse_number= not_followed_by parse_number_pre (plus parse_symbol);;

(*String literal char*)

let idodo_aRange= range '\000' '!';;
let idodo_bRange= range '#' '[';;
let idodo_cRange= range ']' '~';;

let idodo_string_literal_char = disj_list [idodo_aRange;idodo_bRange;idodo_cRange];;


(*String Meta Char*)
let idodo_metaLetters=one_of "tfnr";;
let idodo_merhaot= char '"';;
let idodo_disjMetaChar= disj_list [idodo_metaLetters;idodo_merhaot;idodo_slash];;
let idodo_MetaChar= caten idodo_slash idodo_disjMetaChar;;
let packIdodo_metaChar= pack idodo_MetaChar (fun (slash,letter)->
  match letter with
    |'r'-> '\013'
    |'n'-> '\010'
    |'t'-> '\009'
    |'f'-> '\012'
    |'\\'-> '\092'
    |'"'-> '\034'    
    |_-> raise X_idodo33 
  )

(*String Char*)
let parseStringChar = disj 
                      (pack packIdodo_metaChar (fun (x) -> x::[]))
                      (pack idodo_string_literal_char (fun (x) -> x::[]))
                      ;;      
                      


(*String*)


let stringSeq= star parseStringChar;;
let flattenStringSeq= pack stringSeq (fun (lst)-> List.flatten(lst));;
let parse_string= pack (caten (caten (char '\"') flattenStringSeq) (char '\"')) (fun ((m1, lst),m2)-> String (list_to_string lst));;

                     



let nt_whiteSpace= range '\000' ' ';;
let nt_whitespacePacked= pack nt_whiteSpace (fun (x)-> x::[]);;

let badChars=  (char '\010');;
let allChars= range '\000' '\127';;
let allTheRestChars= diff allChars badChars;;

let nt_whitespaces=star nt_whiteSpace;;


let lineCommentSeq=caten (caten (char ';') (star allTheRestChars)) badChars;;

let lineCommentSeqNew=  disj
                        (pack 
                          (caten (caten (char ';') (star allTheRestChars)) (char '\010')) 
                          (fun ((ch1,chLst),ch2)->(append [ch1] (append chLst [ch2])))
                        )
                        (pack  
                          (caten(caten (char ';') (star allTheRestChars)) nt_epsilon)
                          (fun ((ch1,chLst),ls) -> (append [ch1] chLst)));;



let rec append l1 c =
  match l1 with
  | h::t -> h :: append t c
  | [] -> c;;

(*let packOutLineCommnet= pack lineCommentSeqNew (fun ((x,y),z)-> x::(append y (z::[])));;*)

let packOutLineCommnet=lineCommentSeqNew ;;

let starLineComment=packOutLineCommnet;;


let make_paired nt_left nt_right nt=
let nt= caten nt_left nt in
let nt= pack nt (function (_,e)->e) in
let nt= caten nt nt_right in
let nt= pack nt (function (e,_)->e) in
nt;;


let nt_spcaesAndComments=disj_list[packOutLineCommnet;  nt_whitespacePacked];;

let nt_superStar= star nt_spcaesAndComments;;

(*let nt_spcaesAndComments=nt_whitespacePacked ;;
let = diff packOutLineCommnet emptyString;;*)

(*let nt_spcaesAndComments= disj ddd nt_whitespaces ;;*)

let make_spaced nt=
  make_paired nt_superStar nt_superStar nt;;

let tok_lparen= make_spaced (char '(');;
let tok_rparen= make_spaced (char ')');;



let rec parse_mySexp c_lst=
  
  disj_list[
    make_commentCheck (make_spaced parse_bool);
    make_commentCheck (make_spaced parse_char);
    make_commentCheck (make_spaced parse_number);
    make_commentCheck (make_spaced parse_string);
    make_commentCheck (make_spaced parseList);
    make_commentCheck (make_spaced parseDottedList);
    make_commentCheck (make_spaced parseQuoted);
    make_commentCheck (make_spaced parseQuasiQuoted);
    make_commentCheck (make_spaced parseUnquoted);
    make_commentCheck (make_spaced parseUnquotedSplicing);
    make_commentCheck (make_spaced parse_symbol)
  ] c_lst

  and make_commentCheck nt=
  make_paired (star findSexpCommentsOrSexp) (star findSexpCommentsOrSexp) nt

  and parseList nlst= 
    let listSeq= caten (caten tok_lparen (star parse_mySexp)) tok_rparen in
    let packSeq= pack listSeq (fun ((lparen, lstObjects), rparen)-> 
      List.fold_right (fun e aggr -> Pair(e,aggr)) lstObjects Nil      
      ) in packSeq nlst
  
  and parseDottedList nlst= 
    let listSeq= caten (caten (caten (caten tok_lparen (plus parse_mySexp)) (make_spaced (char '.'))) parse_mySexp) tok_rparen in
    let packSeq= pack listSeq (fun ((((lparen, lstObjects), myDot), lastElem),rparen)-> 
      List.fold_right (fun e aggr -> Pair(e,aggr)) lstObjects lastElem      
        ) in packSeq nlst
  
  and parseQuoted nlst=
      let quotedSeq= caten (make_spaced (char '\'')) parse_mySexp in
      let packQuoted= pack quotedSeq (fun (sign, exp)-> Pair (Symbol ("quote"), Pair(exp, Nil)))
    in packQuoted nlst

  and parseQuasiQuoted nlst=
    let quasiquotedSeq= caten (make_spaced (char '`')) parse_mySexp in
    let packQuasiQuoted= pack quasiquotedSeq (fun (sign, exp)-> Pair (Symbol ("quasiquote"), Pair(exp, Nil)))
  in packQuasiQuoted nlst

  and parseUnquoted nlst=
      let unquotedSeq= caten (make_spaced (char ',')) parse_mySexp in
      let packUnquoted= pack unquotedSeq (fun (sign, exp)-> Pair (Symbol ("unquote"), Pair(exp, Nil)))
  in packUnquoted nlst

    and parseUnquotedSplicing nlst=
    let unqouteSplicingSeq= caten (caten (make_spaced (char ',')) (make_spaced (char '@'))) parse_mySexp in
    let packUnqouteSplicing= pack unqouteSplicingSeq (fun (sign, exp)-> Pair (Symbol ("unquote-splicing"), Pair(exp, Nil)))
  in packUnqouteSplicing nlst

  and findSexpCommentsOrSexp lst=
  let sexpComment = make_spaced (caten (caten (char '#') (char ';')) parse_mySexp) in
  let packlal = pack sexpComment (fun ((x,y), z) -> z) 
in (packlal lst);;

let read_sexprs str = 
  let tokens=string_to_list str in
  (*let print= (Printf.printf "%x\n" (int_of_char (List.nth tokens ((List.length tokens)-1)))) in
  let print2= (debugPrint tokens) in*)
  let ast,rem = (plus parse_mySexp) tokens in
  match rem with
  |[]-> ast
  |lst-> raise X_no_match;;
end;; (* struct Reader *)

(*new new new*)