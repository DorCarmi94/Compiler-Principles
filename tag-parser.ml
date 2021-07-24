#use "reader.ml";;
open Reader;;
type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;
exception X_idodo1;;
exception X_idodo2;;
exception X_idodo3;;
exception X_idodo4;;
exception YYY of string;;
exception UnquoteSplicingException;;


module type TAG_PARSER = sig
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "pset!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)
let rec pairsToVars vars=
match vars with
|Nil-> []
|Pair(Symbol(a),rest)-> a:: (pairsToVars rest);;


let rec print_tuples=
function
| []-> ()
|(a,b)::rest->Printf.printf "%i, %s;" a b;
print_tuples rest


let rec append l1 l2 =
  match l1 with
  | h::t -> h :: append t l2
  | [] -> l2;;

(*Buildings*)

let buildIf test dit dif=
match dif with
|Nil->  Pair(Symbol("if"), Pair(test,Pair(dit,Nil)))
|diff-> Pair(Symbol("if"), Pair(test,Pair(dit,Pair(diff,Nil))));;

let buildLet ribs exprs=
Pair(Symbol("let"), Pair(ribs,exprs));;

let buildRib var ass=
Pair(var, Pair(ass,Nil));;

let buildLambda vars exprs=
Pair(Symbol("lambda"), Pair(vars,exprs));;

let sequenize pairs=
Pair(Pair(Symbol("begin"),pairs),Nil);;

let buildApplic operator operands=
Pair(operator, operands);;

let buildSet var valvalul=
Pair(Symbol("set!"),Pair(Symbol(var),Pair(valvalul,Nil)));;

(*Main let rec*)

let rec parse_expr theExp=


  (*Main*)
  let mainParse sexp=
  match sexp with
    (*Basics*)
  |Nil->Const(Sexpr(Nil))
  |Bool(b1)-> Const (Sexpr(Bool(b1)))
  |Number(n1)->Const (Sexpr(Number(n1)))
  |Char(c1)-> Const (Sexpr (Char(c1)))
  |String(s1)-> Const (Sexpr(String(s1)))
  (*Macro expansions*)
  (*Let*)
  |Pair (Symbol("let"), Pair(ribs,exprs))->
    (handleLet ribs exprs)
  (*LetStar*)
  |Pair(Symbol("let*"), Pair(ribs, exprs))->
    (handleLetStar ribs exprs)
  (*Letrec*)  
  |Pair(Symbol("letrec"), Pair(ribs,exprs))->
    (handleLetRec ribs exprs)
  (*and*)
  |Pair (Symbol("and"), restAnd)->
    (handleAnd restAnd)
  
  (*cond*)
  |Pair(Symbol ("cond"), rst)->
    (parse_expr(handleCond rst))
  
  |Pair(Symbol("define"),Pair(Pair(name,valval), exprs))->
    (handleDefineMIT name valval exprs)


  |Pair(Symbol("quasiquote"), Pair(sexp, Nil))->
    (parse_expr(handleQuasiquote sexp))

  |Pair(Symbol("pset!"), ribs)->
    (handlePset ribs)

  |Pair(Symbol("quote"), Pair (x, Nil))-> Const (Sexpr(x))
  
  (*If*)
  
  |Pair(Symbol("if"), Pair (test, Pair (dit, Nil)))->
      If(parse_expr test, parse_expr dit, Const (Void))
  |Pair(Symbol("if"), Pair (test, Pair (dit, Pair (dif, Nil))))->
      If(parse_expr test, parse_expr dit, parse_expr dif)

  (*Lambdot*)
  | Pair (Symbol("lambda"), Pair(args,body)) ->
    (dorbfs_lambda [] args body)

  (*Disjoint*)
  |Pair(Symbol "or", kisskiss)->
    (handleOr kisskiss)
    

  (*Definition*)
  (*Check if define can have more than one statement in the body*)
  |Pair(Symbol "define", Pair(Symbol (sym), shlulit))->
    Def (parse_expr (Symbol (sym)),handleNonSeqBody shlulit)

  |Pair (Symbol "begin", odShtuyot)->
    handleSeq odShtuyot

  (*Assigment*)
  |Pair(Symbol ("set!") ,Pair(Symbol (sym), Pair(shlulit,Nil)))->
    Set (parse_expr (Symbol (sym)),parse_expr shlulit)
  
  (*Applic*)
  | Pair(Symbol(app), args)->
    Applic (Var(app) ,(collectPairsToList [] args))
  
  
  | Pair(x,y) -> Applic ((parse_expr x), (collectPairsToList [] y))
  (*Explicit Sequence*)
  
  (*Var*)
  | Symbol (x)-> if (List.mem x reserved_word_list) then (raise (YYY x)) else (Var (x))

  in (mainParse theExp)

  (*Functions for macros*)

  (*Let*)
  and handleLet ribs exprs=
    let vars= (extractLetVars [] ribs) in 
    let vals= (extractLetVals [] ribs) in
    let my_exprs= (handleBody exprs) in
    let lam= LambdaSimple(vars,my_exprs) in 
    Applic (lam, vals)

  and extractLetVars varsLst rest_ribs=
    match rest_ribs with
    |Nil->varsLst
    |Pair(Pair(Symbol(var), value), rest)->(extractLetVars (append varsLst (var::[])) rest)

  and extractLetVals valsLst rest_ribs=
  match rest_ribs with
  |Nil-> valsLst
  |Pair(Pair(Symbol(var), Pair(valval,Nil)), rest)-> (extractLetVals (append valsLst ((parse_expr valval)::[])) rest) 
  |Pair(Pair(Symbol(var), valval), rest)->(extractLetVals (append valsLst ((parse_expr valval)::[])) rest) 

  

  (*LetStar*)
  and handleLetStar ribs exprs=
  match ribs with
  |Nil-> parse_expr (Pair(Symbol("let"),Pair(ribs,exprs)))
  |Pair(Pair(var,valval),Nil)-> parse_expr(Pair(Symbol("let"),Pair(ribs,exprs)))
  |Pair(Pair(var,valval),rst)-> parse_expr(Pair(Symbol("let"),Pair(Pair(Pair(var,valval),Nil),Pair(Pair(Symbol ("let*"), Pair(rst,exprs)),Nil))))


  (*LetRec*)
  and handleLetRec ribs exprs=
  let vars= (extractLetVars [] ribs) in 
  let exps= (extractLetValsSatum [] ribs) in
  let idodoVars= (flatListToPairsLetRecIDODO vars) in
  let setVars= (idodoVarsAndSets [] vars exps) in
  let setVars2= (append setVars ((Pair(Symbol("let"),Pair(Nil,exprs)))::[])) in
  let check=Pair(Symbol("let"),Pair(idodoVars,(flatListToPairsLetRec2 setVars2)))in
  parse_expr (check)

  and flatListToPairsLetRecIDODO setVars=
  match setVars with
  |[]->Nil
  |x::rst1->Pair(
                Pair (
                  Symbol(x),
                  Pair(
                  Pair(
                  Symbol("quote"),
                  Pair(Symbol("w"),Nil)
                  ),Nil
                  )
                ),
                (flatListToPairsLetRecIDODO rst1)  
                )

  and flatListToPairsLetRec setVars exprs=
  match setVars with
  |x::[]-> exprs 
  |x::rst1->Pair (x,(flatListToPairsLetRec rst1 exprs))
  
  and flatListToPairsLetRec2 setVars =
  match setVars with
  |[]->Nil
  |x::[]->Pair(x,Nil)
  |x::rst1->Pair (x,(flatListToPairsLetRec2 rst1))
  

  and idodoVarsAndSets sets rst_vars rst_exps=
  match rst_vars with
  |[]-> sets
  |x::rst1-> (match rst_exps with
                  |[]-> raise X_idodo2
                  |y::rst2->  idodoVarsAndSets (append sets ((Pair(Symbol("set!"),Pair(Symbol(x),Pair(y,Nil))))::[])) rst1 rst2
                  )

  and extractLetValsSatum valsLst rest_ribs=
  match rest_ribs with
  |Nil-> valsLst
  |Pair(Pair(Symbol(var), Pair(valval,Nil)), rest)-> (extractLetValsSatum (append valsLst (valval::[])) rest)

  and extractLetValsNoParsi valsLst rest_ribs=
  match rest_ribs with
  |Nil-> valsLst
  |Pair(Pair(Symbol(var), Pair(valval,Nil)), rest)-> (extractLetValsNoParsi (append valsLst (valval::[])) rest) 
  |Pair(Pair(Symbol(var), valval), rest)->(extractLetValsNoParsi (append valsLst (valval::[])) rest) 

  and flatListToSymbolsPairs setVars =
  match setVars with
  |[]->Nil
  |x::[]->Pair(Symbol(x),Nil)
  |x::rst1->Pair (Symbol(x),(flatListToSymbolsPairs rst1))
  
  (*pset*)

  and handlePset ribs=
  let vars=(extractLetVars [] ribs) in
  let vals= (extractLetValsNoParsi [] ribs) in
  let changeVarsNames= (List.map (fun x->String.concat "" [x;"_"]) vars) in
  let flatNewVars= (flatListToSymbolsPairs changeVarsNames) in
  let sets= (giveMeMySets222 vars changeVarsNames) in
  let flatSets= (flatListToPairsLetRec2 sets) in
  let flatNewVars= (flatListToSymbolsPairs changeVarsNames) in
  let flatValues= (flatListToPairsLetRec2 vals) in
  let myLambda= (buildLambda flatNewVars flatSets) in
  let myApplic =(buildApplic myLambda flatValues) in
  (parse_expr myApplic)


  and giveMeMySets222 old_vars new_vars =
  match old_vars with
  |[]-> []
  |ol::rs1-> (match new_vars with
              |[]-> raise X_idodo4
              |nw::rs2-> append ((buildSet ol (Symbol(nw)))::[]) (giveMeMySets222 rs1 rs2))

  (*and macro*)

  and handleAnd andStmnts=
  match andStmnts with
  |Nil->Const(Sexpr(Bool(true)))
  |els-> anotherAndFunction els

  and anotherAndFunction andStmnts=

  match andStmnts with
  |Pair(x,Nil)-> (parse_expr x)
  |Pair(x,y)-> If ((parse_expr x), anotherAndFunction y, Const(Sexpr(Bool(false))))
  |x-> (parse_expr x)
  
  (*MIT Define*)
  and handleDefineMIT name valval exprs =
  parse_expr (Pair(Symbol("define"),Pair(name,Pair(Symbol("lambda"),Pair(valval,exprs)))))

  
  (*cond macro*)

  and collectRibsToList lst rstRibs=
  match rstRibs with
  |Nil-> lst
  |Pair(x, rst)-> (collectRibsToList (append lst (x::[])) rst)
  |x-> raise X_idodo1
 


  and handleCond condStmnts=
  match condStmnts with
    |Nil -> Nil
    |Pair(Pair(varTest,Pair(Symbol("=>"),doExpr)), other) -> (handleArrowCond varTest doExpr other)
    |Pair(Pair(Symbol("else"), doElse), other) -> Pair(Symbol("begin"),doElse)
    |els -> (handleCondFirstCase els)
    
  and handleCondFirstCase exp=
    match exp with
      |Pair(x, Nil)-> (match x with | Pair(exp1, rst) ->  (buildIf exp1 (Pair(Symbol("begin"),rst))  Nil)
                                    |_ -> raise X_idodo1)
      |Pair(x, y)-> (match x with | Pair(exp1, rst) ->  (buildIf exp1 (Pair(Symbol "begin", rst))  (handleCond y))
                                    |_ -> raise X_idodo2)                               
   
      
  and handleArrowCond var1 exp1 rst_ribs =
    match rst_ribs with
      |Nil -> (buildLet (Pair ((buildRib (Symbol "value") var1),
        Pair((buildRib (Symbol "f") ((buildLambda Nil exp1))),Nil))) 
         (Pair ((buildIf (Symbol "value") ((buildRib (Pair (Symbol "f", Nil)) (Symbol "value"))) Nil),Nil)))                                                                                                                             
     
     | rst -> (buildLet (Pair ((buildRib (Symbol "value") var1),
      Pair ((buildRib (Symbol "f") ((buildLambda Nil exp1))),Pair((buildRib (Symbol "rest") ((buildLambda Nil (Pair((handleCond rst),Nil))))), Nil))))
        (Pair((buildIf (Symbol "value") ((buildRib (Pair (Symbol "f", Nil)) (Symbol "value"))) (Pair (Symbol "rest", Nil))),Nil)))                                                                                                                             
         

and handleQuasiquote sexp=
match sexp with
  |Nil-> Nil
  |Pair(Symbol("unquote"),Pair(x, Nil))-> x
  |Pair(Pair(Symbol("unquote"),Pair(x, Nil)), cont) ->Pair (Symbol("cons"),Pair(x,Pair((handleQuasiquote cont),Nil)))
  |Pair(Pair(Symbol("unquote"),x), cont)-> Pair (Symbol("cons"),Pair(x,Pair((handleQuasiquote cont),Nil)))
  |_-> (handleOthers sexp)


and handleOthers sexp=
match sexp with
(*splicing*)
|Pair(Symbol("unquote-splicing"),Pair(x, Nil)) -> (handleAllUnQuoteSplicing sexp)
|Pair(Pair(Symbol("unquote-splicing"),a), b)-> (handleAllUnQuoteSplicing sexp)
|_->(handleInsideSplicingAB sexp)

and handleInsideSplicingAB sexp=
match sexp with
|Pair(Pair(a,b),c)->  Pair(Symbol("cons"), Pair(Pair(Symbol("cons"), Pair(handleQuasiquote a, Pair(handleQuasiquote b, Nil))), Pair(handleQuasiquote c, Nil)))
|Pair(x, y) -> Pair(Symbol("cons"), Pair(Pair(Symbol("quote"), Pair(x,Nil)), Pair((handleQuasiquote y), Nil)))
|x-> Pair(Symbol("quote"),Pair(x,Nil))


and handleAllUnQuoteSplicing sexp=
match sexp with
|Pair(Symbol("unquote-splicing"),Pair(x, Nil)) -> x
|Pair(Pair(Symbol("unquote-splicing"),a), b)-> (handleUnquoteSplicingInternal a b) 

and handleUnquoteSplicingInternal bibi gantz=
match bibi with
  |Pair(bibs, Nil) -> Pair(Symbol("append"), Pair(bibs,Pair((handleQuasiquote gantz),Nil)))
  |bibs ->            Pair(Symbol("append"), Pair(bibs,Pair((handleQuasiquote gantz),Nil)))


  (*Basic functions*)

  (*Or*)
  and handleOr kisskiss=
  match kisskiss with
  |Nil->Const (Sexpr(Bool(false)))
  |Pair(x,Nil)-> (parse_expr x)
  |Pair (x,y)-> Or (collectPairsToList [] kisskiss)
  


  and dorbfs_lambda untilNow rest body=
  match rest with
  | Nil-> LambdaSimple([], handleBody body)
  | Pair(Symbol(sym),Nil) -> LambdaSimple(append untilNow (sym::[]), handleBody body)
  | Pair (Symbol(sym1),Symbol(sym2)) ->LambdaOpt (append untilNow (sym1::[]), sym2, handleBody body)
  | Symbol(sym1) ->LambdaOpt ([], sym1, handleBody body)
  | Pair(Symbol(sym), rst) -> (dorbfs_lambda (append untilNow (sym::[])) rst body)
  | x->  raise X_idodo3

  and colletSexprPairsToList = function  
   | Pair(x,y)-> x:: (colletSexprPairsToList y)
   | Nil -> []
   | x -> [x]


  and collectPairsToList lst rst_pairs=
  match rst_pairs with
  |Nil-> lst
  |Pair(x,Nil)-> append lst ((parse_expr x)::[])
  |Pair (x,y)->(collectPairsToList (append lst ((parse_expr x)::[])) y)
  |exp-> (append lst ((parse_expr exp)::[]))
  
  (*Seq Legal*)
  and checkMySequence x = 
   match x with
   | [] ->  Const(Void)
   | (x::[]) ->  parse_expr x
   | lst ->  Seq (List.map parse_expr lst)
  
   and handleBody body=
   checkMySequence(colletSexprPairsToList body)


  and handleNonSeqBody body=
  match body with
  |Pair(x,Nil)->parse_expr x 
  |els-> parse_expr els

  and handleSeq shtuyot=
  match shtuyot with
  |Nil-> Const (Void)
  |Pair (x, Nil)-> (parse_expr x)
  |bdy -> checkMySequence(colletSexprPairsToList bdy)

  
  and collectExpSeqPairsToList lst rst_pairs=
  match rst_pairs with
  |Nil-> lst
  |Pair(Pair(Symbol("begin"), rst),Nil)->(collectExpSeqPairsToList lst rst)
  |Pair(Pair(Symbol("begin"), rst),more)->(collectExpSeqPairsToList (collectExpSeqPairsToList lst rst) more)
  |Pair(x,Nil)-> append lst ((parse_expr x)::[])
  |Pair (x,y)->(collectExpSeqPairsToList (append lst (((parse_expr x))::[])) y)
  |exp-> (append lst ((parse_expr exp)::[]))
;;


let tag_parse_expressions sexpr= (List.map parse_expr sexpr);;


  
end;; (* struct Tag_Parser *)

(*gantz will save us*)







