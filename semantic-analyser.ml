#use "tag-parser.ml";;
open Tag_Parser;;
type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of var * expr'
  | Def' of var * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq (Var'(var1)) (Var'(var2))) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;

type zug= 
  Zug of int*var;;

type ans=
  |Varlist of var list
  |Nil;;

                       
exception X_syntax_error;;
exception X_No_match_for_exp;;
exception X_Hello;;
exception X_Goodbye;;
exception X_tail_form_exception;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'


  
  (*To delete*)
  val giveMeTheFirst: expr list-> expr'
end;;

module Semantics : SEMANTICS = struct


(*Usefull*)

let rec append l1 l2 =
  match l1 with
  | h::t -> h :: append t l2
  | [] -> l2;;


(*Main logic*)

let rec checkMyExpTagType e num pairs_paramLst=
match e with
| Const (e)-> Const' (e)
| Var(v)-> Var'((checkVarsEnviroment v num pairs_paramLst))
| If(test,dit,dif)-> If' ((checkMyExpTagType test num pairs_paramLst), (checkMyExpTagType dit num pairs_paramLst), (checkMyExpTagType dif num pairs_paramLst))
| Seq(lst)-> Seq'(List.map (fun (x)-> checkMyExpTagType x num pairs_paramLst) lst)
| Or(lst)->  Or'(List.map (fun (x)-> checkMyExpTagType x num pairs_paramLst) lst)
| Def (Var(v),exp)-> Def' (VarFree(v),(checkMyExpTagType exp num pairs_paramLst))
| LambdaSimple (args,body)-> (handleLambda args body (num + 1) pairs_paramLst)
| LambdaOpt (args,opt,body)-> (handleLambdaOpt args opt body (num+1) pairs_paramLst)
| (*Ido ama*) Set(Var(v),exp)-> Set' ((checkVarsEnviroment v num pairs_paramLst), (checkMyExpTagType exp num pairs_paramLst))
| Applic (operator, operands)-> Applic' ((checkMyExpTagType operator num pairs_paramLst), (List.map (fun (x)-> (checkMyExpTagType x num pairs_paramLst)) operands))
| _-> raise X_No_match_for_exp


and parameterize param_lst rst_lst curr_index=
match rst_lst with
|[]-> param_lst
|x::rst->(parameterize (append param_lst [VarParam(x, curr_index)]) rst (curr_index + 1))

and handleLambda argsLst body level pairs_paramLst=
let current_params= (parameterize [] argsLst 0) in
let newPairs= (List.map (fun (x)-> Zug(level,x)) current_params) in
let pairsOfParms= (append newPairs pairs_paramLst) in (*ext_env*) 
let parsed_body=(checkMyExpTagType body level pairsOfParms) in
LambdaSimple' (argsLst, parsed_body)

and handleLambdaOpt argsLst opt body level pairs_paramLst=
let current_params= (parameterize [] (append argsLst [opt]) 0) in
let newPairs= (List.map (fun (x)-> Zug(level,x)) current_params) in
let pairsOfParms= (append newPairs pairs_paramLst) in (*ext_env*) 
let parsed_body=(checkMyExpTagType body level pairsOfParms) in
LambdaOpt' (argsLst,opt, parsed_body)



and checkVarsEnviroment v level paramLst=
match paramLst with
|[]-> VarFree(v)
|Zug(num,VarParam(str,index))::rst->  if ( v=str )
                                      then (
                                        if (num=level)
                                        then VarParam(v,index)
                                        else VarBound(v,(level-num-1),index))
                                      else (checkVarsEnviroment v level rst)

;;


(*Tail Form*)



let rec tailForms e should_tp=
match e with
|Const'(c)-> e
|Var'(x)-> e
|If' (test, dit, dif)-> (If' ((tailForms test false),(tailForms dit should_tp),(tailForms dif should_tp)))
|Seq'(lst)-> Seq' (run_exprs lst should_tp)
|Set'(var,exp)-> Set'(var,(tailForms exp false))
|Def'(var,exp)-> Def'(var,(tailForms exp false))
|Or' (lst)-> Or'(run_exprs lst should_tp)
|LambdaSimple' (args,bdy)-> LambdaSimple' (args, (tailForms bdy true)) 
|LambdaOpt' (args,opt,bdy)-> LambdaOpt' (args,opt,(tailForms bdy true))
|Applic'(operator, operands)-> (handleApplic operator operands should_tp)

and run_exprs exprs should_tail=
match exprs with
|[]->[]
|[ex]-> [tailForms ex should_tail]
|ex::exps-> (tailForms ex false):: (run_exprs exps should_tail)

|_-> raise X_tail_form_exception




and handleApplic operator operands tp=
let annotateOperator= (tailForms operator false) in
let annotateOperands= (List.map (fun (x)-> (tailForms x false)) operands ) in
if tp then (ApplicTP' (annotateOperator, annotateOperands)) else (Applic' (annotateOperator, annotateOperands))

and handleOr lst tp=
let firstAnnotated= (tailForms (List.hd lst) false) in
let rstAnnotated= (List.map (fun (x)-> (tailForms x tp)) (List.tl lst)) in
Or' ((append [firstAnnotated] rstAnnotated))


and handle_sequence expLst rst=
match rst with
|x::[]-> (append expLst [tailForms x true])
|x::y-> (handle_sequence (append expLst [(tailForms x false)]) y)

;;



let rec combineAnswers lst=
match lst with
|[]-> []
|x::y-> (List.flatten lst);;

let rec checkIfThereIsRead varName expr=
match expr with
| Const'(x)-> []
| Var'(m)-> (match m with
            |VarParam(varName, x)-> [VarParam(varName,x)]
            |VarBound(varName,x,y)-> [VarBound(varName,x,y)]
            |els-> [])

| If'(test,dit,dif)-> combineAnswers [(checkIfThereIsRead varName test);(checkIfThereIsRead varName dit);(checkIfThereIsRead varName dif)]
| Seq'(lst)->(combineAnswers (List.map (fun (x)->(checkIfThereIsRead varName x)) lst))
| Set' (something,expr)->(checkIfThereIsRead varName expr)
| Def' (x,expr)-> (checkIfThereIsRead varName expr)
| Or' (lst)-> (combineAnswers (List.map (fun (x)->(checkIfThereIsRead varName x)) lst))
| LambdaSimple'(stringLst, expr)-> if (List.mem varName stringLst) then [] else (checkIfThereIsRead varName expr)
| LambdaOpt' (stringLst,str, expr)-> if (List.mem varName (append stringLst [str])) then [] else (checkIfThereIsRead varName expr)
| Applic' (expr,exprlst)-> (combineAnswers (List.map  (fun (x)->(checkIfThereIsRead varName x)) (append [expr] exprlst)))
| ApplicTP' (expr,exprlst)-> (combineAnswers (List.map  (fun (x)->(checkIfThereIsRead varName x)) (append [expr] exprlst)))
| els-> [];;



let rec checkIfThereIsWrite varName expr=
match expr with
| Const'(x)-> []
| Var'(m)-> []
| If'(test,dit,dif)-> combineAnswers [(checkIfThereIsWrite varName test);(checkIfThereIsWrite varName dit);(checkIfThereIsWrite varName dif)]
| Seq'(lst)->(combineAnswers (List.map (fun (x)->(checkIfThereIsWrite varName x)) lst))
| Set' (VarParam(varName,x),expr)->(append [VarParam(varName,x)] (checkIfThereIsWrite varName expr))
| Set' (VarBound(varName,x,y),expr)-> (append [VarBound(varName,x,y)] (checkIfThereIsWrite varName expr))
| Set' (something,expr)-> (checkIfThereIsWrite varName expr)
| Or' (lst)-> (combineAnswers (List.map (fun (x)->(checkIfThereIsWrite varName x)) lst))
| LambdaSimple'(stringLst, expr)-> if (List.mem varName stringLst) then [] else (checkIfThereIsWrite varName expr)
| LambdaOpt' (stringLst,str, expr)-> if (List.mem varName (append stringLst [str])) then [] else (checkIfThereIsWrite varName expr)
| Applic' (expr,exprlst)-> (combineAnswers (List.map  (fun (x)->(checkIfThereIsWrite varName x)) (append [expr] exprlst)))
| ApplicTP' (expr,exprlst)-> (combineAnswers (List.map  (fun (x)->(checkIfThereIsWrite varName x)) (append [expr] exprlst)))
| els-> [];;

let rec checkIfThereIsBound varsLst=
match varsLst with
| []-> false
| (VarBound(x,a,b)::rst)->true
| (something::rst)->checkIfThereIsBound rst;;


let appendSequences seq1 seq2=
match seq1 with
|Seq'(lst1)-> (match seq2 with
              |Seq'(lst2)-> Seq' (append lst1 lst2)
              |els->raise X_Goodbye)
|elss-> raise X_Goodbye;;





let rec boxMyBdy oneArg bdy=
match bdy with
  | Const'(x)->Const'(x)
  | Var'(VarParam(vp,loEhapt))-> if oneArg=vp then BoxGet' (VarParam(oneArg,loEhapt)) else Var'(VarParam(vp,loEhapt))
  | Var'(VarBound(vp,loEhapt1, loEhapt2))-> if oneArg=vp then BoxGet' (VarBound(oneArg,loEhapt1, loEhapt2)) else Var'(VarBound(vp,loEhapt1, loEhapt2))
  | Var'(something)-> Var'(something)
  | If'(tst,dit,dif)-> If'((boxMyBdy oneArg tst),(boxMyBdy oneArg dit), (boxMyBdy oneArg dif))
  | Seq'(expLst)-> Seq'(List.map (fun (x)-> boxMyBdy oneArg x) expLst)
  | Set' (VarParam(vp,loEhapt),exp)->if vp=oneArg then BoxSet' (VarParam(oneArg,loEhapt),(boxMyBdy oneArg exp)) else Set' (VarParam(vp,loEhapt),(boxMyBdy oneArg exp))
  | Set' (VarBound(vp,loEhapt1,loEhapt2),exp)-> if vp=oneArg then BoxSet' (VarBound(oneArg,loEhapt1,loEhapt2),(boxMyBdy oneArg exp)) else Set' (VarBound(vp,loEhapt1,loEhapt2),(boxMyBdy oneArg exp))
  | Set'(var,exp)-> Set'(var, boxMyBdy oneArg exp)
  | Def'  (var,exp)-> Def'(var,(boxMyBdy oneArg exp))
  | Or'(expLst)-> Or' (List.map (fun (x)-> boxMyBdy oneArg x) expLst)
  | LambdaSimple' (args,bdy)-> (if (List.mem oneArg args ) then LambdaSimple' (args,bdy) else LambdaSimple' (args, (boxMyBdy oneArg bdy)))  
  | LambdaOpt'(args,str,bdy)-> (if (List.mem oneArg args ) then LambdaOpt' (args,str, (boxMyBdy oneArg bdy)) else LambdaOpt' (args,str, (boxMyBdy oneArg bdy)))    
  | Applic' (operator,operands)-> Applic'(boxMyBdy oneArg operator, (List.map (fun (x)-> boxMyBdy oneArg x) operands))
  | ApplicTP' (operator,operands)-> ApplicTP'(boxMyBdy oneArg operator, (List.map (fun (x)-> boxMyBdy oneArg x) operands))
  | Box'(v)->Box'(v)
  | BoxGet'(v)->BoxGet'(v)
  | BoxSet'(v,e)-> BoxSet'(v, boxMyBdy oneArg e)


let getTheBoxSentence varName minor=
Set' (VarParam(varName,minor),Box'(VarParam(varName,minor)));;

let handleBoxBody boxSenteces exp=
match exp with
|Seq'(lst)->   (appendSequences (Seq'(boxSenteces)) exp)
|els-> Seq'((append boxSenteces [exp]));;

let checkIfShouldBoxYesOrNo oneArg minor bdy=
  let readsLst= checkIfThereIsRead oneArg bdy in
  let writeLst= checkIfThereIsWrite oneArg bdy in
  let boundsInRead= checkIfThereIsBound readsLst in
  let boundInWrite= checkIfThereIsBound writeLst in
  if  (
      ((List.length readsLst)>0)
   &  ((List.length writeLst)>0) 
   &  (boundInWrite || boundsInRead) 
      )
      then  true
      else false;;

let checkOneRib oneArg minor bdy=
 (boxMyBdy oneArg bdy);;


let rec checkAndBoxEachArg args minor bdy=
match args with
|[]-> bdy
|x::y->(checkAndBoxEachArg  y (minor+1) (checkOneRib x minor bdy));;


    

let rec getBoxSentencesList args boxLst minor bdy=
match args with
|[]-> boxLst
|x::y-> (getBoxSentencesList y (append boxLst [(getTheBoxSentence x minor)]) (minor+1) bdy)

let checkAndBox args bdy=
let sentenceLst= (getBoxSentencesList args [] 0 bdy) in
let theBody= (checkAndBoxEachArg args 0 bdy) in
match sentenceLst with
|[]-> theBody
|lst-> (handleBoxBody lst theBody);;


let rec handleMyBox e=
  match e with
  | Const'(x)->Const'(x)
  | Var'(x)->Var'(x)
  | If'(tst,dit,dif)-> If'((handleMyBox tst),(handleMyBox dit), (handleMyBox dif))
  | Seq'(expLst)-> Seq'(List.map handleMyBox expLst)
  | Set' (var,exp)-> Set' (var,(handleMyBox exp))
  | Def'  (var,exp)-> Def'(var,(handleMyBox exp))
  | Or'(expLst)-> Or' (List.map handleMyBox expLst)
  | LambdaSimple' (args,bdy)->LambdaSimple' (args, (checkAndBox args  bdy))
  | LambdaOpt'(args,str,bdy)-> LambdaOpt' (args, str,(checkAndBox (append args [str])  bdy))
  | Applic' (operator,operands)-> Applic'(handleMyBox operator, List.map handleMyBox operands)
  | ApplicTP' (operator,operands)-> ApplicTP'(handleMyBox operator, List.map handleMyBox operands);;


let annotate_lexical_addresses e = 
  (checkMyExpTagType e (-1) []);;



let annotate_tail_calls e = 
  (tailForms e false)

let box_set e = 
handleMyBox e;;



let run_semantics expr =
  
  (box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr)));;
  (*
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;*)
  (*
  (box_set
      (annotate_lexical_addresses expr));;*)
  

let giveMeTheFirst lst=
  (run_semantics (List.hd lst));;
    
end;; (* struct Semantics *)


