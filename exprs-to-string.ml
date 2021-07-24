

let signum n =
  if n < 0 then -1
  else if 0 < n then +1
  else 0;;

let rec gcd a b =
  match (a, b) with
  | (0, b) -> b
  | (a, 0) -> a
  | (a, b) -> (gcd b (a mod b));;

let string_from_number = function
  | Fraction(num, den) ->
     let d = gcd num den in
     let (num, den) = (num / d, den / d) in
     ( match (num, den) with
       | (0, _) -> "0"
       | (num, 1) -> Format.sprintf "%d" num
       | (num, -1) -> Format.sprintf "%d" (- num)
       | (num, den) ->
          ( let sgn = signum den in
            Format.sprintf "%d/%d" (sgn * num) (sgn * den ) ) )
  | Float(x) -> Format.sprintf "%f" x;;

let rec string_from_sexpr = function
  | Bool(false) -> "#f"
  | Bool(true) -> "#t"
  | Nil -> "()"
  | Number(num) -> (string_from_number num)
  | Char('\n') -> "#\\newline"
  | Char('\t') -> "#\\tab"
  | Char('\012') -> "#\\page"
  | Char('\r') -> "#\\return"
  | Char(' ') -> "#\\space"
  | Char('\000') -> "#\\nul"
  | Char(ch) -> Format.sprintf "#\\%c" ch
  | String(str) -> Format.sprintf "\"%s\"" str
  | Symbol(sym) -> Format.sprintf "\"Symbol: %s\"" sym
  | Pair(car, cdr) ->
     string_from_sexpr_with_car (string_from_sexpr car) cdr
and string_from_sexpr_with_car car_str e =
  match e with
  | Nil -> Format.sprintf "(%s)" car_str
  | Pair(car, cdr) ->
     string_from_sexpr_with_car
       (Format.sprintf "%s %s" car_str (string_from_sexpr car))
       cdr
  | e -> Format.sprintf "(%s . %s)" car_str (string_from_sexpr e);;

let string_from_constant = function
  | Sexpr(sexpr) -> string_from_sexpr sexpr
  | Void -> "#<void>";;

let string_from_var = function
  | VarFree(v) -> v
  | VarParam(v, _) -> v
  | VarBound(v, _, _) -> v;;

let rec string_from_expr' = function
  | Const'(Sexpr(Nil)) -> "'()"
  | Const'(Sexpr(Symbol(_) as sexpr)) ->
     Format.sprintf "'%s" (string_from_sexpr sexpr)
  | Const'(Sexpr(Pair(_, _) as sexpr)) ->
     Format.sprintf "'%s" (string_from_sexpr sexpr)
  | Const'(c) -> string_from_constant c
  | Var'(v) -> string_from_var v
  | Box'(var) -> Format.sprintf "(box %s)" (string_from_var var)
  | BoxGet'(var) -> Format.sprintf "(car %s)" (string_from_var var)
  | BoxSet'(var, expr') ->
     Format.sprintf "(set-car! %s %s)"
       (string_from_var var)
       (string_from_expr' expr')
  | If'(test, dit, Const'(Void)) ->
     Format.sprintf "(if %s %s)"
       (string_from_expr' test)
       (string_from_expr' dit)
  | If'(test, dit, dif) ->
     Format.sprintf "(if %s %s %s)"
       (string_from_expr' test)
       (string_from_expr' dit)
       (string_from_expr' dif)
  | Seq'([]) -> "(begin)"
  | Seq'(exprs') ->
     Format.sprintf "(begin %s)"
       ( List.fold_left
           (fun a b -> Format.sprintf "%s %s" a (string_from_expr' b))
           ""
           exprs' )
  | Set'(var, body) ->
     Format.sprintf "(set! %s %s)"
       (string_from_var var)
       (string_from_expr' body)
  | Def'(var, body) ->
     Format.sprintf "(define %s %s)"
       (string_from_var var)
       (string_from_expr' body)
  | Or'([]) -> "#f"
  | Or'(exprs') ->
     Format.sprintf
       "(or %s)"
       ( List.fold_left
           (fun a b -> Format.sprintf "%s %s" a (string_from_expr' b))
           ""
           exprs' )
  | LambdaSimple'(params, body) ->
     Format.sprintf
       "(lambda (%s) %s)"
       ( List.fold_left
           (fun a b -> Format.sprintf "%s %s" a b)
           ""
           params )
       (string_from_expr' body)
  | LambdaOpt'([], opt, body) ->
     Format.sprintf
       "(lambda %s %s)"
       opt
       (string_from_expr' body)
  | LambdaOpt'(params, opt, body) ->
     Format.sprintf
       "(lambda (%s . %s) %s)"
       ( List.fold_left
           (fun a b -> Format.sprintf "%s %s" a b)
           ""
           params )
       opt
       (string_from_expr' body)     
  | (Applic'(proc, args) | ApplicTP'(proc, args)) ->
     Format.sprintf
       "(%s)"
       ( List.fold_left
           (fun a b -> Format.sprintf "%s %s" a (string_from_expr' b))
           (string_from_expr' proc)
           args );;

