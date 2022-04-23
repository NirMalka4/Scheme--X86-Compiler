#use "reader.ml";;

type expr =
  | ScmConst of sexpr
  | ScmVar of string
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmSet of expr * expr
  | ScmDef of expr * expr
  | ScmOr of expr list
  | ScmLambdaSimple of string list * expr
  | ScmLambdaOpt of string list * string * expr
  | ScmApplic of expr * (expr list);;

(* util data structure for tag parse let, let* and letrec expressions *)
type let_rib = LetRib of string * expr;;

(* util data structure for tag parse cond expressions *)
type cond_rib = 
  |CondRibDefault of expr * expr list
  |CondRibArrow of expr * expr
  |CondRibElse of expr list
  |CondRibEmpty of expr list

exception X_syntax_error of sexpr * string;;
exception X_reserved_word of string;;
exception X_proper_list_error;;
exception X_not_implemented;;
exception X_empty_list;;
exception X_expected_ScmVar of expr;;
exception X_duplicates_params of string;;

let rec list_to_proper_list = function
| [] -> ScmNil
| hd::[] -> ScmPair (hd, ScmNil)
| hd::tl -> ScmPair (hd, list_to_proper_list tl);;

let rec list_to_improper_list = function
| [] -> raise X_proper_list_error
| hd::[] -> hd
| hd::tl -> ScmPair (hd, list_to_improper_list tl);;

let rec scm_append scm_list sexpr =
match scm_list with
| ScmNil -> sexpr
| ScmPair (car, cdr) -> ScmPair (car, scm_append cdr sexpr)
| _ -> raise (X_syntax_error (scm_list, "Append expects a proper list"))

let rec scm_map f sexpr =
match sexpr with
| ScmNil -> ScmNil
| ScmPair (car, cdr) -> ScmPair (f car, scm_map f cdr)
| _ -> raise (X_syntax_error (sexpr, "Map expects a list"));;

let rec scm_zip f sexpr1 sexpr2 =
match sexpr1, sexpr2 with
| ScmNil, ScmNil -> ScmNil
| ScmPair (car1, cdr1), ScmPair (car2, cdr2) -> ScmPair (f car1 car2, scm_zip f cdr1 cdr2)
| _, _ ->
    let sepxrs = list_to_proper_list [ScmSymbol "sexpr1:"; sexpr1; ScmSymbol "sexpr2:"; sexpr2] in
    raise (X_syntax_error (sepxrs, "Zip expects 2 lists of equal length"));;

let rec scm_list_to_list = function
| ScmPair (hd, tl) -> hd::(scm_list_to_list tl)
| ScmNil -> []
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec scm_is_list = function
| ScmPair (hd, tl) -> scm_is_list tl
| ScmNil -> true
| _ -> false

let rec scm_is_imp_list = function
| ScmPair (hd, tl) -> scm_is_list tl
| sexpr -> true
| _ -> false

let rec scm_list_length = function
| ScmPair (hd, tl) -> 1 + (scm_list_length tl)
| ScmNil -> 0
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec untag expr =
let untag_vars vars = List.map (fun s -> ScmSymbol s) vars in
let untag_tagged_list tag exprs = list_to_proper_list (ScmSymbol tag::(List.map untag exprs)) in

let untag_lambda_opt vars var body =
let vars = match vars with
| [] -> ScmSymbol var
| _ -> list_to_improper_list (untag_vars (vars@[var])) in
list_to_proper_list ([ScmSymbol "lambda"; vars]@body) in

match expr with
| (ScmConst (ScmSymbol(_) as sexpr)
    | ScmConst (ScmNil as sexpr)
    | ScmConst (ScmPair (_, _) as sexpr)) -> list_to_proper_list [ScmSymbol "quote"; sexpr]
| ScmConst s -> s
| ScmVar (name) -> ScmSymbol(name)
| ScmIf (test, dit, ScmConst (ScmVoid)) -> untag_tagged_list "if" [test; dit]
| ScmIf (test, dit, dif) -> untag_tagged_list "if" [test; dit; dif]
| ScmSeq(exprs) -> untag_tagged_list "begin" exprs
| ScmSet (var, value) -> untag_tagged_list "set!" [var; value]
| ScmDef (var, value) -> untag_tagged_list "define" [var; value]
| ScmOr (exprs) -> untag_tagged_list "or" exprs
| ScmLambdaSimple (vars, ScmSeq(body)) ->
    let vars = list_to_proper_list (untag_vars vars) in
    let body = List.map untag body in
    list_to_proper_list ([ScmSymbol "lambda"; vars]@body)
| ScmLambdaSimple (vars, body) ->
    let vars = list_to_proper_list (untag_vars vars) in
    list_to_proper_list ([ScmSymbol "lambda"; vars; untag body])
| ScmLambdaOpt (vars, var, ScmSeq(body)) ->
    let body = List.map untag body in
    untag_lambda_opt vars var body
| ScmLambdaOpt (vars, var, body) ->
    let body = [untag body] in
    untag_lambda_opt vars var body
| ScmApplic(procedure, args) -> list_to_proper_list (List.map untag (procedure::args));;


let rec string_of_expr expr =
string_of_sexpr (untag expr)

let scm_number_eq n1 n2 =
match n1, n2 with
| ScmRational(numerator1, denominator1), ScmRational(numerator2, denominator2) ->
        numerator1 = numerator2 && denominator1 = denominator2
| ScmReal(real1), ScmReal(real2) -> abs_float(real1 -. real2) < 0.001
| _, _ -> false

let rec sexpr_eq s1 s2 =
match s1, s2 with
| (ScmVoid, ScmVoid) | (ScmNil, ScmNil)  -> true
| ScmBoolean(bool1), ScmBoolean(bool2) -> bool1 = bool2
| ScmChar(char1), ScmChar(char2) -> char1 = char2
| ScmString(string1), ScmString(string2) -> String.equal string1 string2
| ScmSymbol(symbol1), ScmSymbol(symbol2) -> String.equal symbol1 symbol2
| ScmNumber(number1), ScmNumber(number2) -> scm_number_eq number1 number2
| ScmVector(sexprs1), ScmVector(sexprs2) -> List.for_all2 sexpr_eq sexprs1 sexprs2
| ScmPair(car1, cdr1), ScmPair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
| _, _ -> false

let rec expr_eq e1 e2 =
  match e1, e2 with
  | ScmConst (sexpr1), ScmConst (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar (var1), ScmVar (var2) -> String.equal var1 var2
  | ScmIf (test1, dit1, dif1), ScmIf (test2, dit2, dif2) -> (expr_eq test1 test2) &&
                                            (expr_eq dit1 dit2) &&
                                              (expr_eq dif1 dif2)
  | (ScmSeq(exprs1), ScmSeq(exprs2) | ScmOr (exprs1), ScmOr (exprs2)) ->
        List.for_all2 expr_eq exprs1 exprs2
  | (ScmSet (var1, val1), ScmSet (var2, val2) | ScmDef (var1, val1), ScmDef (var2, val2)) ->
        (expr_eq var1 var2) && (expr_eq val1 val2)
  | ScmLambdaSimple (vars1, body1), ScmLambdaSimple (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmLambdaOpt (vars1, var1, body1), ScmLambdaOpt (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmApplic (e1, args1), ScmApplic (e2, args2) ->
     (expr_eq e1 e2) && (List.for_all2 expr_eq args1 args2)
  | _ -> false;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
end;; 

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;

let rec is_proper_list sexpr = 
match sexpr with
  |ScmNil -> true
  |ScmPair(_, cdr) -> is_proper_list cdr
  |_-> false;;

let rec improper_args l = 
  match l with
    |ScmPair (hd, tl) -> hd::(improper_args tl)
    |ScmSymbol(x) -> [];;;;
  
let rec improper_more_args l = 
  match l with
    |ScmPair (hd, tl) -> improper_more_args tl
    |ScmSymbol(x) -> [ScmSymbol(x)];;

let is_reserved_word x = ormap (fun reserved_word -> (String.equal reserved_word x)) reserved_word_list;;

let rec tag_parse_expression sexpr =
  let sexpr = macro_expand sexpr in
  match sexpr with
    
  (* Self-Evaluated expressions *)
  |ScmNil -> ScmConst(ScmNil)
  |ScmPair(ScmSymbol "quote", ScmPair(value,ScmNil)) -> ScmConst(value)
  |ScmBoolean(x) -> ScmConst (sexpr)
  |ScmChar(x) -> ScmConst (sexpr)
  |ScmNumber(x) -> ScmConst (sexpr)
  |ScmString(x) -> ScmConst (sexpr)

(* quasiquote expression*)
  |ScmPair(ScmSymbol "quasiquote", ScmPair(value,ScmNil)) -> 
  let rec f sexp =
    match sexp with
      (* Base cases *)
      |ScmSymbol(_) as sym-> ScmPair(ScmSymbol "quote", ScmPair(sym, ScmNil))
      |ScmNil -> ScmPair(ScmSymbol "quote", ScmPair(ScmNil, ScmNil))
      |ScmPair(ScmSymbol "unquote", ScmPair(x, ScmNil)) -> x
      |ScmPair(ScmSymbol "unquote-splicing", x) -> ScmPair(ScmSymbol "quote", ScmPair(ScmPair(ScmSymbol "unquote-splicing", x), ScmNil))
      |ScmVector(x) -> ScmPair(ScmSymbol "list->vector", ScmPair((f (list_to_proper_list x)), ScmNil))
      (* Step *)
      |ScmPair(car,cdr) ->
        (match car with 
          |ScmPair(ScmSymbol "unquote-splicing", ScmPair(value,ScmNil)) -> (list_to_proper_list [ScmSymbol "append"; value; (f cdr);])
          |_-> (list_to_proper_list [ScmSymbol "cons"; (f car); (f cdr);]))
      |_-> sexp in
  tag_parse_expression (f value)

  
  (* var delcartion *)
  |ScmSymbol(x) -> 
    if (is_reserved_word x) then raise (X_reserved_word x) else ScmVar(x)

  (* and expression *)
    |ScmPair (ScmSymbol "and", ScmNil) -> ScmConst(ScmBoolean true)
    |ScmPair (ScmSymbol "and", ScmPair(exp, ScmNil)) -> tag_parse_expression exp
    |ScmPair (ScmSymbol "and", ScmPair(car,cdr)) -> 
      let args = tag_parse_expression car  :: List.map tag_parse_expression (scm_list_to_list cdr) in
      let rec buildAndExp l = 
        match l with 
          car::[] -> car
          |car::cdr -> ScmIf(car, buildAndExp cdr, ScmConst(ScmBoolean false)) in
      buildAndExp args

  (* or expression *)
  |ScmPair (ScmSymbol "or", ScmNil) -> ScmConst(ScmBoolean false)
  |ScmPair (ScmSymbol "or", ScmPair(exp, ScmNil)) -> tag_parse_expression exp
  |ScmPair (ScmSymbol "or", ScmPair(car,cdr)) -> 
    let first = tag_parse_expression car in
    let rest = List.map tag_parse_expression (scm_list_to_list cdr) in
    ScmOr (first::rest)
  
  (* if expression *)
  (* if-then-else *)
  |ScmPair (ScmSymbol "if", ScmPair(test, ScmPair(dit, ScmPair(dif, ScmNil)))) -> ScmIf ((tag_parse_expression test), (tag_parse_expression dit), (tag_parse_expression dif))
  (* if-then *)
  |ScmPair (ScmSymbol "if", ScmPair(test, ScmPair(dit, ScmNil))) -> ScmIf ((tag_parse_expression test), (tag_parse_expression dit), (ScmConst ScmVoid))
  
  (* begin expression *)
  |ScmPair (ScmSymbol "begin", ScmNil) -> ScmConst ScmVoid
  |ScmPair (ScmSymbol "begin", ScmPair(car, cdr)) -> 
    let first = tag_parse_expression car in
    let rest = List.map tag_parse_expression (scm_list_to_list cdr) in
    let body = first::rest in
    if (List.length body) = 1 
    then
      List.hd body
    else
      ScmSeq (body)

  (* set! expression *)
  |ScmPair (ScmSymbol "set!", ScmPair(ScmSymbol(var_name), ScmPair(var_value, ScmNil))) -> ScmSet (ScmVar(var_name),(tag_parse_expression var_value))
  
  (* lambda expression *)
  (* lambda simple *)
  |ScmPair (ScmSymbol "lambda", ScmPair(arglist, body)) ->
    let is_proper_list = scm_is_list arglist in
    if is_proper_list 
    then
      let vars = extract_lambda_params (scm_list_to_list arglist) in
      let exprs = List.map tag_parse_expression (scm_list_to_list body) in
      let n = List.length exprs in
        if (n > 1) 
        then 
          ScmLambdaSimple (vars, ScmSeq (exprs))
        else 
          if n == 1 
          then 
            ScmLambdaSimple (vars, (List.hd exprs))
          else 
            ScmLambdaSimple (vars, ScmConst(ScmVoid))
    else (* lambda opt *)
      let vars = extract_lambda_params (improper_args arglist) in
      let more_vars = match (improper_more_args arglist) with [ScmSymbol(x)] -> x |_-> "never" in
      let exprs = List.map tag_parse_expression (scm_list_to_list body) in
      let n = List.length exprs in
        if (n > 1) 
        then 
          ScmLambdaOpt (vars, more_vars, ScmSeq (exprs))
        else 
          if n == 1 then 
            ScmLambdaOpt (vars, more_vars, (List.hd exprs))
        else 
          ScmLambdaOpt(vars, more_vars, ScmConst(ScmVoid))
      
  (* define expression *)
  (* simple define *)
  |ScmPair (ScmSymbol "define", ScmPair(ScmSymbol(v) as var, value)) -> 
    let var = tag_parse_expression var in
    let exp = List.map tag_parse_expression (scm_list_to_list value) in
    (match var with 
      |ScmVar(v) -> ScmDef (var, (List.hd exp))
      |_-> raise (X_reserved_word v))

  (* MIT define proper list - have to check*)
  |ScmPair (ScmSymbol "define", ScmPair(ScmPair(ScmSymbol(fun_name), arglist), body)) -> 
    let name = ScmVar(fun_name) in
    let is_proper_list = scm_is_list arglist in
    if is_proper_list 
    then
      let vars = extract_lambda_params (scm_list_to_list arglist) in
      let exprs = List.map tag_parse_expression (scm_list_to_list body) in
      let n = List.length exprs in
        if (n > 1) 
        then 
          ScmDef(name, ScmLambdaSimple (vars, ScmSeq (exprs)))
        else 
          if n == 1 
          then 
            ScmDef(name, ScmLambdaSimple (vars, (List.hd exprs)))
          else ScmDef(name, ScmLambdaSimple (vars, ScmConst(ScmVoid)))
    else
      let vars = extract_lambda_params (improper_args arglist) in
      let more_vars = match improper_more_args arglist with [ScmSymbol(x)] -> x |_-> "never" in
      let exprs = List.map tag_parse_expression (scm_list_to_list body) in
      let n = List.length exprs in
        if (n > 1) 
        then 
          ScmDef(name, ScmLambdaOpt (vars, more_vars, ScmSeq (exprs)))
        else
          if n == 1 
          then 
            ScmDef(name, ScmLambdaOpt (vars, more_vars, (List.hd exprs)))
        else 
          ScmDef(name, ScmLambdaOpt(vars, more_vars, ScmConst(ScmVoid)))

  (* Let expression - without variables *)
  |ScmPair(ScmSymbol "let", ScmPair(ScmNil, body)) -> tag_parse_empty_let body

  (* Let expression - with variables *)
  |ScmPair(ScmSymbol "let", ScmPair(bindings, body)) -> 
    let ribs = create_let_ribs (scm_list_to_list bindings) in
    let vars = List.rev_map extract_let_rib_var ribs in
    let vals = List.rev_map extract_let_rib_value ribs in
    let body = List.map tag_parse_expression (scm_list_to_list body) in
    let n = List.length body in
    if n == 1 
    then 
      ScmApplic (ScmLambdaSimple (vars, List.hd body), vals)
    else 
      ScmApplic (ScmLambdaSimple (vars, ScmSeq(body)), vals)

  (* Let* expression *) 
  (* Base case: without variables *)
  |ScmPair(ScmSymbol "let*", ScmPair(ScmNil, body)) -> tag_parse_empty_let body
  
  (*Step: with at least one variable*)
  |ScmPair(ScmSymbol "let*", ScmPair(bindings, body)) -> 
    let ribs = create_let_ribs (scm_list_to_list bindings) in
    let body = List.map tag_parse_expression (scm_list_to_list body) in
    List.fold_left (fun acc curr -> ScmApplic (ScmLambdaSimple([extract_let_rib_var curr], acc), [extract_let_rib_value curr])) (List.hd body) ribs
  
  (* Letrec expression *) 
  (* Base case: without variables *)
  |ScmPair(ScmSymbol "letrec", ScmPair(ScmNil, body)) -> tag_parse_empty_let body
  
  (*Step: with at least one variable*)
  |ScmPair(ScmSymbol "letrec", ScmPair(bindings, body)) -> 
    let ribs = create_let_ribs (scm_list_to_list bindings) in
    let body = List.map tag_parse_expression (scm_list_to_list body) in
    let assinments = List.rev_map (fun rib -> ScmSet(ScmVar (extract_let_rib_var rib), (extract_let_rib_value rib))) ribs in
    let rec init_default_values n value acc = 
      if n==0 then acc else init_default_values (n-1) value (ScmConst(ScmSymbol value)::acc) in
    let n = List.length ribs in
    let default_values = init_default_values n "whatever" [] in
    let vars = List.rev_map extract_let_rib_var ribs in
    ScmApplic (ScmLambdaSimple(vars, ScmSeq(assinments@body)), default_values)
  
  
  (* Cond expression *)
  |ScmPair(ScmSymbol "cond", ScmPair(ScmNil,ScmNil)) -> raise (X_syntax_error (sexpr, "Cond must has at least one rib"))
  |ScmPair(ScmSymbol "cond", ScmPair(rib, ribs)) -> 
    let rib = List.map extract_cond_rib [rib] in
    let ribs = List.map extract_cond_rib (scm_list_to_list ribs) in
    let ribs = rib@ribs in
    let rec buildCondExp ribs = 
      match ribs with
        |[] -> ScmConst(ScmVoid)
        |car::cdr -> 
          match car with
          |CondRibEmpty(_) -> ScmConst(ScmVoid)
          |CondRibElse(exprs)-> 
            let n = List.length exprs in
            if n>1 
            then 
              ScmSeq(exprs)
            else
              List.hd exprs
          |CondRibArrow(test,exprf) -> 
            let params = ["value"; "f"; "rest";] in
            let value = ScmVar "value" in
            let f = ScmVar "f" in 
            let rest = ScmVar "rest" in
            let body = ScmIf (value, ScmApplic((ScmApplic(f, [])), [value]), ScmApplic(rest, [])) in
            let value = test in
            let f = ScmLambdaSimple([], exprf) in
            ScmApplic (ScmLambdaSimple (params, body), [value; f; ScmLambdaSimple([], buildCondExp cdr);])
          |CondRibDefault(test, exprs) -> 
            if ((List.length exprs) > 1) then ScmIf(test, ScmSeq(exprs), buildCondExp cdr) else ScmIf(test, List.hd exprs, buildCondExp cdr) in

    buildCondExp ribs
  

  (* Application expression *)
  (* Application expression - without variables *)
  |ScmPair(proc, ScmNil)->
    ScmApplic(tag_parse_expression proc, []) 

  (* Application expression - with variables *)
  |ScmPair(proc, ScmPair(first, rest)) ->
    let op =  tag_parse_expression proc in
    let args = (tag_parse_expression first) :: (List.map tag_parse_expression (scm_list_to_list rest)) in
    ScmApplic(op, args) 

  |_-> raise (X_syntax_error (sexpr, "Sexpr stracture not recognized"))


(* Extract lambda params *)
and extract_lambda_params params = 
  let map = Hashtbl.create 16 in
  let rec f list acc = 
    match list with
    [] -> acc 
    |car::cdr ->
      match car with 
        |ScmSymbol(var) -> 
          if (is_reserved_word var)
          then 
            raise (X_reserved_word var) 
          else
            if Hashtbl.mem map var 
              then
                raise (X_duplicates_params var)
              else
                begin
                  Hashtbl.add map var var; (* identity function *)
                  f cdr acc@[var];
                end
          |_-> raise (X_syntax_error (car, "invalid lambda parameter")) in
  List.rev (f params [])
  
(* Create LetRib(var,value) out of any binding*)
and create_let_ribs ribs =
  let map = Hashtbl.create 16 in
  let rec f list acc = 
    match list with 
    [] -> acc 
    |car::cdr -> 
      match car with 
        |ScmPair(ScmSymbol(var),ScmPair(value, ScmNil)) -> 
          if (is_reserved_word var)
          then 
            raise (X_reserved_word var) 
          else
            if Hashtbl.mem map var 
              then
                raise (X_duplicates_params var)
              else
                begin
                  Hashtbl.add map var var; (* identity function *)
                  f cdr acc@[LetRib(var, tag_parse_expression value)];
                end
        |_-> raise (X_syntax_error (car, "Let-rib-error: invalid let binding expression")) in
  f ribs []

and extract_let_rib_var rib =
  match rib with
    LetRib(var, value) -> var
    |_-> "never"

and extract_let_rib_value rib =
  match rib with
    LetRib(var, value) -> value
    |_-> ScmConst(ScmString "never")
      
(* Create CondRib corresponding to rib *)
and extract_cond_rib rib = 
  match rib with 
    |ScmPair(test, ScmPair(ScmSymbol "=>", ScmPair(exprf, ScmNil))) ->
      let test = tag_parse_expression test in
      let exprf = tag_parse_expression exprf in
      CondRibArrow(test, exprf)

    |ScmPair(ScmSymbol "else", exprs) ->
      let exprs = List.map tag_parse_expression (scm_list_to_list exprs) in 
      CondRibElse(exprs)

    |ScmPair(test,exprs) -> 
      let test = tag_parse_expression test in
      let exprs = List.map tag_parse_expression (scm_list_to_list exprs) in
      CondRibDefault(test, exprs)
    
    |ScmNil -> CondRibEmpty([])

    |_-> raise (X_syntax_error (rib, "cond-rib-error: invalid cond rib expression"))


and tag_parse_empty_let body = 
  let body = List.map tag_parse_expression (scm_list_to_list body) in
  let n = List.length body in
  if n== 1 
  then 
    ScmApplic (ScmLambdaSimple ([], List.hd body), [])
  else 
    ScmApplic(ScmLambdaSimple ([], ScmSeq(body)), [])

and macro_expand sexpr =
  match sexpr with

  | _ -> sexpr
end;; 

