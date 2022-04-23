(* semantic-analyser.ml
 * The semantic analysis phase of the compiler
 *
 * Programmer: Mayer Goldberg, 2021
 *)
#use "tag-parser.ml";;


exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type var' = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | ScmConst' of sexpr
  | ScmVar' of var'
  | ScmBox' of var'
  | ScmBoxGet' of var'
  | ScmBoxSet' of var' * expr'
  | ScmIf' of expr' * expr' * expr'
  | ScmSeq' of expr' list
  | ScmSet' of var' * expr'
  | ScmDef' of var' * expr'
  | ScmOr' of expr' list
  | ScmLambdaSimple' of string list * expr'
  | ScmLambdaOpt' of string list * string * expr'
  | ScmApplic' of expr' * (expr' list)
  | ScmApplicTP' of expr' * (expr' list);;


let var_eq v1 v2 =
  match v1, v2 with
    | VarFree (name1), VarFree (name2) -> String.equal name1 name2
    | VarBound (name1, major1, minor1), VarBound (name2, major2, minor2) ->
      major1 = major2 && minor1 = minor2 && (String.equal name1 name2)
    | VarParam (name1, index1), VarParam (name2, index2) ->
          index1 = index2 && (String.equal name1 name2)
    | _ -> false

let list_eq eq l1 l2 = (List.length l1) = (List.length l2) && List.for_all2 eq l1 l2;;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | ScmConst' (sexpr1), ScmConst' (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar' (var1), ScmVar' (var2) -> var_eq var1 var2
  | ScmIf' (test1, dit1, dif1), ScmIf' (test2, dit2, dif2) -> (expr'_eq test1 test2) &&
                                            (expr'_eq dit1 dit2) &&
                                              (expr'_eq dif1 dif2)
  | (ScmSeq' (exprs1), ScmSeq' (exprs2) | ScmOr' (exprs1), ScmOr' (exprs2)) ->
        list_eq expr'_eq exprs1 exprs2
  | (ScmSet' (var1, val1), ScmSet' (var2, val2) | ScmDef' (var1, val1), ScmDef' (var2, val2)) ->
        (var_eq var1 var2) && (expr'_eq val1 val2)
  | ScmLambdaSimple' (vars1, body1), ScmLambdaSimple' (vars2, body2) ->
      (list_eq String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmLambdaOpt' (vars1, var1, body1), ScmLambdaOpt' (vars2, var2, body2) ->
      (String.equal var1 var2) &&
        (list_eq String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmApplic' (e1, args1), ScmApplic' (e2, args2) ->
      (expr'_eq e1 e2) && (list_eq expr'_eq args1 args2)
  | ScmApplicTP' (e1, args1), ScmApplicTP' (e2, args2) ->
      (expr'_eq e1 e2) && (list_eq expr'_eq args1 args2)
  | ScmBox' (v1), ScmBox' (v2) -> var_eq v1 v2
  | ScmBoxGet' (v1), ScmBoxGet' (v2) -> var_eq v1 v2
  | ScmBoxSet' (v1, e1), ScmBoxSet' (v2, e2) -> (var_eq v1 v2) && (expr'_eq e1 e2)
  | _ -> false;;

let unannotate_lexical_address = function
| (VarFree name | VarParam (name, _) | VarBound (name, _, _)) -> ScmVar name

let rec unanalyze expr' =
match expr' with
  | ScmConst' s -> ScmConst(s)
  | ScmVar' var -> unannotate_lexical_address var
  | ScmBox' var -> ScmApplic(ScmVar "box", [unannotate_lexical_address var])
  | ScmBoxGet' var -> unannotate_lexical_address var
  | ScmBoxSet' (var, expr') -> ScmSet (unannotate_lexical_address var, unanalyze expr')
  | ScmIf' (test, dit, dif) -> ScmIf (unanalyze test, unanalyze dit, unanalyze dif)
  | ScmSeq' expr's -> ScmSeq (List.map unanalyze expr's)
  | ScmSet' (var, expr') -> ScmSet (unannotate_lexical_address var, unanalyze expr')
  | ScmDef' (var, expr') -> ScmDef (unannotate_lexical_address var, unanalyze expr')
  | ScmOr' expr's -> ScmOr (List.map unanalyze expr's)
  | ScmLambdaSimple' (params, expr') ->
        ScmLambdaSimple (params, unanalyze expr')
  | ScmLambdaOpt'(params, param, expr') ->
        ScmLambdaOpt (params, param, unanalyze expr')
  | (ScmApplic' (expr', expr's) | ScmApplicTP' (expr', expr's)) ->
        ScmApplic (unanalyze expr', List.map unanalyze expr's);;

let string_of_expr' expr' =
    string_of_expr (unanalyze expr');;

(*Use for debugging purposes *)
let rec string_of_expr'_list l acc = 
  match l with
    | [] -> acc
    | car::cdr -> string_of_expr'_list cdr (acc ^ " " ^ (string_of_expr' car));; 

module type SEMANTIC_ANALYSIS = sig
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
  val rdc_rac : 'a list ->'a list * 'a 
  val run_semantics : expr -> expr'
end;; (* end of module type SEMANTIC_ANALYSIS *)

module Semantic_Analysis : SEMANTIC_ANALYSIS = struct

  let rec lookup_in_rib name = function
    | [] -> None
    | name' :: rib ->
       if name = name'
       then Some(0)
       else (match (lookup_in_rib name rib) with
             | None -> None
             | Some minor -> Some (minor + 1));;

  let rec lookup_in_env name = function
    | [] -> None
    | rib :: env ->
       (match (lookup_in_rib name rib) with
        | None ->
           (match (lookup_in_env name env) with
            | None -> None
            | Some(major, minor) -> Some(major + 1, minor))
        | Some minor -> Some(0, minor));;

  let tag_lexical_address_for_var name params env = 
    match (lookup_in_rib name params) with
    | None ->
       (match (lookup_in_env name env) with
        | None -> VarFree name
        | Some(major, minor) -> VarBound(name, major, minor))
    | Some minor -> VarParam(name, minor);;

  (* run this first! *)
  let annotate_lexical_addresses pe = 
   let rec run pe params env =
      match pe with 
      | ScmConst(c) -> ScmConst'(c)
      | ScmVar(name) -> ScmVar' (tag_lexical_address_for_var name params env)
      | ScmIf(test, t, e) -> ScmIf'(run test params env, run t params env, run e params env)
      | ScmSeq(list) -> ScmSeq'(List.map (fun x -> run x params env) list)
      | ScmSet(var_name, value) -> ScmSet'((match (run var_name params env) with ScmVar'(v') -> v' |_-> raise X_this_should_not_happen), run value params env)
      | ScmDef(var_name, value) -> ScmDef'((match (run var_name params env) with ScmVar'(v') -> v' |_-> raise X_this_should_not_happen), run value params env)
      | ScmOr(list) -> ScmOr'(List.map (fun x -> run x params env) list)
      | ScmLambdaSimple(l_params, body) -> ScmLambdaSimple'(l_params, run body l_params (params::env))
      | ScmLambdaOpt(lo_params, opt, body) -> ScmLambdaOpt'(lo_params, opt, run body  (lo_params@[opt]) ((params@[opt])::env))
      | ScmApplic(proc_name, arguments) -> ScmApplic'(run proc_name params env, List.map (fun arg -> run arg params env) arguments)
   in 
   run pe [] [];;

  let rec rdc_rac s =
    match s with
    | [e] -> ([], e)
    | e :: s ->
       let (rdc, rac) = rdc_rac s
       in (e :: rdc, rac)
    | _ -> raise X_this_should_not_happen;;

     
  let annotate_tail_calls pe =
   let rec run pe in_tail =
    match pe with
      | ScmConst'(x) -> pe
      | ScmVar'(x) -> pe
      | ScmIf'(test, dit, dif) -> ScmIf'(test, run dit in_tail, run dif in_tail)
      | ScmSeq'(list) -> ScmSeq'(run_seq list in_tail)
      | ScmSet'(var_name, value) -> ScmSet'(var_name, run value false)
      | ScmDef'(var_name, value) -> ScmDef'(var_name, run value false)
      | ScmOr'(list) -> ScmOr'(run_seq list in_tail)
      | ScmLambdaSimple'(l_params, body) -> ScmLambdaSimple'(l_params, run body true)
      | ScmLambdaOpt'(l_params, opt, body) -> ScmLambdaOpt'(l_params, opt, run body true)
      | ScmApplic'(proc_name, arguments) -> 
                      if in_tail
                      then 
                        ScmApplicTP'(run proc_name false,List.map (fun e -> run e false) arguments)
                      else 
                        ScmApplic'(run proc_name false,List.map (fun e -> run e false) arguments)
      | _ -> raise X_this_should_not_happen


      and run_seq list in_tail = 
        let (hd, tl) = rdc_rac list in
        let hd' = List.map (fun expr' -> run expr' false) hd in
        let tl' = run tl in_tail in
        hd'@[tl'] 

      in 
      run pe false;;

(* boxing *)
let rec box_set expr = 
  match expr with
  | ScmConst'(x) -> expr
  | ScmVar'(x) -> expr
  | ScmBoxGet'(_) -> expr
  | ScmBoxSet'(_) -> expr
  | ScmBox'(_) -> expr
  | ScmIf'(test, dit, dif) -> ScmIf'(box_set test, box_set dit, box_set dif)
  | ScmSeq'(list) -> ScmSeq'(List.map (fun expr' -> box_set expr') list)
  | ScmSet'(var_name, value) -> ScmSet'(var_name, box_set value)
  | ScmDef'(var_name, value) -> ScmDef'(var_name, box_set value)
  | ScmOr'(list) -> ScmOr'(List.map (fun expr' -> box_set expr') list)
  | ScmLambdaSimple'(params, body) -> reconstruct params body expr "dummy"
  | ScmLambdaOpt'(params, opt, body) -> reconstruct params body expr opt
  | ScmApplic'(proc_name, arguments) -> ScmApplic'(box_set proc_name, List.map (fun expr' -> box_set expr') arguments)
  | ScmApplicTP'(proc_name, arguments) -> ScmApplicTP'(box_set proc_name, List.map (fun expr' -> box_set expr') arguments)

(* Scan expr and all its sub-expressions.
   Return a tuple (R, W) where 
   R - lambda expressions which contains read calls to param name
   W - lambda expressions which contains write calls to param name 
   param enclosing_lambda will be changed at most one! *)
and find_reads_writes name enclosing_lambda expr = 
  let read_calls = ref [] in
  let write_calls = ref [] in
  let selector = fun inner outer -> inner in
  let rec f name enclosing_lambda expr selector = 
    match expr with
      | ScmVar'(VarParam(var_name, _)) | ScmVar'(VarBound(var_name, _, _)) 
      | ScmBoxGet'(VarParam(var_name, _)) | ScmBoxGet'(VarBound(var_name, _, _))->
        if (String.equal var_name name)
        then 
          read_calls :=  (enclosing_lambda :: !read_calls)
        else 
          ()                                                                               
      | ScmSet'((VarFree(var_name) | VarParam(var_name, _) | VarBound(var_name, _, _)), value) 
      | ScmBoxSet'((VarFree(var_name) | VarParam(var_name, _) | VarBound(var_name, _, _)), value)->
        if (String.equal var_name name)
        then 
          let () = write_calls :=  (enclosing_lambda :: !write_calls) in
          f name enclosing_lambda value selector
        else 
          f name enclosing_lambda value selector
      | ScmDef'(_, value) -> f name enclosing_lambda value selector                                                                   
      | ScmIf'(test, dit, dif) -> 
        let () = f name enclosing_lambda test selector in
        let () = f name enclosing_lambda dit selector in
        f name enclosing_lambda dif selector
      | ScmOr'(list) -> let dummy = List.map (fun expr' -> f name enclosing_lambda expr' selector) list in ()
      | ScmSeq'(list) -> let dummy = List.map (fun expr' -> f name enclosing_lambda expr' selector) list in ()
      | ScmLambdaSimple'(params, body)-> 
        if (not (List.exists (fun p -> String.equal p name) params))
            then 
              f name (selector expr enclosing_lambda) body (fun inner outer -> outer)
            else 
              ()
      | ScmLambdaOpt'(params, opt, body) -> 
        if (not (String.equal opt name)) && (not (List.exists (fun p -> String.equal p name) params))
          then 
            f name (selector expr enclosing_lambda) body (fun inner outer -> outer)
          else 
            ()
      | ScmApplic'(proc_name, arguments) -> let dummy = List.map (fun expr' -> f name enclosing_lambda expr' selector) (proc_name::arguments) in ()
      | ScmApplicTP'(proc_name, arguments) -> let dummy = List.map (fun expr' -> f name enclosing_lambda expr' selector) (proc_name::arguments) in () 
      | _-> ()
      in
  let () = (f name enclosing_lambda expr selector) in
  (!read_calls, !write_calls)

(* Determine if a paramteter need to be boxed *)
and should_box read_calls write_calls =
  let n = List.length read_calls in
  let m = List.length write_calls in
  if n = 0  || m = 0
  then
    false
  else
    let hd = List.hd read_calls in
    not (List.fold_left (fun acc curr -> acc && (curr == hd)) true (read_calls @ write_calls))
        
(* Create new body in which read,write calls are replaced with ScmBoxGet',ScmBoxSet' *)
and reconstruct params body enclosing_lambda opt  =
  let origin_params = params in

  let add_boxed_params body acc_boxed = 
    if List.length acc_boxed > 0
    then
      match body with
      |ScmSeq'(list) -> ScmSeq'(acc_boxed @ list)
      |_ -> ScmSeq'(acc_boxed  @ [body])
    else
      body in
    
  let rec f params body param_index acc_boxed = 
    match params with
      | [] -> 
        if String.equal opt "dummy"
        then
          ScmLambdaSimple' (origin_params, box_set (add_boxed_params body acc_boxed))
        else
          ScmLambdaOpt' (origin_params, opt, (add_boxed_params body acc_boxed))
      | car::cdr ->
        let (read_calls, write_calls) = find_reads_writes car enclosing_lambda body in
        if should_box read_calls write_calls
        then
          let body = (dfs body car) in
          let param' = VarParam(car, param_index) in
          let boxed_param = ScmSet'(param', ScmBox'(param')) in
          f cdr body (param_index + 1) (acc_boxed @ [boxed_param])
        else
          f cdr body (param_index + 1) acc_boxed 
    in
    (f (if String.equal opt "dummy" then params else params@[opt]) body 0 [])

(* Run DFS scan on body of lambda 
   Replace read, write calls to param with ScmBoxGet', ScmBoxSet' *)
and dfs pe param = 
  match pe with
    | ScmConst'(_) -> pe
    | ScmBoxGet'(_) -> pe
    | ScmBox'(_) -> pe
    | ScmVar'(VarFree(_)) -> pe
    | ScmVar'(VarBound(param', _, _) as v') -> 
      if String.equal param param' 
      then
        ScmBoxGet'(v')
      else
        pe
    | ScmVar'(VarParam(param', _) as v') -> 
      if String.equal param param' 
      then
        ScmBoxGet'(v')
      else
        pe
    | ScmIf'(test, dit, dif) -> ScmIf'(dfs test param, dfs dit param, dfs dif param)
    | ScmSeq'(list) -> ScmSeq' (List.map (fun expr' -> dfs expr' param) list)
    | ScmSet'(VarFree(v) as v', value) -> ScmSet'(v', dfs value param)
    | ScmSet'(VarBound(v, _, _) as v', value) -> 
      if String.equal v param
      then
        ScmBoxSet'(v', dfs value param)
      else
        ScmSet'(v', dfs value param)
    | ScmSet'(VarParam(v,_) as v', value) -> 
      if String.equal v param
      then
        ScmBoxSet'(v', dfs value param)
      else
        ScmSet'(v', dfs value param)
    | ScmBoxSet'(v', value) -> ScmBoxSet'(v', dfs value param)
    | ScmDef'(var_name, value) -> ScmDef'(var_name, dfs value param)
    | ScmOr'(list) -> ScmOr' (List.map (fun expr' -> dfs expr' param) list)
    | ScmLambdaSimple'(l_params, body) ->
      if List.exists (fun p -> String.equal p param) l_params 
      then
        pe
      else
        let body' = dfs body param in
        ScmLambdaSimple'(l_params, body')
    | ScmLambdaOpt'(l_params, opt, body) -> 
      if String.equal opt param || List.exists (fun p -> String.equal p param) l_params
      then
        pe
      else
        let body' = dfs body param in
        ScmLambdaOpt'(l_params, opt, body')
    | ScmApplic'(proc_name, arguments) -> 
        let proc_name' = dfs proc_name param in
        let arguments' = List.map (fun arg' -> dfs arg' param) arguments in
        ScmApplic'(proc_name', arguments')
    | ScmApplicTP'(proc_name, arguments) -> 
        let proc_name' = dfs proc_name param in
        let arguments' = List.map (fun arg' -> dfs arg' param) arguments in
        ScmApplicTP'(proc_name', arguments')
        
  let run_semantics expr =
    box_set
      (annotate_tail_calls
         (annotate_lexical_addresses expr))

end;; (* end of module Semantic_Analysis *)
