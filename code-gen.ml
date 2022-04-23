#use "semantic-analyser.ml";;

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
  val make_consts_tbl : expr' list -> (sexpr * (int * string)) list

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
  val generate : (sexpr * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct

  (* Labels generator *)
  let make_counter () =
    let count = ref (-1) in
    fun () ->
      incr count;
      !count;; 
      
  (* Generator for Lexit labels in or expression *)
  let generate_condition_statments_labels = make_counter ();;
  
  (* Generator for Lcode, Lcont in lambda expression *)
  let generate_lambda_simple_labels = make_counter ();;

  let make_consts_tbl asts = 
    (* var offset: next avalible cell in the constant table *)
    let offset = ref 6 in
    (* map constant sexpr to their offset in the constant table *)
    let table = Hashtbl.create 128 in
    let () = Hashtbl.add table ScmVoid 0 in
    let () = Hashtbl.add table ScmNil 1 in
    let () = Hashtbl.add table (ScmBoolean(false)) 2 in
    let () = Hashtbl.add table (ScmBoolean(true)) 4 in
    (* accumlator - initalize with : void, nil, false, true *)
    let constant_table = ref [(ScmVoid, (0, "db T_VOID")); 
                              (ScmNil, (1, "db T_NIL"));
                              (ScmBoolean(false), (2, "db T_BOOL, 0"));
                              (ScmBoolean(true), (4, "db T_BOOL, 1"));] in
    (* return next avalible offset. advance var offset to next free cell. *)
    let get_offset sexpr = 
      match sexpr with
      | ScmVoid | ScmNil -> 
        let next_offset = !offset in
        let () = offset := !offset + 1 in
        next_offset
      | ScmChar(_) | ScmBoolean(_) -> 
        let next_offset = !offset in
        let () = offset := !offset + 2 in
        next_offset
      | ScmNumber(ScmRational(num, den)) ->
        let next_offset = !offset in
        let () = offset := !offset + 17 in
        next_offset
      | ScmNumber(ScmReal(real)) -> 
        let next_offset = !offset in
        let () = offset := !offset + 9 in
        next_offset
      | ScmSymbol(_)->
        let next_offset = !offset in
        let () = offset := !offset + 9 in
        next_offset
      | ScmString(str) -> 
        let next_offset = !offset in
        let () = offset := !offset + (9 + (String.length str)) in
        next_offset
      | ScmPair(_, _) ->
        let next_offset = !offset in
        let () = offset := !offset + 17 in
        next_offset
    in
    (* Generate 8086 assembly instruction to add param sexpr to the constant table  *)
    let generate_assembly_instruction sexpr offset_car offset_cdr = 
      match sexpr with
      | ScmVoid -> "db T_VOID"
      | ScmNil -> "db T_NIL"
      | ScmBoolean(flag) -> if flag then "db T_BOOL, 0" else "db T_BOOL, 1"
      | ScmChar(ch) -> Printf.sprintf "MAKE_LITERAL_CHAR(%s)" (string_of_int (int_of_char ch)) 
      | ScmNumber(ScmRational (num, den))-> Printf.sprintf "MAKE_LITERAL_RATIONAL(%d, %d)" num den
      | ScmNumber(ScmReal (f))-> Printf.sprintf "MAKE_LITERAL_FLOAT(%f)" f 
      | ScmString(str) -> Printf.sprintf  "MAKE_LITERAL_STRING \"%s\" " str 
      | ScmSymbol(_) -> Printf.sprintf "MAKE_LITERAL_SYMBOL(const_tbl + %d)" offset_car 
      | ScmPair(_, _) -> Printf.sprintf  "MAKE_LITERAL_PAIR(const_tbl + %d, const_tbl + %d)" offset_car offset_cdr
    in
    (* if param sexpr does not contained in table, add it . return it's offset. *)
    let add_literal sexpr = 
      if Hashtbl.mem table sexpr
      then Hashtbl.find table sexpr
      else 
        let offset = get_offset sexpr in
        let () = Hashtbl.add table sexpr offset in
        let assembly_instruction = (generate_assembly_instruction sexpr 0 0) in
        let () = constant_table := !constant_table @ [(sexpr, (offset, assembly_instruction))] in
        offset
    in
    (* allocate literals. return offset of child expressions to their parent *)
    let rec topological_sort sexpr =
      match sexpr with
      | ScmVoid -> 0
      | ScmNil-> 1
      | ScmBoolean(flag) -> if flag then 2 else 1
      | ScmChar(_) | ScmNumber(_) | ScmString(_)-> add_literal sexpr
      | ScmSymbol(str) ->
          let str_offset = topological_sort (ScmString (str)) in
          let offset = get_offset sexpr in
          let assembly_instruction = (generate_assembly_instruction sexpr str_offset 0) in
          let () = constant_table := !constant_table @ [(sexpr, (offset, assembly_instruction))] in
          offset
      | ScmPair(car, cdr) ->
        if Hashtbl.mem table sexpr
        then 
          Hashtbl.find table sexpr
        else
          let car_offset =  topological_sort car in
          let cdr_offset = topological_sort cdr in
          let offset = get_offset sexpr in
          let assembly_instruction = (generate_assembly_instruction sexpr car_offset cdr_offset) in
          let () = constant_table := !constant_table @ [(sexpr, (offset, assembly_instruction))] in
          offset
      | ScmVector(lst) ->
        let lst = List.map topological_sort lst in
        let vector_elements_declartaion = List.fold_left (fun acc curr -> acc ^ (Printf.sprintf "dq const_tbl + %d\n" curr)) "" lst in
        let len = List.length lst in
        let assembly_instruction = Printf.sprintf "db T_VECTOR\n dq %d\n%s\n" len vector_elements_declartaion in
        let off = !offset in
        let () = offset := !offset + (1 + 8 * (len + 1)) in
        let () = constant_table := !constant_table @ [(sexpr, (off, assembly_instruction))] in
        off
    (* Traverse the AST. dispatch ScmConst expression to topological_sort function *)
    and dfs expr' = 
      match expr' with
        | ScmConst'(sexpr) -> 
          let off = topological_sort sexpr in 
          ()
        | ScmVar'(_) | ScmBox' (_) | ScmBoxGet'(_)-> ()
        | ScmIf' (test, dit, dif) -> 
          let off = dfs test in
          let off = dfs dit in
          let off = dfs dif in
          ()
        | ScmSeq'(lst) | ScmOr'(lst) -> 
          let offs = List.map dfs lst in
          ()
        | ScmSet' (_, value) | ScmDef'(_, value) | ScmBoxSet'(_, value) -> 
          let off = dfs value in
          ()
        | ScmLambdaSimple' (_, body) -> 
          let off = dfs body in
          ()
        | ScmLambdaOpt' (_, _, body) ->
          let off = dfs body in
          ()
        | ScmApplic' (e, es) -> 
          let offs = List.map dfs (e::es) in
          ()
        | ScmApplicTP' (e, es) ->
          let offs = List.map dfs (e::es) in
          ()
    in
      let dummy = List.map dfs asts in
      !constant_table;;


  let make_fvars_tbl asts = 
    let table = Hashtbl.create 128 in
    let next_index = ref 32 in
    let free_vals = ref [ ("boolean?", 0); ("flonum?", 1); ("rational?", 2);
    ("pair?", 3); ("null?", 4); ("char?", 5); ("string?", 6);
    ("procedure?", 7); ("symbol?", 8);
    
    ("string-length", 9); ("string-ref", 10); ("string-set!", 11);
    ("make-string", 12); ("symbol->string", 13);
    
    ("char->integer", 14); ("integer->char", 15); ("exact->inexact", 16);
    
    ("eq?", 17);
    
    ("+", 18); ("*", 19); ("/", 20); ("=", 21); ("<", 22);

    ("numerator", 23); ("denominator", 24); ("gcd", 25); ("cons", 26);
    ("car", 27); ("cdr", 28); ("set-car!", 29); ("set-cdr!", 30); ("apply", 31);]

    in
    let init_table () = 
      let dummy = List.map (fun (key, value) -> Hashtbl.add table key value) !free_vals in
      dummy
    in
    let insert_pair fvar_name = 
      if Hashtbl.mem table fvar_name
      then
        ()
      else
        let pair = (fvar_name, !next_index) in
        let () = Hashtbl.add table fvar_name !next_index in
        let () = next_index := (!next_index + 1) in
        let () = free_vals := (!free_vals @ [pair]) in 
        () 
    in
      
   let rec f expr = 
        match expr with
        | ScmVar'(VarFree(fvar_name)) -> insert_pair fvar_name
        | ScmBox'(VarFree(fvar_name)) -> insert_pair fvar_name
        | ScmBoxGet'(VarFree(fvar_name)) -> insert_pair fvar_name
        | ScmBoxSet' (VarFree(fvar_name), e) -> 
          let () = insert_pair fvar_name in 
          f e
        | ScmIf'(test, dit, dif) -> 
          let () = f test in 
          let () = f dit in 
          f dif
        | ScmSeq'(list) -> let m = List.map f list in ()
        | ScmSet'(VarFree(fvar_name), value) -> 
          let () = insert_pair fvar_name in 
          f value
        | ScmSet'(_, value) -> f value
        | ScmDef'(VarFree(fvar_name), value) -> 
          let () = insert_pair fvar_name in 
          f value
        | ScmDef'(_, value) -> f value
        | ScmOr'(list) -> let m = List.map f list in ()
        | ScmLambdaSimple'(_, body) -> f body
        | ScmLambdaOpt'(_, opt, body) -> f body
        | ScmApplic'(proc_name, arguments) -> 
          let () = f proc_name in 
          let m = List.map f arguments in ()
        | ScmApplicTP'(proc_name, arguments) ->
          let () = f proc_name in 
          let m = List.map f arguments in ()
        | _ -> ()
      in
      let init = init_table () in
      let m = List.map f asts in
      !free_vals;; 

  let generate consts fvars e = 
    let const_map = Hashtbl.create 128 
    in
    let fvar_map = Hashtbl.create 128 
    in
    (* Map contant sexpr to its corresponding offset *)
    let init_const_map () = 
      let dummy = List.map (fun (sexpr, (offset, assembly_instruction)) -> Hashtbl.add const_map sexpr offset) consts in
      dummy
    in
    (* Map free variable to its corresponding offset *)
    let init_fvar_map () = 
      let dummy = List.map (fun (fvar, offset) -> Hashtbl.add fvar_map fvar offset) fvars in
      dummy
    in
    let ext_env_code label cnlosing_lambda_num_of_params = 
      Printf.sprintf 
      ";Allocate the extended environment - create vector of size |Env + 1|, copy preivous enrionment
      mov rdx, LEXICAL_ENVIRONMENT
      lea rsi, [rdx + TYPE_SIZE + WORD_SIZE]
      mov rdx, VECTOR_SIZE(rdx)
      mov r12, rdx
      inc rdx ; rdx = |Env| + 1
      MAKE_VECTOR rdi, rdx, rsi, r12, 1 
    
      ;Allocate ExtEnv_0 to point to a vector containing the parameters
      mov r9, %d
      mov r12, r9
      lea r10, [rbp + 4 * WORD_SIZE]  ; r10 contains address of first parameter on the STACK 
      MAKE_VECTOR rdx, r9, r10, r12, 0 ; rdx points to a dynamic vector containing the parameters
      mov qword [rdi + TYPE_SIZE + WORD_SIZE], rdx
      
      MAKE_CLOSURE (rax, rdi, Lcode_%d)
      jmp Lcont_%d\n" 
      cnlosing_lambda_num_of_params label label 
    in
    let cont_code label = 
      Printf.sprintf 
        "Lcont_%d:\n;rest of the code\n" 
          label 
    in
    (* Convert expr', and its nested sub expressions, into assembly 8086 instructions *)
    (* les represent number of parameters in the cnlosing lambda *)
    let rec run expr' les = 
     match expr' with
      | ScmConst'(sexpr) -> Printf.sprintf "mov rax, CONST(%d)\n" (Hashtbl.find const_map sexpr) 
      | ScmVar'(VarParam (_, minor)) -> Printf.sprintf "mov rax, PVAR(%d)\n" minor
      | ScmVar'(VarBound (_, major, minor)) -> 
          Printf.sprintf "BVAR %s, %d, %d\n" "rax" major minor
      | ScmVar'(VarFree (fvar)) -> Printf.sprintf "mov rax, FVAR(%d)\n" (Hashtbl.find fvar_map fvar) 
      | ScmSet'(VarParam (_, minor), expr') -> 
        let expr'_instruction = run expr' les in
        let assignment_instruction = Printf.sprintf "PSET %d\n" minor in
        expr'_instruction ^ assignment_instruction 
      | ScmSet'(VarBound (_, major, minor), expr') ->
        let expr'_instruction = run expr' les in
        let assignment_instruction = Printf.sprintf "BSET %s, %d, %d, %s\n" "rsi" major minor "rax" in
        expr'_instruction ^ assignment_instruction
      | ScmSet'(VarFree (fvar), expr') -> 
        let expr'_instruction = run expr' les in
        let assignment_instruction = Printf.sprintf "FSET %d\n" (Hashtbl.find fvar_map fvar) in
        expr'_instruction ^ assignment_instruction
      | ScmDef' (var', expr') -> run (ScmSet'(var', expr')) les
      | ScmSeq' (lst) -> List.fold_left (fun acc curr -> acc ^ (run curr les)) "" lst
      | ScmOr' (lst) -> (* TODO mark label Lexit_ with % or %% *)
          let (es, e) = Semantic_Analysis.rdc_rac lst in
          let label = generate_condition_statments_labels () in
          let head = List.fold_left (fun acc curr -> acc ^ (run curr les) ^ (Printf.sprintf "cmp rax, SOB_FALSE_ADDRESS\njne Lexit_%d\n" label)) "" es in
          let rest = run e les in
          let rest = rest ^ Printf.sprintf "Lexit_%d:\n" label in
          head ^ rest
      | ScmIf'(test, dit, dif) -> (* TODO mark label Lexit_,Lelse_ with % or %% *)
        let label = generate_condition_statments_labels() in
        let test_suffix = Printf.sprintf "cmp rax, SOB_FALSE_ADDRESS\nje Lelse_%d\n" label in
        let dit_suffix = Printf.sprintf "jmp Lexit_%d\nLelse_%d:\n" label label in
        let dif_suffix = Printf.sprintf "Lexit_%d:\n" label in
        let test_instruction = run test les in
        let dit_instruction =  run dit les in
        let dif_instruction =  run dif les in
        test_instruction ^ test_suffix ^ dit_instruction ^ dit_suffix ^ dif_instruction ^ dif_suffix      
      | ScmBox'(var') ->
        let gen_var = run (ScmVar'(var')) les in
        let box_instruction = "MALLOC r13, WORD_SIZE\nmov qword [r13], rax\nmov rax, r13\n" in
        gen_var ^ box_instruction
      | ScmBoxGet'(var') -> 
        let var'_instruction = run (ScmVar'(var')) les in
        let assignment_instruction =  Printf.sprintf "mov rax, qword [rax]\n" in
        var'_instruction ^ assignment_instruction
      | ScmBoxSet'(var', expr') ->
        let expr'_instruction = run expr' les in
        let var'_instruction = run (ScmVar'(var')) les in
        expr'_instruction ^ "push rax\n" ^ var'_instruction ^ "pop qword [rax]\n" ^ "mov rax, SOB_VOID_ADDRESS\n"
      | ScmLambdaSimple'(params, body) -> 
        let label = generate_lambda_simple_labels() in
        let ext_env = ext_env_code label les in
        let body = Printf.sprintf 
          "
          Lcode_%d:
              push rbp
              mov rbp,rsp
              ; body code
              %s 
              leave
              ret\n" label (run body (List.length params))
        in
        let lcont = cont_code label in
        ext_env ^ body ^ lcont
      | ScmLambdaOpt' (params, opt, body) -> 
        let label = generate_lambda_simple_labels() in
        let n = (List.length params) + 1 in
        let ext_env = ext_env_code label les in
        let body = Printf.sprintf
          "Lcode_%d:
              push rbp
              mov rbp,rsp
              mov r9, %d
              mov r10, PARAMS_COUNT
              ADJUST_STACK_FRAME r9, r10
              ; body code
              %s 
              leave
              ret\n" label n (run body n) 
        in
          let lcont = cont_code label in
          ext_env ^ body ^ lcont
      | ScmApplic' (proc, args) ->
        let push_magic = "push T_MAGIC\n" in
        let push_instruction = "push rax\n" in
        let evaluated_args = List.fold_right (fun curr acc -> acc ^ (run curr les) ^ push_instruction) args "" in
        let param_count = List.length args in 
        let push_param_count_instrtuction = Printf.sprintf "push %d\n" param_count in
        let evaluated_proc = run proc les in
        let restore_stack = "add rsp, WORD_SIZE\npop rbx\nlea rsp, [rsp + (rbx + 1) * WORD_SIZE]\n" in
        (*TODO : let is_closure = "cmp [rax], T_CLOSURE"*) 
        let call_app_instruction = "CLOSURE_ENV r9, rax\npush r9\nCLOSURE_CODE r10, rax\ncall r10\n" in
        push_magic ^ evaluated_args ^ push_param_count_instrtuction ^ evaluated_proc ^ call_app_instruction ^ restore_stack
      | ScmApplicTP' (proc, args) ->
        let push_magic = "push T_MAGIC\n" in
        let push_instruction = "push rax\n" in
        let evaluated_args = List.fold_right (fun curr acc -> acc ^ (run curr les) ^ push_instruction) args "" in
        let param_count = List.length args in 
        let push_param_count_instrtuction = Printf.sprintf "push %d\n" param_count in
        let evaluated_proc = run proc les in
        (*TODO : let is_closure = "cmp [rax], T_CLOSURE"*) 
        let push_env_ret_instruction = "CLOSURE_ENV r9, rax\npush r9\npush qword [rbp + 1 * WORD_SIZE]\n" in
        let fix_stack = Printf.sprintf "SHIFT_FRAME %d\n" (param_count + 4) in
        let push_jmp_instruction = "CLOSURE_CODE r10, rax\njmp r10\n" in
        push_magic ^ evaluated_args ^ push_param_count_instrtuction ^ evaluated_proc ^ push_env_ret_instruction ^ fix_stack ^ push_jmp_instruction

      in
      let dummy = init_const_map () in 
      let fvar_map = init_fvar_map () in
      run e 0;;

end;;
