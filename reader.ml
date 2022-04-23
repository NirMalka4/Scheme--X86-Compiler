(* reader.ml
 * A skeleton for the reader for the 2021-2022 course on compiler-construction
 *)

#use "pc.ml";;

let rec gcd a b =
  match (a, b) with
  | (0, b) -> b
  | (a, 0) -> a
  | (a, b) -> gcd b (a mod b);;

type scm_number =
  | ScmRational of (int * int)
  | ScmReal of float;;

type sexpr =
  | ScmVoid
  | ScmNil
  | ScmBoolean of bool
  | ScmChar of char
  | ScmString of string
  | ScmSymbol of string
  | ScmNumber of scm_number
  | ScmVector of (sexpr list)
  | ScmPair of (sexpr * sexpr);;

module type READER = sig
    val nt_sexpr : sexpr PC.parser
end;; (* end of READER signature *)

module Reader : READER = struct
open PC;;

let unitify nt = pack nt (fun _ -> ());;

let rec nt_whitespace str =
  const (fun ch -> ch <= ' ') str

and nt_end_of_line_or_file str =
  let nt1 = unitify (char '\n') in
  let nt2 = unitify nt_end_of_input in
  let nt1 = disj nt1 nt2 in
  nt1 str

and nt_visible_simple_char = range (char_of_int 33) (char_of_int 127) 
and nt_line_comment str =    
  unitify (caten (caten (word ";") (star ((diff (range (char_of_int 0) (char_of_int 127) )) nt_end_of_line_or_file))) nt_end_of_line_or_file) str

and nt_paired_comment str = 
  let nt1 = char '{' in

  let nt2 = disj_list
                [unitify nt_char;
                unitify nt_string;
                unitify nt_comment;] in

  let nt2' = disj nt2 (unitify (one_of "{}")) in
  let nt3 = diff nt_any nt2' in
  let nt3 = disj (unitify nt3) nt2 in
  let nt3 = star nt3 in
  let nt4 = char '}' in
  let nt1 = unitify (caten nt1 (caten nt3 nt4)) in
  nt1 str

and nt_sexpr_comment str = 
  unitify (caten (word "#;") nt_sexpr) str
  
and nt_comment str =
disj_list
  [nt_sexpr_comment;
  nt_line_comment;
  nt_paired_comment;] str
  
and nt_skip_star str =
  let nt1 = disj (unitify nt_whitespace) nt_comment in
  let nt1 = unitify (star nt1) in
  nt1 str

and make_skipped_star (nt : 'a parser) =
  let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
  let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
  nt1



and int_of_hex digit = 
  let value = (int_of_char digit) in
  if digit <= '9' then (value - 48) else
  if digit <= 'F' then ((value - 65) + 10) else ((value - 97) + 10)

and nt_hex_char str = 
  pack (caten (range '2' '7') (disj_list [(range '0' '9'); (range 'a' 'f'); (range 'A' 'F');]))
      (fun (a,b) -> let msb = (int_of_hex a) in
                    let lsb = (int_of_hex b) in
                    let value = ((msb*16) + lsb) in
                    (char_of_int value))

and nt_number str =

  let sign = maybe (disj (char '+') (char '-')) in 

  let nt_natural = 
    let my_natural = caten (range '1' '9') (star (range '0' '9')) in
    let zero_plus = plus (char '0') in
    let zero_star = star(char '0') in
    disj
        (pack (caten zero_star my_natural)
              (fun ( zeros, (head,tail)) ->
                  (List.fold_left (fun acc curr -> acc*10 + ((int_of_char curr) - 48)) 0 (head::tail)))) 
        (pack (caten sign zero_plus)
                          (fun (sign, zeroes) -> 0)) in

  let integer_create =
          pack (caten sign nt_natural)
              (fun (sign, n) ->
                  match sign with
                                | Some('-') -> (-1 * n)
                                | Some('+') -> n
                                | None -> n
                                | _ -> raise X_no_match) in 

  let nt_integer = pack integer_create (fun n -> ScmNumber(ScmRational(n, 1))) in 


  let nt_fraction = pack (caten (caten integer_create (char '/')) nt_natural)
                          (fun ((n, s), d) ->
                            match d with 
                                |0 -> ScmSymbol(((string_of_int n) ^ "/") ^ (string_of_int d))
                                |_ -> let g = (gcd n d) in
                                      if g>0 then ScmNumber(ScmRational(n / g, d / g))
                                      else ScmNumber(ScmRational((n / g)*(-1), (d / g)*(-1)))) in 
                              

  let nt_integer_part = nt_natural in

  let nt_mantisa = nt_natural in

  let nt_exponent_token = pack(disj_list [(word_ci "e"); (word "*10^"); (word "*10**");]) (fun (token) -> "e") in

  let nt_exponent = pack (caten nt_exponent_token integer_create) (fun (t, n) -> t ^ (string_of_int n)) in 


  let nt_float_a = pack (caten (caten (caten nt_integer_part (char '.')) (maybe nt_mantisa)) (maybe nt_exponent))
                        (fun (((intpart, point), mantisa), exponent) ->
                              let numstr1 = ((string_of_int intpart) ^ ".") in
                              match mantisa with 
                              |Some(m) -> 
                                  (match exponent with 
                                  |Some(e) -> 
                                      let numstr2 = numstr1 ^ (string_of_int m) in
                                      let numstr = numstr2 ^ e in
                                          ScmNumber(ScmReal(float_of_string numstr))
                                      |None -> ScmNumber(ScmReal(float_of_string (numstr1 ^ (string_of_int m)))))
                              
                              |None -> match exponent with 
                                      |Some(e) -> ScmNumber(ScmReal(float_of_string (numstr1 ^  e)))
                                      |None -> ScmNumber(ScmReal(float_of_string numstr1))) in



  let nt_float_b = pack (caten (caten (char '.') nt_mantisa) (maybe nt_exponent))
                        (fun ((point, mantisa), exponent) ->
                              let numstr0 = "." in
                                  match exponent with 
                                  |Some(e) -> 
                                      let numstr1 = numstr0 ^ (string_of_int mantisa) in
                                      let numstr = numstr1 ^ e in
                                          ScmNumber(ScmReal(float_of_string numstr))
                                |None -> ScmNumber(ScmReal(float_of_string (numstr0 ^ (string_of_int mantisa))))) in

                                
    let nt_float_c = pack (caten nt_integer_part nt_exponent)                   
                        (fun (intpart, exponent) ->
                            ScmNumber(ScmReal((float_of_string ((string_of_int intpart) ^ exponent))))) in

    let nt_float = disj_list [nt_float_a; nt_float_b; nt_float_c] in

    (pack (caten (caten nt_skip_star (not_followed_by (disj_list [nt_float; nt_fraction; nt_integer;]) nt_symbol_char)) nt_skip_star)
                          (fun ((lspaces, n), rspaces) -> n)) str

and nt_boolean str = 
  let f = word_ci "#f" in
  let t = word_ci "#t" in
  let p = disj_list [char '('; char ')'; char '.';] in
          (pack (caten (caten nt_skip_star (not_followed_by (disj f t) (diff nt_visible_simple_char p))) nt_skip_star)
                  (fun ((lspaces,bexp), rspaces)-> match bexp with
                                    | ['#'; 'f';] -> ScmBoolean (false)
                                    | ['#'; 'F';] -> ScmBoolean (false)
                                    | ['#'; 't';] -> ScmBoolean (true)
                                    | ['#'; 'T';] -> ScmBoolean (true)
                                    | _ -> raise X_no_match)) str 

(*and nt_char_simple str = raise X_not_yet_implemented
and make_named_char char_name ch = raise X_not_yet_implemented
and nt_char_named str =
  let nt1 =
    disj_list [(make_named_char "newline" '\n');
               (make_named_char "page" '\012');
               (make_named_char "return" '\r');
               (make_named_char "space" ' ');
               (make_named_char "tab" '\t')] in
  nt1 str
and nt_char_hex str = raise X_not_yet_implemented*)
and nt_char str = 
  let nt_char_prefix =word "#\\" in

  let nt_named_char = disj_list [pack (word_ci "newline") (fun e-> (char_of_int 10));
                      pack (word_ci "nul") (fun e-> (char_of_int 0)); pack (word_ci "page") (fun e-> (char_of_int 12));
                      pack (word_ci "return") (fun e-> (char_of_int 13)); pack (word_ci "space") (fun e-> (char_of_int 32));
                      pack (word_ci "tab") (fun e-> (char_of_int 9));] in

  let  nt_hexdecimal_char = pack (caten (char 'x') (nt_hex_char str))
                            (fun (prefix,content) -> content) in

  let nt_legal_char = caten nt_char_prefix (disj_list [nt_named_char; nt_hexdecimal_char; nt_visible_simple_char;]) in

  (pack (caten (caten nt_skip_star (not_followed_by nt_legal_char nt_symbol_char)) nt_skip_star)
  (fun ((lspaces,(prefix, content)), rspaces) -> ScmChar(content))) str 
    
and nt_symbol_char str = 
  let nt1 = disj_list [(range '0' '9');
                          (range 'a' 'z'); 
                          (range 'A' 'Z'); 
                          (char '!'); 
                          (char '$');
                          (char '^');
                          (char '*');
                          (char '-');
                          (char '_');
                          (char '=');
                          (char '+');
                          (char '<');
                          (char '>');
                          (char '?');
                          (char '/');
                          (char ':');] in
    nt1 str
and nt_symbol str =
  let nt1 = plus nt_symbol_char in
  let nt1 = pack nt1 list_to_string in
  let nt1 = pack nt1 (fun name -> ScmSymbol name) in
  let nt1 = diff nt1 nt_number in
  nt1 str

and nt_string str = 
  let nt_string_hex_char = pack (caten (caten (word_ci "\\x")  (plus (nt_hex_char str))) (char ';'))
                            (fun ((prefix, hex_chars),endline) -> ScmString(list_to_string hex_chars)) in 

  let nt_string_literal_char = pack (diff (range (char_of_int 0) (char_of_int 127)) 
                                      (disj_list [(char '\\'); (char '"'); (char '~');]))
                              (fun r -> ScmString (String.make 1 r)) in 
  let nt_string_meta_char = 
    pack (disj_list [pack (word "\\\\") (fun r -> (char_of_int 92)); 
                          pack (word "\\\"") (fun r -> (char_of_int 34)); 
                          pack (word "\\t") (fun r -> (char_of_int 9)); 
                          pack (word "\\f") (fun r -> (char_of_int 12)); 
                          pack (word "\\n") (fun r -> (char_of_int 10)); 
                          pack (word "\\r") (fun r -> (char_of_int 13));])
                          (fun r -> ScmString (String.make 1 r)) in

  let nt_string_interpolated = pack (caten (caten (caten (word "~") (char '{')) nt_sexpr) (char '}'))
                              (fun (((tilde,lp),sexpr),rp) -> ScmPair(ScmSymbol("format"), ScmPair(ScmString ("~a"), ScmPair(sexpr, ScmNil)))) in

  let nt_string_char = disj_list [nt_string_interpolated; nt_string_hex_char; nt_string_meta_char;  nt_string_literal_char;] in

  (pack (caten (caten (caten (caten nt_skip_star (char '\"')) (star nt_string_char)) (char '\"')) nt_skip_star)
        (fun ((((lspaces, lquote),content),rquote),rspaces) -> List.fold_right (fun curr acc -> 
        match curr with 
            | ScmString(x) -> 
                (match acc with 
                    | ScmNil -> curr
                    | ScmString(y) -> ScmString(x^y)
                    | ScmPair(ScmString(prefix),suffix) -> ScmPair(ScmSymbol("string-append"),ScmPair(ScmString(x^prefix),suffix))
                    | ScmPair(ScmSymbol("string-append"),ScmPair(ScmString(prefix),suffix)) -> ScmPair(ScmSymbol("string-append"),ScmPair(ScmString(x^prefix),suffix))
                    | ScmPair(ScmSymbol("string-append"),suffix) -> ScmPair(ScmSymbol("string-append"),ScmPair(curr,suffix))
                    |_-> ScmPair(ScmSymbol("string-append"),ScmPair(curr,ScmPair(acc,ScmNil))))
            | _->
                (match acc with 
                |ScmNil -> curr
                |ScmString(y) -> ScmPair(ScmSymbol("string-append"),ScmPair(curr,ScmPair(acc, ScmNil)))
                |ScmPair(ScmSymbol("string-append"),suffix) -> ScmPair(ScmSymbol("string-append"),ScmPair(curr,suffix))
                |_-> ScmPair(ScmSymbol("string-append"),ScmPair(curr,acc)))) content ScmNil))str


and nt_vector str =
  let nt1 = word "#(" in
  let nt2 = caten nt_skip_star (char ')') in
  let nt2 = pack nt2 (fun _ -> ScmVector []) in
  let nt3 = plus nt_sexpr in
  let nt4 = char ')' in
  let nt3 = caten nt3 nt4 in
  let nt3 = pack nt3 (fun (sexprs, _) -> ScmVector sexprs) in
  let nt2 = disj nt2 nt3 in
  let nt1 = caten nt1 nt2 in
  let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
  nt1 str
and nt_list str = 
  let nt_proper_list = pack (caten (caten (caten (caten  (char '(') nt_skip_star) (star nt_sexpr)) nt_skip_star) (char ')'))
        (fun ((((lp,lspaces),exprs),rspaces),rp)-> List.fold_right (fun a b -> ScmPair(a,b)) exprs ScmNil) in

  let nt_improper_list = pack (caten (caten (caten (caten (caten (caten (char '(') nt_skip_star) (plus nt_sexpr)) (char '.')) nt_skip_star) nt_sexpr) (char ')'))
        (fun ((((((lp,lspaces),head), dot), rspaces),tail),rp) -> List.fold_right (fun a b -> ScmPair(a,b)) head tail) in

  (disj nt_proper_list nt_improper_list) str

and nt_quoted_forms str = 
  let nt_quoted = pack (caten (char '\'') nt_sexpr)
            (fun (lq, expr) -> ScmPair(ScmSymbol("quote"), ScmPair(expr, ScmNil))) in

  let nt_quasi_quoted = pack (caten (char '`') nt_sexpr)
            (fun (lq, expr) -> ScmPair(ScmSymbol("quasiquote"), ScmPair(expr, ScmNil))) in

  let nt_uquoted = pack (caten (char ',') nt_sexpr)
            (fun (lq, expr) -> ScmPair(ScmSymbol("unquote"), ScmPair(expr, ScmNil))) in

  let nt_uquote_and_spliced = pack (caten (word ",@") nt_sexpr)
            (fun (lq, expr) -> ScmPair(ScmSymbol("unquote-splicing"), ScmPair(expr, ScmNil))) in
  
  ((disj_list [nt_quoted; nt_quasi_quoted; nt_uquoted; nt_uquote_and_spliced;]) str)

and nt_sexpr str =
  let nt1 =
    disj_list [nt_number; nt_boolean; nt_char; nt_symbol;
              nt_string; nt_vector; nt_list; nt_quoted_forms] in
  let nt1 = make_skipped_star nt1 in
  nt1 str;;

end;; (* end of struct Reader *)

let rec string_of_sexpr = function
  | ScmVoid -> "#<void>"
  | ScmNil -> "()"
  | ScmBoolean(false) -> "#f"
  | ScmBoolean(true) -> "#t"
  | ScmChar('\n') -> "#\\newline"
  | ScmChar('\r') -> "#\\return"
  | ScmChar('\012') -> "#\\page"
  | ScmChar('\t') -> "#\\tab"
  | ScmChar(' ') -> "#\\space"
  | ScmChar(ch) ->
     if (ch < ' ')
     then let n = int_of_char ch in
          Printf.sprintf "#\\x%x" n
     else Printf.sprintf "#\\%c" ch
  | ScmString(str) ->
     Printf.sprintf "\"%s\""
       (String.concat ""
          (List.map
             (function
              | '\n' -> "\\n"
              | '\012' -> "\\f"
              | '\r' -> "\\r"
              | '\t' -> "\\t"
              | ch ->
                 if (ch < ' ')
                 then Printf.sprintf "\\x%x;" (int_of_char ch)
                 else Printf.sprintf "%c" ch)
             (string_to_list str)))
  | ScmSymbol(sym) -> sym
  | ScmNumber(ScmRational(0, _)) -> "0"
  | ScmNumber(ScmRational(num, 1)) -> Printf.sprintf "%d" num
  | ScmNumber(ScmRational(num, -1)) -> Printf.sprintf "%d" (- num)
  | ScmNumber(ScmRational(num, den)) -> Printf.sprintf "%d/%d" num den
  | ScmNumber(ScmReal(x)) -> Printf.sprintf "%f" x
  | ScmVector(sexprs) ->
     let strings = List.map string_of_sexpr sexprs in
     let inner_string = String.concat " " strings in
     Printf.sprintf "#(%s)" inner_string
  | ScmPair(ScmSymbol "quote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "'%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "quasiquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "`%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote-splicing",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",@%s" (string_of_sexpr sexpr)
  | ScmPair(car, cdr) ->
     string_of_sexpr' (string_of_sexpr car) cdr
and string_of_sexpr' car_string = function
  | ScmNil -> Printf.sprintf "(%s)" car_string
  | ScmPair(cadr, cddr) ->
     let new_car_string =
       Printf.sprintf "%s %s" car_string (string_of_sexpr cadr) in
     string_of_sexpr' new_car_string cddr
  | cdr ->
     let cdr_string = (string_of_sexpr cdr) in
     Printf.sprintf "(%s . %s)" car_string cdr_string;;
