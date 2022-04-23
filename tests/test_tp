
#use "tag-parser.ml";;

type case = {name: string; input: sexpr list; expected: expr list};;

let cases = [
  {name = "1"; input = [ScmPair (ScmSymbol "let", ScmPair (ScmPair (ScmPair (ScmSymbol "x", ScmPair (ScmNumber (ScmRational(1,1)), ScmNil)), ScmPair (ScmPair (ScmSymbol "y", ScmPair (ScmNumber (ScmRational (2,1)), ScmNil)), ScmNil)), ScmPair (ScmSymbol "y", ScmNil)))]; expected = [ScmApplic (ScmLambdaSimple (["x"; "y"], ScmVar "y"),[ScmConst (  (ScmNumber (ScmRational (1,1)))); ScmConst (  (ScmNumber (ScmRational (2,1))))])] };
  {name = "2"; input = [ScmPair (ScmSymbol "let", ScmPair (ScmNil, ScmPair (ScmNumber (ScmRational (10,1)), ScmNil)))]; expected = [ScmApplic (ScmLambdaSimple ([], ScmConst (  (ScmNumber (ScmRational (10,1))))), [])] };
  {name = "3"; input = [ScmPair (ScmSymbol "let", ScmPair (ScmPair (ScmPair (ScmSymbol "x", ScmPair (ScmNumber (ScmRational (1,1)), ScmNil)), ScmNil), ScmPair (ScmSymbol "x", ScmNil)))]; expected = [ScmApplic (ScmLambdaSimple (["x"], ScmVar "x"), [ScmConst (  (ScmNumber (ScmRational (1,1))))])] };
  {name = "4"; input = [ScmPair (ScmSymbol "let", ScmPair (ScmNil, ScmPair (ScmPair (ScmSymbol "begin", ScmPair (ScmNumber (ScmRational (1,1)), ScmPair (ScmNumber (ScmRational (2,1)), ScmPair (ScmNumber (ScmRational (3,1)), ScmNil)))), ScmNil)))]; expected = [ScmApplic(ScmLambdaSimple ([],ScmSeq[ScmConst (  (ScmNumber (ScmRational (1,1)))); ScmConst (  (ScmNumber (ScmRational (2,1))));ScmConst (  (ScmNumber (ScmRational (3,1))))]),[])] };
  {name = "5"; input = [ScmPair (ScmSymbol "let", ScmPair (ScmPair (ScmPair (ScmSymbol "a", ScmPair (ScmNumber (ScmRational (3,1)), ScmNil)), ScmPair (ScmPair (ScmSymbol "b", ScmPair (ScmNumber (ScmRational (10,1)), ScmNil)), ScmNil)), ScmPair (ScmPair (ScmSymbol "+", ScmPair (ScmSymbol "a", ScmPair (ScmSymbol "b", ScmNil))), ScmNil)))]; expected = [ScmApplic (ScmLambdaSimple (["a"; "b"], ScmApplic (ScmVar "+", [ScmVar "a"; ScmVar "b"])),[ScmConst (  (ScmNumber (ScmRational (3,1)))); ScmConst (  (ScmNumber (ScmRational (10,1))))])] };
  {name = "6"; input = [ScmPair (ScmSymbol "let", ScmPair (ScmPair (ScmPair (ScmSymbol "x", ScmPair (ScmChar 'a', ScmNil)), ScmNil), ScmPair (ScmSymbol "x", ScmNil)))]; expected = [ScmApplic (ScmLambdaSimple (["x"], ScmVar "x"), [ScmConst (  (ScmChar 'a'))])] };
  {name = "7"; input = [ScmPair (ScmSymbol "let", ScmPair (ScmPair (ScmPair (ScmSymbol "t", ScmPair (ScmBoolean true, ScmNil)), ScmPair (ScmPair (ScmSymbol "th", ScmPair (ScmNumber (ScmRational (3,1)), ScmNil)), ScmPair (ScmPair (ScmSymbol "el", ScmPair (ScmNumber (ScmRational (4,1)), ScmNil)), ScmNil))), ScmPair (ScmPair (ScmSymbol "if", ScmPair (ScmSymbol "t", ScmPair (ScmSymbol "th", ScmPair (ScmSymbol "el", ScmNil)))), ScmNil)))]; expected = [ScmApplic (ScmLambdaSimple (["t"; "th"; "el"], ScmIf (ScmVar "t", ScmVar "th", ScmVar "el")),[ScmConst (  (ScmBoolean true)); ScmConst (  (ScmNumber (ScmRational (3,1))));ScmConst (  (ScmNumber (ScmRational (4,1))))])] };
  {name = "8"; input = [ScmPair (ScmSymbol "let", ScmPair (ScmPair (ScmPair (ScmSymbol "x", ScmPair (ScmString "asd", ScmNil)), ScmNil), ScmPair (ScmPair (ScmSymbol "define", ScmPair (ScmSymbol "y", ScmPair (ScmNumber (ScmReal 1.23), ScmNil))), ScmNil)))]; expected = [ScmApplic(ScmLambdaSimple (["x"], ScmDef (ScmVar "y", ScmConst (  (ScmNumber (ScmReal 1.23))))),[ScmConst (  (ScmString "asd"))])] };
  {name = "9"; input = [ScmPair (ScmSymbol "let", ScmPair (ScmPair (ScmPair (ScmSymbol "x", ScmPair (ScmString "asd", ScmNil)), ScmNil), ScmPair (ScmPair (ScmSymbol "begin", ScmPair (ScmPair (ScmSymbol "define", ScmPair (ScmSymbol "y", ScmPair (ScmNumber (ScmReal 1.23), ScmNil))), ScmPair (ScmPair (ScmSymbol "set", ScmPair (ScmSymbol "y", ScmPair (ScmNumber (ScmRational (-1,1)), ScmNil))), ScmNil))), ScmNil)))]; expected = [ScmApplic(ScmLambdaSimple (["x"],ScmSeq[ScmDef (ScmVar "y", ScmConst (  (ScmNumber (ScmReal 1.23))));ScmApplic (ScmVar "set", [ScmVar "y"; ScmConst (  (ScmNumber (ScmRational (-1,1))))])]),[ScmConst (  (ScmString "asd"))])] };
  {name = "10"; input = [ScmPair (ScmSymbol "let", ScmPair (ScmPair (ScmPair (ScmSymbol "x", ScmPair (ScmString "asd", ScmNil)), ScmNil), ScmPair (ScmPair (ScmSymbol "begin", ScmPair (ScmSymbol "x", ScmNil)), ScmNil)))]; expected = [ScmApplic (ScmLambdaSimple (["x"], ScmVar "x"), [ScmConst (  (ScmString "asd"))])] };
  {name = "11"; input = [ScmPair (ScmSymbol "quasiquote",                                                       ScmPair (ScmPair (ScmPair (ScmSymbol "unquote", ScmPair (ScmSymbol "x", ScmNil)), ScmNil), ScmNil))  ]; expected = [ScmApplic (ScmVar "cons", [ScmVar "x"; ScmConst (  ScmNil)])] };
  {name = "12"; input = [ScmPair (ScmSymbol "quasiquote",                                                       ScmPair(ScmPair (ScmPair (ScmSymbol "unquote", ScmPair (ScmSymbol "a", ScmNil)),ScmPair (ScmSymbol "b", ScmNil)),ScmNil))]; expected = [ScmApplic (ScmVar "cons",[ScmVar "a";ScmApplic (ScmVar "cons", [ScmConst (  (ScmSymbol "b")); ScmConst (  ScmNil)])])] };
  {name = "13"; input = [ScmPair (ScmSymbol "quasiquote",                                                       ScmPair(ScmPair (ScmSymbol "a",ScmPair (ScmPair (ScmSymbol "unquote", ScmPair (ScmSymbol "b", ScmNil)), ScmNil)),ScmNil))]; expected = [ScmApplic (ScmVar "cons",[ScmConst (  (ScmSymbol "a"));ScmApplic (ScmVar "cons", [ScmVar "b"; ScmConst (  ScmNil)])])] };
  {name = "14"; input = [ScmPair (ScmSymbol "quasiquote",                                                       ScmPair(ScmPair (ScmPair (ScmSymbol "unquote-splicing", ScmPair (ScmSymbol "a", ScmNil)),ScmPair (ScmSymbol "b", ScmNil)),ScmNil))]; expected = [ScmApplic (ScmVar "append",[ScmVar "a";ScmApplic (ScmVar "cons", [ScmConst (  (ScmSymbol "b")); ScmConst (  ScmNil)])])] };
  {name = "15"; input = [ScmPair (ScmSymbol "quasiquote",                                                       ScmPair(ScmPair (ScmSymbol "a",ScmPair (ScmPair (ScmSymbol "unquote-splicing", ScmPair (ScmSymbol "b", ScmNil)), ScmNil)),ScmNil))]; expected = [ScmApplic (ScmVar "cons",[ScmConst (  (ScmSymbol "a"));ScmApplic (ScmVar "append", [ScmVar "b"; ScmConst (  ScmNil)])])] };
  {name = "16"; input = [ScmPair (ScmSymbol "quasiquote",                                                       ScmPair(ScmPair (ScmPair (ScmSymbol "unquote", ScmPair (ScmSymbol "a", ScmNil)),ScmPair (ScmPair (ScmSymbol "unquote-splicing", ScmPair (ScmSymbol "b", ScmNil)), ScmNil)),ScmNil))]; expected = [ScmApplic (ScmVar "cons",[ScmVar "a"; ScmApplic (ScmVar "append", [ScmVar "b"; ScmConst (  ScmNil)])])] };
  {name = "17"; input = [ScmPair (ScmSymbol "lambda",                                                           ScmPair (ScmPair (ScmSymbol "x", ScmPair (ScmSymbol "y", ScmPair (ScmSymbol "z", ScmNil))),ScmPair(ScmPair (ScmSymbol "begin",ScmPair (ScmSymbol "x", ScmPair (ScmSymbol "y", ScmPair (ScmSymbol "z", ScmNil)))),ScmNil)))]; expected = [ScmLambdaSimple (["x"; "y"; "z"], ScmSeq [ScmVar "x"; ScmVar "y"; ScmVar "z"])] };
  {name = "18"; input = [ScmPair (ScmSymbol "lambda",                                                           ScmPair (ScmPair (ScmSymbol "x", ScmPair (ScmSymbol "y", ScmSymbol "vs")),ScmPair(ScmPair (ScmSymbol "begin",ScmPair (ScmSymbol "x", ScmPair (ScmSymbol "y", ScmPair (ScmSymbol "vs", ScmNil)))),ScmNil)))]; expected = [ScmLambdaOpt (["x"; "y"], "vs", ScmSeq [ScmVar "x"; ScmVar "y"; ScmVar "vs"])] };
  {name = "19"; input = [ScmPair (ScmSymbol "lambda",                                                           ScmPair (ScmPair (ScmSymbol "x", ScmSymbol "vs"),ScmPair (ScmPair (ScmSymbol "if", ScmPair (ScmSymbol "x", ScmPair (ScmSymbol "vs", ScmNil))), ScmNil)))]; expected = [ScmLambdaOpt (["x"], "vs", ScmIf (ScmVar "x", ScmVar "vs", ScmConst ScmVoid))] };
  {name = "20"; input = [ScmPair (ScmSymbol "lambda",                                                           ScmPair (ScmPair (ScmSymbol "x", ScmPair (ScmSymbol "y", ScmSymbol "vs")),ScmPair(ScmPair (ScmSymbol "and",ScmPair (ScmNumber (ScmRational (1,1)), ScmPair (ScmNumber (ScmRational (2,1)), ScmPair (ScmNumber (ScmRational (3,1)), ScmNil)))),ScmNil)))]; expected = [ScmLambdaOpt (["x"; "y"], "vs",ScmIf (ScmConst (  (ScmNumber (ScmRational (1,1)))),ScmIf (ScmConst (  (ScmNumber (ScmRational (2,1)))), ScmConst (  (ScmNumber (ScmRational (3,1)))),ScmConst (  (ScmBoolean false))),ScmConst (  (ScmBoolean false))))] };
  {name = "21"; input = [ScmPair (ScmSymbol "lambda",                                                           ScmPair(ScmPair (ScmSymbol "a",ScmPair (ScmSymbol "b", ScmPair (ScmSymbol "c", ScmPair (ScmSymbol "d", ScmSymbol "vs")))),ScmPair(ScmPair (ScmSymbol "if",ScmPair (ScmPair (ScmSymbol ">", ScmPair (ScmSymbol "a", ScmPair (ScmSymbol "b", ScmNil))),ScmPair (ScmPair (ScmSymbol "+", ScmPair (ScmSymbol "c", ScmPair (ScmSymbol "d", ScmNil))),ScmPair (ScmPair (ScmSymbol "list", ScmPair (ScmSymbol "vs", ScmNil)), ScmNil)))),ScmNil)))]; expected = [ScmLambdaOpt (["a"; "b"; "c"; "d"], "vs",ScmIf (ScmApplic (ScmVar ">", [ScmVar "a"; ScmVar "b"]),ScmApplic (ScmVar "+", [ScmVar "c"; ScmVar "d"]), ScmApplic (ScmVar "list", [ScmVar "vs"])))] };
  {name = "22"; input = [ScmPair (ScmSymbol "lambda",                                                           ScmPair (ScmPair (ScmSymbol "b", ScmSymbol "vs"),ScmPair(ScmPair (ScmSymbol "begin",ScmPair (ScmSymbol "b",ScmPair(ScmPair (ScmSymbol "define", ScmPair (ScmSymbol "x", ScmPair (ScmNumber (ScmRational (10,1)), ScmNil))),ScmPair(ScmPair (ScmSymbol "set",ScmPair (ScmSymbol "b",ScmPair(ScmPair (ScmSymbol "+", ScmPair (ScmSymbol "x", ScmPair (ScmNumber (ScmRational (15,1)), ScmNil))),ScmNil))),ScmNil)))),ScmNil)))]; expected = [ScmLambdaOpt (["b"], "vs",ScmSeq[ScmVar "b"; ScmDef (ScmVar "x", ScmConst (  (ScmNumber (ScmRational (10,1)))));ScmApplic (ScmVar "set",[ScmVar "b"; ScmApplic (ScmVar "+", [ScmVar "x"; ScmConst (  (ScmNumber (ScmRational (15,1))))])])])] };
  {name = "23"; input = [ScmPair (ScmSymbol "lambda",                                                           ScmPair (ScmPair (ScmSymbol "a", ScmPair (ScmSymbol "b", ScmSymbol "vs")),ScmPair(ScmPair (ScmSymbol "cond",ScmPair (ScmPair (ScmSymbol "a", ScmPair (ScmNumber (ScmRational (1,1)), ScmNil)),ScmPair (ScmPair (ScmSymbol "b", ScmPair (ScmNumber (ScmRational (2,1)), ScmNil)),ScmPair(ScmPair (ScmSymbol "else",ScmPair (ScmPair (ScmSymbol "+", ScmPair (ScmSymbol "a", ScmPair (ScmSymbol "b", ScmNil))),ScmNil)),ScmNil)))),ScmNil)))]; expected = [ScmLambdaOpt (["a"; "b"], "vs",ScmIf (ScmVar "a", ScmConst (  (ScmNumber (ScmRational(1,1)))),ScmIf (ScmVar "b", ScmConst (  (ScmNumber (ScmRational(2,1)))),ScmApplic (ScmVar "+", [ScmVar "a"; ScmVar "b"]))))] };
  {name = "24"; input = [ScmPair (ScmSymbol "lambda",                                                           ScmPair (ScmPair (ScmSymbol "x", ScmSymbol "vs"), ScmPair (ScmSymbol "vs", ScmNil)))   ]; expected = [ScmLambdaOpt (["x"], "vs", ScmVar "vs")] };
  {name = "25"; input = [ScmPair (ScmSymbol "lambda",                                                           ScmPair (ScmPair (ScmSymbol "x", ScmPair (ScmSymbol "y", ScmSymbol "vs")),ScmPair(ScmPair(ScmPair (ScmSymbol "quasiquote",ScmPair(ScmPair (ScmPair (ScmSymbol "unquote", ScmPair (ScmSymbol "x", ScmNil)),ScmPair (ScmPair (ScmSymbol "unquote-splicing", ScmPair (ScmSymbol "y", ScmNil)), ScmNil)),ScmNil)),ScmNil),ScmNil)))]; expected = [ScmLambdaOpt (["x"; "y"], "vs",ScmApplic(ScmApplic (ScmVar "cons",[ScmVar "x"; ScmApplic (ScmVar "append", [ScmVar "y"; ScmConst (  ScmNil)])]),[]))] };
  {name = "26"; input = [ScmPair (ScmSymbol "let*",                                                             ScmPair(ScmPair (ScmPair (ScmSymbol "x", ScmPair (ScmNumber (ScmRational (1,1)), ScmNil)),ScmPair (ScmPair (ScmSymbol "y", ScmPair (ScmNumber (ScmRational (2,1)), ScmNil)), ScmNil)),ScmPair (ScmSymbol "y", ScmNil)))]; expected = [ScmApplic(ScmLambdaSimple (["x"],ScmApplic (ScmLambdaSimple (["y"], ScmVar "y"), [ScmConst (  (ScmNumber (ScmRational (2,1))))])),[ScmConst (  (ScmNumber (ScmRational (1,1))))])] };
  {name = "27"; input = [ScmPair (ScmSymbol "let*",                                                             ScmPair(ScmPair (ScmPair (ScmSymbol "x", ScmPair (ScmNumber (ScmRational (1,1)), ScmNil)),ScmPair (ScmPair (ScmSymbol "y", ScmPair (ScmNumber (ScmRational (2,1)), ScmNil)),ScmPair (ScmPair (ScmSymbol "z", ScmPair (ScmNumber (ScmRational (3,1)), ScmNil)),ScmPair (ScmPair (ScmSymbol "a", ScmPair (ScmNumber (ScmRational (4,1)), ScmNil)),ScmPair (ScmPair (ScmSymbol "b", ScmPair (ScmNumber (ScmRational (5,1)), ScmNil)),ScmPair (ScmPair (ScmSymbol "c", ScmPair (ScmNumber (ScmRational (6,1)), ScmNil)), ScmNil)))))),ScmPair(ScmPair (ScmSymbol "begin",ScmPair (ScmSymbol "x",ScmPair (ScmSymbol "y",ScmPair (ScmSymbol "z",ScmPair (ScmSymbol "a", ScmPair (ScmSymbol "b", ScmPair (ScmSymbol "c", ScmNil))))))),ScmNil)))]; expected = [ScmApplic(ScmLambdaSimple (["x"],ScmApplic(ScmLambdaSimple (["y"],ScmApplic(ScmLambdaSimple (["z"],ScmApplic(ScmLambdaSimple (["a"],ScmApplic(ScmLambdaSimple (["b"],ScmApplic(ScmLambdaSimple (["c"],ScmSeq [ScmVar "x"; ScmVar "y"; ScmVar "z"; ScmVar "a"; ScmVar "b"; ScmVar "c"]),[ScmConst (  (ScmNumber (ScmRational (6,1))))])),[ScmConst (  (ScmNumber (ScmRational (5,1))))])),[ScmConst (  (ScmNumber (ScmRational (4,1))))])),[ScmConst (  (ScmNumber (ScmRational (3,1))))])),[ScmConst (  (ScmNumber (ScmRational (2,1))))])),[ScmConst (  (ScmNumber (ScmRational (1,1))))])] };
  {name = "28"; input = [ScmPair (ScmSymbol "let*",                                                             ScmPair(ScmPair (ScmPair (ScmSymbol "a", ScmPair (ScmNumber (ScmRational (1,1)), ScmNil)),ScmPair (ScmPair (ScmSymbol "b", ScmPair (ScmNumber (ScmRational (2,1)), ScmNil)),ScmPair (ScmPair (ScmSymbol "c", ScmPair (ScmNumber (ScmRational (3,1)), ScmNil)),ScmPair (ScmPair (ScmSymbol "d", ScmPair (ScmNumber (ScmRational (4,1)), ScmNil)),ScmPair (ScmPair (ScmSymbol "e", ScmPair (ScmNumber (ScmRational (5,1)), ScmNil)),ScmPair (ScmPair (ScmSymbol "f", ScmPair (ScmNumber (ScmRational (5,1)), ScmNil)),ScmPair (ScmPair (ScmSymbol "g", ScmPair (ScmNumber (ScmRational (6,1)), ScmNil)), ScmNil))))))),ScmPair(ScmPair (ScmSymbol "and",ScmPair (ScmSymbol "a",ScmPair (ScmSymbol "b",ScmPair (ScmSymbol "c",ScmPair (ScmSymbol "d",ScmPair (ScmSymbol "e", ScmPair (ScmSymbol "f", ScmPair (ScmSymbol "g", ScmNil)))))))),ScmNil)))]; expected = [ScmApplic(ScmLambdaSimple (["a"],ScmApplic(ScmLambdaSimple (["b"],ScmApplic(ScmLambdaSimple (["c"],ScmApplic(ScmLambdaSimple (["d"],ScmApplic(ScmLambdaSimple (["e"],ScmApplic(ScmLambdaSimple (["f"],ScmApplic(ScmLambdaSimple (["g"],ScmIf (ScmVar "a",ScmIf (ScmVar "b",ScmIf (ScmVar "c",ScmIf (ScmVar "d",ScmIf (ScmVar "e",ScmIf (ScmVar "f", ScmVar "g", ScmConst (  (ScmBoolean false))),ScmConst (  (ScmBoolean false))),ScmConst (  (ScmBoolean false))),ScmConst (  (ScmBoolean false))),ScmConst (  (ScmBoolean false))),ScmConst (  (ScmBoolean false)))),[ScmConst (  (ScmNumber (ScmRational(6,1))))])),[ScmConst (  (ScmNumber (ScmRational (5,1))))])),[ScmConst (  (ScmNumber (ScmRational (5,1))))])),[ScmConst (  (ScmNumber (ScmRational (4,1))))])),[ScmConst (  (ScmNumber (ScmRational (3,1))))])),[ScmConst (  (ScmNumber (ScmRational (2,1))))])),[ScmConst (  (ScmNumber (ScmRational (1,1))))])] };
  {name = "29"; input = [ScmPair (ScmSymbol "let*",                                                             ScmPair (ScmNil,ScmPair(ScmPair (ScmSymbol "begin",ScmPair (ScmNumber (ScmRational (1,1)), ScmPair (ScmNumber (ScmRational (2,1)), ScmPair (ScmNumber (ScmRational (3,1)), ScmNil)))),ScmNil)))]; expected = [ScmApplic(ScmLambdaSimple ([],ScmSeq[ScmConst (  (ScmNumber (ScmRational (1,1)))); ScmConst (  (ScmNumber (ScmRational (2,1))));ScmConst (  (ScmNumber (ScmRational (3,1))))]),[])] };
  {name = "30"; input = [ScmPair (ScmSymbol "let*",                                                             ScmPair(ScmPair (ScmPair (ScmSymbol "a", ScmPair (ScmNumber (ScmRational (3,1)), ScmNil)),ScmPair (ScmPair (ScmSymbol "b", ScmPair (ScmNumber (ScmRational (10,1)), ScmNil)), ScmNil)),ScmPair (ScmPair (ScmSymbol "+", ScmPair (ScmSymbol "a", ScmPair (ScmSymbol "b", ScmNil))), ScmNil)))]; expected = [ScmApplic(ScmLambdaSimple (["a"],ScmApplic (ScmLambdaSimple (["b"], ScmApplic (ScmVar "+", [ScmVar "a"; ScmVar "b"])),[ScmConst (  (ScmNumber (ScmRational (10,1))))])),[ScmConst (  (ScmNumber (ScmRational (3,1))))])] };
  {name = "31"; input = [ScmPair (ScmSymbol "let*",                                                             ScmPair(ScmPair (ScmPair (ScmSymbol "t", ScmPair (ScmBoolean true, ScmNil)),ScmPair (ScmPair (ScmSymbol "th", ScmPair (ScmNumber (ScmRational (3,1)), ScmNil)),ScmPair (ScmPair (ScmSymbol "el", ScmPair (ScmNumber (ScmRational (4,1)), ScmNil)), ScmNil))),ScmPair(ScmPair (ScmSymbol "if",ScmPair (ScmBoolean true, ScmPair (ScmNumber (ScmRational (3,1)), ScmPair (ScmNumber (ScmRational (4,1)), ScmNil)))),ScmNil)))]; expected = [ScmApplic(ScmLambdaSimple (["t"],ScmApplic(ScmLambdaSimple (["th"],ScmApplic(ScmLambdaSimple (["el"],ScmIf (ScmConst (  (ScmBoolean true)), ScmConst (  (ScmNumber (ScmRational (3,1)))),ScmConst (  (ScmNumber (ScmRational (4,1)))))),[ScmConst (  (ScmNumber (ScmRational (4,1))))])),[ScmConst (  (ScmNumber (ScmRational (3,1))))])),[ScmConst (  (ScmBoolean true))])] };
  {name = "32"; input = [ScmPair (ScmSymbol "let*",                                                             ScmPair (ScmPair (ScmPair (ScmSymbol "x", ScmPair (ScmString "asd", ScmNil)), ScmNil),ScmPair(ScmPair (ScmSymbol "define", ScmPair (ScmSymbol "y", ScmPair (ScmNumber (ScmReal 12.3), ScmNil))),ScmNil)))]; expected = [ScmApplic(ScmLambdaSimple (["x"], ScmDef (ScmVar "y", ScmConst (  (ScmNumber (ScmReal 12.3))))),[ScmConst (  (ScmString "asd"))])] };
  {name = "33"; input = [ScmPair (ScmSymbol "cond",                                                             ScmPair(ScmPair (ScmNumber (ScmRational (1,1)), ScmPair (ScmNumber (ScmRational (2,1)), ScmPair (ScmNumber (ScmRational (3,1)), ScmNil))),ScmPair(ScmPair (ScmNumber (ScmRational (4,1)), ScmPair (ScmNumber (ScmRational (5,1)), ScmPair (ScmNumber (ScmRational (6,1)), ScmNil))),ScmNil)))]; expected = [ScmIf (ScmConst (  (ScmNumber (ScmRational (1,1)))),ScmSeq [ScmConst (  (ScmNumber (ScmRational (2,1)))); ScmConst (  (ScmNumber (ScmRational (3,1))))],ScmIf (ScmConst (  (ScmNumber (ScmRational (4,1)))),ScmSeq [ScmConst (  (ScmNumber (ScmRational (5,1)))); ScmConst (  (ScmNumber (ScmRational (6,1))))],ScmConst ScmVoid))] };
  {name = "34"; input = [ScmPair (ScmSymbol "cond",                                                             ScmPair(ScmPair (ScmNumber (ScmRational (1,1)), ScmPair (ScmNumber (ScmRational (2,1)), ScmPair (ScmNumber (ScmRational (3,1)), ScmNil))),ScmPair(ScmPair (ScmNumber (ScmRational (4,1)), ScmPair (ScmNumber (ScmRational (5,1)), ScmPair (ScmNumber (ScmRational (6,1)), ScmNil))),ScmPair(ScmPair (ScmSymbol "else",ScmPair (ScmNumber (ScmRational(7,1)), ScmPair (ScmNumber (ScmRational(8,1)), ScmPair (ScmNumber (ScmRational(9,1)), ScmNil)))),ScmNil))))]; expected = [ScmIf (ScmConst (  (ScmNumber (ScmRational (1,1)))),ScmSeq [ScmConst (  (ScmNumber (ScmRational (2,1)))); ScmConst (  (ScmNumber (ScmRational (3,1))))],ScmIf (ScmConst (  (ScmNumber (ScmRational (4,1)))),ScmSeq [ScmConst (  (ScmNumber (ScmRational (5,1)))); ScmConst (  (ScmNumber (ScmRational (6,1))))],ScmSeq[ScmConst (  (ScmNumber (ScmRational (7,1)))); ScmConst (  (ScmNumber (ScmRational (8,1))));ScmConst (  (ScmNumber (ScmRational (9,1))))]))] };
  {name = "35"; input = [ScmPair (ScmSymbol "cond",                                                             ScmPair(ScmPair (ScmNumber (ScmRational (1,1)), ScmPair (ScmNumber (ScmRational (2,1)), ScmPair (ScmNumber (ScmRational (3,1)), ScmNil))),ScmPair(ScmPair (ScmSymbol "else",ScmPair (ScmNumber (ScmRational (4,1)), ScmPair (ScmNumber (ScmRational (5,1)), ScmPair (ScmNumber (ScmRational (6,1)), ScmNil)))),ScmPair(ScmPair (ScmNumber (ScmRational (7,1)), ScmPair (ScmNumber (ScmRational (8,1)), ScmPair (ScmNumber (ScmRational (9,1)), ScmNil))),ScmNil))))]; expected = [ScmIf (ScmConst (  (ScmNumber (ScmRational (1,1)))),ScmSeq [ScmConst (  (ScmNumber (ScmRational (2,1)))); ScmConst (  (ScmNumber (ScmRational (3,1))))],ScmSeq[ScmConst (  (ScmNumber (ScmRational (4,1)))); ScmConst (  (ScmNumber (ScmRational (5,1))));ScmConst (  (ScmNumber (ScmRational (6,1))))])] };
  {name = "36"; input = [ScmPair (ScmSymbol "cond", ScmPair (ScmPair (ScmSymbol "a", ScmPair (ScmSymbol "=>", ScmPair (ScmSymbol "b", ScmNil))), ScmPair (ScmPair (ScmSymbol "x", ScmPair (ScmNumber (ScmRational (1, 1)), ScmNil)), ScmNil)))]; expected = [ScmApplic (ScmLambdaSimple (["value"; "f"; "rest"], ScmIf (ScmVar "value", ScmApplic (ScmApplic (ScmVar "f", []), [ScmVar "value"]), ScmApplic (ScmVar "rest", []))), [ScmVar "a"; ScmLambdaSimple ([], ScmVar "b"); ScmLambdaSimple ([], ScmIf (ScmVar "x", ScmConst (  (ScmNumber (ScmRational (1, 1)))), ScmConst ScmVoid))])] };
  {name = "37"; input = [ScmPair (ScmSymbol "cond",                                                             ScmPair (ScmPair (ScmSymbol "a", ScmPair (ScmSymbol "=>", ScmPair (ScmSymbol "b", ScmNil))),ScmPair(ScmPair (ScmSymbol "else",ScmPair (ScmNumber (ScmRational (1,1)), ScmPair (ScmNumber (ScmRational (2,1)), ScmPair (ScmNumber (ScmRational (3,1)), ScmNil)))),ScmNil)))]; expected = [ScmApplic(ScmLambdaSimple (["value"; "f"; "rest"],ScmIf (ScmVar "value", ScmApplic (ScmApplic (ScmVar "f", []), [ScmVar "value"]),ScmApplic (ScmVar "rest", []))),[ScmVar "a"; ScmLambdaSimple ([], ScmVar "b");ScmLambdaSimple ([],ScmSeq[ScmConst (  (ScmNumber (ScmRational (1,1)))); ScmConst (  (ScmNumber (ScmRational (2,1))));ScmConst (  (ScmNumber (ScmRational (3,1))))])])] };
  {name = "38"; input = [ScmPair (ScmSymbol "and",                                                              ScmPair (ScmNumber (ScmRational (1,1)),ScmPair (ScmNumber (ScmRational (2,1)),ScmPair (ScmNumber (ScmRational (3,1)),ScmPair (ScmNumber (ScmRational (4,1)),ScmPair (ScmNumber (ScmRational (5,1)),ScmPair (ScmNumber (ScmRational (6,1)),ScmPair (ScmNumber (ScmRational (7,1)),ScmPair (ScmNumber (ScmRational (8,1)),ScmPair (ScmNumber (ScmRational (9,1)), ScmPair (ScmNumber (ScmRational (10,1)), ScmNil)))))))))))]; expected = [ScmIf (ScmConst (  (ScmNumber (ScmRational (1,1)))),ScmIf (ScmConst (  (ScmNumber (ScmRational (2,1)))),ScmIf (ScmConst (  (ScmNumber (ScmRational (3,1)))),ScmIf (ScmConst (  (ScmNumber (ScmRational (4,1)))),ScmIf (ScmConst (  (ScmNumber (ScmRational (5,1)))),ScmIf (ScmConst (  (ScmNumber (ScmRational (6,1)))),ScmIf (ScmConst (  (ScmNumber (ScmRational (7,1)))),ScmIf (ScmConst (  (ScmNumber (ScmRational (8,1)))),ScmIf (ScmConst (  (ScmNumber (ScmRational (9,1)))), ScmConst (  (ScmNumber (ScmRational (10,1)))),ScmConst (  (ScmBoolean false))),ScmConst (  (ScmBoolean false))),ScmConst (  (ScmBoolean false))),ScmConst (  (ScmBoolean false))),ScmConst (  (ScmBoolean false))),ScmConst (  (ScmBoolean false))),ScmConst (  (ScmBoolean false))),ScmConst (  (ScmBoolean false))),ScmConst (  (ScmBoolean false)))] };
  {name = "39"; input = [ScmPair (ScmSymbol "define",ScmPair (ScmPair (ScmSymbol "square", ScmPair (ScmSymbol "x", ScmNil)),ScmPair (ScmPair (ScmSymbol "*", ScmPair (ScmSymbol "x", ScmPair (ScmSymbol "x", ScmNil))), ScmNil)))]; expected = [ScmDef (ScmVar "square",ScmLambdaSimple (["x"], ScmApplic (ScmVar "*", [ScmVar "x"; ScmVar "x"])))] };
  {name = "40"; input = [ScmPair (ScmSymbol "lambda",ScmPair (ScmPair (ScmSymbol "a", ScmPair (ScmSymbol "b", ScmPair (ScmSymbol "c", ScmSymbol "d"))),ScmPair(ScmPair (ScmSymbol "quasiquote",ScmPair(ScmPair(ScmPair (ScmSymbol "a",ScmPair (ScmPair (ScmSymbol "unquote", ScmPair (ScmSymbol "a", ScmNil)), ScmNil)),ScmPair(ScmPair (ScmSymbol "b",ScmPair (ScmPair (ScmSymbol "unquote", ScmPair (ScmSymbol "b", ScmNil)), ScmNil)),ScmPair(ScmPair (ScmSymbol "c",ScmPair (ScmPair (ScmSymbol "unquote", ScmPair (ScmSymbol "c", ScmNil)), ScmNil)),ScmPair(ScmPair (ScmSymbol "d",ScmPair (ScmPair (ScmSymbol "unquote", ScmPair (ScmSymbol "d", ScmNil)), ScmNil)),ScmNil)))),ScmNil)),ScmNil)))]; expected = [ScmLambdaOpt (["a"; "b"; "c"], "d",ScmApplic (ScmVar "cons",[ScmApplic (ScmVar "cons",[ScmConst (  (ScmSymbol "a"));ScmApplic (ScmVar "cons", [ScmVar "a"; ScmConst (  ScmNil)])]);ScmApplic (ScmVar "cons",[ScmApplic (ScmVar "cons",[ScmConst (  (ScmSymbol "b"));ScmApplic (ScmVar "cons", [ScmVar "b"; ScmConst (  ScmNil)])]);ScmApplic (ScmVar "cons",[ScmApplic (ScmVar "cons",[ScmConst (  (ScmSymbol "c"));ScmApplic (ScmVar "cons", [ScmVar "c"; ScmConst (  ScmNil)])]);ScmApplic (ScmVar "cons",[ScmApplic (ScmVar "cons",[ScmConst (  (ScmSymbol "d"));ScmApplic (ScmVar "cons", [ScmVar "d"; ScmConst (  ScmNil)])]);ScmConst (  ScmNil)])])])]))] };
  {name = "41"; input = [ScmPair (ScmSymbol "define",ScmPair (ScmPair (ScmSymbol "cmp", ScmPair (ScmSymbol "a", ScmPair (ScmSymbol "b", ScmNil))),ScmPair(ScmPair (ScmSymbol "if",ScmPair (ScmPair (ScmSymbol ">", ScmPair (ScmSymbol "a", ScmPair (ScmSymbol "b", ScmNil))),ScmPair (ScmNumber (ScmRational (3,1)), ScmPair (ScmNumber (ScmRational (3,1)), ScmNil)))),ScmNil)))]; expected = [ScmDef (ScmVar "cmp",ScmLambdaSimple (["a"; "b"],ScmIf (ScmApplic (ScmVar ">", [ScmVar "a"; ScmVar "b"]), ScmConst (  (ScmNumber (ScmRational (3,1)))),ScmConst (  (ScmNumber (ScmRational (3,1)))))))] };
  {name = "42"; input = [ScmPair (ScmSymbol "define",ScmPair(ScmPair (ScmSymbol "square",ScmPair (ScmSymbol "a", ScmPair (ScmSymbol "b", ScmPair (ScmSymbol "c", ScmNil)))),ScmPair(ScmPair (ScmSymbol "*",ScmPair (ScmSymbol "a", ScmPair (ScmSymbol "b", ScmPair (ScmSymbol "c", ScmNil)))),ScmNil)))]; expected = [ScmDef (ScmVar "square",ScmLambdaSimple (["a"; "b"; "c"],ScmApplic (ScmVar "*", [ScmVar "a"; ScmVar "b"; ScmVar "c"])))] };
  {name = "43"; input = [ScmPair (ScmSymbol "quote",ScmPair(ScmPair (ScmNumber (ScmRational (3,1)), ScmPair (ScmNumber (ScmRational (3,1)), ScmPair (ScmNumber (ScmRational (3,1)), ScmNil))),ScmNil))]; expected = [ScmConst( (ScmPair (ScmNumber (ScmRational (3,1)), ScmPair (ScmNumber (ScmRational (3,1)), ScmPair (ScmNumber (ScmRational (3,1)), ScmNil)))))] };
  {name = "44"; input = [ScmPair (ScmSymbol "quote",ScmPair (ScmPair (ScmNumber (ScmReal 1.2), ScmNumber (ScmReal 3.4)), ScmNil))]; expected = [ScmConst (  (ScmPair (ScmNumber (ScmReal 1.2), ScmNumber (ScmReal 3.4))))] };
  {name = "45"; input = [ScmPair (ScmSymbol "quote",ScmPair(ScmPair (ScmNumber (ScmReal (-0.)),ScmPair (ScmNumber (ScmReal 999.123),ScmPair (ScmPair (ScmNumber (ScmReal 501.1), ScmNumber (ScmReal 0.5)),ScmNumber (ScmReal (-0.555))))),ScmNil))]; expected = [ScmConst( (ScmPair (ScmNumber (ScmReal (-0.)),ScmPair (ScmNumber (ScmReal 999.123),ScmPair (ScmPair (ScmNumber (ScmReal 501.1), ScmNumber (ScmReal 0.5)),ScmNumber (ScmReal (-0.555)))))))] };
  {name = "46"; input = [ScmPair (ScmSymbol "quote",ScmPair(ScmPair (ScmNumber (ScmReal (-0.52)),ScmPair (ScmPair (ScmNumber (ScmReal 0.5234), ScmNumber (ScmReal (-123.4))),ScmNumber (ScmReal (-0.535)))),ScmNil))]; expected = [ScmConst( (ScmPair (ScmNumber (ScmReal (-0.52)),ScmPair (ScmPair (ScmNumber (ScmReal 0.5234), ScmNumber (ScmReal (-123.4))),ScmNumber (ScmReal (-0.535))))))] };
  {name = "47"; input = [ScmPair (ScmSymbol "quote", ScmPair (ScmPair (ScmNumber (ScmReal 0.123), ScmNil), ScmNil))]; expected = [ScmConst (  (ScmPair (ScmNumber (ScmReal 0.123), ScmNil)))] };
  {name = "48"; input = [ScmPair (ScmSymbol "quote", ScmPair (ScmPair (ScmChar '\000', ScmNil), ScmNil))]; expected = [ScmConst (  (ScmPair (ScmChar '\000', ScmNil)))] };
  {name = "49"; input = [ScmChar '\n']; expected = [ScmConst (  (ScmChar '\n'))] };
  {name = "50"; input = [ScmPair (ScmSymbol "quote",ScmPair(ScmPair (ScmNumber (ScmRational (3,1)),ScmPair (ScmNumber (ScmRational (3,1)), ScmPair (ScmNumber (ScmRational (3,1)), ScmPair (ScmChar '\012', ScmNil)))),ScmNil))]; expected = [ScmConst( (ScmPair (ScmNumber (ScmRational (3,1)),ScmPair (ScmNumber (ScmRational (3,1)), ScmPair (ScmNumber (ScmRational (3,1)), ScmPair (ScmChar '\012', ScmNil))))))] };
  {name = "51"; input = [ScmPair (ScmSymbol "quote",ScmPair(ScmPair (ScmPair (ScmChar '\t', ScmNil),ScmPair (ScmPair (ScmChar '\r', ScmNil), ScmPair (ScmPair (ScmChar ' ', ScmNil), ScmNil))),ScmNil))]; expected = [ScmConst( (ScmPair (ScmPair (ScmChar '\t', ScmNil),ScmPair (ScmPair (ScmChar '\r', ScmNil), ScmPair (ScmPair (ScmChar ' ', ScmNil), ScmNil)))))] };
  {name = "52"; input = [ScmPair (ScmSymbol "quote",ScmPair(ScmPair (ScmString "a",ScmPair (ScmString "b", ScmPair (ScmPair (ScmString "c", ScmString "d"), ScmString "e"))),ScmNil))]; expected = [ScmConst( (ScmPair (ScmString "a",ScmPair (ScmString "b", ScmPair (ScmPair (ScmString "c", ScmString "d"), ScmString "e")))))] };
  {name = "53"; input = [ScmPair (ScmSymbol "quote",ScmPair(ScmPair (ScmString "hello",ScmPair (ScmString "world",ScmPair (ScmPair (ScmNumber (ScmReal 1.2), ScmNumber (ScmRational (3,1))), ScmChar '\000'))),ScmNil))]; expected = [ScmConst( (ScmPair (ScmString "hello",ScmPair (ScmString "world",ScmPair (ScmPair (ScmNumber (ScmReal 1.2), ScmNumber (ScmRational (3,1))), ScmChar '\000')))))] };
  {name = "54"; input = [ScmPair (ScmString "should not", ScmPair (ScmString "be", ScmPair (ScmString "list", ScmNil)))]; expected = [ScmApplic (ScmConst (  (ScmString "should not")),[ScmConst (  (ScmString "be")); ScmConst (  (ScmString "list"))])] };
  {name = "55"; input = [ScmString ""]; expected = [ScmConst (  (ScmString ""))] };
  {name = "56"; input = [ScmPair (ScmSymbol "define",ScmPair (ScmPair (ScmSymbol "returnonly", ScmPair (ScmSymbol "x", ScmNil)),ScmPair(ScmPair (ScmSymbol "begin",ScmPair (ScmString "return only", ScmPair (ScmSymbol "x", ScmNil))),ScmNil)))]; expected = [ScmDef (ScmVar "returnonly",ScmLambdaSimple (["x"], ScmSeq [ScmConst (  (ScmString "return only")); ScmVar "x"]))] };
  {name = "57"; input = [ScmPair (ScmSymbol "define",ScmPair(ScmPair (ScmSymbol "applic",ScmPair (ScmSymbol "fun",ScmPair (ScmSymbol "a",ScmPair (ScmSymbol "b",ScmPair (ScmSymbol "c", ScmPair (ScmSymbol "d", ScmPair (ScmSymbol "e", ScmNil))))))),ScmPair(ScmPair (ScmSymbol "fun",ScmPair (ScmSymbol "a",ScmPair (ScmSymbol "b",ScmPair (ScmSymbol "c", ScmPair (ScmSymbol "d", ScmPair (ScmSymbol "e", ScmNil)))))),ScmNil)))]; expected = [ScmDef (ScmVar "applic",ScmLambdaSimple (["fun"; "a"; "b"; "c"; "d"; "e"],ScmApplic (ScmVar "fun", [ScmVar "a"; ScmVar "b"; ScmVar "c"; ScmVar "d"; ScmVar "e"])))] };
  {name = "58"; input = [ScmPair (ScmSymbol "define",ScmPair(ScmPair (ScmSymbol "if_fun",ScmPair (ScmSymbol "if_test",ScmPair (ScmSymbol "if_then", ScmPair (ScmSymbol "if_else", ScmNil)))),ScmPair(ScmPair (ScmSymbol "if",ScmPair (ScmSymbol "if_test",ScmPair (ScmSymbol "if_then", ScmPair (ScmSymbol "if_else", ScmNil)))),ScmNil)))]; expected = [ScmDef (ScmVar "if_fun",ScmLambdaSimple (["if_test"; "if_then"; "if_else"],ScmIf (ScmVar "if_test", ScmVar "if_then", ScmVar "if_else")))] };
  {name = "59"; input = [ScmPair (ScmSymbol "quasiquote",ScmPair (ScmPair (ScmSymbol "a", ScmPair (ScmSymbol "b", ScmNil)), ScmNil))  ]; expected = [ScmApplic (ScmVar "cons",[ScmConst (  (ScmSymbol "a"));ScmApplic (ScmVar "cons", [ScmConst (  (ScmSymbol "b")); ScmConst (  ScmNil)])])] };
  {name = "60"; input = [ScmPair (ScmSymbol "quasiquote",ScmPair (ScmPair (ScmSymbol "f", ScmPair (ScmSymbol "o", ScmNil)), ScmNil))  ]; expected = [ScmApplic (ScmVar "cons",[ScmConst (  (ScmSymbol "f"));ScmApplic (ScmVar "cons", [ScmConst (  (ScmSymbol "o")); ScmConst (  ScmNil)])])] };
  {name = "61"; input = [ScmPair (ScmSymbol "define",ScmPair (ScmPair (ScmSymbol "square", ScmPair (ScmSymbol "x", ScmNil)),ScmPair (ScmPair (ScmSymbol "", ScmPair (ScmSymbol "x", ScmPair (ScmSymbol "x", ScmNil))), ScmNil)))]; expected = [ScmDef (ScmVar "square",ScmLambdaSimple (["x"], ScmApplic (ScmVar "", [ScmVar "x"; ScmVar "x"])))] };
  {name = "62"; input = [ScmPair (ScmSymbol "define",ScmPair (ScmPair (ScmSymbol "pair_two", ScmPair (ScmSymbol "a", ScmPair (ScmSymbol "b", ScmNil))),ScmPair(ScmPair (ScmSymbol "quote",ScmPair (ScmPair (ScmSymbol "a", ScmPair (ScmSymbol "b", ScmNil)), ScmNil)),ScmNil)))]; expected = [ScmDef (ScmVar "pair_two",ScmLambdaSimple (["a"; "b"],ScmConst (  (ScmPair (ScmSymbol "a", ScmPair (ScmSymbol "b", ScmNil))))))] };
  {name = "66"; input = [ScmPair (ScmSymbol "quote",ScmPair(ScmPair (ScmNumber (ScmReal 1.3),ScmPair (ScmNumber (ScmReal (1.4)),ScmPair (ScmNumber (ScmReal 1.5),ScmPair (ScmNumber (ScmRational(5,1)),ScmPair (ScmNumber (ScmReal 1.6), ScmPair (ScmNumber (ScmRational(6,1)), ScmNumber (ScmRational(7,1)))))))),ScmNil))]; expected = [ScmConst( (ScmPair (ScmNumber (ScmReal 1.3),ScmPair (ScmNumber (ScmReal (1.4)),ScmPair (ScmNumber (ScmReal 1.5),ScmPair (ScmNumber (ScmRational(5,1)),ScmPair (ScmNumber (ScmReal 1.6), ScmPair (ScmNumber (ScmRational(6,1)), ScmNumber (ScmRational(7,1))))))))))] };
  {name = "67"; input = [ScmPair(ScmSymbol "let", ScmPair(ScmPair(ScmPair(ScmSymbol "s", ScmPair(ScmNumber (ScmRational(-1,1)), ScmNil)), ScmPair(ScmPair(ScmSymbol "y", ScmPair(ScmString "s", ScmNil)), ScmPair(ScmPair(ScmSymbol "r", ScmPair(ScmChar 'g', ScmNil)), ScmNil))), ScmPair(ScmSymbol "g", ScmPair(ScmSymbol "f", ScmPair(ScmNumber (ScmRational(-1,1)), ScmNil)))))]; expected = [ScmApplic(ScmLambdaSimple(["s"; "y"; "r"],ScmSeq([ScmVar("g"); ScmVar("f"); ScmConst( (ScmNumber (ScmRational(-1,1))))])),[ScmConst( (ScmNumber(ScmRational(-1,1)))); ScmConst( (ScmString("s"))); ScmConst( (ScmChar('g')))])] };
  {name = "68"; input = [ScmPair (ScmSymbol "cond", ScmPair (ScmPair (ScmBoolean false, ScmPair (ScmBoolean false, ScmNil)), ScmPair (ScmPair (ScmSymbol "f", ScmPair (ScmSymbol "=>", ScmPair (ScmSymbol "g", ScmNil))), ScmPair (ScmPair (ScmSymbol "h", ScmPair (ScmSymbol "=>", ScmPair (ScmSymbol "q", ScmNil))), ScmPair (ScmPair (ScmSymbol "else", ScmPair (ScmBoolean true, ScmNil)), ScmNil)))))]
  ; expected = [ScmIf (ScmConst (  (ScmBoolean false)),
      ScmConst (  (ScmBoolean false)),
      ScmApplic (ScmLambdaSimple (["value"; "f"; "rest"],
              ScmIf (ScmVar "value",
              ScmApplic (ScmApplic (ScmVar "f", []), [ScmVar "value"]),
        ScmApplic (ScmVar "rest", []))),
        [ScmVar "f";
         ScmLambdaSimple ([], ScmVar "g");
         ScmLambdaSimple ([],
                ScmApplic (ScmLambdaSimple (["value"; "f"; "rest"],
                 ScmIf (ScmVar "value",
                 ScmApplic (ScmApplic (ScmVar "f", []), [ScmVar "value"]),
                 ScmApplic (ScmVar "rest", []))),
             [ScmVar "h";
              ScmLambdaSimple ([], ScmVar "q");
              ScmLambdaSimple ([], ScmConst (  (ScmBoolean true)))]))]))]
   };
  {name = "69"; input = [ScmPair (ScmSymbol "and", ScmPair (ScmString "hello", ScmPair (ScmSymbol "v", ScmNil))); ScmPair (ScmSymbol "letrec", ScmPair (ScmPair (ScmPair (ScmSymbol "s", ScmPair (ScmNumber (ScmRational (4, 1)), ScmNil)), ScmNil), ScmPair (ScmPair (ScmSymbol "cond", ScmPair (ScmPair (ScmSymbol "f", ScmPair (ScmSymbol "=>", ScmPair (ScmSymbol "g", ScmNil))), ScmPair (ScmPair (ScmSymbol "else", ScmPair (ScmBoolean true, ScmNil)), ScmNil))), ScmNil)))]; expected = [ScmIf (ScmConst (  (ScmString "hello")), ScmVar "v", ScmConst (  (ScmBoolean false)));
   ScmApplic (ScmLambdaSimple (["s"],
      ScmSeq([ScmSet (ScmVar "s",  ScmConst (  (ScmNumber (ScmRational (4,1)))));
          ScmApplic (ScmLambdaSimple (["value"; "f"; "rest"],
                  ScmIf (ScmVar "value",
                ScmApplic (ScmApplic (ScmVar "f", []), [ScmVar "value"]),
          ScmApplic (ScmVar "rest", []))),
            [ScmVar "f";
             ScmLambdaSimple ([], ScmVar "g");
             ScmLambdaSimple ([], ScmConst (  (ScmBoolean true)))])])),
     [ScmConst (  (ScmSymbol "whatever"))])] };
  {name = "70"; input = [ScmPair(ScmSymbol "cond", ScmPair(ScmPair(ScmSymbol "f", ScmPair(ScmSymbol "g", ScmNil)), ScmNil))]; expected = [ScmIf(ScmVar("f"),ScmVar("g"),ScmConst(ScmVoid))] };
  {name = "71"; input = [ScmPair(ScmSymbol "cond", ScmPair(ScmPair(ScmSymbol "f", ScmPair(ScmPair(ScmSymbol "lambda", ScmPair(ScmSymbol "s", ScmPair(ScmSymbol "x", ScmNil))),ScmNil)), ScmNil))]; expected = [ScmIf(ScmVar("f"),ScmLambdaOpt([],"s",ScmVar("x")),ScmConst(ScmVoid))] };
  {name = "72"; input = [ScmPair (ScmPair (ScmSymbol "or", ScmPair (ScmPair (ScmSymbol "and", ScmPair (ScmPair (ScmSymbol "lambda", ScmPair (ScmNil, ScmPair (ScmSymbol "<test>", ScmNil))), ScmPair (ScmPair (ScmSymbol "lambda", ScmPair (ScmNil, ScmPair (ScmSymbol "<then>", ScmNil))), ScmNil))), ScmPair (ScmPair (ScmSymbol "lambda", ScmPair (ScmNil, ScmPair (ScmSymbol "<else>", ScmNil))), ScmNil))), ScmNil)]; expected = [ScmApplic (ScmOr ([ScmIf (ScmLambdaSimple ([], ScmVar "<test>"), ScmLambdaSimple ([], ScmVar "<then>"), ScmConst (  (ScmBoolean false)));ScmLambdaSimple ([], ScmVar "<else>")]), [])] };
  {name = "73"; input = [ScmPair (ScmSymbol "define", ScmPair (ScmPair (ScmSymbol "x", ScmSymbol "z"), ScmPair (ScmPair (ScmSymbol "eq?", ScmPair (ScmChar 'y', ScmPair (ScmPair (ScmSymbol "car", ScmPair (ScmSymbol "z", ScmNil)), ScmNil))), ScmNil)))]; expected = [ScmDef (ScmVar "x", ScmLambdaOpt ([], "z", ScmApplic (ScmVar "eq?", [ScmConst (  (ScmChar 'y'));ScmApplic (ScmVar "car", [ScmVar "z"])])))] };
  {name = "74"; input = [ScmPair (ScmSymbol "define", ScmPair (ScmPair (ScmSymbol "x", ScmSymbol "y"), ScmPair (ScmPair (ScmSymbol "eq?", ScmPair (ScmPair (ScmSymbol "quote", ScmPair (ScmNil, ScmNil)), ScmPair (ScmSymbol "y", ScmNil))), ScmNil)))]; expected = [ScmDef (ScmVar "x", ScmLambdaOpt ([], "y", ScmApplic (ScmVar "eq?", [ScmConst (  (ScmNil));ScmVar "y"])))] };
  {name = "75"; input = [ScmPair (ScmSymbol "or", ScmPair (ScmPair (ScmSymbol "zero?", ScmPair (ScmSymbol "x", ScmNil)), ScmPair (ScmPair (ScmSymbol "zero?", ScmPair (ScmSymbol "y", ScmNil)), ScmPair (ScmPair (ScmSymbol "zero?", ScmPair (ScmSymbol "z", ScmNil)), ScmPair (ScmPair (ScmSymbol "zero?", ScmPair (ScmSymbol "w", ScmNil)), ScmPair (ScmPair (ScmSymbol "zero?", ScmPair (ScmSymbol "v", ScmNil)), ScmNil))))))]; expected = [ScmOr ([ScmApplic (ScmVar "zero?", [ScmVar "x"]);ScmApplic (ScmVar "zero?", [ScmVar "y"]);ScmApplic (ScmVar "zero?", [ScmVar "z"]);ScmApplic (ScmVar "zero?", [ScmVar "w"]);ScmApplic (ScmVar "zero?", [ScmVar "v"])])] };

 {name = "QQ";
 input = [ScmPair (ScmSymbol "quasiquote", ScmPair (ScmSymbol "a", ScmNil))];
 expected = [ScmConst (ScmSymbol "a")]};
{name = "QQ-nil";
 input = [ScmPair (ScmSymbol "quasiquote", ScmPair (ScmNil, ScmNil))];
 expected = [ScmConst ScmNil]};
{name = "QQ-unquote";
 input =
  [ScmPair
   (ScmSymbol "quasiquote",
    ScmPair
     (ScmPair (ScmSymbol "unquote", ScmPair (ScmSymbol "a", ScmNil)), ScmNil))];
 expected = [ScmVar "a"]};
{name = "QQ-unquote-splicing";
 input =
  [ScmPair
   (ScmSymbol "quasiquote",
    ScmPair
     (ScmPair
       (ScmSymbol "unquote-splicing",
        ScmPair
         (ScmPair
           (ScmSymbol "+",
            ScmPair
             (ScmNumber (ScmRational (1, 1)),
              ScmPair (ScmNumber (ScmRational (2, 1)), ScmNil))),
          ScmNil)),
      ScmNil))];
 expected =
  [ScmConst
   (ScmPair
     (ScmSymbol "unquote-splicing",
      ScmPair
       (ScmPair
         (ScmSymbol "+",
          ScmPair
           (ScmNumber (ScmRational (1, 1)),
            ScmPair (ScmNumber (ScmRational (2, 1)), ScmNil))),
        ScmNil)))]};
        {name = "QQ-list";
        input =
         [ScmPair
          (ScmSymbol "quasiquote",
           ScmPair
            (ScmPair
              (ScmChar 'a',
               ScmPair
                (ScmSymbol "b",
                 ScmPair
                  (ScmPair (ScmSymbol "unquote", ScmPair (ScmSymbol "c", ScmNil)),
                   ScmPair
                    (ScmPair
                      (ScmSymbol "unquote-splicing", ScmPair (ScmSymbol "d", ScmNil)),
                     ScmPair
                      (ScmPair (ScmSymbol "quote", ScmPair (ScmSymbol "e", ScmNil)),
                       ScmPair (ScmPair (ScmSymbol "f", ScmNil), ScmNil)))))),
             ScmNil))];
        expected =
         [ScmApplic (ScmVar "cons",
          [ScmConst (ScmChar 'a');
           ScmApplic (ScmVar "cons",
            [ScmConst (ScmSymbol "b");
             ScmApplic (ScmVar "cons",
              [ScmVar "c";
               ScmApplic (ScmVar "append",
                [ScmVar "d";
                 ScmApplic (ScmVar "cons",
                  [ScmApplic (ScmVar "cons",
                    [ScmConst (ScmSymbol "quote");
                     ScmApplic (ScmVar "cons",
                      [ScmConst (ScmSymbol "e"); ScmConst ScmNil])]);
                   ScmApplic (ScmVar "cons",
                    [ScmApplic (ScmVar "cons",
                      [ScmConst (ScmSymbol "f"); ScmConst ScmNil]);
                     ScmConst ScmNil])])])])])])]};
                     {name = "QQ-vector";
                     input =
                      [ScmPair
                       (ScmSymbol "quasiquote",
                        ScmPair
                         (ScmVector
                           [ScmSymbol "a";
                            ScmPair (ScmSymbol "unquote", ScmPair (ScmSymbol "b", ScmNil));
                            ScmPair
                             (ScmSymbol "unquote-splicing", ScmPair (ScmSymbol "c", ScmNil));
                            ScmString "d"],
                          ScmNil))];
                     expected =
                      [ScmApplic (ScmVar "list->vector",
                       [ScmApplic (ScmVar "cons",
                         [ScmConst (ScmSymbol "a");
                          ScmApplic (ScmVar "cons",
                           [ScmVar "b";
                            ScmApplic (ScmVar "append",
                             [ScmVar "c";
                              ScmApplic (ScmVar "cons",
                               [ScmConst (ScmString "d"); ScmConst ScmNil])])])])])]};
  {name = "OR"; input = [ScmPair (ScmSymbol "or", ScmNil)]; expected = [ScmConst (ScmBoolean false)] };
  {name = "AND"; input = [ScmPair (ScmSymbol "and", ScmNil)]; expected = [ScmConst (ScmBoolean true)] };
  {name = "AND_ONE"; input = [ScmPair (ScmSymbol "and", ScmPair (ScmNumber (ScmRational (42, 1)), ScmNil))]; expected = [ScmConst (ScmNumber (ScmRational (42, 1)))] };
  {name = "OR_ONE"; input = [ScmPair (ScmSymbol "or", ScmPair (ScmNumber (ScmRational (42, 1)), ScmNil))]; expected = [ScmConst (ScmNumber (ScmRational (42, 1)))] }
  ];;



let test_case case =
try
let actual = List.fold_right (fun a b -> (Tag_Parser.tag_parse_expression a) :: b) case.input [] in
if List.fold_left (fun a b -> a && b) true (List.map2 expr_eq actual case.expected) then "PASS" else "FAILURE"
with
| X_syntax_error(s, msg) -> Printf.sprintf "Exception: Syntax Error message: %s for sexpr: %s" msg (string_of_sexpr s)
| X_reserved_word(s) -> Printf.sprintf "Exception: Reserved Word: %s" s
| X_not_implemented -> Printf.sprintf "Exception: Syntax not yet implemented"
| _ -> "Unknown Failure"

let test_cases cases =
let names, results =  (List.map (fun case -> case.name) cases),(List.map test_case cases) in
List.map2 (fun name result -> Printf.sprintf "%s: %s" result name) names results;;

List.map (Printf.printf "%s\n") (test_cases cases);;
