#use "semantic-analyser.ml";;

type case = {input: expr; expected: expr'; name: string; };;

let cases = [

{input = ScmLambdaSimple ([], ScmConst (ScmNumber (ScmRational(115,1)))); expected = ScmLambdaSimple'  ([], ScmConst'  (ScmNumber (ScmRational(115,1))));name = "RON_Test_Converted 1"};



{input = ScmLambdaSimple (["x"], ScmSet (ScmVar "x", ScmApplic (ScmLambdaSimple ([], ScmVar "x"), [])));
expected = 

ScmLambdaSimple'  (["x"], ScmSeq'   [ScmSet'    (VarParam ("x", 0), ScmBox'  (VarParam ("x", 0)));   ScmBoxSet'  (VarParam ("x", 0),    ScmApplic'  (ScmLambdaSimple'  ([], ScmBoxGet'  (VarBound ("x", 0, 0))), []))]);
name = "RON_Test_Converted 11"};

{input = ScmConst      (ScmPair      (ScmPair (ScmSymbol "lambda",        ScmPair (ScmNil,         ScmPair          (ScmPair (ScmSymbol "lambda",            ScmPair (ScmPair (ScmSymbol "x", ScmNil),             ScmPair (ScmSymbol "x",              ScmPair               (ScmPair (ScmSymbol "lambda",                 ScmPair (ScmNil,                  ScmPair                   (ScmPair (ScmSymbol "set!",                     ScmPair (ScmSymbol "x", ScmPair (ScmNumber (ScmRational(94,1)), ScmNil))),                   ScmNil))),               ScmNil)))),          ScmNil))),      ScmNil)); expected = ScmConst'   (ScmPair     (ScmPair (ScmSymbol "lambda",       ScmPair (ScmNil,        ScmPair         (ScmPair (ScmSymbol "lambda",           ScmPair (ScmPair (ScmSymbol "x", ScmNil),            ScmPair (ScmSymbol "x",             ScmPair              (ScmPair (ScmSymbol "lambda",                ScmPair (ScmNil,                 ScmPair                  (ScmPair (ScmSymbol "set!",                    ScmPair (ScmSymbol "x", ScmPair (ScmNumber (ScmRational(94,1)), ScmNil))),                  ScmNil))),              ScmNil)))),         ScmNil))),     ScmNil));name = "RON_Test_Converted 2"};


{input = ScmApplic  (ScmLambdaSimple (["x"],    ScmIf (ScmApplic (ScmVar "x", [ScmConst (ScmNumber (ScmRational(88,1)))]),     ScmApplic (ScmVar "x", [ScmConst (ScmNumber (ScmRational(88,1)))]),     ScmApplic      (ScmLambdaSimple (["x"], ScmSet (ScmVar "x", ScmConst (ScmNumber (ScmRational(88,1))))),      [ScmConst (ScmNumber (ScmRational(88,1)))]))),  [ScmLambdaSimple (["x"], ScmVar "x")]); expected = ScmApplic'  (ScmLambdaSimple'  (["x"],   ScmIf'     (ScmApplic'  (ScmVar'  (VarParam ("x", 0)), [ScmConst'  (ScmNumber (ScmRational(88,1)))]),    ScmApplicTP'  (ScmVar'  (VarParam ("x", 0)), [ScmConst'  (ScmNumber (ScmRational(88,1)))]),    ScmApplicTP'      (ScmLambdaSimple'  (["x"],       ScmSet'  (VarParam ("x", 0), ScmConst'  (ScmNumber (ScmRational(88,1))))),     [ScmConst'  (ScmNumber (ScmRational(88,1)))]))), [ScmLambdaSimple'  (["x"], ScmVar'  (VarParam ("x", 0)))]);name = "RON_Test_Converted 3"};


{input = ScmLambdaSimple ([],  ScmSeq   [ScmApplic (ScmLambdaSimple ([], ScmVar "x"), []);    ScmApplic     (ScmLambdaSimple (["x"],       ScmSeq        [ScmSet (ScmVar "x", ScmConst (ScmNumber (ScmRational(104,1))));         ScmLambdaSimple ([], ScmVar "x")]),     [ScmConst (ScmNumber (ScmRational(104,1)))]);    ScmApplic (ScmLambdaOpt ([], "x", ScmVar "x"), [ScmConst (ScmNumber (ScmRational(104,1)))])]); 

expected = ScmLambdaSimple'  
([], ScmSeq'  
 [ScmApplic'  (ScmLambdaSimple'  ([], ScmVar'  (VarFree "x")), []);   ScmApplic'   
   (ScmLambdaSimple'  (["x"],      
   ScmSeq'        [ScmSet'  (VarParam ("x", 0), ScmBox'  (VarParam ("x", 0))); 
          ScmSeq'      
              [ScmBoxSet'  (VarParam ("x", 0),
               ScmConst'  (ScmNumber (ScmRational(104,1))));          ScmLambdaSimple'  ([], ScmBoxGet'  (VarBound ("x", 0, 0)))]]),
                   [ScmConst'  (ScmNumber (ScmRational(104,1)))]);   ScmApplicTP'  (ScmLambdaOpt'  ([], "x", ScmVar'  (VarParam ("x", 0))),    [ScmConst'  (ScmNumber (ScmRational(104,1)))])]);name = "RON_Test_Converted 9"};


{input = ScmApplic (ScmVar "y",  [ScmLambdaSimple (["y"],    ScmSeq     [ScmSet (ScmVar "a", ScmLambdaSimple (["b"], ScmApplic (ScmVar "a", [ScmVar "b"])));      ScmSet (ScmVar "t",       ScmLambdaSimple (["x"],        ScmSeq         [ScmSet (ScmVar "y",           ScmLambdaSimple (["j"], ScmApplic (ScmVar "x", [ScmVar "j"; ScmVar "x"])));          ScmVar "h"]));      ScmApplic (ScmVar "y", [ScmVar "a"])])]); expected = ScmApplic'  (ScmVar'  (VarFree "y"), [ScmLambdaSimple'  (["y"],   ScmSeq'     [ScmSet'  (VarParam ("y", 0), ScmBox'  (VarParam ("y", 0)));     ScmSeq'       [ScmSet'  (VarFree "a",        ScmLambdaSimple'  (["b"],         ScmApplicTP'  (ScmVar'  (VarFree "a"), [ScmVar'  (VarParam ("b", 0))])));       ScmSet'  (VarFree "t",        ScmLambdaSimple'  (["x"],         ScmSeq'           [ScmBoxSet'  (VarBound ("y", 0, 0),            ScmLambdaSimple'  (["j"],             ScmApplicTP'  (ScmVar'  (VarBound ("x", 0, 0)),              [ScmVar'  (VarParam ("j", 0)); ScmVar'  (VarBound ("x", 0, 0))])));           ScmVar'  (VarFree "h")]));       ScmApplicTP'  (ScmBoxGet'  (VarParam ("y", 0)), [ScmVar'  (VarFree "a")])]])]);name = "RON_Test_Converted 12"};

{input = ScmLambdaSimple (["x"],  ScmSeq   [ScmLambdaSimple (["x"], ScmSet (ScmVar "x", ScmVar "x"));    ScmLambdaSimple (["x"], ScmSet (ScmVar "x", ScmVar "x"))]); expected = ScmLambdaSimple'  (["x"], ScmSeq'   [ScmLambdaSimple'  (["x"],    ScmSet'  (VarParam ("x", 0), ScmVar'  (VarParam ("x", 0))));   ScmLambdaSimple'  (["x"],    ScmSet'  (VarParam ("x", 0), ScmVar'  (VarParam ("x", 0))))]);name = "RON_Test_Converted 13"};


{input = ScmLambdaOpt ([], "x",  ScmSeq   [ScmLambdaSimple (["x"], ScmSet (ScmVar "x", ScmConst (ScmNumber (ScmRational(91,1)))));    ScmApplic (ScmVar "car", [ScmVar "x"])]); expected = ScmLambdaOpt'  ([], "x", ScmSeq'   [ScmLambdaSimple'  (["x"],    ScmSet'  (VarParam ("x", 0), ScmConst'  (ScmNumber (ScmRational(91,1)))));   ScmApplicTP'  (ScmVar'  (VarFree "car"), [ScmVar'  (VarParam ("x", 0))])]);name = "RON_Test_Converted 15"};

{input = ScmIf (ScmVar "x", ScmApplic (ScmVar "x", []), ScmVar "x"); expected = ScmIf'  (ScmVar'  (VarFree "x"), ScmApplic'  (ScmVar'  (VarFree "x"), []), ScmVar'  (VarFree "x"));name = "RON_Test_Converted 16"};

{input = ScmLambdaSimple ([],  ScmIf (ScmVar "x", ScmApplic (ScmVar "x", []), ScmApplic (ScmVar "not", [ScmVar "x"]))); expected = ScmLambdaSimple'  ([], ScmIf'  (ScmVar'  (VarFree "x"), ScmApplicTP'  (ScmVar'  (VarFree "x"), []),  ScmApplicTP'  (ScmVar'  (VarFree "not"), [ScmVar'  (VarFree "x")])));name = "RON_Test_Converted 17"};


{input = ScmConst(ScmVoid); expected =  ScmConst'  ScmVoid;name = "RON_Test_Converted 21"};


{input = ScmLambdaSimple (["x"],  ScmSeq [ScmApplic (ScmVar "x", []); ScmSet (ScmVar "x", ScmApplic (ScmVar "x", []))]); expected = ScmLambdaSimple'  (["x"], ScmSeq'   [ScmApplic'  (ScmVar'  (VarParam ("x", 0)), []);   ScmSet'  (VarParam ("x", 0), ScmApplic'  (ScmVar'  (VarParam ("x", 0)), []))]);name = "RON_Test_Converted 19"};

{input = ScmLambdaSimple (["x"],  ScmApplic   (ScmLambdaSimple (["y"],     ScmSeq [ScmSet (ScmVar "x", ScmApplic (ScmVar "y", [])); ScmConst (ScmNumber (ScmRational(50,1)))]),   [])); expected = ScmLambdaSimple'  (["x"], ScmApplicTP'   (ScmLambdaSimple'  (["y"],    ScmSeq'      [ScmSet'  (VarBound ("x", 0, 0),       ScmApplic'  (ScmVar'  (VarParam ("y", 0)), []));      ScmConst'  (ScmNumber (ScmRational(50,1)))]),  []));name = "RON_Test_Converted 20"};



{input = ScmLambdaSimple ([], ScmIf (ScmApplic (ScmVar "f", [ScmVar "x"]),  ScmIf (ScmApplic (ScmVar "g", [ScmVar "y"]), ScmApplic (ScmVar "h", [ScmVar "z"]),   ScmConst (ScmBoolean false)),  ScmConst (ScmBoolean false))); expected = ScmLambdaSimple'  ([], ScmIf'  (ScmApplic'  (ScmVar'  (VarFree "f"), [ScmVar'  (VarFree "x")]),  ScmIf'  (ScmApplic'  (ScmVar'  (VarFree "g"), [ScmVar'  (VarFree "y")]),   ScmApplicTP'  (ScmVar'  (VarFree "h"), [ScmVar'  (VarFree "z")]),   ScmConst'  (ScmBoolean false)),  ScmConst'  (ScmBoolean false)));name = "RON_Test_Converted 29"};



{input = ScmLambdaSimple (["x"], ScmSet (ScmVar "x", ScmApplic (ScmVar "f", [ScmVar "y"]))); expected = ScmLambdaSimple'  (["x"], ScmSet'  (VarParam ("x", 0),  ScmApplic'  (ScmVar'  (VarFree "f"), [ScmVar'  (VarFree "y")])));name = "RON_Test_Converted 31"};

{input = ScmLambdaSimple ([], ScmSet (ScmVar "x",  ScmApplic (ScmVar "f",   [ScmLambdaSimple (["y"], ScmApplic (ScmVar "g", [ScmVar "x"; ScmVar "y"]))]))); expected = ScmLambdaSimple'  ([], ScmSet'  (VarFree "x",  ScmApplic'  (ScmVar'  (VarFree "f"),   [ScmLambdaSimple'  (["y"],     ScmApplicTP'  (ScmVar'  (VarFree "g"),      [ScmVar'  (VarFree "x"); ScmVar'  (VarParam ("y", 0))]))])));name = "RON_Test_Converted 32"};


{input = ScmLambdaSimple (["x"], ScmApplic (ScmVar "list",  [ScmLambdaSimple ([], ScmVar "x"); ScmLambdaSimple (["y"], ScmSet (ScmVar "x", ScmVar "y"))]));
 expected =
  ScmLambdaSimple'  (["x"], 
 ScmSeq'   [ScmSet'  (VarParam ("x", 0), ScmBox'  (VarParam ("x", 0)));   ScmApplicTP'  (ScmVar'  (VarFree "list"),    [ScmLambdaSimple'  ([], ScmBoxGet'  (VarBound ("x", 0, 0)));     ScmLambdaSimple'  (["y"],      ScmBoxSet'  (VarBound ("x", 0, 0), ScmVar'  (VarParam ("y", 0))))])]);name = "RON_Test_Converted 35"};

{input = ScmLambdaSimple (["x"; "y"; "z"], ScmApplic (ScmVar "+", [ScmVar "x"; ScmVar "y"; ScmVar "z"])); expected = ScmLambdaSimple'  (["x"; "y"; "z"], ScmApplicTP'  (ScmVar'  (VarFree "+"),  [ScmVar'  (VarParam ("x", 0)); ScmVar'  (VarParam ("y", 1));   ScmVar'  (VarParam ("z", 2))]));name = "RON_Test_Converted 36"};


{input = ScmLambdaSimple (["x"; "y"; "z"], ScmApplic (ScmVar "+",  [ScmVar "x"; ScmVar "y";   ScmLambdaSimple (["z"],    ScmApplic (ScmVar "+", [ScmVar "z"; ScmVar "x"; ScmConst (ScmNumber (ScmRational(41,1)))]))])); expected = ScmLambdaSimple'  (["x"; "y"; "z"], ScmApplicTP'  (ScmVar'  (VarFree "+"),  [ScmVar'  (VarParam ("x", 0)); ScmVar'  (VarParam ("y", 1));   ScmLambdaSimple'  (["z"],    ScmApplicTP'  (ScmVar'  (VarFree "+"),     [ScmVar'  (VarParam ("z", 0)); ScmVar'  (VarBound ("x", 0, 0));      ScmConst'  (ScmNumber (ScmRational(41,1)))]))]));name = "RON_Test_Converted 37"};


{input = ScmLambdaSimple (["x"; "y"; "z"], ScmApplic (ScmVar "+",  [ScmVar "x"; ScmVar "y";   ScmLambdaSimple (["z"],    ScmApplic (ScmVar "+",     [ScmVar "z";      ScmLambdaSimple (["x"], ScmApplic (ScmVar "+", [ScmVar "x"; ScmVar "y"; ScmVar "z"]))]))])); expected = ScmLambdaSimple'  (["x"; "y"; "z"], ScmApplicTP'  (ScmVar'  (VarFree "+"),  [ScmVar'  (VarParam ("x", 0)); ScmVar'  (VarParam ("y", 1));   ScmLambdaSimple'  (["z"],    ScmApplicTP'  (ScmVar'  (VarFree "+"),     [ScmVar'  (VarParam ("z", 0));      ScmLambdaSimple'  (["x"],       ScmApplicTP'  (ScmVar'  (VarFree "+"),        [ScmVar'  (VarParam ("x", 0)); ScmVar'  (VarBound ("y", 1, 1));         ScmVar'  (VarBound ("z", 0, 0))]))]))]));name = "RON_Test_Converted 40"};




{input = ScmDef (ScmVar "test", ScmLambdaSimple (["x"],  ScmApplic (ScmVar "list",   [ScmLambdaSimple ([], ScmVar "x"); ScmLambdaSimple (["y"], ScmSet (ScmVar "x", ScmVar "y"))])));
expected = 
  ScmDef'  (VarFree "test", 
  ScmLambdaSimple'  (["x"],  
  ScmSeq'    [ScmSet'  (VarParam ("x", 0), ScmBox'  (VarParam ("x", 0)));    ScmApplicTP'  (ScmVar'  (VarFree "list"),     [ScmLambdaSimple'  ([], ScmBoxGet'  (VarBound ("x", 0, 0)));      ScmLambdaSimple'  (["y"],       ScmBoxSet'  (VarBound ("x", 0, 0), ScmVar'(VarParam ("y", 0))))])]));name = "RON_Test_Converted 44"};


{input = ScmDef (ScmVar "test", ScmLambdaSimple (["x"; "y"],  ScmSet (ScmVar "x", ScmApplic (ScmVar "*", [ScmVar "x"; ScmVar "y"])))); expected = ScmDef'  (VarFree "test", ScmLambdaSimple'  (["x"; "y"],  ScmSet'  (VarParam ("x", 0),   ScmApplic'  (ScmVar'  (VarFree "*"),    [ScmVar'  (VarParam ("x", 0)); ScmVar'  (VarParam ("y", 1))]))));name = "RON_Test_Converted 45"};


{input = ScmDef (ScmVar "test", ScmLambdaSimple (["x"; "y"],  ScmIf (ScmVar "x", ScmLambdaSimple ([], ScmSet (ScmVar "y", ScmVar "x")),   ScmLambdaSimple (["z"], ScmSet (ScmVar "x", ScmVar "z")))));
 expected = 
 ScmDef'  (VarFree "test", ScmLambdaSimple'  (["x"; "y"],
  ScmSeq'    [ScmSet'  (VarParam ("x", 0), ScmBox'  (VarParam ("x", 0)));        ScmIf'  (ScmBoxGet'  (VarParam ("x", 0)), 
      ScmLambdaSimple'  ([],      ScmSet'  (VarBound ("y", 0, 1), ScmBoxGet'  (VarBound ("x", 0, 0)))),     ScmLambdaSimple'  (["z"],      ScmBoxSet'  (VarBound ("x", 0, 0), ScmVar'  (VarParam ("z", 0)))))]));name = "RON_Test_Converted 46"};

{input = ScmDef (ScmVar "test", ScmLambdaSimple (["x"; "y"],  ScmApplic (ScmVar "list",   [ScmLambdaSimple ([],     ScmSet (ScmVar "x",      ScmApplic (ScmVar "+", [ScmVar "x"; ScmConst (ScmNumber (ScmRational(31,1)))])));    ScmLambdaSimple ([], ScmVar "y")]))); expected = ScmDef'  (VarFree "test", ScmLambdaSimple'  (["x"; "y"],  ScmApplicTP'  (ScmVar'  (VarFree "list"),   [ScmLambdaSimple'  ([],     ScmSet'  (VarBound ("x", 0, 0),      ScmApplic'  (ScmVar'  (VarFree "+"),       [ScmVar'  (VarBound ("x", 0, 0)); ScmConst'  (ScmNumber (ScmRational(31,1)))])));    ScmLambdaSimple'  ([], ScmVar'  (VarBound ("y", 0, 1)))])));name = "RON_Test_Converted 47"};



{input = ScmDef (ScmVar "test", ScmLambdaSimple (["x"],  ScmLambdaSimple (["op"],   ScmIf (ScmApplic (ScmVar "eq?", [ScmVar "op"; ScmConst (ScmSymbol "read")]),    ScmLambdaSimple ([], ScmVar "x"),    ScmIf (ScmApplic (ScmVar "eq?", [ScmVar "op"; ScmConst (ScmSymbol "write")]),     ScmLambdaSimple (["val"], ScmSet (ScmVar "x", ScmVar "val")), ScmConst ScmVoid)))));
 
expected = 
ScmDef'  (VarFree "test", 
ScmLambdaSimple'  (["x"], 
 ScmLambdaSimple'  (["op"], 
   ScmIf'     (ScmApplic'
      (ScmVar'  (VarFree "eq?"),    
        [ScmVar'  (VarParam ("op", 0)); ScmConst'  (ScmSymbol "read")]),    ScmLambdaSimple'  ([], ScmVar'  (VarBound ("x", 1, 0))),   
       ScmIf'      (ScmApplic'  (ScmVar'  (VarFree "eq?"),       [ScmVar'                (VarParam ("op", 0)); 
       ScmConst'  (ScmSymbol "write")]),    
        ScmLambdaSimple'  (["val"],      ScmSet'  (VarBound ("x", 1, 0), ScmVar'  (VarParam ("val", 0)))),     ScmConst'  ScmVoid)))));name = "RON_Test_Converted 48"};




{input = ScmDef (ScmVar "test", ScmLambdaSimple (["x"],  ScmApplic   (ScmLambdaSimple (["y"],     ScmApplic (ScmVar "cons",      [ScmLambdaSimple ([], ScmVar "x");       ScmApplic (ScmVar "cons", [ScmSet (ScmVar "x", ScmVar "y"); ScmConst (ScmNil)])])),   [ScmConst (ScmNumber (ScmRational(52,1)))]))); expected = ScmDef'  (VarFree "test", ScmLambdaSimple'  (["x"],  ScmApplicTP'    (ScmLambdaSimple'  (["y"],     ScmApplicTP'  (ScmVar'  (VarFree "cons"),      [ScmLambdaSimple'  ([], ScmVar'  (VarBound ("x", 1, 0)));       ScmApplic'  (ScmVar'  (VarFree "cons"),        [ScmSet'  (VarBound ("x", 0, 0), ScmVar'  (VarParam ("y", 0)));         ScmConst'  (ScmNil)])])),   [ScmConst'  (ScmNumber (ScmRational(52,1)))])));name = "RON_Test_Converted 49"};


{input = ScmDef (ScmVar "test", ScmLambdaSimple (["x"; "y"; "z"],  ScmApplic (ScmVar "list",   [ScmLambdaSimple ([],     ScmApplic (ScmVar "list",      [ScmLambdaSimple (["x"], ScmSet (ScmVar "x", ScmVar "z"));       ScmLambdaSimple ([], ScmSet (ScmVar "x", ScmVar "z")); ScmVar "x"]));    ScmLambdaSimple (["y"], ScmSet (ScmVar "x", ScmVar "y"))]))); 

expected =
 ScmDef'  (VarFree "test",
  ScmLambdaSimple'  (["x"; "y"; "z"], 
   ScmSeq'    
   [ScmSet'  (VarParam ("x", 0), ScmBox'  (VarParam ("x", 0)));         ScmApplicTP'  (ScmVar'  (VarFree "list"),
        [ScmLambdaSimple'  ([],          ScmApplicTP'  (ScmVar'  (VarFree "list"),    
      [ScmLambdaSimple'  (["x"],  
     ScmSet'  (VarParam ("x", 0), ScmVar'  (VarBound ("z", 1, 2))));         
     ScmLambdaSimple'  ([],          ScmBoxSet'  (VarBound ("x", 1, 0), ScmVar'  (VarBound ("z", 1, 2))));         ScmBoxGet'  (VarBound ("x", 0, 0))])); 
     ScmLambdaSimple'  (["y"],       ScmBoxSet'  (VarBound ("x", 0, 0), ScmVar'  (VarParam ("y", 0))))])]));
     
     name = "RON_Test_Converted 51"};


{input = ScmLambdaSimple (["x"; "y"], ScmApplic (ScmVar "list",  [ScmLambdaSimple ([], ScmVar "x"); ScmLambdaSimple (["z"], ScmSet (ScmVar "y", ScmVar "z"));   ScmLambdaSimple (["z"], ScmSet (ScmVar "x", ScmVar "z"))])); expected = ScmLambdaSimple'  (["x"; "y"], ScmSeq'   [ScmSet'  (VarParam ("x", 0), ScmBox'  (VarParam ("x", 0)));   ScmApplicTP'  (ScmVar'  (VarFree "list"),    [ScmLambdaSimple'  ([], ScmBoxGet'  (VarBound ("x", 0, 0)));     ScmLambdaSimple'  (["z"],      ScmSet'  (VarBound ("y", 0, 1), ScmVar'  (VarParam ("z", 0))));     ScmLambdaSimple'  (["z"],      ScmBoxSet'  (VarBound ("x", 0, 0), ScmVar'  (VarParam ("z", 0))))])]);name = "RON_Test_Converted 53"};










{input = ScmLambdaSimple (["x"; "y"], ScmApplic (ScmVar "list",  [ScmLambdaSimple ([], ScmVar "x"); ScmLambdaSimple ([], ScmVar "y");   ScmLambdaSimple (["z"], ScmSet (ScmVar "y", ScmVar "z"));   ScmLambdaSimple (["z"], ScmSet (ScmVar "x", ScmVar "z"))])); expected = ScmLambdaSimple'  (["x"; "y"], ScmSeq'   [ScmSet'  (VarParam ("x", 0), ScmBox'  (VarParam ("x", 0)));   ScmSet'  (VarParam ("y", 1), ScmBox'  (VarParam ("y", 1)));   ScmApplicTP'  (ScmVar'  (VarFree "list"),    [ScmLambdaSimple'  ([], ScmBoxGet'  (VarBound ("x", 0, 0)));     ScmLambdaSimple'  ([], ScmBoxGet'  (VarBound ("y", 0, 1)));     ScmLambdaSimple'  (["z"],      ScmBoxSet'  (VarBound ("y", 0, 1), ScmVar'  (VarParam ("z", 0))));     ScmLambdaSimple'  (["z"],      ScmBoxSet'  (VarBound ("x", 0, 0), ScmVar'  (VarParam ("z", 0))))])]);name = "RON_Test_Converted 54"};



{input = ScmDef (ScmVar "func", ScmLambdaOpt ([], "x",  ScmApplic (ScmVar "list",   [ScmLambdaSimple ([], ScmVar "x"); ScmLambdaSimple (["z"], ScmSet (ScmVar "x", ScmVar "z"));    ScmLambdaSimple (["z"], ScmSet (ScmVar "x", ScmVar "z"))])));

 expected = ScmDef'
   (VarFree "func", 
   ScmLambdaOpt'  ([], "x",  ScmSeq'  
     [ScmSet'  (VarParam ("x", 0), ScmBox'  (VarParam ("x", 0)));    ScmApplicTP'  (ScmVar'  (VarFree "list"),     [ScmLambdaSimple'  ([], ScmBoxGet'  (VarBound ("x", 0, 0)));     
      ScmLambdaSimple'  (["z"], 
            ScmBoxSet'  (VarBound ("x", 0, 0), ScmVar' (VarParam ("z", 0))));      ScmLambdaSimple'  (["z"],       ScmBoxSet'  (VarBound ("x", 0, 0), ScmVar' (VarParam ("z", 0))))])]));
            
            name = "RON_Test_Converted 55"};

{input = ScmDef (ScmVar "func", ScmLambdaOpt ([], "x",  ScmLambdaSimple (["samerib"],   ScmApplic (ScmVar "list",    [ScmLambdaSimple ([], ScmVar "x");     ScmLambdaSimple (["z"], ScmSet (ScmVar "x", ScmVar "z"))])))); expected =

 ScmDef'  (VarFree "func", ScmLambdaOpt'  ([], "x",  ScmLambdaSimple'  (["samerib"],   ScmApplicTP'  (ScmVar'  (VarFree "list"),    [ScmLambdaSimple'  ([], ScmVar'  (VarBound ("x", 1, 0)));     ScmLambdaSimple'  (["z"],      ScmSet'  (VarBound ("x", 1, 0), ScmVar'  (VarParam ("z", 0))))]))));name = "RON_Test_Converted 56"};





{input = ScmDef (ScmVar "x", ScmApplic (ScmVar "+",  [ScmConst (ScmNumber (ScmRational(61,1))); ScmConst (ScmNumber (ScmRational(61,1)))])); expected = 
ScmDef'  (VarFree "x", ScmApplic'  (ScmVar'  (VarFree "+"),  [ScmConst'  (ScmNumber (ScmRational(61,1))); ScmConst'  (ScmNumber (ScmRational(61,1)))]));name = "RON_Test_Converted 58"};

{input = ScmLambdaOpt (["x"], "y", ScmVar "x"); expected =  ScmLambdaOpt'  (["x"], "y", ScmVar'  (VarParam ("x", 0)));name = "RON_Test_Converted 59"};







{input = ScmApplic (ScmLambdaSimple (["x"],   ScmApplic (ScmLambdaSimple (["y"], ScmApplic (ScmVar "+", [ScmVar "x"; ScmVar "y"])),    [ScmApplic (ScmVar "g", [ScmVar "x"])])), [ScmApplic (ScmVar "f", [ScmVar "y"])]); expected = 
ScmApplic'  (ScmLambdaSimple'  (["x"],   ScmApplicTP'     (ScmLambdaSimple'  (["y"],      ScmApplicTP'  (ScmVar'  (VarFree "+"),       [ScmVar'  (VarBound ("x", 0, 0)); ScmVar'  (VarParam ("y", 0))])),    [ScmApplic'  (ScmVar'  (VarFree "g"), [ScmVar'  (VarParam ("x", 0))])])), [ScmApplic'  (ScmVar'  (VarFree "f"), [ScmVar'  (VarFree "y")])]);name = "RON_Test_Converted 60"};

{input = ScmLambdaSimple (["x"; "y"; "z"; "w"],  ScmIf (ScmApplic (ScmVar "foo?", [ScmVar "x"]), ScmApplic (ScmVar "goo", [ScmVar "y"]),   ScmApplic (ScmVar "boo", [ScmApplic (ScmVar "doo", [ScmVar "z"])]))); expected = ScmLambdaSimple'  (["x"; "y"; "z"; "w"], ScmIf'  (ScmApplic'  (ScmVar'  (VarFree "foo?"), [ScmVar'  (VarParam ("x", 0))]),  ScmApplicTP'  (ScmVar'  (VarFree "goo"), [ScmVar'  (VarParam ("y", 1))]),  ScmApplicTP'  (ScmVar'  (VarFree "boo"),   [ScmApplic'  (ScmVar'  (VarFree "doo"), [ScmVar'  (VarParam ("z", 2))])])));name = "RON_Test_Converted 61"};







{input = ScmLambdaSimple ([],  ScmIf (ScmApplic (ScmVar "f", [ScmVar "x"]),   ScmIf (ScmApplic (ScmVar "g", [ScmVar "y"]), ScmApplic (ScmVar "h", [ScmVar "z"]),    ScmConst (ScmBoolean false)),   ScmConst (ScmBoolean false))); expected = ScmLambdaSimple'  ([], ScmIf'  (ScmApplic'  (ScmVar'  (VarFree "f"), [ScmVar'  (VarFree "x")]),  ScmIf'  (ScmApplic'  (ScmVar'  (VarFree "g"), [ScmVar'  (VarFree "y")]),   ScmApplicTP'  (ScmVar'  (VarFree "h"), [ScmVar'  (VarFree "z")]),   ScmConst'  (ScmBoolean false)),  ScmConst'  (ScmBoolean false)));name = "RON_Test_Converted 63"};



{input = ScmLambdaSimple (["x"; "y"; "z"; "a"; "b"],  ScmApplic (ScmVar "f",   [ScmIf (ScmApplic (ScmVar "g?", [ScmVar "x"]),     ScmIf (ScmApplic (ScmVar "u003e", [ScmConst (ScmNumber (ScmRational(89,1))); ScmVar "a"]),      ScmApplic (ScmVar "h", [ScmVar "y"]), ScmVar "b"),     ScmApplic (ScmVar "w", [ScmVar "z"]))])); 

expected = ScmLambdaSimple'  (["x"; "y"; "z"; "a"; "b"], ScmApplicTP'  (ScmVar'  (VarFree "f"),  [ScmIf'  (ScmApplic'  (ScmVar'  (VarFree "g?"), [ScmVar'  (VarParam ("x", 0))]),    ScmIf'      (ScmApplic'  (ScmVar'  (VarFree "u003e"),       [ScmConst'  (ScmNumber (ScmRational(89,1))); ScmVar'  (VarParam ("a", 3))]),     ScmApplic'  (ScmVar'  (VarFree "h"), [ScmVar'  (VarParam ("y", 1))]),     ScmVar'  (VarParam ("b", 4))),    ScmApplic'  (ScmVar'  (VarFree "w"), [ScmVar'  (VarParam ("z", 2))]))]));name = "RON_Test_Converted 64"};




{input = ScmLambdaSimple (["x"; "y"; "z"; "a"; "b"],  ScmIf (ScmApplic (ScmVar "g?", [ScmVar "x"]),   ScmIf (ScmApplic (ScmVar "u003e", [ScmConst (ScmNumber (ScmRational(59,1))); ScmVar "a"]),    ScmApplic (ScmVar "h", [ScmVar "y"]), ScmApplic (ScmVar "w", [ScmVar "b"])),   ScmIf (ScmApplic (ScmVar "u003c", [ScmConst (ScmNumber (ScmRational(59,1))); ScmVar "a"]),    ScmApplic (ScmVar "w", [ScmVar "b"]), ScmApplic (ScmVar "w", [ScmVar "z"])))); 

expected = ScmLambdaSimple'  (["x"; "y"; "z"; "a"; "b"], ScmIf'  (ScmApplic'  (ScmVar'  (VarFree "g?"), [ScmVar'  (VarParam ("x", 0))]),  ScmIf'    (ScmApplic'  (ScmVar'  (VarFree "u003e"),     [ScmConst'  (ScmNumber (ScmRational(59,1))); ScmVar'  (VarParam ("a", 3))]),   ScmApplicTP'  (ScmVar'  (VarFree "h"), [ScmVar'  (VarParam ("y", 1))]),   ScmApplicTP'  (ScmVar'  (VarFree "w"), [ScmVar'  (VarParam ("b", 4))])),  ScmIf'    (ScmApplic'  (ScmVar'  (VarFree "u003c"),     [ScmConst'  (ScmNumber (ScmRational(59,1))); ScmVar'  (VarParam ("a", 3))]),   ScmApplicTP'  (ScmVar'  (VarFree "w"), [ScmVar'  (VarParam ("b", 4))]),   ScmApplicTP'  (ScmVar'  (VarFree "w"), [ScmVar'  (VarParam ("z", 2))]))));name = "RON_Test_Converted 65"};

{input = ScmLambdaSimple (["x"; "y"; "z"; "a"; "b"],  ScmIf (ScmOr [ScmApplic (ScmVar "f", [ScmApplic (ScmVar "g", [ScmVar "x"])]); ScmVar "y"],   ScmIf (ScmApplic (ScmVar "f", [ScmVar "x"]),    ScmIf (ScmApplic (ScmVar "g", [ScmVar "y"]), ScmApplic (ScmVar "h", [ScmVar "z"]),     ScmConst (ScmBoolean false)),    ScmConst (ScmBoolean false)),   ScmApplic (ScmVar "h", [ScmVar "z"]))); expected = ScmLambdaSimple'  (["x"; "y"; "z"; "a"; "b"], ScmIf'   (ScmOr'     [ScmApplic'  (ScmVar'  (VarFree "f"),      [ScmApplic'  (ScmVar'  (VarFree "g"), [ScmVar'  (VarParam ("x", 0))])]);     ScmVar'  (VarParam ("y", 1))],  ScmIf'  (ScmApplic'  (ScmVar'  (VarFree "f"), [ScmVar'  (VarParam ("x", 0))]),   ScmIf'  (ScmApplic'  (ScmVar'  (VarFree "g"), [ScmVar'  (VarParam ("y", 1))]),    ScmApplicTP'  (ScmVar'  (VarFree "h"), [ScmVar'  (VarParam ("z", 2))]),    ScmConst'  (ScmBoolean false)),   ScmConst'  (ScmBoolean false)),  ScmApplicTP'  (ScmVar'  (VarFree "h"), [ScmVar'  (VarParam ("z", 2))])));name = "RON_Test_Converted 66"};








{input = ScmApplic  (ScmLambdaSimple (["a"],    ScmApplic     (ScmLambdaSimple (["b"],       ScmApplic        (ScmLambdaSimple (["c"],          ScmApplic           (ScmLambdaSimple (["e"],             ScmIf              (ScmApplic (ScmVar "eq?", [ScmVar "a"; ScmConst (ScmNumber (ScmRational(27,1)))]),              ScmApplic (ScmVar "e", [ScmVar "a"; ScmVar "b"]),              ScmApplic (ScmVar "c", [ScmVar "a"; ScmVar "b"]))),           [ScmVar "f"])),        [ScmVar "d"])),     [ScmConst (ScmNumber (ScmRational(27,1)))])),  [ScmConst (ScmNumber (ScmRational(27,1)))]); 
expected = ScmApplic'  (ScmLambdaSimple'  (["a"],   ScmApplicTP'     (ScmLambdaSimple'  (["b"],      ScmApplicTP'        (ScmLambdaSimple'  (["c"],         ScmApplicTP'           (ScmLambdaSimple'  (["e"],            ScmIf'              (ScmApplic'  (ScmVar'  (VarFree "eq?"),               [ScmVar'  (VarBound ("a", 2, 0)); ScmConst'  (ScmNumber (ScmRational(27,1)))]),             ScmApplicTP'  (ScmVar'  (VarParam ("e", 0)),              [ScmVar'  (VarBound ("a", 2, 0)); ScmVar'  (VarBound ("b", 1, 0))]),             ScmApplicTP'  (ScmVar'  (VarBound ("c", 0, 0)),              [ScmVar'  (VarBound ("a", 2, 0)); ScmVar'  (VarBound ("b", 1, 0))]))),          [ScmVar'  (VarFree "f")])),       [ScmVar'  (VarFree "d")])),    [ScmConst'  (ScmNumber (ScmRational(27,1)))])), [ScmConst'  (ScmNumber (ScmRational(27,1)))]);name = "RON_Test_Converted 69"};



{input = ScmApplic  (ScmLambdaSimple (["a"],    ScmApplic     (ScmLambdaSimple (["c"],       ScmApplic        (ScmLambdaSimple (["e"],          ScmIf (ScmApplic (ScmVar "x", [ScmVar "u003e"; ScmConst (ScmNumber (ScmRational(115,1)))]),           ScmLambdaSimple (["x"], ScmApplic (ScmVar "a", [ScmVar "x"])),           ScmLambdaSimple (["x"], ScmApplic (ScmVar "c", [ScmVar "x"])))),        [ScmVar "f"])),     [ScmVar "d"])),  [ScmVar "b"]); expected = ScmApplic'  (ScmLambdaSimple'  (["a"],   ScmApplicTP'     (ScmLambdaSimple'  (["c"],      ScmApplicTP'        (ScmLambdaSimple'  (["e"],         ScmIf'           (ScmApplic'  (ScmVar'  (VarFree "x"),            [ScmVar'  (VarFree "u003e"); ScmConst'  (ScmNumber (ScmRational(115,1)))]),          ScmLambdaSimple'  (["x"],           ScmApplicTP'  (ScmVar'  (VarBound ("a", 2, 0)),            [ScmVar'  (VarParam ("x", 0))])),          ScmLambdaSimple'  (["x"],           ScmApplicTP'  (ScmVar'  (VarBound ("c", 1, 0)),            [ScmVar'  (VarParam ("x", 0))])))),       [ScmVar'  (VarFree "f")])),    [ScmVar'  (VarFree "d")])), [ScmVar'  (VarFree "b")]);name = "RON_Test_Converted 71"};




{input = ScmLambdaSimple (["x"],  ScmLambdaOpt (["x"], "y",   ScmIf (ScmApplic (ScmVar "x", [ScmVar "u003e"; ScmConst (ScmNumber (ScmRational(60,1)))]),    ScmLambdaSimple (["x"], ScmApplic (ScmVar "a", [ScmVar "x"])),    ScmLambdaSimple (["x"], ScmApplic (ScmVar "c", [ScmVar "x"]))))); 

expected = ScmLambdaSimple'  (["x"], ScmLambdaOpt'  (["x"], "y",  ScmIf'    (ScmApplic'  (ScmVar'  (VarParam ("x", 0)),     [ScmVar'  (VarFree "u003e"); ScmConst'  (ScmNumber (ScmRational(60,1)))]),   ScmLambdaSimple'  (["x"],    ScmApplicTP'  (ScmVar'  (VarFree "a"), [ScmVar'  (VarParam ("x", 0))])),   ScmLambdaSimple'  (["x"],    ScmApplicTP'  (ScmVar'  (VarFree "c"), [ScmVar'  (VarParam ("x", 0))])))));name = "RON_Test_Converted 72"};

{input = ScmLambdaSimple (["x"],  ScmLambdaOpt (["a"], "y",   ScmIf (ScmApplic (ScmVar "x", [ScmVar "u003e"; ScmConst (ScmNumber (ScmRational(62,1)))]),    ScmLambdaSimple (["x"], ScmApplic (ScmVar "a", [ScmVar "x"])),    ScmLambdaSimple (["x"], ScmApplic (ScmVar "c", [ScmVar "x"]))))); 

expected = ScmLambdaSimple'  (["x"], 
          ScmLambdaOpt'  (["a"], "y",  
            ScmIf'    
            (ScmApplic'  (ScmVar'  (VarBound ("x", 0, 0)), 
                [ScmVar'  (VarFree "u003e"); ScmConst'  (ScmNumber (ScmRational(62,1)))]),
                   ScmLambdaSimple'  (["x"], 
                      ScmApplicTP'  (ScmVar'  (VarBound ("a", 0, 0)), [ScmVar'  (VarParam ("x", 0))])),   
                      ScmLambdaSimple'  (["x"],
                       ScmApplicTP'  (ScmVar'  (VarFree "c"), [ScmVar'  (VarParam ("x", 0))])))));
                       name = "RON_Test_Converted 73"};

{input = ScmLambdaSimple (["a"],  ScmSeq   [ScmLambdaSimple ([],     ScmLambdaSimple (["x"; "y"; "z"],      ScmOr [ScmApplic (ScmVar "x", [ScmVar "y"]); ScmApplic (ScmVar "a", [ScmVar "z"])]));    ScmLambdaSimple (["x"], ScmApplic (ScmVar "a", [ScmVar "x"]))]); 

expected = ScmLambdaSimple'  (["a"], ScmSeq'   [ScmLambdaSimple'  ([],    ScmLambdaSimple'  (["x"; "y"; "z"],     ScmOr'       [ScmApplic'  (ScmVar'  (VarParam ("x", 0)), [ScmVar'  (VarParam ("y", 1))]);       ScmApplicTP'  (ScmVar'  (VarBound ("a", 1, 0)), [ScmVar'  (VarParam ("z", 2))])]));   ScmLambdaSimple'  (["x"],    ScmApplicTP'  (ScmVar'  (VarBound ("a", 0, 0)), [ScmVar'  (VarParam ("x", 0))]))]);name = "RON_Test_Converted 74"};


{input = ScmSeq  [ScmLambdaSimple (["x"; "y"],    ScmLambdaSimple (["y"; "z"], ScmApplic (ScmVar "x", [ScmVar "y"; ScmVar "z"])));   ScmLambdaSimple (["z"], ScmApplic (ScmVar "x", [ScmVar "y"; ScmVar "z"]))]; 
expected = ScmSeq'  [ScmLambdaSimple'  (["x"; "y"],   ScmLambdaSimple'  (["y"; "z"],    ScmApplicTP'  (ScmVar'  (VarBound ("x", 0, 0)),     [ScmVar'  (VarParam ("y", 0)); ScmVar'  (VarParam ("z", 1))])));  ScmLambdaSimple'  (["z"],   ScmApplicTP'  (ScmVar'  (VarFree "x"),    [ScmVar'  (VarFree "y"); ScmVar'  (VarParam ("z", 0))]))];name = "RON_Test_Converted 75"};





{input = ScmLambdaSimple (["x"],  ScmApplic (ScmVar "x",   [ScmLambdaSimple (["y"; "z"],     ScmApplic (ScmVar "x",      [ScmVar "y"; ScmVar "z";       ScmLambdaSimple ([],        ScmApplic (ScmVar "x",         [ScmVar "y"; ScmVar "z";          ScmLambdaSimple (["z"], ScmApplic (ScmVar "x", [ScmVar "y"; ScmVar "z"]))]))]))]));

 expected = ScmLambdaSimple'  (["x"], ScmApplicTP'  (ScmVar'  (VarParam ("x", 0)),  [ScmLambdaSimple'  (["y"; "z"],    ScmApplicTP'  (ScmVar'  (VarBound ("x", 0, 0)),     [ScmVar'  (VarParam ("y", 0)); ScmVar'  (VarParam ("z", 1));      ScmLambdaSimple'  ([],       ScmApplicTP'  (ScmVar'  (VarBound ("x", 1, 0)),        [ScmVar'  (VarBound ("y", 0, 0)); ScmVar'  (VarBound ("z", 0, 1));         ScmLambdaSimple'  (["z"],          ScmApplicTP'  (ScmVar'  (VarBound ("x", 2, 0)),           [ScmVar'  (VarBound ("y", 1, 0)); ScmVar'  (VarParam ("z", 0))]))]))]))]));name = "RON_Test_Converted 77"};
 
 
 

{input = ScmLambdaSimple (["x"],  ScmApplic (ScmVar "x",   [ScmLambdaSimple (["y"; "z"],     ScmApplic (ScmVar "x",      [ScmVar "y"; ScmVar "z";       ScmLambdaSimple ([],        ScmApplic (ScmVar "x",         [ScmVar "y"; ScmVar "z";          ScmLambdaSimple (["z"], ScmApplic (ScmVar "x", [ScmVar "y"; ScmVar "z"]))]))]));    ScmLambdaSimple (["x"],     ScmLambdaSimple (["y"; "z"], ScmApplic (ScmVar "x", [ScmVar "y"; ScmVar "z"])))])); 
expected = ScmLambdaSimple'  (["x"], ScmApplicTP'  (ScmVar'  (VarParam ("x", 0)),  [ScmLambdaSimple'  (["y"; "z"],    ScmApplicTP'  (ScmVar'  (VarBound ("x", 0, 0)),     [ScmVar'  (VarParam ("y", 0)); ScmVar'  (VarParam ("z", 1));      ScmLambdaSimple'  ([],       ScmApplicTP'  (ScmVar'  (VarBound ("x", 1, 0)),        [ScmVar'  (VarBound ("y", 0, 0)); ScmVar'  (VarBound ("z", 0, 1));         ScmLambdaSimple'  (["z"],          ScmApplicTP'  (ScmVar'  (VarBound ("x", 2, 0)),           [ScmVar'  (VarBound ("y", 1, 0)); ScmVar'  (VarParam ("z", 0))]))]))]));   ScmLambdaSimple'  (["x"],    ScmLambdaSimple'  (["y"; "z"],     ScmApplicTP'  (ScmVar'  (VarBound ("x", 0, 0)),      [ScmVar'  (VarParam ("y", 0)); ScmVar'  (VarParam ("z", 1))])))]));name = "RON_Test_Converted 78"};

{input = ScmLambdaSimple (["x"; "y"; "z"],  ScmSeq   [ScmApplic (ScmVar "x",     [ScmLambdaSimple (["x"],       ScmLambdaSimple (["y"],        ScmLambdaSimple (["z"], ScmApplic (ScmVar "x", [ScmVar "y"; ScmVar "z"]))))]);    ScmLambdaSimple ([], ScmApplic (ScmVar "z", []))]); expected = ScmLambdaSimple'  (["x"; "y"; "z"], ScmSeq'   [ScmApplic'  (ScmVar'  (VarParam ("x", 0)),    [ScmLambdaSimple'  (["x"],      ScmLambdaSimple'  (["y"],       ScmLambdaSimple'  (["z"],        ScmApplicTP'  (ScmVar'  (VarBound ("x", 1, 0)),         [ScmVar'  (VarBound ("y", 0, 0)); ScmVar'  (VarParam ("z", 0))]))))]);   ScmLambdaSimple'  ([], ScmApplicTP'  (ScmVar'  (VarBound ("z", 0, 2)), []))]);name = "RON_Test_Converted 79"};


{input = ScmLambdaSimple (["x"],  ScmApplic (ScmVar "eq?",   [ScmLambdaSimple (["x"], ScmApplic (ScmVar "x", []));    ScmLambdaSimple ([], ScmLambdaSimple (["x"], ScmApplic (ScmVar "x", [])))]));
 expected = ScmLambdaSimple'  (["x"], ScmApplicTP'  (ScmVar'  (VarFree "eq?"),  [ScmLambdaSimple'  (["x"], ScmApplicTP'  (ScmVar'  (VarParam ("x", 0)), []));   ScmLambdaSimple'  ([],    ScmLambdaSimple'  (["x"], ScmApplicTP'  (ScmVar'  (VarParam ("x", 0)), [])))]));name = "RON_Test_Converted 80"};

{input = ScmLambdaSimple (["x"],  ScmLambdaSimple ([],   ScmSeq    [ScmApplic (ScmLambdaSimple (["x"], ScmApplic (ScmVar "x", [])), [ScmVar "x"]);     ScmLambdaSimple ([], ScmLambdaSimple ([], ScmApplic (ScmVar "x", [])))])); 
expected = ScmLambdaSimple'  (["x"],
            ScmLambdaSimple'  ([],
              ScmSeq'
                  [ScmApplic'
                    (ScmLambdaSimple'  (["x"], ScmApplicTP'  (ScmVar'  (VarParam ("x", 0)), [])),
                         [ScmVar'  (VarBound ("x", 0, 0))]);
                             ScmLambdaSimple'  ([],
                                  ScmLambdaSimple'  ([], ScmApplicTP'  (ScmVar'  (VarBound ("x", 2, 0)), [])))]));name = "RON_Test_Converted 81"};








 

];;




let test_case case =
try
let actual = Semantic_Analysis.run_semantics case.input in
if (expr'_eq actual case.expected) then "PASS" else "FAILURE"
with
| X_syntax_error(s, msg) -> Printf.sprintf "Exception: Syntax Error message: %s for sexpr: %s" msg (string_of_sexpr s)
| X_reserved_word(s) -> Printf.sprintf "Exception: Reserved Word: %s" s
| X_not_implemented -> Printf.sprintf "Exception: Syntax not yet implemented"
| _ -> "Unknown Failure"


let test_cases cases =
let names, results =  (List.map (fun case -> case.name) cases),(List.map test_case cases) in
List.map2 (fun name result -> Printf.sprintf "%s: %s" result name) names results;;

List.map (Printf.printf "%s\n") (test_cases cases);;
