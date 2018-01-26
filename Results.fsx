
(*
Fail results from FCS tests (x10)
*)

let matching (expected:seq<'T>) (actual:seq<'T>) =
    let mutable matched = 0  
    let expLen = Seq.length expected
    let actLen = Seq.length actual
    let mutable result = true
    if expLen <> actLen then
        printfn "Error, expected len: %i while actual len %i " expLen actLen
        result <- result && false
    for ex in expected do
        let mutable found = false
        for ac in actual do
            if ex = ac then
                found <- true
                matched <- matched + 1
        if not found then
            printfn "NOT_FOUND: %A" ex
        result <- result && found 
    if matched < actLen then
        printfn "Error, matched: %i of %i items" matched actLen
    result

/// test 1 matches although ordering causing failure
let expected = [("N", "file2", (2, 7), (2, 8), ["module"]);
 ("val y2", "file2", (13, 4), (13, 6), ["val"]);
 ("val pair2", "file2", (24, 10), (24, 15), ["val"]);
 ("val pair1", "file2", (24, 4), (24, 9), ["val"]);
 ("val enumValue", "file2", (31, 4), (31, 13), ["val"]);
 ("val op_PlusPlus", "file2", (33, 5), (33, 7), ["val"]);
 ("val c1", "file2", (35, 4), (35, 6), ["val"]);
 ("val c2", "file2", (37, 4), (37, 6), ["val"]);
 ("val mmmm1", "file2", (39, 4), (39, 9), ["val"]);
 ("val mmmm2", "file2", (40, 4), (40, 9), ["val"]);
 ("D1", "file2", (6, 5), (6, 7), ["class"]);
 ("member .ctor", "file2", (6, 5), (6, 7), ["member"; "ctor"]);
 ("member get_SomeProperty", "file2", (7, 13), (7, 25), ["member"; "getter"]);
 ("property SomeProperty", "file2", (7, 13), (7, 25), ["member"; "prop"]);
 ("D2", "file2", (9, 5), (9, 7), ["class"]);
 ("member .ctor", "file2", (9, 5), (9, 7), ["member"; "ctor"]);
 ("member get_SomeProperty", "file2", (10, 13), (10, 25), ["member"; "getter"]);
 ("property SomeProperty", "file2", (10, 13), (10, 25), ["member"; "prop"]);
 ("D3", "file2", (16, 5), (16, 7), ["class"]);
 ("member .ctor", "file2", (16, 5), (16, 7), ["member"; "ctor"]);
 ("member get_SomeProperty", "file2", (22, 13), (22, 25), ["member"; "getter"]);
 ("property SomeProperty", "file2", (22, 13), (22, 25), ["member"; "prop"]);
 ("field a", "file2", (16, 8), (16, 9), ["field"; "compgen"]);
 ("field b", "file2", (17, 8), (17, 9), ["field"; "compgen"]);
 ("field x", "file2", (20, 16), (20, 17), ["field"; "default"; "mutable"]);
 ("SaveOptions", "file2", (27, 5), (27, 16), ["enum"; "valuetype"]);
 ("field value__", "file2", (28, 2), (29, 25), ["field"; "compgen"]);
 ("field None", "file2", (28, 4), (28, 8), ["field"; "static"; "0"]);
 ("field DisableFormatting", "file2", (29, 4), (29, 21),
  ["field"; "static"; "1"]); ("M", "file1", (2, 7), (2, 8), ["module"]);
 ("val xxx", "file1", (7, 4), (7, 7), ["val"]);
 ("val fff", "file1", (8, 4), (8, 7), ["val"]);
 ("C", "file1", (4, 5), (4, 6), ["class"]);
 ("member .ctor", "file1", (4, 5), (4, 6), ["member"; "ctor"]);
 ("member get_P", "file1", (5, 13), (5, 14), ["member"; "getter"]);
 ("property P", "file1", (5, 13), (5, 14), ["member"; "prop"]);
 ("CAbbrev", "file1", (10, 5), (10, 12), ["abbrev"]);
 ("property P", "file1", (5, 13), (5, 14), ["member"; "prop"])]

let actual = [("N", "file2", (2, 7), (2, 8), ["module"]);
 ("val y2", "file2", (13, 4), (13, 6), ["val"]);
 ("val pair1", "file2", (24, 4), (24, 9), ["val"]);
 ("val pair2", "file2", (24, 10), (24, 15), ["val"]);
 ("val enumValue", "file2", (31, 4), (31, 13), ["val"]);
 ("val op_PlusPlus", "file2", (33, 5), (33, 7), ["val"]);
 ("val c1", "file2", (35, 4), (35, 6), ["val"]);
 ("val c2", "file2", (37, 4), (37, 6), ["val"]);
 ("val mmmm1", "file2", (39, 4), (39, 9), ["val"]);
 ("val mmmm2", "file2", (40, 4), (40, 9), ["val"]);
 ("D1", "file2", (6, 5), (6, 7), ["class"]);
 ("member .ctor", "file2", (6, 5), (6, 7), ["member"; "ctor"]);
 ("member get_SomeProperty", "file2", (7, 13), (7, 25), ["member"; "getter"]);
 ("property SomeProperty", "file2", (7, 13), (7, 25), ["member"; "prop"]);
 ("D2", "file2", (9, 5), (9, 7), ["class"]);
 ("member .ctor", "file2", (9, 5), (9, 7), ["member"; "ctor"]);
 ("member get_SomeProperty", "file2", (10, 13), (10, 25), ["member"; "getter"]);
 ("property SomeProperty", "file2", (10, 13), (10, 25), ["member"; "prop"]);
 ("D3", "file2", (16, 5), (16, 7), ["class"]);
 ("member .ctor", "file2", (16, 5), (16, 7), ["member"; "ctor"]);
 ("member get_SomeProperty", "file2", (22, 13), (22, 25), ["member"; "getter"]);
 ("property SomeProperty", "file2", (22, 13), (22, 25), ["member"; "prop"]);
 ("field a", "file2", (16, 8), (16, 9), ["field"; "compgen"]);
 ("field b", "file2", (17, 8), (17, 9), ["field"; "compgen"]);
 ("field x", "file2", (20, 16), (20, 17), ["field"; "default"; "mutable"]);
 ("SaveOptions", "file2", (27, 5), (27, 16), ["enum"; "valuetype"]);
 ("field value__", "file2", (28, 2), (29, 25), ["field"; "compgen"]);
 ("field None", "file2", (28, 4), (28, 8), ["field"; "static"; "0"]);
 ("field DisableFormatting", "file2", (29, 4), (29, 21),
  ["field"; "static"; "1"]); ("M", "file1", (2, 7), (2, 8), ["module"]);
 ("val xxx", "file1", (7, 4), (7, 7), ["val"]);
 ("val fff", "file1", (8, 4), (8, 7), ["val"]);
 ("C", "file1", (4, 5), (4, 6), ["class"]);
 ("member .ctor", "file1", (4, 5), (4, 6), ["member"; "ctor"]);
 ("member get_P", "file1", (5, 13), (5, 14), ["member"; "getter"]);
 ("property P", "file1", (5, 13), (5, 14), ["member"; "prop"]);
 ("CAbbrev", "file1", (10, 5), (10, 12), ["abbrev"]);
 ("property P", "file1", (5, 13), (5, 14), ["member"; "prop"])]

matching actual expected

// 2) pass
let expexted2 = ["N"; "val y2"; "val pair2"; "val pair1"; "val enumValue"; "val op_PlusPlus";
 "val c1"; "val c2"; "val mmmm1"; "val mmmm2"; "D1"; "member .ctor";
 "member get_SomeProperty"; "property SomeProperty"; "D2"; "member .ctor";
 "member get_SomeProperty"; "property SomeProperty"; "D3"; "member .ctor";
 "member get_SomeProperty"; "property SomeProperty"; "field x"; "SaveOptions";
 "field None"; "field DisableFormatting"; "M"; "val xxx"; "val fff"; "C";
 "member .ctor"; "member get_P"; "property P"; "CAbbrev"; "property P"]

let actual2 = ["N"; "val y2"; "val pair1"; "val pair2"; "val enumValue"; "val op_PlusPlus";
 "val c1"; "val c2"; "val mmmm1"; "val mmmm2"; "D1"; "member .ctor";
 "member get_SomeProperty"; "property SomeProperty"; "D2"; "member .ctor";
 "member get_SomeProperty"; "property SomeProperty"; "D3"; "member .ctor";
 "member get_SomeProperty"; "property SomeProperty"; "field x"; "SaveOptions";
 "field None"; "field DisableFormatting"; "M"; "val xxx"; "val fff"; "C";
 "member .ctor"; "member get_P"; "property P"; "CAbbrev"; "property P"]

matching expexted2 actual2

// 3) Error, expected len: 20 while actual len 15
(*
    NOT_FOUND: ("val arg1", "arg1", "file1", ((12, 31), (12, 35)), ["defn"], [])
    NOT_FOUND: ("unit", "unit", "file1", ((12, 43), (12, 47)), ["type"], ["abbrev"])
    NOT_FOUND: ("val raise", "raise", "file1", ((13, 18), (13, 23)), [], ["val"])
    NOT_FOUND: ("System", "System", "file1", ((13, 25), (13, 31)), [], ["namespace"])
    NOT_FOUND: ("member .ctor", ".ctor", "file1", ((13, 25), (13, 55)), [], ["member"])
    val it : bool = false
*)
let expected3 = [|("generic parameter a", "a", "file1", ((4, 18), (4, 20)), ["type"], []);
  ("generic parameter a", "a", "file1", ((5, 22), (5, 24)), ["type"], []);
  ("unit", "unit", "file1", ((5, 28), (5, 32)), ["type"], ["abbrev"]);
  ("member Method1", "Method1", "file1", ((5, 13), (5, 20)), ["defn"],
   ["slot"; "member"]);
  ("generic parameter a", "a", "file1", ((6, 22), (6, 24)), ["type"], []);
  ("unit", "unit", "file1", ((6, 28), (6, 32)), ["type"], ["abbrev"]);
  ("member Method2", "Method2", "file1", ((6, 13), (6, 20)), ["defn"],
   ["slot"; "member"]);
  ("IMyInterface`1", "IMyInterface", "file1", ((4, 5), (4, 17)), ["defn"],
   ["interface"]);
  ("IMyInterface`1", "IMyInterface", "file1", ((8, 14), (8, 26)), ["type"],
   ["interface"]);
  ("int", "int", "file1", ((8, 27), (8, 30)), ["type"], ["abbrev"]);
  ("val x", "x", "file1", ((9, 21), (9, 22)), ["defn"], []);
  ("string", "string", "file1", ((9, 37), (9, 43)), ["type"], ["abbrev"]);
  ("val x", "x", "file1", ((12, 21), (12, 22)), ["defn"], []);
  ("int", "int", "file1", ((12, 37), (12, 40)), ["type"], ["abbrev"]);
  ("val arg1", "arg1", "file1", ((12, 31), (12, 35)), ["defn"], []);
  ("unit", "unit", "file1", ((12, 43), (12, 47)), ["type"], ["abbrev"]);
  ("val raise", "raise", "file1", ((13, 18), (13, 23)), [], ["val"]);
  ("System", "System", "file1", ((13, 25), (13, 31)), [], ["namespace"]);
  ("member .ctor", ".ctor", "file1", ((13, 25), (13, 55)), [], ["member"]);
  ("Impl", "Impl", "file1", ((2, 7), (2, 11)), ["defn"], ["module"])|]
let actual3 = [|("generic parameter a", "a", "file1", ((4, 18), (4, 20)), ["type"], []);
  ("generic parameter a", "a", "file1", ((5, 22), (5, 24)), ["type"], []);
  ("unit", "unit", "file1", ((5, 28), (5, 32)), ["type"], ["abbrev"]);
  ("member Method1", "Method1", "file1", ((5, 13), (5, 20)), ["defn"],
   ["slot"; "member"]);
  ("generic parameter a", "a", "file1", ((6, 22), (6, 24)), ["type"], []);
  ("unit", "unit", "file1", ((6, 28), (6, 32)), ["type"], ["abbrev"]);
  ("member Method2", "Method2", "file1", ((6, 13), (6, 20)), ["defn"],
   ["slot"; "member"]);
  ("IMyInterface`1", "IMyInterface", "file1", ((4, 5), (4, 17)), ["defn"],
   ["interface"]);
  ("IMyInterface`1", "IMyInterface", "file1", ((8, 14), (8, 26)), ["type"],
   ["interface"]);
  ("int", "int", "file1", ((8, 27), (8, 30)), ["type"], ["abbrev"]);
  ("val x", "x", "file1", ((9, 21), (9, 22)), ["defn"], []);
  ("string", "string", "file1", ((9, 37), (9, 43)), ["type"], ["abbrev"]);
  ("val x", "x", "file1", ((12, 21), (12, 22)), ["defn"], []);
  ("int", "int", "file1", ((12, 37), (12, 40)), ["type"], ["abbrev"]);
  ("Impl", "Impl", "file1", ((2, 7), (2, 11)), ["defn"], ["module"])|]

matching expected3 actual3