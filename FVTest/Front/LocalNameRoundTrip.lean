import FV.Front.Bundle

/-! # #1163: the linked name of a local symbol parses back

A unit's local symbol that the object merge left local is named `sym@tag` in the bundle's linked
program (`Front.PCgu.fin`). It happens for a data object that only code `Opt.ConstPhi` removed
uses: once_cell's `imp::{impl#4}::initialize::{closure#0}` branches on a constant compare, the
Lean code does not reach its two panic paths, so the merge does not rename their messages
`.Ldata10`, `.Ldata11`. The renamed function's printed CLIF then held `%.Ldata10@b7f1e7e76b13`,
which the lexer read as the name `` (it stopped at `.`), so `Front.mkInput` rejected the function
and link-check stopped the whole executable before its binary check. `Parse.lexLine` reads `.`,
`$`, `@` in a `%name` now.
-/

namespace LocalNameRoundTrip

open Clif Front

/-- The shape of the once_cell function, minimised: a constant compare, a panic path that alone
uses two data objects. -/
def src : String := "function %f(i64) -> i8 uext system_v {
    gv0 = symbol colocated %c_Ldatae
    gv1 = symbol colocated %c_Ldata10
    gv2 = symbol colocated %c_Ldata11+16
    sig0 = (i64, i64) system_v
    fn0 = %panic(i64, i64) system_v

block0(v0: i64):
    v1 = iconst.i64 0
    v2 = iconst.i64 4294967295
    v3 = icmp.i64 ugt v1, v2
    brif.i8 v3, block1, block2

block1 cold:
    v4 = symbol_value.i64 gv1
    v5 = symbol_value.i64 gv2
    call fn0(v4, v5)
    trap user1

block2:
    v6 = symbol_value.i64 gv0
    v7 = iconst.i8 0
    return v7
}
"

/-- The first function of `src`, parsed. -/
def parsed : Option (Except ParseError Function) :=
  (parseFile src).funcs.head?.map ParsedFunction.func

/-- The function as parsed. -/
def f : Function := match parsed with
  | some (.ok g) => g
  | _ => default

/-- The linked names: `c_Ldatae` renamed by the merge, the other two local symbols left local. -/
def fin (n : String) : String :=
  if n == "c_Ldatae" then "__fv_b7f1e7e76b13_Ldatae"
  else if n == "c_Ldata10" then ".Ldata10@b7f1e7e76b13"
  else if n == "c_Ldata11" then ".Ldata11@b7f1e7e76b13"
  else n

#guard parsed matches some (.ok _)

-- the renamed function's printed CLIF parses back to it
#guard (mkInput [] (f.rename fin) "") matches .ok _
#guard match mkInput [] (f.rename fin) "" with
  | .ok fi => (fi.clif.splitOn "%.Ldata10@b7f1e7e76b13\n").length == 2 &&
      (fi.clif.splitOn "%.Ldata11@b7f1e7e76b13+16\n").length == 2
  | .error _ => false

-- a name stops at the characters that follow one in Cranelift's syntax
#guard (Parse.lexLine "fn0 = %a.b@c$d(i64) system_v".toList #[]).1.toList.take 4 ==
  [.word "fn0", .punct '=', .name "a.b@c$d", .punct '(']
#guard (Parse.lexLine "gv0 = symbol %.L1@t-8, %x+2".toList #[]).1.toList.drop 3 ==
  [.name ".L1@t", .int "-8", .punct ',', .name "x", .int "+2"]

end LocalNameRoundTrip
