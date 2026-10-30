import FVTest.E2E.FloatLinkT
import FV.E2E.LinkScopeInputT2

/-!
Non-vacuity of the strengthened typed input scope `fnScopeInTB2` (S11 slice 8), and the two
counterexamples that make its typing checks necessary:

* `fW` (`FloatFinalT`: float load/const/select/store/bitcast) is in `fnScopeInTB2`; the subset-E
  `fInt` is in it by the integer inclusion `fnScopeInTB2_of_fnScopeInB`;
* `fEntry` (signature `(f64, i64)`, entry block `(v0: i64, v1: i64)`) passes every conjunct of
  `fnScopeInTB` except the run-time `ctlSpillB`, and fails `entryClassOkB`;
* `fSel` (`fW` with `select.f64 v1, v0, v3`, `v0 : i64`) passes every conjunct of `fnScopeInTB`
  except the run-time `formsCoveredB`, and fails `selectTypedB`.

Checks by `native_decide`/`#guard` (witness only). `lake build FVTest.E2E.FloatScopeT2`.
-/

open Backend Backend.Proof Backend.Proof.Driver E2E E2E.LinkCheck

namespace FloatScopeT2

open FloatDriverT FloatFinalT FloatLinkT

/-- Entry block parameters of the other class than the signature's. -/
def fEntry : Clif.Function := fnOfText
  "function %e(f64, i64) -> i64 {
block0(v0: i64, v1: i64):
    return v0
}
"

/-- `fW` with its float `select` selecting the integer parameter `v0`. -/
def fSel : Clif.Function :=
  { fW with blocks := fW.blocks.map fun b => { b with body := b.body.map fun s =>
      match s.inst with
      | .select ty c _ y => { s with inst := .select ty c 0 y }
      | _ => s } }

#guard fSel.blocks.any fun b => b.body.any fun s => s.inst matches .select .f64 _ 0 _

#guard fnScopeInFailsT fEntry == ["ctlSpillB"] && !entryClassOkB fEntry &&
  fnScopeInFailsT2 fEntry == ["ctlSpillB", "entryClassOkB"]
#guard fnScopeInFailsT fSel == ["formsCoveredB"] && !Compile.selectTypedB fSel &&
  fnScopeInFailsT2 fSel == ["formsCoveredB", "selectTypedB"]
#guard fnScopeInFailsT2 fW == [] && fnScopeInFailsT2 fInt == []

theorem fnScopeInTB2_w : fnScopeInTB2 fW = true := by native_decide
theorem fnScopeInTB2_int : fnScopeInTB2 fInt = true :=
  fnScopeInTB2_of_fnScopeInB (by native_decide)
theorem not_entry : fnScopeInTB2 fEntry = false := by native_decide
theorem not_sel : fnScopeInTB2 fSel = false := by native_decide

/-- **Witness**: `fW`'s `fnScopeInTB` from `fnScopeInTB2`. -/
theorem fnScopeInTB_w2 : fnScopeInTB fW = true := fnScopeInTB_of_T2 fnScopeInTB2_w

end FloatScopeT2
