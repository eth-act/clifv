import FVTest.Opt.MidValDivWitness
import FV.Opt.Proof.MidValPhi

/-! # The validator's constant-phi removal: witnesses (#1119, removed block parameters)

`ConstPhi.run` (what `lean-backend` compiles) keeps every parameter of a function with a
`try_call` when removing them would lower its fresh value, and Cranelift removes them; the
validator compared such pairs block by block and rejected them (`shape:params`, `jump arity`).
`phiPre` (`FV/Opt/MidValFold.lean`, inside `foldPre`) applies `ConstPhi`'s solution without that
condition (`phiOk`); `check_soundC` composes the check with `foldPre_simU`, through
`phiPre_simU` (`FV/Opt/Proof/MidValPhi.lean`).

* Hand-made: a `try_call` function whose `block3(v3)` only receives `v0`: `ConstPhi.run` keeps
  the parameter (`v3` is the largest value), `phiPre` removes it (`try_params`); the pair
  against Cranelift's `g` is accepted (`pos_try`), and rejected without the prep
  (`pos_try_c0_rejects`).
* Negative: a parameter receiving two different values is not removed (`two_phiPre`), `phiOk`
  rejects the solution naming one of them (`two_phiOk_wrong`), and the pair against a `g` that
  returns that value instead is rejected (`neg_two`) and no simulation (`two_not_sim`), so every
  certificate with every hint list is rejected (`two_rejected`).
* Real pairs (crypto-bigint 0.7.11 and serde_json 1.0.154 test builds, `FVTest/Opt/midval/real_phi_*.clif`),
  each a function with `try_call`s whose parameters `ConstPhi.run` keeps, rejected before
  (`checkC0`) and accepted by `checkCertC` with the requests `emitC` gives (decided), with the
  simulation and the program refinement: `bigint` (num_bigint, `block5(v43)`), `dissimilar`
  (`block3(v7, v58)`), `criterion` (`block3(v55, v57)`).
-/

namespace Opt.MidVal.PhiWitness

open Clif Pairs NormWitness CondWitness FoldWitness

/-! ## Hand-made pairs -/

def tryF : String := "function %f(i64) -> i64 system_v {
    sig0 = (i64) -> i64 system_v
    fn0 = %g(i64) -> i64 system_v
block0(v0: i64):
    try_call fn0(v0), sig0, block1(ret0), [ tag0: block2(exn0) ]
block1(v1: i64):
    jump block3(v0)
block2(v2: i64) cold:
    return v2
block3(v3: i64):
    return v3
}"

def tryG : String := "function %f(i64) -> i64 system_v {
    sig0 = (i64) -> i64 system_v
    fn0 = %g(i64) -> i64 system_v
block0(v0: i64):
    try_call fn0(v0), sig0, block1(ret0), [ tag0: block2(exn0) ]
block1(v1: i64):
    jump block3
block2(v2: i64) cold:
    return v2
block3:
    return v0
}"

/-- `ConstPhi.run` keeps `block3`'s parameter, `phiPre` removes it. -/
theorem try_params : (fn? tryF).map (fun f => ((ConstPhi.run f).blocks.map (·.params.length),
    (phiPre (ConstPhi.run f)).blocks.map (·.params.length))) = some ([1, 1, 1, 1], [1, 1, 1, 0]) := by
  native_decide

theorem pos_try : acceptsC tryF tryG = some true := by native_decide
theorem pos_try_c0_rejects : acceptsC0 tryF tryG = some false := by native_decide

/-! ## Negative pairs -/

def twoF : String := "function %f(i32, i32) -> i32 {
block0(v0: i32, v1: i32):
    brif v0, block1, block2
block1:
    jump block3(v0)
block2:
    jump block3(v1)
block3(v2: i32):
    return v2
}"

def wrongG : String := "function %f(i32, i32) -> i32 {
block0(v0: i32, v1: i32):
    brif v0, block1, block2
block1:
    jump block3
block2:
    jump block3
block3:
    return v0
}"

/-- `f`: `block3(v2)` receives `v0` from `block1` and `v1` from `block2`; `g` (`ret = some r`):
`block3` returns `r`. -/
def fnTwo (ret : Option ValueId) : Function :=
  { name := "f", sig := { params := [ap .i32, ap .i32], returns := [ap .i32], callConv := none },
    blocks := [
      { id := 0, params := [(0, .i32), (1, .i32)], cold := false, body := [],
        term := .brif 0 ⟨1, []⟩ ⟨2, []⟩ },
      { id := 1, params := [], cold := false, body := [],
        term := .jump ⟨3, if ret.isSome then [] else [0]⟩ },
      { id := 2, params := [], cold := false, body := [],
        term := .jump ⟨3, if ret.isSome then [] else [1]⟩ },
      { id := 3, params := if ret.isSome then [] else [(2, .i32)], cold := false, body := [],
        term := .ret [ret.getD 2] }] }

def twoFn : Function := fnTwo none
def wrongFn : Function := fnTwo (some 0)

theorem twoF_text : fn? twoF = some twoFn := by native_decide
theorem wrongG_text : fn? wrongG = some wrongFn := by native_decide

/-- Two different values: nothing to remove. -/
theorem two_phiPre : phiPre twoFn = twoFn := by native_decide

/-- The solution `v2 := v0` is rejected (`block2` passes `v1`). -/
theorem two_phiOk_wrong : phiOk twoFn [(2, 0)] = false := by native_decide

theorem neg_two : acceptsC twoF wrongG = some false := by native_decide

/-- For `v0 = 0, v1 = 5`, `f` returns 5 and `g` 0. -/
theorem two_not_sim : ¬ FunSimMU twoFn wrongFn :=
  not_funSimMU_ret_ne (b := twoFn.blocks.head!) (b' := wrongFn.blocks.head!)
    (args := [⟨.i32, 0⟩, ⟨.i32, 5⟩]) (regs := (Regs.empty.set 0 ⟨.i32, 0⟩).set 1 ⟨.i32, 5⟩)
    (m := Mem.empty) (vals := [⟨.i32, 5⟩]) (vals' := [⟨.i32, 0⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.refl _ _))) rfl
    (.step rfl (.step rfl (.refl _ _))) rfl (by decide)

/-- The re-check rejects every certificate and every hint list (prep requests included). -/
theorem two_rejected (cert : Cert) (hints : List (BlockId × List Wrap)) :
    checkCertC (ConstPhi.run twoFn) wrongFn cert hints = false := by
  cases h : checkCertC (ConstPhi.run twoFn) wrongFn cert hints
  · rfl
  · exact absurd (checkedC_simMU h) two_not_sim

/-! ## Real pairs -/

def bigintF : String := include_str "midval/real_phi_bigint.unopt.clif"
def bigintG : String := include_str "midval/real_phi_bigint.opt.clif"
def dissimilarF : String := include_str "midval/real_phi_dissimilar.unopt.clif"
def dissimilarG : String := include_str "midval/real_phi_dissimilar.opt.clif"
def criterionF : String := include_str "midval/real_phi_criterion.unopt.clif"
def criterionG : String := include_str "midval/real_phi_criterion.opt.clif"

theorem real_bigint_c0_rejects : c0Verdict bigintF bigintG = some false := by native_decide
theorem real_bigint_checked : checkedC bigintF bigintG = some (true, true) := by native_decide
theorem real_bigint_sim : SimRefinesC bigintF bigintG := simC_of_checked real_bigint_checked

theorem real_dissimilar_c0_rejects : c0Verdict dissimilarF dissimilarG = some false := by
  native_decide
theorem real_dissimilar_checked : checkedC dissimilarF dissimilarG = some (true, true) := by
  native_decide
theorem real_dissimilar_sim : SimRefinesC dissimilarF dissimilarG :=
  simC_of_checked real_dissimilar_checked

theorem real_criterion_c0_rejects : c0Verdict criterionF criterionG = some false := by
  native_decide
theorem real_criterion_checked : checkedC criterionF criterionG = some (true, true) := by
  native_decide
theorem real_criterion_sim : SimRefinesC criterionF criterionG :=
  simC_of_checked real_criterion_checked

end Opt.MidVal.PhiWitness
