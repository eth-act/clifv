import FVTest.Opt.MidValPhiWitness
import FV.Opt.Proof.MidValPhiM

/-! # Constant-phi removal in a function with a `call_indirect`: witnesses (#1119)

`phiOk` starts with `Opt.check`, which rejects every function with a `call_indirect`
(`Opt.Wf.noCI`), so `phiPre` left the parameters Cranelift removes in such functions, and the
pair was rejected (`shape:params`, `jump arity`). `phiOkM` (`FV/Opt/MidValFold.lean`) is `phiOk`
with the validator's `wfCheck`; `phiPre_simU` goes through `phiOkM_simU`
(`FV/Opt/Proof/MidValPhiM.lean`).

* Hand-made: `block1(v2)` only receives the result of a `call_indirect`: `phiOk` rejects the
  solution (`ci_phiOk`), `phiOkM` accepts it (`ci_phiOkM`), `phiPre` removes the parameter
  (`ci_params`); the pair against Cranelift's `g` is accepted (`pos_ci`) and rejected without
  the prep (`pos_ci_c0_rejects`).
* Negative: in a function with a `call_indirect`, a parameter receiving two different values is
  not removed (`twoM_phiPre`), `phiOkM` rejects the solution naming one of them
  (`twoM_phiOkM_wrong`), and the pair against a `g` that returns the other value is rejected
  (`neg_twoM`) and no simulation (`twoM_not_sim`), so every certificate with every hint list is
  rejected (`twoM_rejected`).
* Real pairs (`FVTest/Opt/midval/real_phim_*.clif`: crypto-bigint 0.7.11's proptest, serde_json
  1.0.154's toml_parser, memchr 2.8.3's test build), each a function with a `call_indirect` whose
  removed parameters `phiOk` kept, rejected before (`checkC0`) and accepted by `checkCertC` with
  the requests `emitC` gives (decided), with the simulation and the program refinement.
-/

namespace Opt.MidVal.PhiMWitness

open Clif Pairs NormWitness CondWitness FoldWitness PhiWitness

/-! ## Hand-made pair -/

def ciF : String := "function %f(i64) -> i32 {
    sig0 = () -> i32
block0(v0: i64):
    v1 = call_indirect sig0, v0()
    jump block1(v1)
block1(v2: i32):
    return v2
}"

def ciG : String := "function %f(i64) -> i32 {
    sig0 = () -> i32
block0(v0: i64):
    v1 = call_indirect sig0, v0()
    jump block1
block1:
    return v1
}"

/-- `Opt.check` rejects the function (`call_indirect`), so `phiOk` rejects the solution. -/
theorem ci_phiOk : (fn? ciF).map (fun f => phiOk f (ConstPhi.solve f)) = some false := by
  native_decide

/-- `wfCheck` accepts it, and `phiOkM` the solution `v2 := v1`. -/
theorem ci_phiOkM : (fn? ciF).map (fun f => (ConstPhi.solve f, phiOkM f (ConstPhi.solve f))) =
    some ([(2, 1)], true) := by
  native_decide

/-- `ConstPhi.run` keeps `block1`'s parameter, `phiPre` removes it. -/
theorem ci_params : (fn? ciF).map (fun f => ((ConstPhi.run f).blocks.map (·.params.length),
    (phiPre (ConstPhi.run f)).blocks.map (·.params.length))) = some ([1, 1], [1, 0]) := by
  native_decide

theorem pos_ci : acceptsC ciF ciG = some true := by native_decide
theorem pos_ci_c0_rejects : acceptsC0 ciF ciG = some false := by native_decide

/-! ## Negative pair -/

def twoMF : String := "function %f(i32, i32, i64) -> i32 {
    sig0 = () -> i32
block0(v0: i32, v1: i32, v2: i64):
    brif v0, block1, block2
block1:
    jump block3(v0)
block2:
    v4 = call_indirect sig0, v2()
    jump block3(v1)
block3(v3: i32):
    return v3
}"

def wrongMG : String := "function %f(i32, i32, i64) -> i32 {
    sig0 = () -> i32
block0(v0: i32, v1: i32, v2: i64):
    brif v0, block1, block2
block1:
    jump block3
block2:
    v4 = call_indirect sig0, v2()
    jump block3
block3:
    return v1
}"

/-- `f`: `block3(v3)` receives `v0` from `block1` and `v1` from `block2` (which makes a
`call_indirect`); `g` (`ret = some r`): `block3` returns `r`. -/
def fnTwoM (ret : Option ValueId) : Function :=
  { name := "f", sig := { params := [ap .i32, ap .i32, ap .i64], returns := [ap .i32], callConv := none },
    sigDecls := [(0, { params := [], returns := [ap .i32], callConv := none })],
    blocks := [
      { id := 0, params := [(0, .i32), (1, .i32), (2, .i64)], cold := false, body := [],
        term := .brif 0 ⟨1, []⟩ ⟨2, []⟩ },
      { id := 1, params := [], cold := false, body := [],
        term := .jump ⟨3, if ret.isSome then [] else [0]⟩ },
      { id := 2, params := [], cold := false, body := [⟨[4], .callIndirect 0 2 []⟩],
        term := .jump ⟨3, if ret.isSome then [] else [1]⟩ },
      { id := 3, params := if ret.isSome then [] else [(3, .i32)], cold := false, body := [],
        term := .ret [ret.getD 3] }] }

def twoMFn : Function := fnTwoM none
def wrongMFn : Function := fnTwoM (some 1)

theorem twoMF_text : fn? twoMF = some twoMFn := by native_decide
theorem wrongMG_text : fn? wrongMG = some wrongMFn := by native_decide

/-- Two different values: nothing to remove. -/
theorem twoM_phiPre : phiPre twoMFn = twoMFn := by native_decide

/-- `wfCheck` accepts the function, but the solution `v3 := v0` is rejected (`block2` passes
`v1`). -/
theorem twoM_phiOkM_wrong : phiOkM twoMFn [(3, 0)] = false := by native_decide

theorem neg_twoM : acceptsC twoMF wrongMG = some false := by native_decide

/-- For `v0 = 5, v1 = 7`, `f` returns 5 and `g` 7 (neither reaches the `call_indirect`). -/
theorem twoM_not_sim : ¬ FunSimMU twoMFn wrongMFn :=
  not_funSimMU_ret_ne (b := twoMFn.blocks.head!) (b' := wrongMFn.blocks.head!)
    (args := [⟨.i32, 5⟩, ⟨.i32, 7⟩, ⟨.i64, 0⟩])
    (regs := ((Regs.empty.set 0 ⟨.i32, 5⟩).set 1 ⟨.i32, 7⟩).set 2 ⟨.i64, 0⟩)
    (m := Mem.empty) (vals := [⟨.i32, 5⟩]) (vals' := [⟨.i32, 7⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.refl _ _))) rfl
    (.step rfl (.step rfl (.refl _ _))) rfl (by decide)

/-- The re-check rejects every certificate and every hint list (prep requests included). -/
theorem twoM_rejected (cert : Cert) (hints : List (BlockId × List Wrap)) :
    checkCertC (ConstPhi.run twoMFn) wrongMFn cert hints = false := by
  cases h : checkCertC (ConstPhi.run twoMFn) wrongMFn cert hints
  · rfl
  · exact absurd (checkedC_simMU h) twoM_not_sim

/-! ## Real pairs -/

def proptestF : String := include_str "midval/real_phim_proptest.unopt.clif"
def proptestG : String := include_str "midval/real_phim_proptest.opt.clif"
def tomlF : String := include_str "midval/real_phim_toml.unopt.clif"
def tomlG : String := include_str "midval/real_phim_toml.opt.clif"
def memchrF : String := include_str "midval/real_phim_memchr.unopt.clif"
def memchrG : String := include_str "midval/real_phim_memchr.opt.clif"

theorem real_proptest_c0_rejects : c0Verdict proptestF proptestG = some false := by native_decide
theorem real_proptest_checked : checkedC proptestF proptestG = some (true, true) := by
  native_decide
theorem real_proptest_sim : SimRefinesC proptestF proptestG :=
  simC_of_checked real_proptest_checked

theorem real_toml_c0_rejects : c0Verdict tomlF tomlG = some false := by native_decide
theorem real_toml_checked : checkedC tomlF tomlG = some (true, true) := by native_decide
theorem real_toml_sim : SimRefinesC tomlF tomlG := simC_of_checked real_toml_checked

theorem real_memchr_c0_rejects : c0Verdict memchrF memchrG = some false := by native_decide
theorem real_memchr_checked : checkedC memchrF memchrG = some (true, true) := by native_decide
theorem real_memchr_sim : SimRefinesC memchrF memchrG := simC_of_checked real_memchr_checked

end Opt.MidVal.PhiMWitness
