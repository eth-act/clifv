import FVTest.Opt.MidValDropWitness
import FV.Opt.Proof.MidValFwd

/-! # Store-to-load forwarding before the folds, and `selfCmp`: witnesses (#1119 family A, agent StoreFold1)

`fwdPre` (`FV/Opt/MidValFwd.lean`) removes the loads whose location holds a known value, renaming
their results to that value, so that `foldPre`/`foldPreK` see the constant branch conditions
Cranelift folded; `checkCertC` tries those copies when the checker accepts `fwdPre f` against `f`
(`fwdOk`; `fwdOk_simMU`, `FV/Opt/Proof/MidValFwd.lean`). `selfCmp` (family 7, `dropStep`):
`icmp cc ty x x` is a constant.

Each pair below is decided: rejected by main's checker before this change (`checkCPrev`: main's
`checkC`, with main's family 7 without `selfCmp`, `*_prev_rejects`) and accepted by `checkC`
now; look-alikes are rejected (`neg_*`).

* Hand-made: a branch on a byte loaded right after storing the constant 1 to the same address,
  against a `jump` to the `then` block (`pos_fwd`) and to the `else` block (`neg_fwd`); a branch
  on `icmp eq x, x` against a `jump` to the `then` block (`pos_self`), and on `icmp ult x, x`
  against the same `jump` (`neg_self`).
* Real pairs of the shared #1119 corpus (`FVTest/Opt/midval/real_fwd_*.clif`), accepted by
  `checkCertC` with the hints and fold requests `emitC` gives, with the simulation and the
  program refinement (`*_sim`), and `fwdOk` decided on the source with the forwarding
  simulations (`*_fwd`, the non-vacuity witnesses of `fwdOk_simMU`, `fwdFoldPre_simMU`,
  `fwdFoldPreK_simMU`):
  - `const`: crypto-bigint's test build, `_RNxC13crypto_bigint12H5o2LecSMBHx`: `uextend` of a
    constant stored to a stack slot, loaded back through another `stack_addr`, compared with the
    same constant;
  - `chain`: crypto-bigint's test build, `_RNxC13crypto_bigint12HbQxECUhWzp5`: the constant 2
    stored, loaded, stored to a second slot and loaded again, then `icmp ult 0, x`;
  - `self`: serde_json's test build, `_RNxC10serde_json12HiQy0IKdvZKU`: two loads of one field,
    compared with `icmp eq` (load against load, then `selfCmp`).
-/

namespace Opt.MidVal.FwdWitness
open Clif Pairs NormWitness CondWitness FoldWitness

/-! ## Main's checker (before this change) -/

/-- Main's family 7 (without `selfCmp`). -/
def dropStepPrev (aty : Tm → Option Ty) (tms : Array Tm) : Inst → Option Tm
  | .binary op ty a b =>
    if op == .isub then subAdd tms ty a b
    else if op == .iadd then addSub tms ty a b
    else absTyped aty tms op ty a b
  | _ => none

/-- Main's default normaliser. -/
def normPrev (f : Function) : Norm :=
  Norm.orElse (Norm.stdT f) (Norm.guard (dropStepPrev (atomTy f)))

/-- Main's `checkC`: hints, then the prep copies `foldPre` and `foldPreK` for `foldCands`, with
main's normaliser. -/
def checkCPrev (f g : Function) : Except Reject (List (BlockId × List Wrap)) :=
  match checkC0 f g (normPrev f) with
  | .ok h => .ok h
  | .error e =>
    let bs := match foldCands f g with
      | [] => (f.blocks.head?.map (·.id)).toList
      | bs => bs
    let prep (f' : Function) : Except Reject (List (BlockId × List Wrap)) :=
      if f'.blocks == f.blocks then .error e
      else if f'.blocks.map (·.id) != g.blocks.map (·.id) then .error e
      else match checkC0 f' g (normPrev f') with
        | .ok h => .ok (h ++ bs.map fun b => (b, []))
        | .error e' => .error e'
    if bs.isEmpty then .error e
    else match prep (foldPre f bs) with
      | .ok h => .ok h
      | .error _ => prep (foldPreK f bs)

/-- The verdict of `checkCPrev` on a hand-made pair. -/
def acceptsPrev (f g : String) : Option Bool := do
  pure (checkCPrev (ConstPhi.run (← fn? f)) (← fn? g)).isOk

/-- The verdict of `checkCPrev` on a decoded dump pair. -/
def realPrev (fT gT : String) : Option Bool := do
  let f := ConstPhi.run (← RealWitness.decode fT)
  let g ← RealWitness.decode gT
  pure (checkCPrev f g).isOk

/-! ## Hand-made pairs -/

def fwdF : String := "function %f(i64) -> i32 {\nblock0(v0: i64):\n    v1 = iconst.i8 1\n    store.i8 v1, v0\n    v2 = load.i8 v0\n    brif v2, block1, block2\n\nblock1:\n    v3 = iconst.i32 1\n    return v3\n\nblock2:\n    v4 = iconst.i32 0\n    return v4\n}"
def fwdG : String := "function %f(i64) -> i32 {\nblock0(v0: i64):\n    v1 = iconst.i8 1\n    store.i8 v1, v0\n    jump block1\n\nblock1:\n    v3 = iconst.i32 1\n    return v3\n}"
def fwdWrongG : String := "function %f(i64) -> i32 {\nblock0(v0: i64):\n    v1 = iconst.i8 1\n    store.i8 v1, v0\n    jump block2\n\nblock2:\n    v4 = iconst.i32 0\n    return v4\n}"

theorem pos_fwd : acceptsC fwdF fwdG = some true := by native_decide
theorem pos_fwd_prev_rejects : acceptsPrev fwdF fwdG = some false := by native_decide
theorem neg_fwd : acceptsC fwdF fwdWrongG = some false := by native_decide

def selfF : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    v1 = icmp eq v0, v0\n    brif v1, block1, block2\n\nblock1:\n    v3 = iconst.i32 1\n    return v3\n\nblock2:\n    v4 = iconst.i32 0\n    return v4\n}"
def selfG : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    jump block1\n\nblock1:\n    v3 = iconst.i32 1\n    return v3\n}"
def selfUltF : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    v1 = icmp ult v0, v0\n    brif v1, block1, block2\n\nblock1:\n    v3 = iconst.i32 1\n    return v3\n\nblock2:\n    v4 = iconst.i32 0\n    return v4\n}"

theorem pos_self : acceptsC selfF selfG = some true := by native_decide
theorem pos_self_prev_rejects : acceptsPrev selfF selfG = some false := by native_decide
theorem neg_self : acceptsC selfUltF selfG = some false := by native_decide

/-! ## Real pairs (module doc) -/

def constF : String := include_str "midval/real_fwd_const.unopt.clif"
def constG : String := include_str "midval/real_fwd_const.opt.clif"
def chainF : String := include_str "midval/real_fwd_chain.unopt.clif"
def chainG : String := include_str "midval/real_fwd_chain.opt.clif"
def selfF' : String := include_str "midval/real_fwd_self.unopt.clif"
def selfG' : String := include_str "midval/real_fwd_self.opt.clif"

/-- `fwdOk` on the decoded source after constant-phi removal. -/
def fwdOkReal (fT : String) : Option Bool := do
  pure (fwdOk (ConstPhi.run (← RealWitness.decode fT)))

/-- The forwarding simulations on a decoded source where `fwdOk` holds. -/
def FwdSims (fT : String) : Prop :=
  ∃ f, (RealWitness.decode fT).map ConstPhi.run = some f ∧ FunSimMU f (fwdPre f) ∧
    ∀ bs, FunSimMU f (foldPre (fwdPre f) bs) ∧ FunSimMU f (foldPreK (fwdPre f) bs)

theorem fwdSims_of {fT : String} (h : fwdOkReal fT = some true) : FwdSims fT := by
  unfold fwdOkReal at h
  cases hd : RealWitness.decode fT with
  | none => rw [hd] at h; cases h
  | some f0 =>
    rw [hd] at h
    have hf : fwdOk (ConstPhi.run f0) = true := by simpa using h
    exact ⟨ConstPhi.run f0, by rw [hd]; rfl, fwdOk_simMU hf,
      fun bs => ⟨fwdFoldPre_simMU hf bs, fwdFoldPreK_simMU hf bs⟩⟩

theorem real_const_prev_rejects : realPrev constF constG = some false := by native_decide
theorem real_const_checked : checkedC constF constG = some (true, true) := by native_decide
theorem real_const_sim : SimRefinesC constF constG := simC_of_checked real_const_checked
theorem real_const_fwdOk : fwdOkReal constF = some true := by native_decide
theorem real_const_fwd : FwdSims constF := fwdSims_of real_const_fwdOk

theorem real_chain_prev_rejects : realPrev chainF chainG = some false := by native_decide
theorem real_chain_checked : checkedC chainF chainG = some (true, true) := by native_decide
theorem real_chain_sim : SimRefinesC chainF chainG := simC_of_checked real_chain_checked
theorem real_chain_fwdOk : fwdOkReal chainF = some true := by native_decide
theorem real_chain_fwd : FwdSims chainF := fwdSims_of real_chain_fwdOk

theorem real_self_prev_rejects : realPrev selfF' selfG' = some false := by native_decide
theorem real_self_checked : checkedC selfF' selfG' = some (true, true) := by native_decide
theorem real_self_sim : SimRefinesC selfF' selfG' := simC_of_checked real_self_checked
theorem real_self_fwdOk : fwdOkReal selfF' = some true := by native_decide
theorem real_self_fwd : FwdSims selfF' := fwdSims_of real_self_fwdOk

end Opt.MidVal.FwdWitness
