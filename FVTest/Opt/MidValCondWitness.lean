import FVTest.Opt.MidValNormWitness
import FV.Opt.MidValCond
import FV.Opt.Proof.MidValCondProg

/-! # Branch conditions in the mid-end validator: witnesses (#1119 stage 2, family 3, route D)

`checkC` accepts `g` for `f` when `f`'s `brif` conditions are `g`'s under truth-keeping
wrappers (`icmp ne x, 0`, `icmp ugt x, 0`, `icmp ult 0, x`, extensions); the re-check
`checkCertC` checks `f` against `condPrep g hints`, and `check_soundC` composes that with
`condPrep_simU` (`FV/Opt/Proof/MidValCondSim.lean`).

* Hand-made: `brif (icmp ne x, 0)` against `brif x` (`pos_ne`) and `brif (uextend.i64 x)`
  against `brif x` with `x` an `i8` (`pos_ext`) are accepted, and rejected without hints
  (`*_check_rejects`). The look-alike `brif (icmp eq x, 1)` against `brif x` is rejected
  (`neg_eq`), it is no simulation (`eq_not_sim`: for `x = 2`, `f` returns 0 and `g` 1), so
  every certificate with every hint list is rejected (`eq_rejected`); `icmp ugt x, 1` is rejected
  too (`neg_ugt1`), no simulation (`ugt1_not_sim`: for `x = 1`) and rejected with every
  certificate and hint list (`ugt1_rejected`).
* Real pairs (crypto-bigint 0.7.11's test build, `FVTest/Opt/midval/real_cond_*.clif`), each
  rejected without hints and accepted by `checkCertC` with the hints `emitC` gives (decided),
  with the simulation and the program refinement (`*_sim`, `validatedC_refines`): `ext`
  (`brif (uextend.i64 (load.i8 …))` against `brif (load.i8 …)`, a drop glue of
  `Result<Option<u8>, serde_json::Error>`), `ne` (`brif (icmp ne …, 0)` in a proptest runner with
  `try_call`s).
-/

namespace Opt.MidVal.CondWitness

open Clif Pairs NormWitness

/-- The verdict with branch-condition hints (`checkC`, after constant-phi removal of `f`). -/
def acceptsC (f g : String) : Option Bool := do
  pure (checkC (ConstPhi.run (← fn? f)) (← fn? g)).isOk

/-! ## Hand-made pairs -/

def neF : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    v1 = iconst.i32 0\n    v2 = icmp ne v0, v1\n    brif v2, block1, block2\n\nblock1:\n    v3 = iconst.i32 1\n    return v3\n\nblock2:\n    v4 = iconst.i32 0\n    return v4\n}"
def neG : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    brif v0, block1, block2\n\nblock1:\n    v3 = iconst.i32 1\n    return v3\n\nblock2:\n    v4 = iconst.i32 0\n    return v4\n}"

theorem pos_ne : acceptsC neF neG = some true := by native_decide
theorem pos_ne_check_rejects : accepts neF neG = some false := by native_decide

def extF : String := "function %f(i8) -> i32 {\nblock0(v0: i8):\n    v1 = uextend.i64 v0\n    brif v1, block1, block2\n\nblock1:\n    v3 = iconst.i32 1\n    return v3\n\nblock2:\n    v4 = iconst.i32 0\n    return v4\n}"
def extG : String := "function %f(i8) -> i32 {\nblock0(v0: i8):\n    brif v0, block1, block2\n\nblock1:\n    v3 = iconst.i32 1\n    return v3\n\nblock2:\n    v4 = iconst.i32 0\n    return v4\n}"

theorem pos_ext : acceptsC extF extG = some true := by native_decide
theorem pos_ext_check_rejects : accepts extF extG = some false := by native_decide

def eqF : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    v1 = iconst.i32 1\n    v2 = icmp eq v0, v1\n    brif v2, block1, block2\n\nblock1:\n    v3 = iconst.i32 1\n    return v3\n\nblock2:\n    v4 = iconst.i32 0\n    return v4\n}"
def ugt1F : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    v1 = iconst.i32 1\n    v2 = icmp ugt v0, v1\n    brif v2, block1, block2\n\nblock1:\n    v3 = iconst.i32 1\n    return v3\n\nblock2:\n    v4 = iconst.i32 0\n    return v4\n}"

theorem neg_eq : acceptsC eqF neG = some false := by native_decide
theorem neg_ugt1 : acceptsC ugt1F neG = some false := by native_decide

/-! ## The look-alike is no simulation -/

/-- `x ↦ if c then 1 else 0` on an `i32` parameter, with the statements `body` computing the
condition `c` in the entry block. -/
def fnBr (body : List Stmt) (c : ValueId) : Function :=
  { name := "f", sig := { params := [ap .i32], returns := [ap .i32], callConv := none },
    blocks := [
      { id := 0, params := [(0, .i32)], cold := false, body, term := .brif c ⟨1, []⟩ ⟨2, []⟩ },
      { id := 1, params := [], cold := false, body := [{ results := [3], inst := .iconst .i32 1 }],
        term := .ret [3] },
      { id := 2, params := [], cold := false, body := [{ results := [4], inst := .iconst .i32 0 }],
        term := .ret [4] }] }

def eqFn : Function :=
  fnBr [{ results := [1], inst := .iconst .i32 1 }, { results := [2], inst := .icmp .eq .i32 0 1 }] 2
def brGn : Function := fnBr [] 0

theorem eqF_text : fn? eqF = some eqFn := by native_decide
theorem neG_text : fn? neG = some brGn := by native_decide

theorem eq_not_sim : ¬ FunSimMU eqFn brGn :=
  not_funSimMU_ret_ne (b := eqFn.blocks.head!) (b' := brGn.blocks.head!)
    (args := [⟨.i32, 2⟩]) (regs := Regs.empty.set 0 ⟨.i32, 2⟩) (m := Mem.empty)
    (vals := [⟨.i32, 0⟩]) (vals' := [⟨.i32, 1⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.step rfl (.step rfl (.refl _ _))))) rfl
    (.step rfl (.step rfl (.refl _ _))) rfl (by decide)

/-- The re-check with hints rejects every certificate and every hint list for `neg_eq`. -/
theorem eq_rejected (cert : Cert) (hints : List (BlockId × List Wrap)) :
    checkCertC (ConstPhi.run eqFn) brGn cert hints = false := by
  cases h : checkCertC (ConstPhi.run eqFn) brGn cert hints
  · rfl
  · exact absurd (checkedC_simMU h) eq_not_sim

def ugt1Fn : Function :=
  fnBr [{ results := [1], inst := .iconst .i32 1 }, { results := [2], inst := .icmp .ugt .i32 0 1 }] 2

theorem ugt1F_text : fn? ugt1F = some ugt1Fn := by native_decide

/-- `icmp ugt x, 1` is no simulation of `brif x`: for `x = 1`, `f` returns 0 and `g` 1. -/
theorem ugt1_not_sim : ¬ FunSimMU ugt1Fn brGn :=
  not_funSimMU_ret_ne (b := ugt1Fn.blocks.head!) (b' := brGn.blocks.head!)
    (args := [⟨.i32, 1⟩]) (regs := Regs.empty.set 0 ⟨.i32, 1⟩) (m := Mem.empty)
    (vals := [⟨.i32, 0⟩]) (vals' := [⟨.i32, 1⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.step rfl (.step rfl (.refl _ _))))) rfl
    (.step rfl (.step rfl (.refl _ _))) rfl (by decide)

/-- The re-check with hints rejects every certificate and every hint list for `neg_ugt1`. -/
theorem ugt1_rejected (cert : Cert) (hints : List (BlockId × List Wrap)) :
    checkCertC (ConstPhi.run ugt1Fn) brGn cert hints = false := by
  cases h : checkCertC (ConstPhi.run ugt1Fn) brGn cert hints
  · rfl
  · exact absurd (checkedC_simMU h) ugt1_not_sim

/-! ## Real pairs -/

/-- A decoded dump pair with the certificate and hints `emitC` gives it. -/
def pairC (fT gT : String) :
    Option (Function × Function × Cert × List (BlockId × List Wrap)) := do
  let f ← RealWitness.decode fT
  let g ← RealWitness.decode gT
  let (cert, h) ← (emitC (ConstPhi.run f) g).toOption
  pure (f, g, cert, h)

/-- The verdict without hints on a decoded dump pair. -/
def plainVerdict (fT gT : String) : Option Bool := do
  let f ← RealWitness.decode fT
  let g ← RealWitness.decode gT
  pure (check (ConstPhi.run f) g).isOk

/-- The re-check with hints of the emitted certificate, and whether hints were needed. -/
def checkedC (fT gT : String) : Option (Bool × Bool) :=
  (pairC fT gT).map fun p => (checkCertC (ConstPhi.run p.1) p.2.1 p.2.2.1 p.2.2.2, !p.2.2.2.isEmpty)

/-- The simulation and the program refinement for the decoded pair. -/
def SimRefinesC (fT gT : String) : Prop :=
  ∃ f g, ((pairC fT gT).map fun p => (p.1, p.2.1)) = some (f, g) ∧ FunSimMU f g ∧
    ∀ (syms : String → Option Nat) (env : XEnv), EnvKeepsSymbolsX env →
      ∀ n (xs xs' : XState), SRU syms xs xs' →
        ∃ n', XOutcomeRefines (Clif.runLoopX env { funcs := [f] } n xs)
          (Clif.runLoopX env { funcs := [g] } n' xs')

theorem simC_of_checked {fT gT : String} {b : Bool} (h : checkedC fT gT = some (true, b)) :
    SimRefinesC fT gT := by
  unfold checkedC at h
  cases hp : pairC fT gT with
  | none => rw [hp] at h; cases h
  | some p =>
    obtain ⟨f, g, cert, hints⟩ := p
    rw [hp] at h
    have hc : checkCertC (ConstPhi.run f) g cert hints = true := by
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h; exact h.1
    exact ⟨f, g, by rw [hp]; rfl, checkedC_simMU hc, fun syms env hE =>
      validatedC_refines (p := { funcs := [f] }) (q := { funcs := [g] }) hE
        (.checked cert hints hc .nil)⟩

def extF' : String := include_str "midval/real_cond_ext.unopt.clif"
def extG' : String := include_str "midval/real_cond_ext.opt.clif"
def neF' : String := include_str "midval/real_cond_ne.unopt.clif"
def neG' : String := include_str "midval/real_cond_ne.opt.clif"

theorem real_ext_plain_rejects : plainVerdict extF' extG' = some false := by native_decide
theorem real_ext_checked : checkedC extF' extG' = some (true, true) := by native_decide
theorem real_ext_sim : SimRefinesC extF' extG' := simC_of_checked real_ext_checked

theorem real_ne_plain_rejects : plainVerdict neF' neG' = some false := by native_decide
theorem real_ne_checked : checkedC neF' neG' = some (true, true) := by native_decide
theorem real_ne_sim : SimRefinesC neF' neG' := simC_of_checked real_ne_checked

end Opt.MidVal.CondWitness
