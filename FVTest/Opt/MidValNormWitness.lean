import FVTest.Opt.MidValPairs
import FV.Opt.Proof.MidValNeg
import FV.Opt.Proof.MidValProg
import FVTest.Opt.MidValWitness

/-! # Constant evaluation in the mid-end validator: hand-made witnesses (#1119 stage 2)

The validator's default normaliser `Norm.std` evaluates a pure node whose operands are constants
by `Clif.evalInst` (`evalConst`). Two semantic corner cases, each with the right fold (accepted)
and a look-alike wrong one (rejected):

* **shift amount ≥ width**: `ishl.i32 1, 33` is `2` (the amount is taken modulo the width), not
  `0` as in C or LLVM. `pos_shift` (`g` returns `iconst 2`) is accepted; `neg_shift` (`g` returns
  `iconst 0`) is rejected, and it is no simulation (`shift_not_sim`: `f` returns `2`, `g` `0`),
  so the re-check rejects every certificate (`shift_rejected`, by `check_sound`);
* **signedness**: `sshr.i8 -128, 1` is `-64` (`0xc0`, arithmetic shift), not `0x40` (logical).
  `pos_sshr` is accepted; `neg_sshr` is rejected, no simulation (`sshr_not_sim`), every
  certificate rejected (`sshr_rejected`).

Both positive pairs are rejected by stage 1's identity normaliser (`*_id_rejects`): the fold is
what accepts them.

**A real pair** (crypto-bigint 0.7.11's test build, `criterion`'s `_RNxC9criterion12HfNVJlKK03zX`,
`<rayon::slice::sort::InsertionHole<f64> as Drop>::drop`; `FVTest/Opt/midval/real_fold.*.clif`):
`f` passes `imul 1, 8` to `memcpy`, Cranelift's `g` passes `iconst 8`. Stage 1 rejects it
(`real_id_rejects`), the re-check with `Norm.std` accepts the emitted certificate (`real_checked`),
and `check_sound` gives the simulation and the program refinement (`real_simMU`,
`real_refines`). -/

namespace Opt.MidVal.NormWitness

open Clif Pairs

/-- The verdict with stage 1's identity normaliser. -/
def acceptsId (f g : String) : Option Bool := do
  pure (check (ConstPhi.run (← fn? f)) (← fn? g) Norm.id).isOk

def shiftF : String := "function %f() -> i32 {\nblock0:\n    v1 = iconst.i32 1\n    v2 = iconst.i32 33\n    v3 = ishl v1, v2\n    return v3\n}"
def shiftG2 : String := "function %f() -> i32 {\nblock0:\n    v9 = iconst.i32 2\n    return v9\n}"
def shiftG0 : String := "function %f() -> i32 {\nblock0:\n    v9 = iconst.i32 0\n    return v9\n}"

def sshrF : String := "function %f() -> i8 {\nblock0:\n    v1 = iconst.i8 -128\n    v2 = iconst.i8 1\n    v3 = sshr v1, v2\n    return v3\n}"
def sshrGc0 : String := "function %f() -> i8 {\nblock0:\n    v9 = iconst.i8 -64\n    return v9\n}"
def sshrG40 : String := "function %f() -> i8 {\nblock0:\n    v9 = iconst.i8 64\n    return v9\n}"

theorem pos_shift : accepts shiftF shiftG2 = some true := by native_decide
theorem pos_shift_id_rejects : acceptsId shiftF shiftG2 = some false := by native_decide
theorem neg_shift : accepts shiftF shiftG0 = some false := by native_decide

theorem pos_sshr : accepts sshrF sshrGc0 = some true := by native_decide
theorem pos_sshr_id_rejects : acceptsId sshrF sshrGc0 = some false := by native_decide
theorem neg_sshr : accepts sshrF sshrG40 = some false := by native_decide

/-! ## The negative pairs are no simulations -/

def ap (t : Ty) : AbiParam := { ty := t, ext := .none, purpose := .normal }
def sigR (t : Ty) : Signature := { params := [], returns := [ap t], callConv := none }

/-- `f`: two constants and a binary node on them, returned. -/
def binF (t : Ty) (op : BinaryOp) (a b : BitVec t.width) : Function :=
  { name := "f", sig := sigR t, blocks := [
    { id := 0, params := [], cold := false,
      body := [{ results := [1], inst := .iconst t a }, { results := [2], inst := .iconst t b },
        { results := [3], inst := .binary op t 1 2 }],
      term := .ret [3] }] }

/-- `g`: one constant, returned. -/
def cstB (t : Ty) (c : BitVec t.width) : Block :=
  { id := 0, params := [], cold := false, body := [{ results := [9], inst := .iconst t c }],
    term := .ret [9] }
def cstG (t : Ty) (c : BitVec t.width) : Function := { name := "f", sig := sigR t, blocks := [cstB t c] }

theorem shiftF_text : fn? shiftF = some (binF .i32 .ishl 1 33) := by native_decide
theorem shiftG0_text : fn? shiftG0 = some (cstG .i32 0) := by native_decide
theorem sshrF_text : fn? sshrF = some (binF .i8 .sshr 0x80 1) := by native_decide
theorem sshrG40_text : fn? sshrG40 = some (cstG .i8 0x40) := by native_decide

theorem shift_not_sim : ¬ FunSimMU (binF .i32 .ishl 1 33) (cstG .i32 0) :=
  not_funSimMU_ret_ne (b := (binF .i32 .ishl 1 33).blocks.head!) (b' := cstB .i32 0) (args := [])
    (regs := Regs.empty) (m := Mem.empty) (vals := [⟨.i32, 2⟩]) (vals' := [⟨.i32, 0⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.step rfl (.refl _ _)))) rfl
    (.step rfl (.refl _ _)) rfl (by decide)

/-- The re-check rejects every certificate for `neg_shift`. -/
theorem shift_rejected (cert : Cert) :
    checkCert (ConstPhi.run (binF .i32 .ishl 1 33)) (cstG .i32 0) cert = false := by
  cases h : checkCert (ConstPhi.run (binF .i32 .ishl 1 33)) (cstG .i32 0) cert
  · rfl
  · exact absurd (checked_simMU h) shift_not_sim

theorem sshr_not_sim : ¬ FunSimMU (binF .i8 .sshr 0x80 1) (cstG .i8 0x40) :=
  not_funSimMU_ret_ne (b := (binF .i8 .sshr 0x80 1).blocks.head!) (b' := cstB .i8 0x40) (args := [])
    (regs := Regs.empty) (m := Mem.empty) (vals := [⟨.i8, 0xc0⟩]) (vals' := [⟨.i8, 0x40⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.step rfl (.refl _ _)))) rfl
    (.step rfl (.refl _ _)) rfl (by decide)

/-- The re-check rejects every certificate for `neg_sshr`. -/
theorem sshr_rejected (cert : Cert) :
    checkCert (ConstPhi.run (binF .i8 .sshr 0x80 1)) (cstG .i8 0x40) cert = false := by
  cases h : checkCert (ConstPhi.run (binF .i8 .sshr 0x80 1)) (cstG .i8 0x40) cert
  · rfl
  · exact absurd (checked_simMU h) sshr_not_sim

/-! ## A real pair -/

def realF : String := include_str "midval/real_fold.unopt.clif"
def realG : String := include_str "midval/real_fold.opt.clif"

/-- The decoded pair and the certificate `emit` gives (default normaliser `Norm.std`). -/
def realPair : Option (Function × Function × Cert) := do
  let f ← RealWitness.decode realF
  let g ← RealWitness.decode realG
  let cert ← (emit (ConstPhi.run f) g).toOption
  pure (f, g, cert)

/-- Stage 1's identity normaliser rejects the pair (decided). -/
theorem real_id_rejects :
    ((RealWitness.decode realF).bind fun f => (RealWitness.decode realG).map fun g =>
      (check (ConstPhi.run f) g Norm.id).isOk) = some false := by
  native_decide

/-- The re-check accepts (decided). -/
theorem real_checked :
    (realPair.map fun p => checkCert (ConstPhi.run p.1) p.2.1 p.2.2) = some true := by
  native_decide

theorem real_some : ∃ f g cert, realPair = some (f, g, cert) ∧
    checkCert (ConstPhi.run f) g cert = true := by
  have h := real_checked
  cases hp : realPair with
  | none => rw [hp] at h; cases h
  | some p =>
    obtain ⟨f, g, cert⟩ := p
    rw [hp] at h
    exact ⟨f, g, cert, rfl, by simpa using h⟩

/-- **Soundness on the real pair**: the optimised function simulates the unoptimised one. -/
theorem real_simMU : ∃ f g, (realPair.map fun p => (p.1, p.2.1)) = some (f, g) ∧ FunSimMU f g := by
  obtain ⟨f, g, cert, hp, hc⟩ := real_some
  exact ⟨f, g, by rw [hp]; rfl, checked_simMU hc⟩

/-- **The program corollary on the real pair**: the one-function programs refine. -/
theorem real_refines : ∃ f g, (realPair.map fun p => (p.1, p.2.1)) = some (f, g) ∧
    ∀ (syms : String → Option Nat) (env : XEnv), EnvKeepsSymbolsX env →
      ∀ n (xs xs' : XState), SRU syms xs xs' →
        ∃ n', XOutcomeRefines (Clif.runLoopX env { funcs := [f] } n xs)
          (Clif.runLoopX env { funcs := [g] } n' xs') := by
  obtain ⟨f, g, cert, hp, hc⟩ := real_some
  exact ⟨f, g, by rw [hp]; rfl, fun syms env hE =>
    validated_refines (p := { funcs := [f] }) (q := { funcs := [g] }) hE
      (.checked cert hc .nil)⟩

end Opt.MidVal.NormWitness
