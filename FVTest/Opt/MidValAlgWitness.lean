import FVTest.Opt.MidValNormWitness

/-! # Single-node algebraic rules in the mid-end validator: witnesses (#1119 stage 2, family 2)

The validator's default normaliser `Norm.std` is constant evaluation (family 1), then the
single-node algebraic rules `Norm.alg` (family 2, `FV/Opt/Proof/MidValNormAlg.lean`). For each
rule: a hand-made pair it accepts, rejected by family 1 alone (`*_const_rejects`), and a
look-alike it rejects.

* `selIcmp`: `select.i32 (icmp …), 1, 0` is `uextend.i32 (icmp …)` (`pos_sel`). The look-alike
  `select.i32 c, 1, 0` with `c` an `i8` parameter (not an `icmp`, so not 0/1) against
  `uextend.i32 c` is rejected (`neg_sel`), and it is no simulation (`sel_not_sim`: for `c = 2`
  `f` returns 1, `g` 2), so the re-check rejects every certificate (`sel_rejected`).
* `mulPow2`: `imul x, 8` is `ishl x, 3` (`pos_mul`); `ishl x, 4` is rejected (`neg_mul`).
* `addStack`: `iadd (stack_addr ss0), 8` is `stack_addr ss0+8` (`pos_stack`); `ss0+4` is
  rejected (`neg_stack`).
* `redExt`: `ireduce.i16 (sextend.i64 y)` with `y` an `i8` node is `sextend.i16 y` (`pos_red`);
  the look-alike `uextend.i16 y` is rejected (`neg_red`) and no simulation (`red_not_sim`: for
  `y = 0x80`, `f` returns `0xff80`, `g` `0x0080`), so every certificate is rejected
  (`red_rejected`). The unsound shape without a width check, `ireduce.i16 (uextend.i64 v0)` with
  `v0` an `i8` parameter (an atom: its type is not in the table) folded to `v0`, is rejected
  (`neg_redAtom`) and no simulation (`redAtom_not_sim`: for `v0 = 0x80`, `f` returns the `i16`
  `0x0080`, `g` the `i8` `0x80`), so every certificate is rejected (`redAtom_rejected`).

**Real pairs** (crypto-bigint 0.7.11's test build, `FVTest/Opt/midval/real_alg_*.clif`), each
rejected by family 1 alone, accepted by the re-check with `Norm.std` (decided), with the
simulation and the program refinement from `check_sound` (`*_sim`):

* `mul`: crypto_bigint's `_RNxC13crypto_bigint12H1irghiiSHXv` (`<*mut u32>::offset`): `imul v1, 4`
  is Cranelift's `ishl v1, 2` (`mulPow2`);
* `stack`: regex_automata's `_RNxC14regex_automata12HiAs7os3Ml1v`
  (`Compiler::build_from_hir`): `iadd (stack_addr ss0), (imul 0, 8)` is `stack_addr ss0`
  (`evalConst`, then `addStack`);
* `sel`: walkdir's `_RNxC7walkdir11Hh5UlsiILot`: `select (icmp eq x, -1), 0, 1` is
  `uextend.i64 (icmp ne x, -1)` (`selIcmp` with the inverted comparison), and its
  `ireduce.i32` is `uextend.i32 (icmp ne x, -1)` (`redExt`). -/

namespace Opt.MidVal.AlgWitness

open Clif Pairs NormWitness

/-- The verdict with family 1 alone (constant evaluation, `evalConst`). -/
def acceptsConst (f g : String) : Option Bool := do
  pure (check (ConstPhi.run (← fn? f)) (← fn? g) evalConst).isOk

/-! ## Hand-made pairs -/

def selF : String := "function %f(i32, i32) -> i32 {\nblock0(v0: i32, v1: i32):\n    v2 = icmp eq v0, v1\n    v3 = iconst.i32 1\n    v4 = iconst.i32 0\n    v5 = select v2, v3, v4\n    return v5\n}"
def selG : String := "function %f(i32, i32) -> i32 {\nblock0(v0: i32, v1: i32):\n    v2 = icmp eq v0, v1\n    v5 = uextend.i32 v2\n    return v5\n}"
def selNegF : String := "function %f(i8) -> i32 {\nblock0(v0: i8):\n    v3 = iconst.i32 1\n    v4 = iconst.i32 0\n    v5 = select v0, v3, v4\n    return v5\n}"
def selNegG : String := "function %f(i8) -> i32 {\nblock0(v0: i8):\n    v5 = uextend.i32 v0\n    return v5\n}"

theorem pos_sel : accepts selF selG = some true := by native_decide
theorem pos_sel_const_rejects : acceptsConst selF selG = some false := by native_decide
theorem neg_sel : accepts selNegF selNegG = some false := by native_decide

def mulF : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 8\n    v2 = imul v0, v1\n    return v2\n}"
def mulG3 : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v3 = iconst.i64 3\n    v2 = ishl v0, v3\n    return v2\n}"
def mulG4 : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v3 = iconst.i64 4\n    v2 = ishl v0, v3\n    return v2\n}"

theorem pos_mul : accepts mulF mulG3 = some true := by native_decide
theorem pos_mul_const_rejects : acceptsConst mulF mulG3 = some false := by native_decide
theorem neg_mul : accepts mulF mulG4 = some false := by native_decide

def stackF : String := "function %f() -> i64 {\n    ss0 = explicit_slot 16, align = 8\n\nblock0:\n    v0 = stack_addr.i64 ss0\n    v1 = iconst.i64 8\n    v2 = iadd v0, v1\n    return v2\n}"
def stackG8 : String := "function %f() -> i64 {\n    ss0 = explicit_slot 16, align = 8\n\nblock0:\n    v2 = stack_addr.i64 ss0+8\n    return v2\n}"
def stackG4 : String := "function %f() -> i64 {\n    ss0 = explicit_slot 16, align = 8\n\nblock0:\n    v2 = stack_addr.i64 ss0+4\n    return v2\n}"

theorem pos_stack : accepts stackF stackG8 = some true := by native_decide
theorem pos_stack_const_rejects : acceptsConst stackF stackG8 = some false := by native_decide
theorem neg_stack : accepts stackF stackG4 = some false := by native_decide

def redF : String := "function %f(i8) -> i16 {\nblock0(v0: i8):\n    v1 = iadd v0, v0\n    v2 = sextend.i64 v1\n    v3 = ireduce.i16 v2\n    return v3\n}"
def redGs : String := "function %f(i8) -> i16 {\nblock0(v0: i8):\n    v1 = iadd v0, v0\n    v3 = sextend.i16 v1\n    return v3\n}"
def redGu : String := "function %f(i8) -> i16 {\nblock0(v0: i8):\n    v1 = iadd v0, v0\n    v3 = uextend.i16 v1\n    return v3\n}"

theorem pos_red : accepts redF redGs = some true := by native_decide
theorem pos_red_const_rejects : acceptsConst redF redGs = some false := by native_decide
theorem neg_red : accepts redF redGu = some false := by native_decide

def redAtomF : String := "function %f(i8) -> i16 {\nblock0(v0: i8):\n    v1 = uextend.i64 v0\n    v2 = ireduce.i16 v1\n    return v2\n}"
def redAtomG : String := "function %f(i8) -> i16 {\nblock0(v0: i8):\n    return v0\n}"

theorem neg_redAtom : accepts redAtomF redAtomG = some false := by native_decide

/-! ## Two look-alikes are no simulations -/

/-- A one-parameter function of one block. -/
def fn1 (pt rt : Ty) (body : List Stmt) (r : ValueId) : Function :=
  { name := "f", sig := { params := [ap pt], returns := [ap rt], callConv := none },
    blocks := [{ id := 0, params := [(0, pt)], cold := false, body, term := .ret [r] }] }

def selNegFn : Function :=
  fn1 .i8 .i32 [{ results := [3], inst := .iconst .i32 1 }, { results := [4], inst := .iconst .i32 0 },
    { results := [5], inst := .select .i32 0 3 4 }] 5
def selNegGn : Function := fn1 .i8 .i32 [{ results := [5], inst := .extend .uextend .i32 0 }] 5

def redFn : Function :=
  fn1 .i8 .i16 [{ results := [1], inst := .binary .iadd .i8 0 0 },
    { results := [2], inst := .extend .sextend .i64 1 }, { results := [3], inst := .ireduce .i16 2 }] 3
def redGun : Function :=
  fn1 .i8 .i16 [{ results := [1], inst := .binary .iadd .i8 0 0 },
    { results := [3], inst := .extend .uextend .i16 1 }] 3
def redAtomFn : Function :=
  fn1 .i8 .i16 [{ results := [1], inst := .extend .uextend .i64 0 },
    { results := [2], inst := .ireduce .i16 1 }] 2
def redAtomGn : Function := fn1 .i8 .i16 [] 0

theorem selNegF_text : fn? selNegF = some selNegFn := by native_decide
theorem selNegG_text : fn? selNegG = some selNegGn := by native_decide
theorem redF_text : fn? redF = some redFn := by native_decide
theorem redGu_text : fn? redGu = some redGun := by native_decide
theorem redAtomF_text : fn? redAtomF = some redAtomFn := by native_decide
theorem redAtomG_text : fn? redAtomG = some redAtomGn := by native_decide

theorem sel_not_sim : ¬ FunSimMU selNegFn selNegGn :=
  not_funSimMU_ret_ne (b := selNegFn.blocks.head!) (b' := selNegGn.blocks.head!)
    (args := [⟨.i8, 2⟩]) (regs := Regs.empty.set 0 ⟨.i8, 2⟩) (m := Mem.empty)
    (vals := [⟨.i32, 1⟩]) (vals' := [⟨.i32, 2⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.step rfl (.refl _ _)))) rfl
    (.step rfl (.refl _ _)) rfl (by decide)

/-- The re-check rejects every certificate for `neg_sel`. -/
theorem sel_rejected (cert : Cert) :
    checkCert (ConstPhi.run selNegFn) selNegGn cert = false := by
  cases h : checkCert (ConstPhi.run selNegFn) selNegGn cert
  · rfl
  · exact absurd (checked_simMU h) sel_not_sim

theorem red_not_sim : ¬ FunSimMU redFn redGun :=
  not_funSimMU_ret_ne (b := redFn.blocks.head!) (b' := redGun.blocks.head!)
    (args := [⟨.i8, 0x40⟩]) (regs := Regs.empty.set 0 ⟨.i8, 0x40⟩) (m := Mem.empty)
    (vals := [⟨.i16, 0xff80⟩]) (vals' := [⟨.i16, 0x0080⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.step rfl (.refl _ _)))) rfl
    (.step rfl (.step rfl (.refl _ _))) rfl (by decide)

/-- The re-check rejects every certificate for `neg_red`. -/
theorem red_rejected (cert : Cert) :
    checkCert (ConstPhi.run redFn) redGun cert = false := by
  cases h : checkCert (ConstPhi.run redFn) redGun cert
  · rfl
  · exact absurd (checked_simMU h) red_not_sim

theorem redAtom_not_sim : ¬ FunSimMU redAtomFn redAtomGn :=
  not_funSimMU_ret_ne (b := redAtomFn.blocks.head!) (b' := redAtomGn.blocks.head!)
    (args := [⟨.i8, 0x80⟩]) (regs := Regs.empty.set 0 ⟨.i8, 0x80⟩) (m := Mem.empty)
    (vals := [⟨.i16, 0x0080⟩]) (vals' := [⟨.i8, 0x80⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.refl _ _))) rfl
    (.refl _ _) rfl (by decide)

/-- The re-check rejects every certificate for `neg_redAtom`. -/
theorem redAtom_rejected (cert : Cert) :
    checkCert (ConstPhi.run redAtomFn) redAtomGn cert = false := by
  cases h : checkCert (ConstPhi.run redAtomFn) redAtomGn cert
  · rfl
  · exact absurd (checked_simMU h) redAtom_not_sim

/-! ## Real pairs -/

/-- A decoded dump pair and the certificate `emit` gives it (default normaliser `Norm.std`). -/
def pairD (fT gT : String) : Option (Function × Function × Cert) := do
  let f ← RealWitness.decode fT
  let g ← RealWitness.decode gT
  let cert ← (emit (ConstPhi.run f) g).toOption
  pure (f, g, cert)

/-- The verdict of family 1 alone on a decoded dump pair. -/
def constVerdict (fT gT : String) : Option Bool := do
  let f ← RealWitness.decode fT
  let g ← RealWitness.decode gT
  pure (check (ConstPhi.run f) g evalConst).isOk

/-- The simulation and the program refinement for the decoded pair. -/
def SimRefines (fT gT : String) : Prop :=
  ∃ f g, ((pairD fT gT).map fun p => (p.1, p.2.1)) = some (f, g) ∧ FunSimMU f g ∧
    ∀ (syms : String → Option Nat) (env : XEnv), EnvKeepsSymbolsX env →
      ∀ n (xs xs' : XState), SRU syms xs xs' →
        ∃ n', XOutcomeRefines (Clif.runLoopX env { funcs := [f] } n xs)
          (Clif.runLoopX env { funcs := [g] } n' xs')

/-- An accepted re-check gives the simulation and the program refinement (`check_sound`). -/
theorem sim_of_checked {fT gT : String}
    (h : ((pairD fT gT).map fun p => checkCert (ConstPhi.run p.1) p.2.1 p.2.2) = some true) :
    SimRefines fT gT := by
  cases hp : pairD fT gT with
  | none => rw [hp] at h; cases h
  | some p =>
    obtain ⟨f, g, cert⟩ := p
    rw [hp] at h
    have hc : checkCert (ConstPhi.run f) g cert = true := by simpa using h
    exact ⟨f, g, by rw [hp]; rfl, checked_simMU hc, fun syms env hE =>
      validated_refines (p := { funcs := [f] }) (q := { funcs := [g] }) hE
        (.checked cert hc .nil)⟩

def mulF' : String := include_str "midval/real_alg_mul.unopt.clif"
def mulG' : String := include_str "midval/real_alg_mul.opt.clif"
def stackF' : String := include_str "midval/real_alg_stack.unopt.clif"
def stackG' : String := include_str "midval/real_alg_stack.opt.clif"
def selF' : String := include_str "midval/real_alg_sel.unopt.clif"
def selG' : String := include_str "midval/real_alg_sel.opt.clif"

theorem real_mul_const_rejects : constVerdict mulF' mulG' = some false := by native_decide
theorem real_mul_checked :
    ((pairD mulF' mulG').map fun p => checkCert (ConstPhi.run p.1) p.2.1 p.2.2) = some true := by
  native_decide
theorem real_mul_sim : SimRefines mulF' mulG' := sim_of_checked real_mul_checked

theorem real_stack_const_rejects : constVerdict stackF' stackG' = some false := by native_decide
theorem real_stack_checked :
    ((pairD stackF' stackG').map fun p => checkCert (ConstPhi.run p.1) p.2.1 p.2.2) =
      some true := by
  native_decide
theorem real_stack_sim : SimRefines stackF' stackG' := sim_of_checked real_stack_checked

theorem real_sel_const_rejects : constVerdict selF' selG' = some false := by native_decide
theorem real_sel_checked :
    ((pairD selF' selG').map fun p => checkCert (ConstPhi.run p.1) p.2.1 p.2.2) = some true := by
  native_decide
theorem real_sel_sim : SimRefines selF' selG' := sim_of_checked real_sel_checked

end Opt.MidVal.AlgWitness
