import FVTest.Opt.MidValAlgWitness

/-! # The typed rules of the mid-end validator: witnesses (#1119 stage 2, the typed seam)

The validator's default normaliser `Norm.stdT f` is `Norm.std` (families 1–2), then the typed
rules (`typedStep (atomTy f)`, `FV/Opt/Proof/MidValNormTyped.lean`), which read an atom's static
type in `f`. For each rule: hand-made pairs accepted by the default and rejected by `Norm.std`
alone (`*_std_rejects`), and a look-alike that is rejected, no simulation, so the re-check
rejects every certificate (by `check_sound`).

* `selTyped`: `select (icmp eq x, 0), 0, 1` against Cranelift's `select x, 1, 0` with `x` an
  `i32` parameter: both are `uextend.i64 (icmp ne x, 0)` (`pos_sel`). The look-alike with the
  arms swapped, `uextend.i64 (icmp ne x, 0)` against `select x, 0, 1` (`icmp eq`), is rejected
  (`neg_sel`), no simulation (`sel_not_sim`: for `x = 1`, `f` returns 1, `g` 0), and every
  certificate is rejected (`sel_rejected`).
* `redTyped`: `ireduce.i16 (uextend.i64 x)` is `x` for an `i16` parameter `x` (`pos_red`),
  `uextend.i16 x` for an `i8` one (`pos_redU`), `ireduce.i16 x` for an `i32` one (`pos_redR`,
  through `sextend.i64`). The look-alike with an atom of another width, the same `f` with an
  `i32` parameter against `g` returning `x` itself, is rejected (`neg_red`), no simulation
  (`red_not_sim`: for `x = 0x10000`, `f` returns the `i16` `0`, `g` the `i32` `0x10000`), and
  every certificate is rejected (`red_rejected`).

**Real pairs** (crypto-bigint 0.7.11's test build, `FVTest/Opt/midval/real_typed_*.clif`), each
rejected by `Norm.std` alone, accepted by the re-check with the default normaliser (decided),
with the simulation and the program refinement from `check_sound` (`*_sim`):

* `red`: clap_builder's `_RNxC12clap_builder12HkDy5L79c8E7` (a drop glue of
  `io::error::ErrorData<CustomOwner>`): `br_table (ireduce.i32 (uextend.i64 (load.i8 …)))` is
  Cranelift's `br_table (uextend.i32 (load.i8 …))`;
* `sel`: clap_builder's `_RNxC12clap_builder12H7SppLYnbcG4` (`<Once<&str>>::size_hint`):
  `select (icmp eq (load.i64 …), 0), 0, 1` is Cranelift's `select (load.i64 …), 1, 0`. -/

namespace Opt.MidVal.TypedWitness

open Clif Pairs NormWitness AlgWitness

/-- The verdict with the untyped normaliser `Norm.std` (families 1–2). -/
def acceptsStd (f g : String) : Option Bool := do
  pure (check (ConstPhi.run (← fn? f)) (← fn? g) Norm.std).isOk

/-! ## Hand-made pairs -/

def selF : String := "function %f(i32) -> i64 {\nblock0(v0: i32):\n    v1 = iconst.i32 0\n    v2 = icmp eq v0, v1\n    v3 = iconst.i64 0\n    v4 = iconst.i64 1\n    v5 = select v2, v3, v4\n    return v5\n}"
def selG : String := "function %f(i32) -> i64 {\nblock0(v0: i32):\n    v3 = iconst.i64 1\n    v4 = iconst.i64 0\n    v5 = select v0, v3, v4\n    return v5\n}"
def selNegF : String := "function %f(i32) -> i64 {\nblock0(v0: i32):\n    v1 = iconst.i32 0\n    v2 = icmp ne v0, v1\n    v3 = uextend.i64 v2\n    return v3\n}"
def selNegG : String := "function %f(i32) -> i64 {\nblock0(v0: i32):\n    v3 = iconst.i64 0\n    v4 = iconst.i64 1\n    v5 = select v0, v3, v4\n    return v5\n}"

theorem pos_sel : accepts selF selG = some true := by native_decide
theorem pos_sel_std_rejects : acceptsStd selF selG = some false := by native_decide
theorem neg_sel : accepts selNegF selNegG = some false := by native_decide

def redF : String := "function %f(i16) -> i16 {\nblock0(v0: i16):\n    v1 = uextend.i64 v0\n    v2 = ireduce.i16 v1\n    return v2\n}"
def redG : String := "function %f(i16) -> i16 {\nblock0(v0: i16):\n    return v0\n}"
def redUF : String := "function %f(i8) -> i16 {\nblock0(v0: i8):\n    v1 = uextend.i64 v0\n    v2 = ireduce.i16 v1\n    return v2\n}"
def redUG : String := "function %f(i8) -> i16 {\nblock0(v0: i8):\n    v2 = uextend.i16 v0\n    return v2\n}"
def redRF : String := "function %f(i32) -> i16 {\nblock0(v0: i32):\n    v1 = sextend.i64 v0\n    v2 = ireduce.i16 v1\n    return v2\n}"
def redRG : String := "function %f(i32) -> i16 {\nblock0(v0: i32):\n    v2 = ireduce.i16 v0\n    return v2\n}"
def redNegF : String := "function %f(i32) -> i16 {\nblock0(v0: i32):\n    v1 = uextend.i64 v0\n    v2 = ireduce.i16 v1\n    return v2\n}"
def redNegG : String := "function %f(i32) -> i16 {\nblock0(v0: i32):\n    return v0\n}"

theorem pos_red : accepts redF redG = some true := by native_decide
theorem pos_red_std_rejects : acceptsStd redF redG = some false := by native_decide
theorem pos_redU : accepts redUF redUG = some true := by native_decide
theorem pos_redU_std_rejects : acceptsStd redUF redUG = some false := by native_decide
theorem pos_redR : accepts redRF redRG = some true := by native_decide
theorem pos_redR_std_rejects : acceptsStd redRF redRG = some false := by native_decide
theorem neg_red : accepts redNegF redNegG = some false := by native_decide

/-! ## The look-alikes are no simulations -/

def selNegFn : Function :=
  fn1 .i32 .i64 [{ results := [1], inst := .iconst .i32 0 },
    { results := [2], inst := .icmp .ne .i32 0 1 }, { results := [3], inst := .extend .uextend .i64 2 }] 3
def selNegGn : Function :=
  fn1 .i32 .i64 [{ results := [3], inst := .iconst .i64 0 }, { results := [4], inst := .iconst .i64 1 },
    { results := [5], inst := .select .i64 0 3 4 }] 5

def redNegFn : Function :=
  fn1 .i32 .i16 [{ results := [1], inst := .extend .uextend .i64 0 },
    { results := [2], inst := .ireduce .i16 1 }] 2
def redNegGn : Function := fn1 .i32 .i16 [] 0

theorem selNegF_text : fn? selNegF = some selNegFn := by native_decide
theorem selNegG_text : fn? selNegG = some selNegGn := by native_decide
theorem redNegF_text : fn? redNegF = some redNegFn := by native_decide
theorem redNegG_text : fn? redNegG = some redNegGn := by native_decide

theorem sel_not_sim : ¬ FunSimMU selNegFn selNegGn :=
  not_funSimMU_ret_ne (b := selNegFn.blocks.head!) (b' := selNegGn.blocks.head!)
    (args := [⟨.i32, 1⟩]) (regs := Regs.empty.set 0 ⟨.i32, 1⟩) (m := Mem.empty)
    (vals := [⟨.i64, 1⟩]) (vals' := [⟨.i64, 0⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.step rfl (.refl _ _)))) rfl
    (.step rfl (.step rfl (.step rfl (.refl _ _)))) rfl (by decide)

/-- The re-check rejects every certificate for `neg_sel`. -/
theorem sel_rejected (cert : Cert) :
    checkCert (ConstPhi.run selNegFn) selNegGn cert = false := by
  cases h : checkCert (ConstPhi.run selNegFn) selNegGn cert
  · rfl
  · exact absurd (checked_simMU h) sel_not_sim

theorem red_not_sim : ¬ FunSimMU redNegFn redNegGn :=
  not_funSimMU_ret_ne (b := redNegFn.blocks.head!) (b' := redNegGn.blocks.head!)
    (args := [⟨.i32, 0x10000⟩]) (regs := Regs.empty.set 0 ⟨.i32, 0x10000⟩) (m := Mem.empty)
    (vals := [⟨.i16, 0⟩]) (vals' := [⟨.i32, 0x10000⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.refl _ _))) rfl
    (.refl _ _) rfl (by decide)

/-- The re-check rejects every certificate for `neg_red`. -/
theorem red_rejected (cert : Cert) :
    checkCert (ConstPhi.run redNegFn) redNegGn cert = false := by
  cases h : checkCert (ConstPhi.run redNegFn) redNegGn cert
  · rfl
  · exact absurd (checked_simMU h) red_not_sim

/-! ## Real pairs -/

/-- The verdict of `Norm.std` alone on a decoded dump pair. -/
def stdVerdict (fT gT : String) : Option Bool := do
  let f ← RealWitness.decode fT
  let g ← RealWitness.decode gT
  pure (check (ConstPhi.run f) g Norm.std).isOk

def redF' : String := include_str "midval/real_typed_red.unopt.clif"
def redG' : String := include_str "midval/real_typed_red.opt.clif"
def selF' : String := include_str "midval/real_typed_sel.unopt.clif"
def selG' : String := include_str "midval/real_typed_sel.opt.clif"

theorem real_red_std_rejects : stdVerdict redF' redG' = some false := by native_decide
theorem real_red_checked :
    ((pairD redF' redG').map fun p => checkCert (ConstPhi.run p.1) p.2.1 p.2.2) = some true := by
  native_decide
theorem real_red_sim : SimRefines redF' redG' := sim_of_checked real_red_checked

theorem real_sel_std_rejects : stdVerdict selF' selG' = some false := by native_decide
theorem real_sel_checked :
    ((pairD selF' selG').map fun p => checkCert (ConstPhi.run p.1) p.2.1 p.2.2) = some true := by
  native_decide
theorem real_sel_sim : SimRefines selF' selG' := sim_of_checked real_sel_checked

end Opt.MidVal.TypedWitness
