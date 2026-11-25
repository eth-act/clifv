import FVTest.Opt.MidValZeroWitness
import FVTest.Opt.MidValFam4Witness
import FV.Opt.Proof.MidValCondProg

/-! # Family 5, swapped unit comparisons and parameters kept after the folds: witnesses (#1119, agent MidendNext3)

Three changes to the mid-end validator (#1119 issuecomment-7165335641):

* **Family 5** (`fam5Step`, the last step of `Norm.base`; `FV/Opt/Proof/MidValNormFam5.lean`):
  `x + (-y)` is `x - y` (`pos_addNeg`), `(-x) * 3` is `x * (-3)` (`pos_mulNeg`), `ireduce.i16
  (ireduce.i32 x)` of an `i64` `x` is `ireduce.i16 x` (`pos_redRed`); each rejected with main's
  normaliser (`normPrev`, `*_prev_rejects`). Look-alikes rejected and no simulation, so the
  re-check rejects every certificate: `x + (-y)` against `y - x` (`neg_addNeg`), `(-x) * 3`
  against `x * 3` (`neg_mulNeg`), the inner truncation dropped (`neg_redRed`). The typing premise
  of `redRed` is needed: it is no normaliser sound in every frame (`redRed_not_normSound`: a
  parameter declared `i64` holding an `i32` makes the inner `ireduce.i32` have no value, while
  `ireduce.i16` of it has one).
* **Swapped unit comparisons** (`icmpSwapUnit` in `algStep2`): `brif (icmp ult 0, x)` against
  `brif x` (`pos_swapU`): with main's normaliser the comparison became `icmp ugt x, 0` while the
  branch-condition copy of `g` rebuilt `icmp ugt x, 0`, normalised to `icmp ne x, 0`, so the
  re-check of the hints failed (`pos_swapU_prev_rejects`). Look-alike: `icmp ult 1, x` (`x >u 1`)
  against `brif x` is rejected (`neg_swapU`), no simulation, every certificate with every hint
  list rejected (`swapU1_rejected`).
* **Parameters kept after the folds** (`foldPreK`, tried by `checkCertC` after `foldPre`;
  `foldPreK_simU`): `block3(v3)` receives `7` from `block1` and `v0` from `block2`; the branch to
  `block1` folds away and Cranelift keeps the parameter (its constant-phi removal ran before), as
  `foldPreK` does, while `foldPre`'s final `ConstPhi.run` removes it (`pos_keep`,
  `keep_c0_rejects`, `keep_foldPre_rejects`, `keep_foldPreK_accepts`). Look-alike: `g` passing
  the folded-away `7` (`neg_keep`, `keep7_rejected`).
-/

namespace Opt.MidVal.Fam5Witness
open Clif Pairs NormWitness AlgWitness CondWitness FoldWitness ZeroWitness Fam4Witness

/-! ## Main's normaliser (before this change) -/

/-- `algStep2` without `icmpSwapUnit`. -/
def algStep2Prev (tms : Array Tm) : Inst → Option Tm
  | .icmp cc ty a b =>
    (icmpSwap tms cc ty a b).orElse fun _ => (icmpBool tms cc ty a b).orElse fun _ =>
      icmpUnit tms cc ty a b
  | i => algStep2 tms i

/-- `Norm.base` with `algStep2Prev` and without family 5. -/
def basePrev (f : Function) : Norm :=
  Norm.orElse
    (Norm.orElse (Norm.orElse evalConst (Norm.orElse (Norm.guard algStep2Prev) Norm.alg))
      (Norm.guard (typedStep (atomTy f))))
    (Norm.orElse (Norm.guard (idStep (atomTy f)))
      (Norm.orElse (Norm.guard affStep) (Norm.guard swapStep)))

def narrowPrev (f : Function) : Nat → Norm
  | 0 => basePrev f
  | k + 1 => Norm.orElse (basePrev f) (Norm.guard (narrowStep (narrowPrev f k) (atomTy f)))

/-- Main's default normaliser before this change. -/
def normPrev (f : Function) : Norm := narrowPrev f 3

/-- The verdict of `check` with main's normaliser. -/
def acceptsPrev (f g : String) : Option Bool := do
  let f' := ConstPhi.run (← fn? f)
  pure (check f' (← fn? g) (normPrev f')).isOk

/-- The verdict of `checkC0` (branch-condition hints, no folds) with main's normaliser. -/
def acceptsC0Prev (f g : String) : Option Bool := do
  let f' := ConstPhi.run (← fn? f)
  pure (checkC0 f' (← fn? g) (normPrev f')).isOk

/-! ## Family 5 -/

def addNegF : String := "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    v2 = ineg v1\n    v3 = iadd v0, v2\n    return v3\n}"
def addNegG : String := "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    v3 = isub v0, v1\n    return v3\n}"
def addNegWrongG : String := "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    v3 = isub v1, v0\n    return v3\n}"

theorem pos_addNeg : accepts addNegF addNegG = some true := by native_decide
theorem pos_addNeg_prev_rejects : acceptsPrev addNegF addNegG = some false := by native_decide
theorem neg_addNeg : accepts addNegF addNegWrongG = some false := by native_decide

def mulNegF : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = ineg v0\n    v2 = iconst.i64 3\n    v3 = imul v1, v2\n    return v3\n}"
def mulNegG : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v4 = iconst.i64 -3\n    v3 = imul v0, v4\n    return v3\n}"
def mulNegWrongG : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v4 = iconst.i64 3\n    v3 = imul v0, v4\n    return v3\n}"

theorem pos_mulNeg : accepts mulNegF mulNegG = some true := by native_decide
theorem pos_mulNeg_prev_rejects : acceptsPrev mulNegF mulNegG = some false := by native_decide
theorem neg_mulNeg : accepts mulNegF mulNegWrongG = some false := by native_decide

def redRedF : String := "function %f(i64) -> i16 {\nblock0(v0: i64):\n    v1 = ireduce.i32 v0\n    v2 = ireduce.i16 v1\n    return v2\n}"
def redRedG : String := "function %f(i64) -> i16 {\nblock0(v0: i64):\n    v2 = ireduce.i16 v0\n    return v2\n}"
def redDropF : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = ireduce.i32 v0\n    v2 = ireduce.i16 v1\n    v3 = uextend.i64 v2\n    return v3\n}"
def redDropG : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = ireduce.i32 v0\n    v3 = uextend.i64 v1\n    return v3\n}"

theorem pos_redRed : accepts redRedF redRedG = some true := by native_decide
theorem pos_redRed_prev_rejects : acceptsPrev redRedF redRedG = some false := by native_decide
theorem neg_redRed : accepts redDropF redDropG = some false := by native_decide

/-! ### The look-alikes are no simulations -/

/-- A two-parameter `i64` function of one block returning `r`. -/
def fn2b (body : List Stmt) (r : ValueId) : Function :=
  { name := "f", sig := { params := [ap .i64, ap .i64], returns := [ap .i64], callConv := none },
    blocks := [{ id := 0, params := [(0, .i64), (1, .i64)], cold := false, body, term := .ret [r] }] }

def addNegFn : Function :=
  fn2b [{ results := [2], inst := .unary .ineg .i64 1 },
    { results := [3], inst := .binary .iadd .i64 0 2 }] 3
def addNegWrongGn : Function := fn2b [{ results := [3], inst := .binary .isub .i64 1 0 }] 3

theorem addNegF_text : fn? addNegF = some addNegFn := by native_decide
theorem addNegWrongG_text : fn? addNegWrongG = some addNegWrongGn := by native_decide

/-- For `x = 0`, `y = 1`: `f` returns `-1`, `g` 1. -/
theorem addNeg_not_sim : ¬ FunSimMU addNegFn addNegWrongGn :=
  not_funSimMU_ret_ne (b := addNegFn.blocks.head!) (b' := addNegWrongGn.blocks.head!)
    (args := [⟨.i64, 0⟩, ⟨.i64, 1⟩])
    (regs := (Regs.empty.set 0 ⟨.i64, 0⟩).set 1 ⟨.i64, 1⟩) (m := Mem.empty)
    (vals := [⟨.i64, -1⟩]) (vals' := [⟨.i64, 1⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.refl _ _))) rfl (.step rfl (.refl _ _)) rfl
    (by decide)

/-- The re-check rejects every certificate for `neg_addNeg`. -/
theorem addNeg_rejected (cert : Cert) :
    checkCert (ConstPhi.run addNegFn) addNegWrongGn cert = false := by
  cases h : checkCert (ConstPhi.run addNegFn) addNegWrongGn cert
  · rfl
  · exact absurd (checked_simMU h) addNeg_not_sim

def mulNegFn : Function :=
  fn1 .i64 .i64 [{ results := [1], inst := .unary .ineg .i64 0 },
    { results := [2], inst := .iconst .i64 3 }, { results := [3], inst := .binary .imul .i64 1 2 }] 3
def mulNegWrongGn : Function :=
  fn1 .i64 .i64 [{ results := [4], inst := .iconst .i64 3 },
    { results := [3], inst := .binary .imul .i64 0 4 }] 3

theorem mulNegF_text : fn? mulNegF = some mulNegFn := by native_decide
theorem mulNegWrongG_text : fn? mulNegWrongG = some mulNegWrongGn := by native_decide

/-- For `x = 1`: `f` returns `-3`, `g` 3. -/
theorem mulNeg_not_sim : ¬ FunSimMU mulNegFn mulNegWrongGn :=
  not_funSimMU_ret_ne (b := mulNegFn.blocks.head!) (b' := mulNegWrongGn.blocks.head!)
    (args := [⟨.i64, 1⟩]) (regs := Regs.empty.set 0 ⟨.i64, 1⟩) (m := Mem.empty)
    (vals := [⟨.i64, -3⟩]) (vals' := [⟨.i64, 3⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.step rfl (.refl _ _)))) rfl
    (.step rfl (.step rfl (.refl _ _))) rfl (by decide)

/-- The re-check rejects every certificate for `neg_mulNeg`. -/
theorem mulNeg_rejected (cert : Cert) :
    checkCert (ConstPhi.run mulNegFn) mulNegWrongGn cert = false := by
  cases h : checkCert (ConstPhi.run mulNegFn) mulNegWrongGn cert
  · rfl
  · exact absurd (checked_simMU h) mulNeg_not_sim

def redDropFn : Function :=
  fn1 .i64 .i64 [{ results := [1], inst := .ireduce .i32 0 },
    { results := [2], inst := .ireduce .i16 1 }, { results := [3], inst := .extend .uextend .i64 2 }] 3
def redDropGn : Function :=
  fn1 .i64 .i64 [{ results := [1], inst := .ireduce .i32 0 },
    { results := [3], inst := .extend .uextend .i64 1 }] 3

theorem redDropF_text : fn? redDropF = some redDropFn := by native_decide
theorem redDropG_text : fn? redDropG = some redDropGn := by native_decide

/-- For `x = 0x10000`: `f` returns 0, `g` `0x10000`. -/
theorem redDrop_not_sim : ¬ FunSimMU redDropFn redDropGn :=
  not_funSimMU_ret_ne (b := redDropFn.blocks.head!) (b' := redDropGn.blocks.head!)
    (args := [⟨.i64, 0x10000⟩]) (regs := Regs.empty.set 0 ⟨.i64, 0x10000⟩) (m := Mem.empty)
    (vals := [⟨.i64, 0⟩]) (vals' := [⟨.i64, 0x10000⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.step rfl (.refl _ _)))) rfl
    (.step rfl (.step rfl (.refl _ _))) rfl (by decide)

/-- The re-check rejects every certificate for `neg_redRed`. -/
theorem redDrop_rejected (cert : Cert) :
    checkCert (ConstPhi.run redDropFn) redDropGn cert = false := by
  cases h : checkCert (ConstPhi.run redDropFn) redDropGn cert
  · rfl
  · exact absurd (checked_simMU h) redDrop_not_sim

/-! ### The typing premise of `redRed` is needed -/

def redTms : Array Tm := #[.param 0 0, .node (.ireduce .i32 0), .node (.ireduce .i16 0)]

theorem redRed_fires :
    Norm.guard (fam5Step (atomTy fn2)) redTms (.ireduce .i16 1) =
      some (.node (.ireduce .i16 0)) := by
  native_decide

theorem redRed_frame :
    tmVal fn2 redTms (fr2 ⟨.i32, 7⟩ ⟨.i64, 0⟩) Mem.empty 2 ≠
      evalNode (tmFrame fn2 redTms (fr2 ⟨.i32, 7⟩ ⟨.i64, 0⟩) Mem.empty) Mem.empty
        (.ireduce .i16 1) := by
  native_decide

/-- `redRed` is no normaliser sound in every frame (a parameter declared `i64` holding an `i32`:
the inner `ireduce.i32` has no value, `ireduce.i16` of the parameter has one). -/
theorem redRed_not_normSound : ¬ NormSound (Norm.guard (fam5Step (atomTy fn2))) := fun h =>
  redRed_frame (h redTms _ _ redRed_fires fn2 (fr2 ⟨.i32, 7⟩ ⟨.i64, 0⟩) Mem.empty 2 rfl)

/-! ## Swapped unit comparisons -/

def swapUG : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    brif v0, block1, block2\n\nblock1:\n    v4 = iconst.i32 1\n    return v4\n\nblock2:\n    v5 = iconst.i32 0\n    return v5\n}"

/-- `brif (icmp ult 0, v0)` against `brif v0`. -/
theorem pos_swapU : acceptsC (cmpText "ult" "v1" "v0") swapUG = some true := by native_decide
theorem pos_swapU_prev_rejects : acceptsC0Prev (cmpText "ult" "v1" "v0") swapUG = some false := by
  native_decide
theorem pos_swapU_check_rejects : accepts (cmpText "ult" "v1" "v0") swapUG = some false := by
  native_decide

/-- `brif (icmp ult 1, v0)` (`v0 >u 1`) against `brif v0`. -/
theorem neg_swapU : acceptsC (cmpText "ult" "v1" "v0" "1") swapUG = some false := by native_decide

theorem swapU1F_text : fn? (cmpText "ult" "v1" "v0" "1") = some (cmpFn .ult 1 0 1) := by
  native_decide
theorem swapUG_text : fn? swapUG = some (fnBr2 [] 0) := by native_decide

/-- For `v0 = 1`, `f` returns 0 and `g` 1. -/
theorem swapU1_not_sim : ¬ FunSimMU (cmpFn .ult 1 0 1) (fnBr2 [] 0) :=
  not_funSimMU_ret_ne (b := (cmpFn .ult 1 0 1).blocks.head!) (b' := (fnBr2 [] 0).blocks.head!)
    (args := [⟨.i32, 1⟩]) (regs := Regs.empty.set 0 ⟨.i32, 1⟩) (m := Mem.empty)
    (vals := [⟨.i32, 0⟩]) (vals' := [⟨.i32, 1⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.step rfl (.step rfl (.refl _ _))))) rfl
    (.step rfl (.step rfl (.refl _ _))) rfl (by decide)

/-- The re-check rejects every certificate and every hint list (prep requests included). -/
theorem swapU1_rejected (cert : Cert) (hints : List (BlockId × List Wrap)) :
    checkCertC (ConstPhi.run (cmpFn .ult 1 0 1)) (fnBr2 [] 0) cert hints = false := by
  cases h : checkCertC (ConstPhi.run (cmpFn .ult 1 0 1)) (fnBr2 [] 0) cert hints
  · rfl
  · exact absurd (checkedC_simMU h) swapU1_not_sim

/-! ## Parameters kept after the folds -/

def keepF : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    v1 = iconst.i32 0\n    brif v1, block1, block2\n\nblock1:\n    v2 = iconst.i32 7\n    jump block3(v2)\n\nblock2:\n    jump block3(v0)\n\nblock3(v3: i32):\n    return v3\n}"
def keepG : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    jump block2\n\nblock2:\n    jump block3(v0)\n\nblock3(v3: i32):\n    return v3\n}"
def keep7G : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    jump block2\n\nblock2:\n    v2 = iconst.i32 7\n    jump block3(v2)\n\nblock3(v3: i32):\n    return v3\n}"

/-- The verdict of `checkC0` on a prepared copy `prep (ConstPhi.run f) [0]` of `f`. -/
def prepVerdict (prep : Function → List BlockId → Function) (f g : String) : Option Bool := do
  pure (checkC0 (prep (ConstPhi.run (← fn? f)) [0]) (← fn? g)).isOk

theorem pos_keep : acceptsC keepF keepG = some true := by native_decide
theorem keep_c0_rejects : acceptsC0 keepF keepG = some false := by native_decide
theorem keep_foldPre_rejects : prepVerdict foldPre keepF keepG = some false := by native_decide
theorem keep_foldPreK_accepts : prepVerdict foldPreK keepF keepG = some true := by native_decide
theorem neg_keep : acceptsC keepF keep7G = some false := by native_decide

def keepFn : Function :=
  { name := "f", sig := { params := [ap .i32], returns := [ap .i32], callConv := none },
    blocks := [
      { id := 0, params := [(0, .i32)], cold := false,
        body := [{ results := [1], inst := .iconst .i32 0 }], term := .brif 1 ⟨1, []⟩ ⟨2, []⟩ },
      { id := 1, params := [], cold := false,
        body := [{ results := [2], inst := .iconst .i32 7 }], term := .jump ⟨3, [2]⟩ },
      { id := 2, params := [], cold := false, body := [], term := .jump ⟨3, [0]⟩ },
      { id := 3, params := [(3, .i32)], cold := false, body := [], term := .ret [3] }] }

def keep7Gn : Function :=
  { name := "f", sig := { params := [ap .i32], returns := [ap .i32], callConv := none },
    blocks := [
      { id := 0, params := [(0, .i32)], cold := false, body := [], term := .jump ⟨2, []⟩ },
      { id := 2, params := [], cold := false,
        body := [{ results := [2], inst := .iconst .i32 7 }], term := .jump ⟨3, [2]⟩ },
      { id := 3, params := [(3, .i32)], cold := false, body := [], term := .ret [3] }] }

theorem keepF_text : fn? keepF = some keepFn := by native_decide
theorem keep7G_text : fn? keep7G = some keep7Gn := by native_decide

/-- For `v0 = 0`, `f` returns 0 and `g` 7. -/
theorem keep7_not_sim : ¬ FunSimMU keepFn keep7Gn :=
  not_funSimMU_ret_ne (b := keepFn.blocks.head!) (b' := keep7Gn.blocks.head!)
    (args := [⟨.i32, 0⟩]) (regs := Regs.empty.set 0 ⟨.i32, 0⟩) (m := Mem.empty)
    (vals := [⟨.i32, 0⟩]) (vals' := [⟨.i32, 7⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.step rfl (.refl _ _)))) rfl
    (.step rfl (.step rfl (.step rfl (.refl _ _)))) rfl (by decide)

/-- The re-check rejects every certificate and every hint list (prep requests included). -/
theorem keep7_rejected (cert : Cert) (hints : List (BlockId × List Wrap)) :
    checkCertC (ConstPhi.run keepFn) keep7Gn cert hints = false := by
  cases h : checkCertC (ConstPhi.run keepFn) keep7Gn cert hints
  · rfl
  · exact absurd (checkedC_simMU h) keep7_not_sim

/-! ## Real pairs

crypto-bigint 0.7.11's test build in the shared #1119 corpus (`FVTest/Opt/midval/real_fam5_*.clif`),
each rejected by main's checker and accepted by `checkCertC` with the requests `emitC` gives
(decided), with the simulation and the program refinement:

* `swapu`: criterion_plot's `_RNxC14criterion_plot12HlvmxBvKJBcj`: `brif (icmp ult 0, v2)` →
  `brif v2` (rejected by `checkC0` with main's normaliser);
* `keep`: criterion's `_RNxC9criterion12H84QfGq6mN3g`: a parameter that receives one value once
  the folded branch is gone, kept by Cranelift (rejected by `checkC0` and by `checkC0` on
  `foldPre`'s copy);
* `addneg`: crossbeam_utils' `_RNxC15crossbeam_utils12Hhguywabqfqx`: `iadd x, (ineg y)` →
  `isub x, y`;
* `mulneg`: criterion's `_RNxC9criterion12H8igFZrLuENJ`: `imul (ineg x), 72` → `imul x, -72`;
* `redred`: criterion's `_RNxC9criterion12HanQREEPIKDl`: `br_table (ireduce.i32 (ireduce.i64
  (load.i128 …)))` → `br_table (ireduce.i32 (load.i128 …))`.
-/

def swapuF : String := include_str "midval/real_fam5_swapu.unopt.clif"
def swapuG : String := include_str "midval/real_fam5_swapu.opt.clif"
def keepF' : String := include_str "midval/real_fam5_keep.unopt.clif"
def keepG' : String := include_str "midval/real_fam5_keep.opt.clif"
def addnegF : String := include_str "midval/real_fam5_addneg.unopt.clif"
def addnegG : String := include_str "midval/real_fam5_addneg.opt.clif"
def mulnegF : String := include_str "midval/real_fam5_mulneg.unopt.clif"
def mulnegG : String := include_str "midval/real_fam5_mulneg.opt.clif"
def redredF : String := include_str "midval/real_fam5_redred.unopt.clif"
def redredG : String := include_str "midval/real_fam5_redred.opt.clif"

/-- The verdict of `checkC0` with main's normaliser on a decoded dump pair. -/
def c0VerdictPrev (fT gT : String) : Option Bool := do
  let f := ConstPhi.run (← RealWitness.decode fT)
  let g ← RealWitness.decode gT
  pure (checkC0 f g (normPrev f)).isOk

/-- The verdict of `checkC0` on `foldPre`'s copy for `checkC`'s requests (`foldCands`). -/
def foldPreVerdict (fT gT : String) : Option Bool := do
  let f := ConstPhi.run (← RealWitness.decode fT)
  let g ← RealWitness.decode gT
  pure (checkC0 (foldPre f (foldCands f g)) g).isOk

theorem real_swapu_prev_rejects : c0VerdictPrev swapuF swapuG = some false := by native_decide
theorem real_swapu_checked : checkedC swapuF swapuG = some (true, true) := by native_decide
theorem real_swapu_sim : SimRefinesC swapuF swapuG := simC_of_checked real_swapu_checked

theorem real_keep_c0_rejects : c0Verdict keepF' keepG' = some false := by native_decide
theorem real_keep_foldPre_rejects : foldPreVerdict keepF' keepG' = some false := by native_decide
theorem real_keep_checked : checkedC keepF' keepG' = some (true, true) := by native_decide
theorem real_keep_sim : SimRefinesC keepF' keepG' := simC_of_checked real_keep_checked

theorem real_addneg_prev_rejects : c0VerdictPrev addnegF addnegG = some false := by native_decide
theorem real_addneg_checked : checkedC addnegF addnegG = some (true, false) := by native_decide
theorem real_addneg_sim : SimRefinesC addnegF addnegG := simC_of_checked real_addneg_checked

theorem real_mulneg_prev_rejects : c0VerdictPrev mulnegF mulnegG = some false := by native_decide
theorem real_mulneg_checked : checkedC mulnegF mulnegG = some (true, false) := by native_decide
theorem real_mulneg_sim : SimRefinesC mulnegF mulnegG := simC_of_checked real_mulneg_checked

theorem real_redred_prev_rejects : c0VerdictPrev redredF redredG = some false := by native_decide
theorem real_redred_checked : checkedC redredF redredG = some (true, false) := by native_decide
theorem real_redred_sim : SimRefinesC redredF redredG := simC_of_checked real_redred_checked

end Opt.MidVal.Fam5Witness
