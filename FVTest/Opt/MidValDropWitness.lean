import FVTest.Opt.MidValFam6Witness

/-! # Family 7, operand-dropping rewrites: witnesses (#1119, agent MidendNext7)

Family 7 of the mid-end validator's normaliser (`dropStep`, the last step of `Norm.stdD`,
`FV/Opt/MidVal.lean`; proofs `FV/Opt/Proof/MidValNormDrop.lean`). Each hand-made pair is
accepted, and rejected with main's normaliser before this change (`Norm.stdT`,
`*_prev_rejects`):

* `subAdd`: `(x + y) - x` against `y` (`pos_subAdd`);
* `addSub`: `(x - y) + y` against `x` (`pos_addSub`);
* `absTyped`: `x * 0` against `0` (`pos_mul0`), `x | -1` against `-1` (`pos_orOnes`).

Look-alikes are rejected (`neg_*`) and are no simulations, so the re-check rejects every
certificate (`*_rejected`). The rules are not `NormSoundT` rules (`dropStep_not_normSoundT`: in
a frame where `x` has no value, `(x + y) - x` has none and `y` has one), which is why their
obligation is `NormSoundD` (the node's operands have values).

Real pairs (decided: rejected by main's `checkC`, accepted by `checkCertC` with the requests
`emitC` gives, with the simulation and the program refinement) are at the end.
-/

namespace Opt.MidVal.DropWitness
open Clif Pairs NormWitness AlgWitness CondWitness FoldWitness

/-! ## Main's normaliser (before this change) -/

/-- The verdict of `check` with main's normaliser `Norm.stdT`. -/
def acceptsPrev (f g : String) : Option Bool := do
  let f' := ConstPhi.run (← fn? f)
  pure (check f' (← fn? g) (Norm.stdT f')).isOk

/-- `checkC` with main's normaliser (the same steps: hints, then the prep copies `foldPre` and
`foldPreK` for `foldCands`). -/
def checkCPrev (f g : Function) : Except Reject (List (BlockId × List Wrap)) :=
  match checkC0 f g (Norm.stdT f) with
  | .ok h => .ok h
  | .error e =>
    let bs := match foldCands f g with
      | [] => (f.blocks.head?.map (·.id)).toList
      | bs => bs
    let prep (f' : Function) : Except Reject (List (BlockId × List Wrap)) :=
      if f'.blocks == f.blocks then .error e
      else if f'.blocks.map (·.id) != g.blocks.map (·.id) then .error e
      else match checkC0 f' g (Norm.stdT f') with
        | .ok h => .ok (h ++ bs.map fun b => (b, []))
        | .error e' => .error e'
    if bs.isEmpty then .error e
    else match prep (foldPre f bs) with
      | .ok h => .ok h
      | .error _ => prep (foldPreK f bs)

/-- The verdict of `checkCPrev` on a decoded dump pair. -/
def realPrev (fT gT : String) : Option Bool := do
  let f := ConstPhi.run (← RealWitness.decode fT)
  let g ← RealWitness.decode gT
  pure (checkCPrev f g).isOk

/-! ## Hand-made pairs -/

def subAddF : String := "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    v2 = iadd v0, v1\n    v3 = isub v2, v0\n    return v3\n}"
def subAddG : String := "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    return v1\n}"
def subAddWrongG : String := "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    return v0\n}"

theorem pos_subAdd : accepts subAddF subAddG = some true := by native_decide
theorem pos_subAdd_prev_rejects : acceptsPrev subAddF subAddG = some false := by native_decide
theorem neg_subAdd : accepts subAddF subAddWrongG = some false := by native_decide

def addSubF : String := "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    v2 = isub v0, v1\n    v3 = iadd v2, v1\n    return v3\n}"
def addSubG : String := "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    return v0\n}"
def addSubWrongG : String := "function %f(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    return v1\n}"

theorem pos_addSub : accepts addSubF addSubG = some true := by native_decide
theorem pos_addSub_prev_rejects : acceptsPrev addSubF addSubG = some false := by native_decide
theorem neg_addSub : accepts addSubF addSubWrongG = some false := by native_decide

def mul0F : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 0\n    v2 = imul v0, v1\n    return v2\n}"
def mul0G : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v3 = iconst.i64 0\n    return v3\n}"
def mul0WrongG : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    return v0\n}"

theorem pos_mul0 : accepts mul0F mul0G = some true := by native_decide
theorem pos_mul0_prev_rejects : acceptsPrev mul0F mul0G = some false := by native_decide
theorem neg_mul0 : accepts mul0F mul0WrongG = some false := by native_decide

def orOnesF : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 -1\n    v2 = bor v0, v1\n    return v2\n}"
def orOnesG : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v3 = iconst.i64 -1\n    return v3\n}"
def orOnesWrongG : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v3 = iconst.i64 0\n    return v3\n}"

theorem pos_orOnes : accepts orOnesF orOnesG = some true := by native_decide
theorem pos_orOnes_prev_rejects : acceptsPrev orOnesF orOnesG = some false := by native_decide
theorem neg_orOnes : accepts orOnesF orOnesWrongG = some false := by native_decide

/-! ### The look-alikes are no simulations -/

def subAddFn : Function :=
  Fam5Witness.fn2b [{ results := [2], inst := .binary .iadd .i64 0 1 },
    { results := [3], inst := .binary .isub .i64 2 0 }] 3
def subAddWrongGn : Function := Fam5Witness.fn2b [] 0

theorem subAddF_text : fn? subAddF = some subAddFn := by native_decide
theorem subAddWrongG_text : fn? subAddWrongG = some subAddWrongGn := by native_decide

/-- For `x = 1`, `y = 2`: `f` returns 2, `g` 1. -/
theorem subAdd_not_sim : ¬ FunSimMU subAddFn subAddWrongGn :=
  not_funSimMU_ret_ne (b := subAddFn.blocks.head!) (b' := subAddWrongGn.blocks.head!)
    (args := [⟨.i64, 1⟩, ⟨.i64, 2⟩])
    (regs := (Regs.empty.set 0 ⟨.i64, 1⟩).set 1 ⟨.i64, 2⟩) (m := Mem.empty)
    (vals := [⟨.i64, 2⟩]) (vals' := [⟨.i64, 1⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.refl _ _))) rfl (.refl _ _) rfl
    (by decide)

/-- The re-check rejects every certificate for `neg_subAdd`. -/
theorem subAdd_rejected (cert : Cert) :
    checkCert (ConstPhi.run subAddFn) subAddWrongGn cert = false := by
  cases h : checkCert (ConstPhi.run subAddFn) subAddWrongGn cert
  · rfl
  · exact absurd (checked_simMU h) subAdd_not_sim

def addSubFn : Function :=
  Fam5Witness.fn2b [{ results := [2], inst := .binary .isub .i64 0 1 },
    { results := [3], inst := .binary .iadd .i64 2 1 }] 3
def addSubWrongGn : Function := Fam5Witness.fn2b [] 1

theorem addSubF_text : fn? addSubF = some addSubFn := by native_decide
theorem addSubWrongG_text : fn? addSubWrongG = some addSubWrongGn := by native_decide

/-- For `x = 1`, `y = 2`: `f` returns 1, `g` 2. -/
theorem addSub_not_sim : ¬ FunSimMU addSubFn addSubWrongGn :=
  not_funSimMU_ret_ne (b := addSubFn.blocks.head!) (b' := addSubWrongGn.blocks.head!)
    (args := [⟨.i64, 1⟩, ⟨.i64, 2⟩])
    (regs := (Regs.empty.set 0 ⟨.i64, 1⟩).set 1 ⟨.i64, 2⟩) (m := Mem.empty)
    (vals := [⟨.i64, 1⟩]) (vals' := [⟨.i64, 2⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.refl _ _))) rfl (.refl _ _) rfl
    (by decide)

/-- The re-check rejects every certificate for `neg_addSub`. -/
theorem addSub_rejected (cert : Cert) :
    checkCert (ConstPhi.run addSubFn) addSubWrongGn cert = false := by
  cases h : checkCert (ConstPhi.run addSubFn) addSubWrongGn cert
  · rfl
  · exact absurd (checked_simMU h) addSub_not_sim

def mul0Fn : Function :=
  fn1 .i64 .i64 [{ results := [1], inst := .iconst .i64 0 },
    { results := [2], inst := .binary .imul .i64 0 1 }] 2
def mul0WrongGn : Function := fn1 .i64 .i64 [] 0

theorem mul0F_text : fn? mul0F = some mul0Fn := by native_decide
theorem mul0WrongG_text : fn? mul0WrongG = some mul0WrongGn := by native_decide

/-- For `x = 1`: `f` returns 0, `g` 1. -/
theorem mul0_not_sim : ¬ FunSimMU mul0Fn mul0WrongGn :=
  not_funSimMU_ret_ne (b := mul0Fn.blocks.head!) (b' := mul0WrongGn.blocks.head!)
    (args := [⟨.i64, 1⟩]) (regs := Regs.empty.set 0 ⟨.i64, 1⟩) (m := Mem.empty)
    (vals := [⟨.i64, 0⟩]) (vals' := [⟨.i64, 1⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.refl _ _))) rfl (.refl _ _) rfl (by decide)

/-- The re-check rejects every certificate for `neg_mul0`. -/
theorem mul0_rejected (cert : Cert) :
    checkCert (ConstPhi.run mul0Fn) mul0WrongGn cert = false := by
  cases h : checkCert (ConstPhi.run mul0Fn) mul0WrongGn cert
  · rfl
  · exact absurd (checked_simMU h) mul0_not_sim

def orOnesFn : Function :=
  fn1 .i64 .i64 [{ results := [1], inst := .iconst .i64 (-1) },
    { results := [2], inst := .binary .bor .i64 0 1 }] 2
def orOnesWrongGn : Function := fn1 .i64 .i64 [{ results := [3], inst := .iconst .i64 0 }] 3

theorem orOnesF_text : fn? orOnesF = some orOnesFn := by native_decide
theorem orOnesWrongG_text : fn? orOnesWrongG = some orOnesWrongGn := by native_decide

/-- For `x = 1`: `f` returns `-1`, `g` 0. -/
theorem orOnes_not_sim : ¬ FunSimMU orOnesFn orOnesWrongGn :=
  not_funSimMU_ret_ne (b := orOnesFn.blocks.head!) (b' := orOnesWrongGn.blocks.head!)
    (args := [⟨.i64, 1⟩]) (regs := Regs.empty.set 0 ⟨.i64, 1⟩) (m := Mem.empty)
    (vals := [⟨.i64, -1⟩]) (vals' := [⟨.i64, 0⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.refl _ _))) rfl (.step rfl (.refl _ _)) rfl
    (by decide)

/-- The re-check rejects every certificate for `neg_orOnes`. -/
theorem orOnes_rejected (cert : Cert) :
    checkCert (ConstPhi.run orOnesFn) orOnesWrongGn cert = false := by
  cases h : checkCert (ConstPhi.run orOnesFn) orOnesWrongGn cert
  · rfl
  · exact absurd (checked_simMU h) orOnes_not_sim

/-! ### The rules are not `NormSoundT` rules -/

def dropTms : Array Tm := #[.param 0 0, .param 0 1, .node (.binary .iadd .i64 0 1)]

/-- A frame of `Fam4Witness.fn2` where `x` (`v0`) has no value and `y` (`v1`) is 5. -/
def frD : Frame :=
  { func := Fam4Witness.fn2, regs := Regs.empty.set 1 ⟨.i64, 5⟩, slots := [], body := [],
    term := .ret [] }

theorem dropStep_fires :
    Norm.guard (dropStep (atomTy Fam4Witness.fn2)) dropTms (.binary .isub .i64 2 0) =
      some (.param 0 1) := by
  native_decide

theorem drop_frame :
    tmVal Fam4Witness.fn2 dropTms frD Mem.empty 1 ≠
      evalNode (tmFrame Fam4Witness.fn2 dropTms frD Mem.empty) Mem.empty (.binary .isub .i64 2 0) := by
  native_decide

theorem drop_val0 : tmVal Fam4Witness.fn2 dropTms frD Mem.empty 0 = none := by native_decide

theorem drop_val1 : tmVal Fam4Witness.fn2 dropTms frD Mem.empty 1 = some ⟨.i64, 5⟩ := by
  native_decide

theorem drop_ty1 : atomTy Fam4Witness.fn2 (.param 0 1) = some .i64 := by native_decide

/-- The atoms below the node are typed in `frD`: `x` has no value, `y` holds an `i64`. -/
theorem drop_atomsTyped :
    AtomsTyped Fam4Witness.fn2 dropTms frD Mem.empty (.binary .isub .i64 2 0) := by
  intro u a ty v _ hu hty hv
  rcases u with _ | _ | _ | u
  · rw [drop_val0] at hv
    cases hv
  · have h1 : dropTms[1]? = some (.param 0 1) := rfl
    rw [h1] at hu
    cases hu
    rw [drop_ty1] at hty
    cases hty
    rw [drop_val1] at hv
    cases hv
    rfl
  · have h2 : dropTms[2]? = some (.node (.binary .iadd .i64 0 1)) := rfl
    rw [h2] at hu
    cases hu
    simp [atomTy] at hty
  · have h3 : dropTms[u + 3]? = none := by simp [dropTms]
    rw [h3] at hu
    cases hu

/-- Family 7 is no normaliser sound under typing: in `frD`, `(x + y) - x` has no value and `y`
has one. -/
theorem dropStep_not_normSoundT :
    ¬ NormSoundT Fam4Witness.fn2 (Norm.guard (dropStep (atomTy Fam4Witness.fn2))) :=
  fun h => drop_frame (h dropTms _ _ dropStep_fires frD Mem.empty 1 rfl drop_atomsTyped)

/-! ## Real pairs

Pairs of the shared #1119 corpus (`FVTest/Opt/midval/real_drop_*.clif`), each rejected by main's
`checkC` (`checkCPrev`) and accepted by `checkCertC` with the requests `emitC` gives (decided),
with the simulation and the program refinement:

* `sub`: serde_json's test build, `_RNxC10dissimilar12Hh0IIBJQkjmz`: a stored
  `(a + b) - a` → `b` (`subAdd`);
* `mul0`: semver's test build, criterion's `_RNxC9criterion12HhMPOIRGWCsV`: a call argument
  `p + (n + 1) * 0` → `p` (`absTyped`, then the neutral constant of family 4);
* `addsub`: semver's test build, memchr's `_RNxC6memchr12HlFTkvsRv1Zb`: a jump argument
  `(x - r) + r` → `x` (`addSub`).
-/

def subF : String := include_str "midval/real_drop_sub.unopt.clif"
def subG : String := include_str "midval/real_drop_sub.opt.clif"
def mul0F' : String := include_str "midval/real_drop_mul0.unopt.clif"
def mul0G' : String := include_str "midval/real_drop_mul0.opt.clif"
def addsubF : String := include_str "midval/real_drop_addsub.unopt.clif"
def addsubG : String := include_str "midval/real_drop_addsub.opt.clif"

theorem real_sub_prev_rejects : realPrev subF subG = some false := by native_decide
theorem real_sub_checked : checkedC subF subG = some (true, false) := by native_decide
theorem real_sub_sim : SimRefinesC subF subG := simC_of_checked real_sub_checked

theorem real_mul0_prev_rejects : realPrev mul0F' mul0G' = some false := by native_decide
theorem real_mul0_checked : checkedC mul0F' mul0G' = some (true, false) := by native_decide
theorem real_mul0_sim : SimRefinesC mul0F' mul0G' := simC_of_checked real_mul0_checked

theorem real_addsub_prev_rejects : realPrev addsubF addsubG = some false := by native_decide
theorem real_addsub_checked : checkedC addsubF addsubG = some (true, false) := by native_decide
theorem real_addsub_sim : SimRefinesC addsubF addsubG := simC_of_checked real_addsub_checked

end Opt.MidVal.DropWitness
