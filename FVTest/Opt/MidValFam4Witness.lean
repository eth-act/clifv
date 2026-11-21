import FVTest.Opt.MidValTypedWitness
import FV.Opt.Proof.MidValNormFam4

/-! # Family 4 of the mid-end validator: witnesses (#1119 stage 2, agent MidendNorm5)

The default normaliser `Norm.stdT f = Norm.narrowN f 3` adds four steps to `Norm.std` and the
typed rules (`FV/Opt/Proof/MidValNormFam4.lean`). For each step: hand-made pairs accepted by the
default and rejected by the normaliser before family 4 (`*_t0_rejects`), and look-alikes that
are rejected (`neg_*`), no simulation, so the re-check rejects every certificate (by
`check_sound`):

* `idStep`: `imul x, 1` (`pos_id`) and `iadd 0, x` (`pos_idL`) are `x`. Look-alikes: `iadd x, 1`
  is not `x` (`neg_idOne`, `idOne_not_sim`: for `x = 0`, `f` returns 1, `g` 0) and `isub 0, x` is
  not `x` (`isub` is not commutative: `neg_idSubL`, `idSubL_not_sim`: for `x = 1`, `f` returns
  `-1`, `g` 1). The typing premise is needed: the rule is no sound normaliser in every frame
  (`idStep_not_normSound`: a parameter declared `i64` holding an `i32` value is the value, while
  `iadd.i64` of it with `0` is `stuck`);
* `affStep`: `(x + 3) - 5` is `x + (-2)` (`pos_aff`). Look-alike with the sign error, `x + 8`
  (`neg_aff`, `aff_not_sim`: for `x = 0`, `f` returns `-2`, `g` 8);
* `swapStep`: `band 255, x` is `band x, 255` (`pos_swap`). Look-alike with a non-commutative
  operation, `isub 7, x` against `isub x, 7` (`neg_swap`, `swap_not_sim`: for `x = 0`, `f`
  returns 7, `g` `-7`);
* `narrowStep`: `ireduce.i32 (imul x, 5)` is `imul.i32 (ireduce.i32 x), 5` (`pos_narrow`).
  Look-alike with a shift, which truncation does not commute with: `ireduce.i32 (ushr x, 1)`
  against `ushr.i32 (ireduce.i32 x), 1` (`neg_narrow`, `narrow_not_sim`: for `x = 2^32`, `f`
  returns `2^31`, `g` 0). The typing premise is needed (`narrowStep_not_normSound`: operands
  declared `i64` holding `i128` values make the `iadd.i64` `stuck` but not the narrowed `iadd.i32`).

**Real pairs** (the release dumps of the measured crates, `FVTest/Opt/midval/real_fam4_*.clif`),
each rejected by the normaliser before family 4 and accepted by the re-check with the default
normaliser (decided), with the simulation and the program refinement from `check_sound`
(`real_*_sim`):

* `id`: blake2's `_RNxC3mac12H8Wt5rLuKukP`: `call memcmp(…, imul x, 1)` is `call memcmp(…, x)`;
* `aff`: regex_syntax's `_RNxC12regex_syntax12H1YveCFqb7Cq`: `isub x, K` is `iadd x, -K`;
* `swap`: regex_syntax's `_RNxC12regex_syntax12H7R5jhjf3Ia4`: a constant on the left of a
  commutative operation;
* `narrow`: core's `<u32 as Mul>::mul` (itoa's test build,
  `_RNvXs25_NtNtCsazjiGSRkgVH_4core3ops5arithmNtB6_3Mul3mul`):
  `ireduce.i32 (imul (uextend.i64 x), (uextend.i64 y))` is `imul.i32 x, y`. -/

namespace Opt.MidVal.Fam4Witness

open Clif Pairs NormWitness AlgWitness

/-- The validator's default normaliser before family 4: `Norm.std`, then the typed rules. -/
def normT0 (f : Function) : Norm := Norm.orElse Norm.std (Norm.guard (typedStep (atomTy f)))

/-- The verdict with the normaliser before family 4. -/
def acceptsT0 (f g : String) : Option Bool := do
  let f' := ConstPhi.run (← fn? f)
  pure (check f' (← fn? g) (normT0 f')).isOk

/-! ## Hand-made pairs -/

def idF : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 1\n    v2 = imul v0, v1\n    return v2\n}"
def idLF : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 0\n    v2 = iadd v1, v0\n    return v2\n}"
def idG : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    return v0\n}"
def idOneF : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 1\n    v2 = iadd v0, v1\n    return v2\n}"
def idSubLF : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 0\n    v2 = isub v1, v0\n    return v2\n}"

theorem pos_id : accepts idF idG = some true := by native_decide
theorem pos_id_t0_rejects : acceptsT0 idF idG = some false := by native_decide
theorem pos_idL : accepts idLF idG = some true := by native_decide
theorem pos_idL_t0_rejects : acceptsT0 idLF idG = some false := by native_decide
theorem neg_idOne : accepts idOneF idG = some false := by native_decide
theorem neg_idSubL : accepts idSubLF idG = some false := by native_decide

def affF : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 3\n    v2 = iadd v0, v1\n    v3 = iconst.i64 5\n    v4 = isub v2, v3\n    return v4\n}"
def affG : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v5 = iconst.i64 -2\n    v4 = iadd v0, v5\n    return v4\n}"
def affNegG : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v5 = iconst.i64 8\n    v4 = iadd v0, v5\n    return v4\n}"

theorem pos_aff : accepts affF affG = some true := by native_decide
theorem pos_aff_t0_rejects : acceptsT0 affF affG = some false := by native_decide
theorem neg_aff : accepts affF affNegG = some false := by native_decide

def swapF : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 255\n    v2 = band v1, v0\n    return v2\n}"
def swapG : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 255\n    v2 = band v0, v1\n    return v2\n}"
def swapNegF : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 7\n    v2 = isub v1, v0\n    return v2\n}"
def swapNegG : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 7\n    v2 = isub v0, v1\n    return v2\n}"

theorem pos_swap : accepts swapF swapG = some true := by native_decide
theorem pos_swap_t0_rejects : acceptsT0 swapF swapG = some false := by native_decide
theorem neg_swap : accepts swapNegF swapNegG = some false := by native_decide

def narrowF : String := "function %f(i64) -> i32 {\nblock0(v0: i64):\n    v1 = iconst.i64 5\n    v2 = imul v0, v1\n    v3 = ireduce.i32 v2\n    return v3\n}"
def narrowG : String := "function %f(i64) -> i32 {\nblock0(v0: i64):\n    v4 = ireduce.i32 v0\n    v5 = iconst.i32 5\n    v6 = imul v4, v5\n    return v6\n}"
def narrowNegF : String := "function %f(i64) -> i32 {\nblock0(v0: i64):\n    v1 = iconst.i64 1\n    v2 = ushr v0, v1\n    v3 = ireduce.i32 v2\n    return v3\n}"
def narrowNegG : String := "function %f(i64) -> i32 {\nblock0(v0: i64):\n    v4 = ireduce.i32 v0\n    v5 = iconst.i32 1\n    v6 = ushr v4, v5\n    return v6\n}"

theorem pos_narrow : accepts narrowF narrowG = some true := by native_decide
theorem pos_narrow_t0_rejects : acceptsT0 narrowF narrowG = some false := by native_decide
theorem neg_narrow : accepts narrowNegF narrowNegG = some false := by native_decide

/-! ## The look-alikes are no simulations -/

def idOneFn : Function :=
  fn1 .i64 .i64 [{ results := [1], inst := .iconst .i64 1 },
    { results := [2], inst := .binary .iadd .i64 0 1 }] 2
def idSubLFn : Function :=
  fn1 .i64 .i64 [{ results := [1], inst := .iconst .i64 0 },
    { results := [2], inst := .binary .isub .i64 1 0 }] 2
def idGn : Function := fn1 .i64 .i64 [] 0
def affFn : Function :=
  fn1 .i64 .i64 [{ results := [1], inst := .iconst .i64 3 },
    { results := [2], inst := .binary .iadd .i64 0 1 }, { results := [3], inst := .iconst .i64 5 },
    { results := [4], inst := .binary .isub .i64 2 3 }] 4
def affNegGn : Function :=
  fn1 .i64 .i64 [{ results := [5], inst := .iconst .i64 8 },
    { results := [4], inst := .binary .iadd .i64 0 5 }] 4
def swapNegFn : Function :=
  fn1 .i64 .i64 [{ results := [1], inst := .iconst .i64 7 },
    { results := [2], inst := .binary .isub .i64 1 0 }] 2
def swapNegGn : Function :=
  fn1 .i64 .i64 [{ results := [1], inst := .iconst .i64 7 },
    { results := [2], inst := .binary .isub .i64 0 1 }] 2
def narrowNegFn : Function :=
  fn1 .i64 .i32 [{ results := [1], inst := .iconst .i64 1 },
    { results := [2], inst := .binary .ushr .i64 0 1 }, { results := [3], inst := .ireduce .i32 2 }] 3
def narrowNegGn : Function :=
  fn1 .i64 .i32 [{ results := [4], inst := .ireduce .i32 0 }, { results := [5], inst := .iconst .i32 1 },
    { results := [6], inst := .binary .ushr .i32 4 5 }] 6

theorem idOneF_text : fn? idOneF = some idOneFn := by native_decide
theorem idSubLF_text : fn? idSubLF = some idSubLFn := by native_decide
theorem idG_text : fn? idG = some idGn := by native_decide
theorem affF_text : fn? affF = some affFn := by native_decide
theorem affNegG_text : fn? affNegG = some affNegGn := by native_decide
theorem swapNegF_text : fn? swapNegF = some swapNegFn := by native_decide
theorem swapNegG_text : fn? swapNegG = some swapNegGn := by native_decide
theorem narrowNegF_text : fn? narrowNegF = some narrowNegFn := by native_decide
theorem narrowNegG_text : fn? narrowNegG = some narrowNegGn := by native_decide

theorem idOne_not_sim : ¬ FunSimMU idOneFn idGn :=
  not_funSimMU_ret_ne (b := idOneFn.blocks.head!) (b' := idGn.blocks.head!)
    (args := [⟨.i64, 0⟩]) (regs := Regs.empty.set 0 ⟨.i64, 0⟩) (m := Mem.empty)
    (vals := [⟨.i64, 1⟩]) (vals' := [⟨.i64, 0⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.refl _ _))) rfl (.refl _ _) rfl (by decide)

/-- The re-check rejects every certificate for `neg_idOne`. -/
theorem idOne_rejected (cert : Cert) : checkCert (ConstPhi.run idOneFn) idGn cert = false := by
  cases h : checkCert (ConstPhi.run idOneFn) idGn cert
  · rfl
  · exact absurd (checked_simMU h) idOne_not_sim

theorem idSubL_not_sim : ¬ FunSimMU idSubLFn idGn :=
  not_funSimMU_ret_ne (b := idSubLFn.blocks.head!) (b' := idGn.blocks.head!)
    (args := [⟨.i64, 1⟩]) (regs := Regs.empty.set 0 ⟨.i64, 1⟩) (m := Mem.empty)
    (vals := [⟨.i64, -1⟩]) (vals' := [⟨.i64, 1⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.refl _ _))) rfl (.refl _ _) rfl (by decide)

/-- The re-check rejects every certificate for `neg_idSubL`. -/
theorem idSubL_rejected (cert : Cert) : checkCert (ConstPhi.run idSubLFn) idGn cert = false := by
  cases h : checkCert (ConstPhi.run idSubLFn) idGn cert
  · rfl
  · exact absurd (checked_simMU h) idSubL_not_sim

theorem aff_not_sim : ¬ FunSimMU affFn affNegGn :=
  not_funSimMU_ret_ne (b := affFn.blocks.head!) (b' := affNegGn.blocks.head!)
    (args := [⟨.i64, 0⟩]) (regs := Regs.empty.set 0 ⟨.i64, 0⟩) (m := Mem.empty)
    (vals := [⟨.i64, -2⟩]) (vals' := [⟨.i64, 8⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.step rfl (.step rfl (.refl _ _))))) rfl
    (.step rfl (.step rfl (.refl _ _))) rfl (by decide)

/-- The re-check rejects every certificate for `neg_aff`. -/
theorem aff_rejected (cert : Cert) : checkCert (ConstPhi.run affFn) affNegGn cert = false := by
  cases h : checkCert (ConstPhi.run affFn) affNegGn cert
  · rfl
  · exact absurd (checked_simMU h) aff_not_sim

theorem swap_not_sim : ¬ FunSimMU swapNegFn swapNegGn :=
  not_funSimMU_ret_ne (b := swapNegFn.blocks.head!) (b' := swapNegGn.blocks.head!)
    (args := [⟨.i64, 0⟩]) (regs := Regs.empty.set 0 ⟨.i64, 0⟩) (m := Mem.empty)
    (vals := [⟨.i64, 7⟩]) (vals' := [⟨.i64, -7⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.refl _ _))) rfl
    (.step rfl (.step rfl (.refl _ _))) rfl (by decide)

/-- The re-check rejects every certificate for `neg_swap`. -/
theorem swap_rejected (cert : Cert) : checkCert (ConstPhi.run swapNegFn) swapNegGn cert = false := by
  cases h : checkCert (ConstPhi.run swapNegFn) swapNegGn cert
  · rfl
  · exact absurd (checked_simMU h) swap_not_sim

theorem narrow_not_sim : ¬ FunSimMU narrowNegFn narrowNegGn :=
  not_funSimMU_ret_ne (b := narrowNegFn.blocks.head!) (b' := narrowNegGn.blocks.head!)
    (args := [⟨.i64, 0x100000000⟩]) (regs := Regs.empty.set 0 ⟨.i64, 0x100000000⟩) (m := Mem.empty)
    (vals := [⟨.i32, 0x80000000⟩]) (vals' := [⟨.i32, 0⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.step rfl (.refl _ _)))) rfl
    (.step rfl (.step rfl (.step rfl (.refl _ _)))) rfl (by decide)

/-- The re-check rejects every certificate for `neg_narrow`. -/
theorem narrow_rejected (cert : Cert) :
    checkCert (ConstPhi.run narrowNegFn) narrowNegGn cert = false := by
  cases h : checkCert (ConstPhi.run narrowNegFn) narrowNegGn cert
  · rfl
  · exact absurd (checked_simMU h) narrow_not_sim

/-! ## The typing premises are needed

Both typed steps are sound only in frames where the atoms below the node hold values of their
static types (`NormSoundT`): as normalisers sound in every frame (`NormSound`) they are false. -/

/-- A two-parameter function of one block (its body does not matter: only `atomVal` reads it). -/
def fn2 : Function :=
  { name := "f", sig := { params := [ap .i64, ap .i64], returns := [ap .i64], callConv := none },
    blocks := [{ id := 0, params := [(0, .i64), (1, .i64)], cold := false, body := [], term := .ret [0] }] }

/-- A frame of `fn2` whose parameters hold `x` and `y`. -/
def fr2 (x y : Val) : Frame :=
  { func := fn2, regs := (Regs.empty.set 0 x).set 1 y, slots := [], body := [], term := .ret [] }

def idTms : Array Tm := #[.param 0 0, .node (.iconst .i64 0)]

theorem idStep_fires :
    Norm.guard (idStep (atomTy fn2)) idTms (.binary .iadd .i64 0 1) = some (.param 0 0) := by
  native_decide

theorem idStep_frame :
    tmVal fn2 idTms (fr2 ⟨.i32, 7⟩ ⟨.i64, 0⟩) Mem.empty 0 ≠
      evalNode (tmFrame fn2 idTms (fr2 ⟨.i32, 7⟩ ⟨.i64, 0⟩) Mem.empty) Mem.empty
        (.binary .iadd .i64 0 1) := by
  native_decide

/-- `idStep` is no normaliser sound in every frame (a parameter declared `i64` holding an `i32`). -/
theorem idStep_not_normSound : ¬ NormSound (Norm.guard (idStep (atomTy fn2))) := fun h =>
  idStep_frame (h idTms _ _ idStep_fires fn2 (fr2 ⟨.i32, 7⟩ ⟨.i64, 0⟩) Mem.empty 0 rfl)

def narrowTms : Array Tm :=
  #[.param 0 0, .param 0 1, .node (.binary .iadd .i64 0 1), .node (.ireduce .i32 0),
    .node (.ireduce .i32 1), .node (.binary .iadd .i32 3 4)]

theorem narrowStep_fires :
    Norm.guard (narrowStep Norm.id (atomTy fn2)) narrowTms (.ireduce .i32 2) =
      some (.node (.binary .iadd .i32 3 4)) := by
  native_decide

theorem narrowStep_frame :
    tmVal fn2 narrowTms (fr2 ⟨.i128, 1⟩ ⟨.i128, 2⟩) Mem.empty 5 ≠
      evalNode (tmFrame fn2 narrowTms (fr2 ⟨.i128, 1⟩ ⟨.i128, 2⟩) Mem.empty) Mem.empty
        (.ireduce .i32 2) := by
  native_decide

/-- `narrowStep` is no normaliser sound in every frame (operands declared `i64` holding `i128`
values: the `iadd.i64` is `stuck`, the narrowed `iadd.i32` is not). -/
theorem narrowStep_not_normSound : ¬ NormSound (Norm.guard (narrowStep Norm.id (atomTy fn2))) :=
  fun h => narrowStep_frame
    (h narrowTms _ _ narrowStep_fires fn2 (fr2 ⟨.i128, 1⟩ ⟨.i128, 2⟩) Mem.empty 5 rfl)

/-! ## Real pairs -/

def idF' : String := include_str "midval/real_fam4_id.unopt.clif"
def idG' : String := include_str "midval/real_fam4_id.opt.clif"
def affF' : String := include_str "midval/real_fam4_aff.unopt.clif"
def affG' : String := include_str "midval/real_fam4_aff.opt.clif"
def swapF' : String := include_str "midval/real_fam4_swap.unopt.clif"
def swapG' : String := include_str "midval/real_fam4_swap.opt.clif"
def narrowF' : String := include_str "midval/real_fam4_narrow.unopt.clif"
def narrowG' : String := include_str "midval/real_fam4_narrow.opt.clif"

/-- The verdict of the normaliser before family 4 on a decoded dump pair. -/
def t0Verdict (fT gT : String) : Option Bool := do
  let f := ConstPhi.run (← RealWitness.decode fT)
  let g ← RealWitness.decode gT
  pure (check f g (normT0 f)).isOk

theorem real_id_t0_rejects : t0Verdict idF' idG' = some false := by native_decide
theorem real_id_checked :
    ((pairD idF' idG').map fun p => checkCert (ConstPhi.run p.1) p.2.1 p.2.2) = some true := by
  native_decide
theorem real_id_sim : SimRefines idF' idG' := sim_of_checked real_id_checked

theorem real_aff_t0_rejects : t0Verdict affF' affG' = some false := by native_decide
theorem real_aff_checked :
    ((pairD affF' affG').map fun p => checkCert (ConstPhi.run p.1) p.2.1 p.2.2) = some true := by
  native_decide
theorem real_aff_sim : SimRefines affF' affG' := sim_of_checked real_aff_checked

theorem real_swap_t0_rejects : t0Verdict swapF' swapG' = some false := by native_decide
theorem real_swap_checked :
    ((pairD swapF' swapG').map fun p => checkCert (ConstPhi.run p.1) p.2.1 p.2.2) = some true := by
  native_decide
theorem real_swap_sim : SimRefines swapF' swapG' := sim_of_checked real_swap_checked

theorem real_narrow_t0_rejects : t0Verdict narrowF' narrowG' = some false := by native_decide
theorem real_narrow_checked :
    ((pairD narrowF' narrowG').map fun p => checkCert (ConstPhi.run p.1) p.2.1 p.2.2) =
      some true := by
  native_decide
theorem real_narrow_sim : SimRefines narrowF' narrowG' := sim_of_checked real_narrow_checked

end Opt.MidVal.Fam4Witness
