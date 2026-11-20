import FVTest.Opt.MidValAlgWitness

/-! # The second set of single-node algebraic rules: witnesses (#1119 stage 2, family 2)

`Norm.std` is constant evaluation, then `Norm.alg2` (this set), then `Norm.alg` (the first set).
For each rule of the second set, a hand-made pair accepted by `Norm.std` and rejected without the
second set (`*_alg2_needed`: constant evaluation and the first set alone), and a look-alike
rejected (`neg_*`). Three look-alikes are proved to be no simulation, so every certificate is
rejected:

* `icmpBool`: an `icmp` compared with `2` is not the inverted comparison (`bool_not_sim`: for
  arguments `0, 1`, `f` returns `0`, `g` `1`);
* `icmpUnit`: `icmp ult x, 2` is not `icmp eq x, 0` (`unit_not_sim`: for `x = 1`, `f` returns `1`,
  `g` `0`);
* `bmaskBool`: `bmask` of a parameter (not an `icmp`, so not 0/1) is not its negation
  (`bmask_not_sim`: for `2`, `f` returns `0xff`, `g` `0xfe`).

Real pairs (`FVTest/Opt/midval/real_alg2_*.clif`, the release dumps of the measured crates) are
rejected without the second set, and accepted by the re-check with `Norm.std` (decided), with
the simulation and the program refinement from `check_sound` (`real_*_sim`):

* `sub`: num_traits' `_RNxC10num_traits12H46cyi9wwwPC`: `isub 0, x` → `ineg x` (`subNeg`);
* `mul2`: criterion's `_RNxC9criterion12H41dCMSBazd6`: `imul x, 2` → `iadd x, x` (`mulTwo`);
* `swap`: semver's `_RNxC6semver12H5cWTS75JJES`: `icmp ule 48, x` → `icmp uge x, 48` (`icmpSwap`);
* `unit`: regex_syntax's `_RNxC12regex_syntax12Hi2fYLhNOZYe`: `icmp ult x, 1` → `icmp eq x, 0`
  (`icmpUnit`);
* `bool`: toml's `_RNxC4toml12HaAuvQkfirqf`: `icmp eq (select (icmp eq x, -1), 0, 1), 1` →
  `icmp ne x, -1` (`selIcmp`, then `icmpBool`). -/

namespace Opt.MidVal.Alg2Witness

open Clif Pairs NormWitness AlgWitness

/-- The verdict without the second set (constant evaluation, then the first set). -/
def acceptsNoAlg2 (f g : String) : Option Bool := do
  pure (check (ConstPhi.run (← fn? f)) (← fn? g) (Norm.orElse evalConst Norm.alg)).isOk

/-! ## Hand-made pairs -/

def swapF : String := "function %f(i8) -> i8 {\nblock0(v0: i8):\n    v1 = iconst.i8 48\n    v2 = icmp ule v1, v0\n    return v2\n}"
def swapG : String := "function %f(i8) -> i8 {\nblock0(v0: i8):\n    v1 = iconst.i8 48\n    v2 = icmp uge v0, v1\n    return v2\n}"
def swapGbad : String := "function %f(i8) -> i8 {\nblock0(v0: i8):\n    v1 = iconst.i8 48\n    v2 = icmp ule v0, v1\n    return v2\n}"

theorem pos_swap : accepts swapF swapG = some true := by native_decide
theorem swap_alg2_needed : acceptsNoAlg2 swapF swapG = some false := by native_decide
theorem neg_swap : accepts swapF swapGbad = some false := by native_decide

def boolF : String := "function %f(i32, i32) -> i8 {\nblock0(v0: i32, v1: i32):\n    v2 = icmp eq v0, v1\n    v3 = iconst.i8 0\n    v4 = icmp eq v2, v3\n    return v4\n}"
def boolG : String := "function %f(i32, i32) -> i8 {\nblock0(v0: i32, v1: i32):\n    v5 = icmp ne v0, v1\n    return v5\n}"
def boolF2 : String := "function %f(i32, i32) -> i8 {\nblock0(v0: i32, v1: i32):\n    v2 = icmp eq v0, v1\n    v3 = iconst.i8 2\n    v4 = icmp eq v2, v3\n    return v4\n}"

theorem pos_bool : accepts boolF boolG = some true := by native_decide
theorem bool_alg2_needed : acceptsNoAlg2 boolF boolG = some false := by native_decide
theorem neg_bool : accepts boolF2 boolG = some false := by native_decide

def unitF : String := "function %f(i32) -> i8 {\nblock0(v0: i32):\n    v1 = iconst.i32 1\n    v2 = icmp ult v0, v1\n    return v2\n}"
def unitG : String := "function %f(i32) -> i8 {\nblock0(v0: i32):\n    v3 = iconst.i32 0\n    v2 = icmp eq v0, v3\n    return v2\n}"
def unitF2 : String := "function %f(i32) -> i8 {\nblock0(v0: i32):\n    v1 = iconst.i32 2\n    v2 = icmp ult v0, v1\n    return v2\n}"

theorem pos_unit : accepts unitF unitG = some true := by native_decide
theorem unit_alg2_needed : acceptsNoAlg2 unitF unitG = some false := by native_decide
theorem neg_unit : accepts unitF2 unitG = some false := by native_decide

def subF : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 0\n    v2 = isub v1, v0\n    return v2\n}"
def subG : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v2 = ineg v0\n    return v2\n}"
def subF2 : String := "function %f(i64) -> i64 {\nblock0(v0: i64):\n    v1 = iconst.i64 0\n    v2 = isub v0, v1\n    return v2\n}"

theorem pos_sub : accepts subF subG = some true := by native_decide
theorem sub_alg2_needed : acceptsNoAlg2 subF subG = some false := by native_decide
theorem neg_sub : accepts subF2 subG = some false := by native_decide

def mul2F : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    v1 = iconst.i32 2\n    v2 = imul v0, v1\n    return v2\n}"
def mul2Gadd : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    v2 = iadd v0, v0\n    return v2\n}"
def mul2Gshl : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    v1 = iconst.i64 1\n    v2 = ishl v0, v1\n    return v2\n}"
def mul2Gshl2 : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    v1 = iconst.i64 2\n    v2 = ishl v0, v1\n    return v2\n}"

theorem pos_mul2 : accepts mul2F mul2Gadd = some true := by native_decide
theorem mul2_alg2_needed : acceptsNoAlg2 mul2F mul2Gadd = some false := by native_decide
theorem pos_shl1 : accepts mul2F mul2Gshl = some true := by native_decide
theorem neg_mul2 : accepts mul2F mul2Gshl2 = some false := by native_decide

def bmaskF : String := "function %f(i32, i32) -> i8 {\nblock0(v0: i32, v1: i32):\n    v2 = icmp eq v0, v1\n    v3 = bmask.i8 v2\n    return v3\n}"
def bmaskG : String := "function %f(i32, i32) -> i8 {\nblock0(v0: i32, v1: i32):\n    v2 = icmp eq v0, v1\n    v3 = ineg v2\n    return v3\n}"
def bmaskF2 : String := "function %f(i8) -> i8 {\nblock0(v0: i8):\n    v1 = bmask.i8 v0\n    return v1\n}"
def bmaskG2 : String := "function %f(i8) -> i8 {\nblock0(v0: i8):\n    v1 = ineg v0\n    return v1\n}"

theorem pos_bmask : accepts bmaskF bmaskG = some true := by native_decide
theorem bmask_alg2_needed : acceptsNoAlg2 bmaskF bmaskG = some false := by native_decide
theorem neg_bmask : accepts bmaskF2 bmaskG2 = some false := by native_decide

def xorF : String := "function %f(i16) -> i16 {\nblock0(v0: i16):\n    v1 = iconst.i16 -1\n    v2 = bxor v0, v1\n    return v2\n}"
def xorG : String := "function %f(i16) -> i16 {\nblock0(v0: i16):\n    v2 = bnot v0\n    return v2\n}"
def xorF2 : String := "function %f(i16) -> i16 {\nblock0(v0: i16):\n    v1 = iconst.i16 0x7fff\n    v2 = bxor v0, v1\n    return v2\n}"

theorem pos_xor : accepts xorF xorG = some true := by native_decide
theorem xor_alg2_needed : acceptsNoAlg2 xorF xorG = some false := by native_decide
theorem neg_xor : accepts xorF2 xorG = some false := by native_decide

/-! ## Three look-alikes are no simulations -/

/-- A function of one block with the given parameters. -/
def fnN (ps : List Ty) (rt : Ty) (body : List Stmt) (r : ValueId) : Function :=
  { name := "f", sig := { params := ps.map ap, returns := [ap rt], callConv := none },
    blocks := [Block.mk 0 ((List.range ps.length).zip ps) false body (.ret [r])] }

def boolF2n : Function :=
  fnN [.i32, .i32] .i8 [{ results := [2], inst := .icmp .eq .i32 0 1 },
    { results := [3], inst := .iconst .i8 2 }, { results := [4], inst := .icmp .eq .i8 2 3 }] 4
def boolGn : Function := fnN [.i32, .i32] .i8 [{ results := [5], inst := .icmp .ne .i32 0 1 }] 5

def unitF2n : Function :=
  fnN [.i32] .i8 [{ results := [1], inst := .iconst .i32 2 },
    { results := [2], inst := .icmp .ult .i32 0 1 }] 2
def unitGn : Function :=
  fnN [.i32] .i8 [{ results := [3], inst := .iconst .i32 0 },
    { results := [2], inst := .icmp .eq .i32 0 3 }] 2

def bmaskF2n : Function := fnN [.i8] .i8 [{ results := [1], inst := .bmask .i8 0 }] 1
def bmaskG2n : Function := fnN [.i8] .i8 [{ results := [1], inst := .unary .ineg .i8 0 }] 1

theorem boolF2_text : fn? boolF2 = some boolF2n := by native_decide
theorem boolG_text : fn? boolG = some boolGn := by native_decide
theorem unitF2_text : fn? unitF2 = some unitF2n := by native_decide
theorem unitG_text : fn? unitG = some unitGn := by native_decide
theorem bmaskF2_text : fn? bmaskF2 = some bmaskF2n := by native_decide
theorem bmaskG2_text : fn? bmaskG2 = some bmaskG2n := by native_decide

theorem bool_not_sim : ¬ FunSimMU boolF2n boolGn :=
  not_funSimMU_ret_ne (b := boolF2n.blocks.head!) (b' := boolGn.blocks.head!)
    (args := [⟨.i32, 0⟩, ⟨.i32, 1⟩]) (regs := (Regs.empty.set 0 ⟨.i32, 0⟩).set 1 ⟨.i32, 1⟩)
    (m := Mem.empty) (vals := [⟨.i8, 0⟩]) (vals' := [⟨.i8, 1⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.step rfl (.refl _ _)))) rfl
    (.step rfl (.refl _ _)) rfl (by decide)

theorem bool_rejected (cert : Cert) : checkCert (ConstPhi.run boolF2n) boolGn cert = false := by
  cases h : checkCert (ConstPhi.run boolF2n) boolGn cert
  · rfl
  · exact absurd (checked_simMU h) bool_not_sim

theorem unit_not_sim : ¬ FunSimMU unitF2n unitGn :=
  not_funSimMU_ret_ne (b := unitF2n.blocks.head!) (b' := unitGn.blocks.head!)
    (args := [⟨.i32, 1⟩]) (regs := Regs.empty.set 0 ⟨.i32, 1⟩)
    (m := Mem.empty) (vals := [⟨.i8, 1⟩]) (vals' := [⟨.i8, 0⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.refl _ _))) rfl
    (.step rfl (.step rfl (.refl _ _))) rfl (by decide)

theorem unit_rejected (cert : Cert) : checkCert (ConstPhi.run unitF2n) unitGn cert = false := by
  cases h : checkCert (ConstPhi.run unitF2n) unitGn cert
  · rfl
  · exact absurd (checked_simMU h) unit_not_sim

theorem bmask_not_sim : ¬ FunSimMU bmaskF2n bmaskG2n :=
  not_funSimMU_ret_ne (b := bmaskF2n.blocks.head!) (b' := bmaskG2n.blocks.head!)
    (args := [⟨.i8, 2⟩]) (regs := Regs.empty.set 0 ⟨.i8, 2⟩)
    (m := Mem.empty) (vals := [⟨.i8, 0xff⟩]) (vals' := [⟨.i8, 0xfe⟩])
    rfl rfl rfl rfl rfl (.step rfl (.refl _ _)) rfl
    (.step rfl (.refl _ _)) rfl (by decide)

theorem bmask_rejected (cert : Cert) :
    checkCert (ConstPhi.run bmaskF2n) bmaskG2n cert = false := by
  cases h : checkCert (ConstPhi.run bmaskF2n) bmaskG2n cert
  · rfl
  · exact absurd (checked_simMU h) bmask_not_sim

/-! ## Real pairs -/

/-- The verdict without the second set on a decoded dump pair. -/
def noAlg2Verdict (fT gT : String) : Option Bool := do
  let f ← RealWitness.decode fT
  let g ← RealWitness.decode gT
  pure (check (ConstPhi.run f) g (Norm.orElse evalConst Norm.alg)).isOk

def subF' : String := include_str "midval/real_alg2_sub.unopt.clif"
def subG' : String := include_str "midval/real_alg2_sub.opt.clif"
theorem real_sub_alg2_needed : noAlg2Verdict subF' subG' = some false := by native_decide
theorem real_sub_checked :
    ((pairD subF' subG').map fun p => checkCert (ConstPhi.run p.1) p.2.1 p.2.2) = some true := by
  native_decide
theorem real_sub_sim : SimRefines subF' subG' := sim_of_checked real_sub_checked

def mul2F' : String := include_str "midval/real_alg2_mul2.unopt.clif"
def mul2G' : String := include_str "midval/real_alg2_mul2.opt.clif"
theorem real_mul2_alg2_needed : noAlg2Verdict mul2F' mul2G' = some false := by native_decide
theorem real_mul2_checked :
    ((pairD mul2F' mul2G').map fun p => checkCert (ConstPhi.run p.1) p.2.1 p.2.2) = some true := by
  native_decide
theorem real_mul2_sim : SimRefines mul2F' mul2G' := sim_of_checked real_mul2_checked

def swapF' : String := include_str "midval/real_alg2_swap.unopt.clif"
def swapG' : String := include_str "midval/real_alg2_swap.opt.clif"
theorem real_swap_alg2_needed : noAlg2Verdict swapF' swapG' = some false := by native_decide
theorem real_swap_checked :
    ((pairD swapF' swapG').map fun p => checkCert (ConstPhi.run p.1) p.2.1 p.2.2) = some true := by
  native_decide
theorem real_swap_sim : SimRefines swapF' swapG' := sim_of_checked real_swap_checked

def unitF' : String := include_str "midval/real_alg2_unit.unopt.clif"
def unitG' : String := include_str "midval/real_alg2_unit.opt.clif"
theorem real_unit_alg2_needed : noAlg2Verdict unitF' unitG' = some false := by native_decide
theorem real_unit_checked :
    ((pairD unitF' unitG').map fun p => checkCert (ConstPhi.run p.1) p.2.1 p.2.2) = some true := by
  native_decide
theorem real_unit_sim : SimRefines unitF' unitG' := sim_of_checked real_unit_checked

def boolF' : String := include_str "midval/real_alg2_bool.unopt.clif"
def boolG' : String := include_str "midval/real_alg2_bool.opt.clif"
theorem real_bool_alg2_needed : noAlg2Verdict boolF' boolG' = some false := by native_decide
theorem real_bool_checked :
    ((pairD boolF' boolG').map fun p => checkCert (ConstPhi.run p.1) p.2.1 p.2.2) = some true := by
  native_decide
theorem real_bool_sim : SimRefines boolF' boolG' := sim_of_checked real_bool_checked

end Opt.MidVal.Alg2Witness
