import FVTest.Opt.MidValCondWitness
import FV.Opt.Proof.MidValFold

/-! # Constant-condition branch folding in the mid-end validator: witnesses (#1119, `rewrite:blocks`)

`checkC` folds, in a copy of `f`, the `brif`/`br_table` of the blocks whose branch is a `jump`
in `g` when the condition has a constant (`foldPre f bs`: `foldBr`, then constant-phi removal,
which drops the blocks that became unreachable); the re-check `checkCertC` does the same for the
fold requests among its hints, and `check_soundC` composes the check with `foldPre_simU`.

* Hand-made: `brif (icmp ult 64, 0)` against a `jump` to the `else` block without the `then`
  block (`pos_ult`), a constant defined in the entry block and branched on in another block
  (`pos_cross`), a `br_table` on a constant (`pos_table`) are accepted, and rejected without
  folding (`*_check_rejects`, `*_c0_rejects`: the checker without and with branch-condition
  hints).
* Negative: a branch on a parameter is not folded (`param_not_folded`: `foldBr` leaves the
  function unchanged), and the pair against a `jump` is rejected (`neg_param`) and no simulation
  (`param_not_sim`), so every certificate with every hint list is rejected (`param_rejected`);
  the fold keeps the block the constant selects and drops the other (`ult_blocks`), and the pair
  against `g` that keeps the other block instead is rejected (`neg_keep_wrong`), no simulation
  (`keep_wrong_not_sim`) and rejected with every certificate and hint list
  (`keep_wrong_rejected`); a `br_table` folded to the wrong entry is rejected (`neg_table`), no
  simulation (`table_not_sim`), rejected with every certificate and hint list
  (`table_rejected`).
* Real pairs (crypto-bigint 0.7.11 and memchr 2.8.3 test builds, `FVTest/Opt/midval/real_fold_*.clif`),
  each rejected before (without hints and with them, `*_c0_rejects`) and accepted by `checkCertC`
  with the hints and fold requests `emitC` gives (decided), with the simulation and the program
  refinement: `mul` (criterion: `brif (icmp ule (imul 160, 48), 4096)`), `table` (`brif (icmp
  ugt 0, 0xffff_ffff)` and a `br_table` on `ireduce.i32` of a constant of another block, with a
  `try_call`), `dom` (quickcheck: a `brif` on a block parameter that constant-phi removal turns
  into a constant once the unreachable block is gone; it was a `rewrite:domtree` rejection).
-/

namespace Opt.MidVal.FoldWitness

open Clif Pairs NormWitness CondWitness

/-- The verdict of the checker with branch-condition hints but without folding (`checkC0`). -/
def acceptsC0 (f g : String) : Option Bool := do
  pure (checkC0 (ConstPhi.run (← fn? f)) (← fn? g)).isOk

/-! ## Hand-made pairs -/

def ultF : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    v1 = iconst.i32 64\n    v2 = iconst.i32 0\n    v3 = icmp ult v1, v2\n    brif v3, block1, block2\n\nblock1:\n    v4 = iconst.i32 1\n    return v4\n\nblock2:\n    v5 = iconst.i32 0\n    return v5\n}"
def ultG : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    jump block2\n\nblock2:\n    v5 = iconst.i32 0\n    return v5\n}"

theorem pos_ult : acceptsC ultF ultG = some true := by native_decide
theorem pos_ult_check_rejects : accepts ultF ultG = some false := by native_decide
theorem pos_ult_c0_rejects : acceptsC0 ultF ultG = some false := by native_decide

def crossF : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    v1 = iconst.i8 1\n    jump block1\n\nblock1:\n    brif v1, block2, block3\n\nblock2:\n    v4 = iconst.i32 1\n    return v4\n\nblock3:\n    v5 = iconst.i32 0\n    return v5\n}"
def crossG : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    jump block1\n\nblock1:\n    jump block2\n\nblock2:\n    v4 = iconst.i32 1\n    return v4\n}"

theorem pos_cross : acceptsC crossF crossG = some true := by native_decide
theorem pos_cross_check_rejects : accepts crossF crossG = some false := by native_decide
theorem pos_cross_c0_rejects : acceptsC0 crossF crossG = some false := by native_decide

def tableF : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    v1 = iconst.i32 1\n    br_table v1, block1, [block2, block3]\n\nblock1:\n    v4 = iconst.i32 1\n    return v4\n\nblock2:\n    v5 = iconst.i32 2\n    return v5\n\nblock3:\n    v6 = iconst.i32 3\n    return v6\n}"
def tableG : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    jump block3\n\nblock3:\n    v6 = iconst.i32 3\n    return v6\n}"

theorem pos_table : acceptsC tableF tableG = some true := by native_decide
theorem pos_table_check_rejects : accepts tableF tableG = some false := by native_decide
theorem pos_table_c0_rejects : acceptsC0 tableF tableG = some false := by native_decide

/-! ## Negative pairs -/

/-- `f`: the entry block computes `body` and branches on `c` to `block1` (returns 1) or `block2`
(returns 0). -/
def fnBr2 (body : List Stmt) (c : ValueId) : Function :=
  { name := "f", sig := { params := [ap .i32], returns := [ap .i32], callConv := none },
    blocks := [
      { id := 0, params := [(0, .i32)], cold := false, body, term := .brif c ⟨1, []⟩ ⟨2, []⟩ },
      { id := 1, params := [], cold := false, body := [{ results := [4], inst := .iconst .i32 1 }],
        term := .ret [4] },
      { id := 2, params := [], cold := false, body := [{ results := [5], inst := .iconst .i32 0 }],
        term := .ret [5] }] }

/-- `g`: the entry block jumps to block `k`, which returns `r`. -/
def fnJump (k : BlockId) (res : ValueId) (r : BitVec 32) : Function :=
  { name := "f", sig := { params := [ap .i32], returns := [ap .i32], callConv := none },
    blocks := [
      { id := 0, params := [(0, .i32)], cold := false, body := [], term := .jump ⟨k, []⟩ },
      { id := k, params := [], cold := false, body := [{ results := [res], inst := .iconst .i32 r }],
        term := .ret [res] }] }

def ultFn : Function :=
  fnBr2 [{ results := [1], inst := .iconst .i32 64 }, { results := [2], inst := .iconst .i32 0 },
    { results := [3], inst := .icmp .ult .i32 1 2 }] 3

theorem ultF_text : fn? ultF = some ultFn := by native_decide

/-- The fold keeps the block the constant selects (`block2`) and drops the other (`block1`). -/
theorem ult_blocks : ((foldPre (ConstPhi.run ultFn) [0]).blocks.map (·.id)) = [0, 2] := by
  native_decide

/-! ### A branch on a parameter -/

def paramF : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    brif v0, block1, block2\n\nblock1:\n    v4 = iconst.i32 1\n    return v4\n\nblock2:\n    v5 = iconst.i32 0\n    return v5\n}"

def paramFn : Function := fnBr2 [] 0
def jump2Fn : Function := fnJump 2 5 0

theorem paramF_text : fn? paramF = some paramFn := by native_decide
theorem ultG_text : fn? ultG = some jump2Fn := by native_decide

/-- A branch on a parameter is not folded. -/
theorem param_not_folded : foldBr paramFn [0] = paramFn := by native_decide

theorem neg_param : acceptsC paramF ultG = some false := by native_decide

/-- For `v0 = 1`, `f` returns 1 and `g` 0. -/
theorem param_not_sim : ¬ FunSimMU paramFn jump2Fn :=
  not_funSimMU_ret_ne (b := paramFn.blocks.head!) (b' := jump2Fn.blocks.head!)
    (args := [⟨.i32, 1⟩]) (regs := Regs.empty.set 0 ⟨.i32, 1⟩) (m := Mem.empty)
    (vals := [⟨.i32, 1⟩]) (vals' := [⟨.i32, 0⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.refl _ _))) rfl
    (.step rfl (.step rfl (.refl _ _))) rfl (by decide)

/-- The re-check rejects every certificate and every hint list (fold requests included). -/
theorem param_rejected (cert : Cert) (hints : List (BlockId × List Wrap)) :
    checkCertC (ConstPhi.run paramFn) jump2Fn cert hints = false := by
  cases h : checkCertC (ConstPhi.run paramFn) jump2Fn cert hints
  · rfl
  · exact absurd (checkedC_simMU h) param_not_sim

/-! ### The other block kept -/

def keepWrongG : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    jump block1\n\nblock1:\n    v4 = iconst.i32 1\n    return v4\n}"

def jump1Fn : Function := fnJump 1 4 1

theorem keepWrongG_text : fn? keepWrongG = some jump1Fn := by native_decide

theorem neg_keep_wrong : acceptsC ultF keepWrongG = some false := by native_decide

/-- `64 <u 0` is false: `f` returns 0, `g` 1. -/
theorem keep_wrong_not_sim : ¬ FunSimMU ultFn jump1Fn :=
  not_funSimMU_ret_ne (b := ultFn.blocks.head!) (b' := jump1Fn.blocks.head!)
    (args := [⟨.i32, 7⟩]) (regs := Regs.empty.set 0 ⟨.i32, 7⟩) (m := Mem.empty)
    (vals := [⟨.i32, 0⟩]) (vals' := [⟨.i32, 1⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.step rfl (.step rfl (.step rfl (.refl _ _))))))
    rfl (.step rfl (.step rfl (.refl _ _))) rfl (by decide)

theorem keep_wrong_rejected (cert : Cert) (hints : List (BlockId × List Wrap)) :
    checkCertC (ConstPhi.run ultFn) jump1Fn cert hints = false := by
  cases h : checkCertC (ConstPhi.run ultFn) jump1Fn cert hints
  · rfl
  · exact absurd (checkedC_simMU h) keep_wrong_not_sim

/-! ### A `br_table` folded to the wrong entry -/

def tableWrongG : String := "function %f(i32) -> i32 {\nblock0(v0: i32):\n    jump block2\n\nblock2:\n    v5 = iconst.i32 2\n    return v5\n}"

def tableFn : Function :=
  { name := "f", sig := { params := [ap .i32], returns := [ap .i32], callConv := none },
    blocks := [
      { id := 0, params := [(0, .i32)], cold := false,
        body := [{ results := [1], inst := .iconst .i32 1 }],
        term := .brTable 1 ⟨1, []⟩ [⟨2, []⟩, ⟨3, []⟩] },
      { id := 1, params := [], cold := false, body := [{ results := [4], inst := .iconst .i32 1 }],
        term := .ret [4] },
      { id := 2, params := [], cold := false, body := [{ results := [5], inst := .iconst .i32 2 }],
        term := .ret [5] },
      { id := 3, params := [], cold := false, body := [{ results := [6], inst := .iconst .i32 3 }],
        term := .ret [6] }] }

def tableWrongFn : Function := fnJump 2 5 2

theorem tableF_text : fn? tableF = some tableFn := by native_decide
theorem tableWrongG_text : fn? tableWrongG = some tableWrongFn := by native_decide

theorem neg_table : acceptsC tableF tableWrongG = some false := by native_decide

/-- Entry 1 of the table is `block3`: `f` returns 3, `g` 2. -/
theorem table_not_sim : ¬ FunSimMU tableFn tableWrongFn :=
  not_funSimMU_ret_ne (b := tableFn.blocks.head!) (b' := tableWrongFn.blocks.head!)
    (args := [⟨.i32, 0⟩]) (regs := Regs.empty.set 0 ⟨.i32, 0⟩) (m := Mem.empty)
    (vals := [⟨.i32, 3⟩]) (vals' := [⟨.i32, 2⟩])
    rfl rfl rfl rfl rfl (.step rfl (.step rfl (.step rfl (.refl _ _)))) rfl
    (.step rfl (.step rfl (.refl _ _))) rfl (by decide)

theorem table_rejected (cert : Cert) (hints : List (BlockId × List Wrap)) :
    checkCertC (ConstPhi.run tableFn) tableWrongFn cert hints = false := by
  cases h : checkCertC (ConstPhi.run tableFn) tableWrongFn cert hints
  · rfl
  · exact absurd (checkedC_simMU h) table_not_sim

/-! ## Real pairs -/

/-- The verdict of the checker with branch-condition hints but without folding, on a decoded
dump pair. -/
def c0Verdict (fT gT : String) : Option Bool := do
  let f ← RealWitness.decode fT
  let g ← RealWitness.decode gT
  pure (checkC0 (ConstPhi.run f) g).isOk

def mulF : String := include_str "midval/real_fold_mul.unopt.clif"
def mulG : String := include_str "midval/real_fold_mul.opt.clif"
def tableF' : String := include_str "midval/real_fold_table.unopt.clif"
def tableG' : String := include_str "midval/real_fold_table.opt.clif"
def domF : String := include_str "midval/real_fold_dom.unopt.clif"
def domG : String := include_str "midval/real_fold_dom.opt.clif"

theorem real_mul_c0_rejects : c0Verdict mulF mulG = some false := by native_decide
theorem real_mul_checked : checkedC mulF mulG = some (true, true) := by native_decide
theorem real_mul_sim : SimRefinesC mulF mulG := simC_of_checked real_mul_checked

theorem real_table_c0_rejects : c0Verdict tableF' tableG' = some false := by native_decide
theorem real_table_checked : checkedC tableF' tableG' = some (true, true) := by native_decide
theorem real_table_sim : SimRefinesC tableF' tableG' := simC_of_checked real_table_checked

theorem real_dom_c0_rejects : c0Verdict domF domG = some false := by native_decide
theorem real_dom_checked : checkedC domF domG = some (true, true) := by native_decide
theorem real_dom_sim : SimRefinesC domF domG := simC_of_checked real_dom_checked

end Opt.MidVal.FoldWitness
