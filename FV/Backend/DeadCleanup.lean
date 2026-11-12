import FV.Backend.RegallocOps
import Std.Data.HashSet

/-! Conservative dead virtual-register producer cleanup. Instruction selection
and its validator still operate on the original VCode. This stage preserves
register numbering and every block/function field except instruction arrays. -/

namespace Backend.DeadCleanup

def pureAlu : ALUOp → Bool
  | .add | .sub | .orr | .orrNot | .and | .andNot | .eor | .eorNot => true
  | _ => false

/-- The producers that neither read nor write the flags: no flag access, memory access,
call, trap or control. -/
def pureNoFlags : MInst → Bool
  | .mov .. | .movWide .. | .loadAddr .. => true
  | .aluRRR op .. | .aluRRImm12 op .. | .aluRRImmLogic op ..
  | .aluRRImmShift op .. | .aluRRRShift op .. | .aluRRRExtend op .. => pureAlu op
  | .aluRRRR .mAdd .. | .aluRRRR .mSub .. => true
  | _ => false

/-- The shifts (`lsl`/`lsr`/`asr`, by register or immediate). -/
@[simp] def shiftOp : ALUOp → Bool
  | .lsl | .lsr | .asr => true
  | _ => false

/-- The explicit whitelist excludes flag writers, memory accesses, calls, traps and control:
`pureNoFlags`, the integer extensions (`uxtb`/`sxth`/…), the shifts (`shiftOp`) and the
one-operand bit operations (`rbit`/`clz`/`cls`/`rev*`), the float constant moves (`fmov #imm`,
`movi`, #967: they may sit between a dead `fcmp` and the `fcmp` of its `select`), and `cset`,
which reads the flags but writes only its def. Cranelift does not lower an instruction none of
whose results is used (`machinst/lower.rs`), e.g. the boolean of an `icmp` that the `brif` rule
re-compares, with the operand extension of that compare (#552), or the `ishl` that the `bor`
rule folds into a shifted operand (`isa/aarch64/inst.isle`, `alu_rs_imm_logic_commutative` with
`lshl_from_imm64`, #555).
The shifts and bit operations are outside `pureNoFlags`, whose forms `ABIReadOnly` accepts. -/
def pureForm : MInst → Bool
  | .mov .. | .movWide .. | .loadAddr .. | .extend .. | .cset .. | .bitRR .. => true
  | .aluRRR op .. | .aluRRImmShift op .. => pureAlu op || shiftOp op
  | .aluRRImm12 op .. | .aluRRImmLogic op .. | .aluRRRShift op .. | .aluRRRExtend op .. =>
    pureAlu op
  | .aluRRRR .mAdd .. | .aluRRRR .mSub .. => true
  | .fpuMoveFPImm .. | .vecDupImm .. => true
  | _ => false

theorem pureForm_of_pureNoFlags {i : MInst} (h : pureNoFlags i = true) : pureForm i = true := by
  cases i with
  | aluRRRR op sz rd rn rm ra => cases op <;> simp_all [pureNoFlags, pureForm]
  | _ => simp_all [pureNoFlags, pureForm]

/-- The producers that neither read nor write the flags (`pureForm` but `cset`): what may sit
between a dropped compare and the compare that overwrites its flags. -/
def flagFree (m : MInst) : Bool :=
  pureForm m && !(match m with | .cset .. => true | _ => false)

theorem pureForm_of_flagFree {i : MInst} (h : flagFree i = true) : pureForm i = true := by
  simp only [flagFree, Bool.and_eq_true] at h
  exact h.1

def regNums (rs : List Reg) : List Nat :=
  rs.filterMap fun r => match r with | .vreg n _ => some n | _ => none

/-- Includes fixed ABI uses: `MInst.uses` alone omits call/return pairs. Unknown
operand views preserve all classed registers, preventing speculative removal. -/
def uses (nregs : Nat) (m : MInst) : List Nat :=
  match m.operands with
  | .ok ops => (ops.toList.filter fun o => o.kind == .use).map (·.vreg)
  | .error _ => List.range nregs

def defs (m : MInst) : List Nat :=
  match m.operands with
  | .ok ops => (ops.toList.filter fun o => o.kind == .def).map (·.vreg)
  | .error _ => []

def discard (m : MInst) (live : List Nat) : Bool :=
  pureForm m && m.clobbers.isEmpty && m.defs.all Reg.isVirtual &&
    !(defs m).isEmpty && (defs m).all (fun n => !live.contains n)

/-- Cranelift's compares (`cmp`/`cmn`/`tst`: `subs`/`adds`/`ands` into `xzr`; the float
compare `fcmp` of two float vregs) in the forms `ispec` specifies: they write all four NZCV
flags from their register uses only, read no flags and define no register. -/
def cmpForm : MInst → Bool
  | .aluRRR .subS _ .xzr (.vreg ..) _ => true
  | .aluRRImm12 .subS _ .xzr (.vreg ..) _ => true
  | .aluRRImm12 .addS _ .xzr (.vreg ..) _ => true
  | .aluRRRExtend .subS _ .xzr (.vreg ..) (.vreg ..) _ => true
  | .aluRRImmLogic .andS _ .xzr (.vreg ..) _ => true
  | .fpuCmp _ (.vreg _ .float) (.vreg _ .float) => true
  | _ => false

@[simp] def isJump : MInst → Bool
  | .jump _ => true
  | _ => false

/-- The flags are dead at the head of a retained suffix: a compare overwrites them after
flag-free producers only, before anything reads them. (A rule treating the flags as dead
across a `jump` to a block that compares first never changed generated code and was removed,
#608.) -/
@[simp] def flagsDead : List MInst → Bool
  | [] => false
  | k :: ks => cmpForm k || (flagFree k && flagsDead ks)

/-- A compare whose flags are dead: what is left of an `icmp` or `fcmp` whose user (`brif`,
`select`, `uextend`) compares again once its dead `cset` is gone (#552, #967). Cranelift never
lowers that compare: no lowered instruction uses its result (`machinst/lower.rs`,
`lower_clif_block`), and its users' rules look through it to its operands
(`isa/aarch64/lower.isle`). -/
@[simp] def dropCmp (m : MInst) (kept : List MInst) : Bool :=
  cmpForm m && (defs m).isEmpty && flagsDead kept

/-- Scan backwards; removing a dead producer does not make its inputs live. -/
def scan (nregs : Nat) : List MInst → List Nat → List MInst × List Nat
  | [], live => ([], live)
  | m :: ms, exit =>
    let (kept, live) := scan nregs ms exit
    if discard m live || dropCmp m kept then (kept, live)
    else (m :: kept, uses nregs m ++ live.filter (fun n => !(defs m).contains n))

def blockUses (nregs : Nat) (b : VBlock) : List Nat :=
  regNums b.branchArgs.toList ++ b.insts.toList.flatMap (uses nregs)

/-- Every read of every block, including the current block (self-loops need no SSA
assumption): the boundary of the first round. -/
def allUses (vc : VCode) : List Nat :=
  vc.blocks.toList.flatMap (blockUses vc.classes.size)

/-- The reads of what a scan with boundary `L` keeps of every block, and every branch
argument. -/
def keptUses (vc : VCode) (L : List Nat) : List Nat :=
  vc.blocks.toList.flatMap fun b =>
    regNums b.branchArgs.toList ++
      (scan vc.classes.size b.insts.toList L).1.flatMap (uses vc.classes.size)

/-! ## The scan as the compiler runs it

`scan` keeps its live set as a list: a block of `n` instructions costs `n²` list operations, and
the boundary takes a second round (#968). The compiler runs both rounds with a hash set
(`scanH`), which keeps the same code (`scanH_kept`): the first round through `keptUses`
(`keptUses_eq_impl`, `@[csimp]`, registered before `exitLive` so that its compiled code uses
it), the second through `clean` (`clean_eq_impl`, `@[csimp]`), which computes the boundary once
per function. -/

/-- `discard` against a hash set of live registers. -/
def discardH (m : MInst) (live : Std.HashSet Nat) : Bool :=
  pureForm m && m.clobbers.isEmpty && m.defs.all Reg.isVirtual &&
    !(defs m).isEmpty && (defs m).all (fun n => !live.contains n)

/-- `scan` with a hash set of live registers. -/
def scanH (nregs : Nat) : List MInst → Std.HashSet Nat → List MInst × Std.HashSet Nat
  | [], live => ([], live)
  | m :: ms, exit =>
    let (kept, live) := scanH nregs ms exit
    if discardH m live || dropCmp m kept then (kept, live)
    else (m :: kept, (uses nregs m).foldl (·.insert ·) ((defs m).foldl (·.erase ·) live))

theorem liveErase_contains (ds : List Nat) (H : Std.HashSet Nat) (n : Nat) :
    (ds.foldl (·.erase ·) H).contains n = (!ds.contains n && H.contains n) := by
  induction ds generalizing H with
  | nil => simp
  | cons d ds ih =>
    rw [List.foldl_cons, ih, Std.HashSet.contains_erase, List.contains_cons]
    by_cases hdn : d = n
    · subst hdn
      simp
    · have h1 : (d == n) = false := by simpa using hdn
      have h2 : (n == d) = false := by simp [Ne.symm hdn]
      simp [h1, h2]

theorem liveInsert_contains (us : List Nat) (H : Std.HashSet Nat) (n : Nat) :
    (us.foldl (·.insert ·) H).contains n = (us.contains n || H.contains n) := by
  induction us generalizing H with
  | nil => simp
  | cons u us ih =>
    rw [List.foldl_cons, ih, Std.HashSet.contains_insert, List.contains_cons]
    by_cases hun : u = n
    · subst hun
      simp
    · have h1 : (u == n) = false := by simpa using hun
      have h2 : (n == u) = false := by simp [Ne.symm hun]
      simp [h1, h2]

/-- The hash set of a list's registers. -/
def liveSet (L : List Nat) : Std.HashSet Nat := L.foldl (·.insert ·) ∅

theorem liveSet_contains (L : List Nat) (n : Nat) : (liveSet L).contains n = L.contains n := by
  simp [liveSet, liveInsert_contains]

/-- `scanH` keeps what `scan` keeps, and its live set has the same members. -/
theorem scanH_kept (nregs : Nat) : ∀ (ms : List MInst) (L : List Nat) (H : Std.HashSet Nat),
    (∀ n, H.contains n = L.contains n) →
    (scanH nregs ms H).1 = (scan nregs ms L).1 ∧
      ∀ n, (scanH nregs ms H).2.contains n = (scan nregs ms L).2.contains n
  | [], _, _, h => ⟨rfl, h⟩
  | m :: ms, L, H, h => by
    obtain ⟨hk, hl⟩ := scanH_kept nregs ms L H h
    rcases h1 : scanH nregs ms H with ⟨k1, H1⟩
    rcases h2 : scan nregs ms L with ⟨k2, L2⟩
    rw [h1, h2] at hk hl
    simp only at hk hl
    subst hk
    have hd : discardH m H1 = discard m L2 := by
      have hf : (fun n => !H1.contains n) = (fun n => !L2.contains n) :=
        funext fun n => by rw [hl n]
      simp only [discardH, discard, hf]
    simp only [scanH, scan, h1, h2, hd]
    split
    · exact ⟨rfl, hl⟩
    · refine ⟨rfl, fun n => ?_⟩
      rw [liveInsert_contains, liveErase_contains, hl n, List.contains_append]
      cases hu : (uses nregs m).contains n <;> cases hd : (defs m).contains n <;>
        cases hL : L2.contains n <;> simp_all

/-- `keptUses` as the compiler runs it: `scanH` against the boundary's hash set. -/
def keptUsesImpl (vc : VCode) (L : List Nat) : List Nat :=
  let H := liveSet L
  vc.blocks.toList.flatMap fun b =>
    regNums b.branchArgs.toList ++
      (scanH vc.classes.size b.insts.toList H).1.flatMap (uses vc.classes.size)

@[csimp] theorem keptUses_eq_impl : @keptUses = @keptUsesImpl := by
  funext vc L
  simp only [keptUses, keptUsesImpl]
  congr 1
  funext b
  rw [(scanH_kept vc.classes.size b.insts.toList L (liveSet L) (liveSet_contains L)).1]

/-- The registers live at every block boundary: the reads of the code that a first round, with
every read live (`allUses`), keeps. A read of an instruction the first round drops does not
count, so the head of a dead chain goes too: the operand extension of a dropped compare, whose
only reader is that compare (#968; Cranelift lowers neither). The same set holds at every
boundary, including the current block's (self-loops). -/
def exitLive (vc : VCode) (_idx : Nat) (_b : VBlock) : List Nat :=
  keptUses vc (allUses vc)

def cleanBlock (vc : VCode) (idx : Nat) (b : VBlock) : VBlock :=
  { b with insts :=
      (scan vc.classes.size b.insts.toList (exitLive vc idx b)).1.toArray }

def clean (vc : VCode) : VCode :=
  { vc with blocks := vc.blocks.mapIdx (cleanBlock vc) }

/-- `clean` as the compiler runs it: the boundary's hash set is built once per function, not
once per block, and every block runs `scanH` against it. -/
def cleanImpl (vc : VCode) : VCode :=
  let H := liveSet (exitLive vc 0 default)
  { vc with blocks := vc.blocks.map fun b =>
      { b with insts := (scanH vc.classes.size b.insts.toList H).1.toArray } }

@[csimp] theorem clean_eq_impl : @clean = @cleanImpl := by
  funext vc
  simp only [clean, cleanImpl]
  congr 1
  apply Array.ext
  · simp
  · intro i _ _
    simp only [Array.getElem_mapIdx, Array.getElem_map, cleanBlock,
      (scanH_kept _ _ _ _ (liveSet_contains (exitLive vc 0 default))).1]
    rfl

/-- An invalid CFG is left untouched. Successful CFG construction supplies
the block-termination fact needed by the generic simulation. -/
def prune (vc : VCode) : VCode :=
  match vc.cfg with
  | .ok _ => clean vc
  | .error _ => vc

end Backend.DeadCleanup
