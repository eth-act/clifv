module

public import FV.Backend.RegallocOps

@[expose] public section

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
one-operand bit operations (`rbit`/`clz`/`cls`/`rev*`), and `cset`, which reads the flags but
writes only its def. Cranelift does not lower an instruction none of whose results is used
(`machinst/lower.rs`), e.g. the boolean of an `icmp` that the `brif` rule re-compares, with the
operand extension of that compare (#552), or the `ishl` that the `bor` rule folds into a shifted
operand (`isa/aarch64/inst.isle`, `alu_rs_imm_logic_commutative` with `lshl_from_imm64`, #555).
The shifts and bit operations are outside `pureNoFlags`, whose forms `ABIReadOnly` accepts. -/
def pureForm : MInst → Bool
  | .mov .. | .movWide .. | .loadAddr .. | .extend .. | .cset .. | .bitRR .. => true
  | .aluRRR op .. | .aluRRImmShift op .. => pureAlu op || shiftOp op
  | .aluRRImm12 op .. | .aluRRImmLogic op .. | .aluRRRShift op .. | .aluRRRExtend op .. =>
    pureAlu op
  | .aluRRRR .mAdd .. | .aluRRRR .mSub .. => true
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

/-- Cranelift's compares (`cmp`/`cmn`/`tst`: `subs`/`adds`/`ands` into `xzr`) in the forms
`ispec` specifies: they write all four NZCV flags from their register uses only, read no
flags and define no register. -/
def cmpForm : MInst → Bool
  | .aluRRR .subS _ .xzr (.vreg ..) _ => true
  | .aluRRImm12 .subS _ .xzr (.vreg ..) _ => true
  | .aluRRImm12 .addS _ .xzr (.vreg ..) _ => true
  | .aluRRRExtend .subS _ .xzr (.vreg ..) (.vreg ..) _ => true
  | .aluRRImmLogic .andS _ .xzr (.vreg ..) _ => true
  | _ => false

@[simp] def isJump : MInst → Bool
  | .jump _ => true
  | _ => false

/-- The flags are dead at the head of a retained suffix: a compare overwrites them after
flag-free producers only, before anything reads them; or, when the block's flags are dead at
its exit (`e`, `exitDead`), its `jump` comes first. -/
@[simp] def flagsDead (e : Bool) : List MInst → Bool
  | [] => false
  | k :: ks => cmpForm k || (flagFree k && flagsDead e ks) || (isJump k && e)

/-- A compare whose flags are dead: what is left of an `icmp` whose user (`brif`, `select`)
compares again once its dead `cset` is gone (#552). Cranelift never lowers that `icmp`: no
lowered instruction uses its result (`machinst/lower.rs`, `lower_clif_block`), and its
users' rules look through it to its operands (`isa/aarch64/lower.isle`). -/
@[simp] def dropCmp (e : Bool) (m : MInst) (kept : List MInst) : Bool :=
  cmpForm m && (defs m).isEmpty && flagsDead e kept

/-- Scan backwards; removing a dead producer does not make its inputs live. `e`: the flags are
dead at the block's exit. -/
def scan (nregs : Nat) (e : Bool) : List MInst → List Nat → List MInst × List Nat
  | [], live => ([], live)
  | m :: ms, exit =>
    let (kept, live) := scan nregs e ms exit
    if discard m live || dropCmp e m kept then (kept, live)
    else (m :: kept, uses nregs m ++ live.filter (fun n => !(defs m).contains n))

def blockUses (nregs : Nat) (b : VBlock) : List Nat :=
  regNums b.branchArgs.toList ++ b.insts.toList.flatMap (uses nregs)

/-- All block reads, including the current block, are live at every boundary.
Including the current block handles self-loops without an SSA assumption. -/
def exitLive (vc : VCode) (_idx : Nat) (_b : VBlock) : List Nat :=
  vc.blocks.toList.flatMap (blockUses vc.classes.size)

/-- The flags are dead at the entry of the block labelled `l` (the CFG's successor: the first
block with that label): its own instructions overwrite them by a compare after flag-free
producers only. -/
def entryDead (vc : VCode) (l : Label) : Bool :=
  match vc.blocks.findIdx? (·.label == l) with
  | some s => match vc.blocks[s]? with
    | some b => flagsDead false b.insts.toList
    | none => false
  | none => false

/-- The block ends with a `jump` to a block whose flags are dead at entry. -/
def jumpsToDead (vc : VCode) (b : VBlock) : Bool :=
  match b.insts.back? with
  | some (.jump l) => entryDead vc l
  | _ => false

/-- The flags are dead at the exit of the blocks labelled `lb`: each ends with a `jump` to a
block whose flags are dead at entry, e.g. an unused `icmp` before the `jump` to a block that
compares again (#552). Keyed by the label, so that it is unchanged when `prepare` retargets a
terminator. -/
def exitDead (vc : VCode) (lb : Label) : Bool :=
  vc.blocks.all fun b => b.label != lb || jumpsToDead vc b

def cleanBlock (vc : VCode) (idx : Nat) (b : VBlock) : VBlock :=
  { b with insts :=
      (scan vc.classes.size (exitDead vc b.label) b.insts.toList (exitLive vc idx b)).1.toArray }

def clean (vc : VCode) : VCode :=
  { vc with blocks := vc.blocks.mapIdx (cleanBlock vc) }

/-- An invalid CFG is left untouched. Successful CFG construction supplies
the block-termination fact needed by the generic simulation. -/
def prune (vc : VCode) : VCode :=
  match vc.cfg with
  | .ok _ => clean vc
  | .error _ => vc

end Backend.DeadCleanup
