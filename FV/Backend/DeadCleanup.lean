import FV.Backend.RegallocOps

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

/-- The explicit whitelist excludes flag writers, memory accesses, calls, traps and control:
`pureNoFlags` and `cset`, which reads the flags but writes only its def. Cranelift does not
lower an instruction none of whose results is used (`machinst/lower.rs`), e.g. the boolean of
an `icmp` that the `brif` rule re-compares (#552). -/
def pureForm : MInst → Bool
  | .mov .. | .movWide .. | .loadAddr .. | .cset .. => true
  | .aluRRR op .. | .aluRRImm12 op .. | .aluRRImmLogic op ..
  | .aluRRImmShift op .. | .aluRRRShift op .. | .aluRRRExtend op .. => pureAlu op
  | .aluRRRR .mAdd .. | .aluRRRR .mSub .. => true
  | _ => false

theorem pureForm_of_pureNoFlags {i : MInst} (h : pureNoFlags i = true) : pureForm i = true := by
  cases i with
  | aluRRRR op sz rd rn rm ra => cases op <;> simp_all [pureNoFlags, pureForm]
  | _ => simp_all [pureNoFlags, pureForm]

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
@[simp] def cmpForm : MInst → Bool
  | .aluRRR .subS _ .xzr (.vreg ..) _ => true
  | .aluRRImm12 .subS _ .xzr (.vreg ..) _ => true
  | .aluRRImm12 .addS _ .xzr (.vreg ..) _ => true
  | .aluRRRExtend .subS _ .xzr (.vreg ..) (.vreg ..) _ => true
  | .aluRRImmLogic .andS _ .xzr (.vreg ..) _ => true
  | _ => false

/-- A compare whose flags the next retained instruction, itself a compare, overwrites before
anything reads them: what is left of an `icmp` whose user (`brif`, `select`) compares again
once its dead `cset` is gone (#552). Cranelift never lowers that `icmp`: no lowered
instruction uses its result (`machinst/lower.rs`, `lower_clif_block`). -/
@[simp] def dropCmp (m : MInst) (kept : List MInst) : Bool :=
  cmpForm m && (defs m).isEmpty && (kept.head?.map cmpForm).getD false

/-- Scan backwards; removing a dead producer does not make its inputs live. -/
def scan (nregs : Nat) : List MInst → List Nat → List MInst × List Nat
  | [], live => ([], live)
  | m :: ms, exit =>
    let (kept, live) := scan nregs ms exit
    if discard m live || dropCmp m kept then (kept, live)
    else (m :: kept, uses nregs m ++ live.filter (fun n => !(defs m).contains n))

def blockUses (nregs : Nat) (b : VBlock) : List Nat :=
  regNums b.branchArgs.toList ++ b.insts.toList.flatMap (uses nregs)

/-- All block reads, including the current block, are live at every boundary.
Including the current block handles self-loops without an SSA assumption. -/
def exitLive (vc : VCode) (_idx : Nat) (_b : VBlock) : List Nat :=
  vc.blocks.toList.flatMap (blockUses vc.classes.size)

def cleanBlock (vc : VCode) (idx : Nat) (b : VBlock) : VBlock :=
  { b with insts := (scan vc.classes.size b.insts.toList (exitLive vc idx b)).1.toArray }

def clean (vc : VCode) : VCode :=
  { vc with blocks := vc.blocks.mapIdx (cleanBlock vc) }

/-- An invalid CFG is left untouched. Successful CFG construction supplies
the block-termination fact needed by the generic simulation. -/
def prune (vc : VCode) : VCode :=
  match vc.cfg with
  | .ok _ => clean vc
  | .error _ => vc

end Backend.DeadCleanup
