import FV.Backend.RegallocOps

/-! Conservative dead virtual-register producer cleanup. Instruction selection
and its validator still operate on the original VCode. This stage preserves
register numbering and every block/function field except instruction arrays. -/

namespace Backend.DeadCleanup

def pureAlu : ALUOp → Bool
  | .add | .sub | .orr | .orrNot | .and | .andNot | .eor | .eorNot => true
  | _ => false

/-- The explicit whitelist excludes flags, memory accesses, calls, traps and control. -/
def pureForm : MInst → Bool
  | .mov .. | .movWide .. | .loadAddr .. => true
  | .aluRRR op .. | .aluRRImm12 op .. | .aluRRImmLogic op ..
  | .aluRRImmShift op .. | .aluRRRShift op .. | .aluRRRExtend op .. => pureAlu op
  | .aluRRRR .mAdd .. | .aluRRRR .mSub .. => true
  | _ => false

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

/-- Scan backwards; removing a dead producer does not make its inputs live. -/
def scan (nregs : Nat) : List MInst → List Nat → List MInst × List Nat
  | [], live => ([], live)
  | m :: ms, exit =>
    let (kept, live) := scan nregs ms exit
    if discard m live then (kept, live)
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

end Backend.DeadCleanup
