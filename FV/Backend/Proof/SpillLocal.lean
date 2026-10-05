import FV.Backend.SpillAlloc

/-!
# The spill allocator's instruction-local facts (V4 (a), step 3)

`spillInst` gives every operand of an instruction a register (`spillLocs`): a fixed operand its
register, a reuse operand the register of the operand it reuses, every other operand the next
register of its class from `spillPool` minus the instruction's fixed registers and clobbers.
`OpsOk ops clob` lists what the operands must satisfy for the checker's static checks
(`CheckCtx.checkStatic`) to accept these locations (`checkStatic_spill`), and for the loads in
front of the instruction to leave every use's vreg in its location (`spillLocs_useEq`: two
uses in one location carry one vreg). `SpillInstOk` adds the instruction-level facts
(`operands` succeeds; the uses of a `Rets` avoid the callee-saved registers, which the restores
in front of it fill). `EdgesOk` collects the CFG-level facts (branch arguments against the
target's parameters, a `try_call`'s successors).

All of this is state-independent; the dataflow invariant that the homes hold their vregs
(`docs/TO-PROVE.md` V4 step 4) is not part of it.
-/

namespace Backend.Proof.Spill
open Backend

deriving instance ReflBEq, LawfulBEq for RegClass
deriving instance ReflBEq, LawfulBEq for Reg
/-! ## The facts -/

/-- A constraint the spill allocator meets with a fresh scratch register (`spillLocs`'s
catch-all case). -/
def scratch : Constraint → Bool
  | .fixed _ | .reuse _ => false
  | _ => true

/-- The scratch registers of class `c` (`spillLocs`'s `free`). -/
def freeRegs (ops : Array Operand) (clob : List Reg) (c : RegClass) : List Reg :=
  (spillPool c).filter fun r => !(fixedRegs ops ++ clob).contains r

/-- The number of scratch operands of class `c` in `os`. -/
def nScratch (c : RegClass) (os : List Operand) : Nat :=
  (os.filter fun o => scratch o.con && o.cls == c).length

/-- **The operand facts** the spill allocation of one instruction needs (operands `ops`,
clobbers `clob`). -/
structure OpsOk (ops : Array Operand) (clob : List Reg) : Prop where
  /-- No operand must be on the stack (the allocation puts every operand in a register). -/
  noStack : ∀ o ∈ ops.toList, o.con ≠ .stack
  /-- No late uses. -/
  useEarly : ∀ o ∈ ops.toList, o.kind = .use → o.pos = .early
  /-- A fixed register is allocatable and of the operand's class. -/
  fixedReg : ∀ o ∈ ops.toList, ∀ p, o.con = .fixed p → p.allocatable = true ∧ p.realClass? = some o.cls
  /-- Two fixed uses of one register carry one vreg. -/
  fixedUse : ∀ o ∈ ops.toList, ∀ o' ∈ ops.toList, ∀ p, o.kind = .use → o'.kind = .use →
    o.con = .fixed p → o'.con = .fixed p → o.vreg = o'.vreg
  /-- Fixed defs are pairwise distinct. -/
  fixedDefs : ∀ (j j' : Nat) (o o' : Operand) (p : Reg), ops.toList[j]? = some o → ops.toList[j']? = some o' →
    o.kind = .def → o'.kind = .def → o.con = .fixed p → o'.con = .fixed p → j = j'
  /-- A fixed def is not clobbered. -/
  fixedDefClob : ∀ o ∈ ops.toList, ∀ p, o.kind = .def → o.con = .fixed p → p ∉ clob
  /-- An early def gets a scratch register. -/
  earlyDef : ∀ o ∈ ops.toList, o.kind = .def → o.pos = .early → scratch o.con = true
  /-- A reuse operand is a late def reusing a scratch use of its class, the only one reusing
  it. -/
  reuse : ∀ (j : Nat) (o : Operand) (i : Nat), ops.toList[j]? = some o → o.con = .reuse i → o.kind = .def ∧ o.pos = .late ∧
    ∃ oi, ops.toList[i]? = some oi ∧ oi.kind = .use ∧ scratch oi.con = true ∧ oi.cls = o.cls ∧
      ∀ (j' : Nat) (o' : Operand), ops.toList[j']? = some o' → o'.con = .reuse i → j' = j
  /-- Enough scratch registers. -/
  enough : ∀ c, nScratch c ops.toList ≤ (freeRegs ops clob c).length
  /-- The defs carry pairwise distinct vregs. -/
  defsNodup : ((ops.toList.filter (·.kind == .def)).map (·.vreg)).Nodup

/-- **The instruction facts**: the operand view exists and meets `OpsOk`; a `Rets`'s operands
are fixed outside the callee-saved registers. -/
def SpillInstOk (i : MInst) : Prop :=
  ∃ ops, i.operands = .ok ops ∧ OpsOk ops i.clobbers ∧
    ∀ us, i = .rets us → ∀ o ∈ ops.toList, ∃ p, o.con = .fixed p ∧ p ∉ calleeSaved

/-- **The CFG facts** (successors `succs`, predecessors `preds` of `vc.cfg`). -/
structure EdgesOk (vc : VCode) (succs preds : Array (Array Nat)) : Prop where
  /-- The entry block exists, is no branch target and has no parameters. -/
  entry : vc.blocks.size ≠ 0 ∧ preds[0]? = some #[] ∧ (vc.blocks[0]!).params = #[]
  /-- A block with branch arguments ends in an instruction without operands and has one
  successor, whose parameters match the arguments (vregs of one class each) and are pairwise
  distinct. -/
  args : ∀ (b : Nat) (vb : VBlock), vc.blocks[b]? = some vb → vb.branchArgs ≠ #[] →
    (∃ i, vb.insts.back? = some i ∧ i.operands = .ok #[]) ∧ ∃ t tb,
    succs[b]? = some #[t] ∧ vc.blocks[t]? = some tb ∧ tb.params.size = vb.branchArgs.size ∧
    (∀ (k : Nat) (a p : Reg), vb.branchArgs[k]? = some a → tb.params[k]? = some p →
      ∃ x y c, a = .vreg x c ∧ p = .vreg y c) ∧
    (tb.params.toList.map Reg.homeNum).Nodup
  /-- Without branch arguments, every successor is parameterless. -/
  noArgs : ∀ (b : Nat) (vb : VBlock) (ss : Array Nat) (s : Nat) (sb : VBlock),
    vc.blocks[b]? = some vb → vb.branchArgs = #[] → succs[b]? = some ss →
    s ∈ ss.toList → vc.blocks[s]? = some sb → sb.params = #[]
  /-- A `try_call`'s block has no branch arguments and is the only predecessor of each of its
  successors. -/
  tryEdge : ∀ (b : Nat) (vb : VBlock) (info : CallInfo) (ti : TryInfo) (ss : Array Nat) (s : Nat),
    vc.blocks[b]? = some vb → vb.insts.back? = some (.tryCall info ti) →
    vb.branchArgs = #[] ∧ (succs[b]? = some ss → s ∈ ss.toList → preds[s]? = some #[b])

/-- Every vreg the code mentions has the class `vc.classes` records for it (so each vreg has
one home). -/
def ClassesOk (vc : VCode) : Prop :=
  (∀ (b : Nat) (vb : VBlock) (k : Nat) (i : MInst) (ops : Array Operand), vc.blocks[b]? = some vb →
    vb.insts[k]? = some i → i.operands = .ok ops → ∀ o ∈ ops.toList, vc.classes[o.vreg]? = some o.cls) ∧
  ∀ (b : Nat) (vb : VBlock), vc.blocks[b]? = some vb →
    ∀ r ∈ vb.params.toList ++ vb.branchArgs.toList, ∃ n c, r = .vreg n c ∧ vc.classes[n]? = some c

/-- **The local facts of a prepared VCode**: every instruction meets `SpillInstOk`, the CFG
meets `EdgesOk`, the classes are consistent. -/
def SpillLocalOk (vc : VCode) : Prop :=
  (∀ (b : Nat) (vb : VBlock) (k : Nat) (i : MInst), vc.blocks[b]? = some vb → vb.insts[k]? = some i →
    SpillInstOk i) ∧ ClassesOk vc ∧
  ∀ succs preds, vc.cfg = .ok (succs, preds) → EdgesOk vc succs preds
/-! ## The locations `spillLocs` computes -/

/-- `spillLocs`'s fold step. -/
def sstep (st : Array Loc × List Reg × List Reg) (o : Operand) : Array Loc × List Reg × List Reg :=
  let (acc, is, fs) := st
  match o.con with
  | .fixed p => (acc.push (.reg p), is, fs)
  | .reuse _ => (acc.push (.reg .sp), is, fs)
  | _ => match o.cls with
    | .int => match is with
      | r :: rest => (acc.push (.reg r), rest, fs)
      | [] => (acc.push (.reg .sp), is, fs)
    | .float => match fs with
      | r :: rest => (acc.push (.reg r), is, rest)
      | [] => (acc.push (.reg .sp), is, fs)

/-- The scratch lists by class. -/
def byCls (is fs : List Reg) : RegClass → List Reg
  | .int => is
  | .float => fs

/-- The location `sstep` gives operand `o` after the operands `pre`. -/
def baseLoc (is fs : List Reg) (pre : List Operand) (o : Operand) : Loc :=
  match o.con with
  | .fixed p => .reg p
  | .reuse _ => .reg .sp
  | _ => match (byCls is fs o.cls)[nScratch o.cls pre]? with
    | some r => .reg r
    | none => .reg .sp

/-- The base locations (before the reuse operands are resolved). -/
def baseLocs (ops : Array Operand) (clob : List Reg) : Array Loc :=
  (ops.foldl sstep (#[], freeRegs ops clob .int, freeRegs ops clob .float)).1

theorem spillLocs_eq (ops : Array Operand) (clob : List Reg) :
    spillLocs ops clob = (ops.zip (baseLocs ops clob)).map fun (o, l) => match o.con with
      | .reuse i => (baseLocs ops clob)[i]?.getD (.reg .sp)
      | _ => l := rfl

end Backend.Proof.Spill
