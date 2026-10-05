import FV.Backend.Proof.SpillLocal
import FV.Backend.Proof.RegallocSound

/-!
# The spill allocation's dataflow invariant (V4 (a), step 4): the statement

`AllocChecked vc (spillAlloc vc)` (`FV/Backend/Proof/RegallocSound.lean`) asks for verified
in-states of every block. Since the register-level theorem chooses the initial vreg file
(`RegLevelCorrectEx`, `entryRho`), the entry in-state may have the home of every vreg holding it,
so no vreg has to be *defined* on every path to its uses. What remains is *availability*: "the home
of vreg `v` holds `v`" is lost only where the allocated code kills a def without storing it — the
defs of a terminator (a `try_call`'s live ones are stored at the start of its successors,
`entryStored`), the scratch defs past `MInst.keptDefs` — and for a parameter whose branch argument
is unavailable.

`SpillAvail vc D` is that must-analysis on the VCode, with explicit sets `D b` (availability on
entry to block `b`, before its entry stores): every vreg is available on entry to the entry block;
every use is available where it is read (`availAt`, from `D b` and the entry stores through the
block's instructions, `availInst`); every edge `b → s` delivers `D s` (`edgeAvail`: a parameter of
`s` is available iff its argument is, by the two-phase copy and the checker's parallel copy).

The in-states of the spill allocation are then: the home of every vreg in `D b` holds it, the save
slot of every callee-saved register holds its entry value (on entry to block 0: the register
itself), and on entry to a successor of a `try_call` the registers of the defs live on that edge
(`termEdgeDefs`) hold them. `SpillStep4` — each `spillInst` group, the argument copies, the saves,
restores and entry stores re-establish them — is proven (`spillStep4`,
`FV/Backend/Proof/SpillStep4.lean`). `SpillAvailable` (`FV/E2E/AllocDirect.lean`) asks for the sets
`D` of the pipeline's output.
-/

namespace Backend.Proof.Spill

open Backend

/-- The vregs of `i`'s defs that `spillInst` stores to their homes: the kept defs
(`MInst.keptDefs`) of an instruction that is not a terminator. -/
def storedDefs (i : MInst) (ops : Array Operand) : List Nat :=
  if i.isTerminator then [] else
    let defs := ops.toList.filter (·.kind == .def)
    (match i.keptDefs with
      | none => defs
      | some n => defs.take n).map Operand.vreg

/-- Availability after instruction `i` from availability `A` before it: the home of a def holds it
iff `spillInst` stores it; other homes are untouched. -/
def availInst (i : MInst) (A : Nat → Bool) (v : Nat) : Bool :=
  match i.operands with
  | .error _ => A v
  | .ok ops =>
    if (ops.toList.filter (·.kind == .def)).any (·.vreg == v) then (storedDefs i ops).contains v
    else A v

/-- Availability before instruction `k` of a block with instructions `insts`, from `A` at its
start. -/
def availAt (insts : Array MInst) (A : Nat → Bool) (k : Nat) : Nat → Bool :=
  (insts.toList.take k).foldl (fun A i => availInst i A) A

/-- The vregs the entry stores of block `s` put in their homes (`spillEntryStores`: the defs of
the only predecessor's terminator live on the edge, `termEdgeDefs`). -/
def entryStored (vc : VCode) (succs preds : Array (Array Nat)) (s : Nat) : List Nat :=
  match preds[s]? with
  | some #[b] =>
    match vc.blocks[b]?, succs[b]? with
    | some vb, some ss =>
      match ss.toList.idxOf? s with
      | some j => (termEdgeDefs vb j).map (·.1.vreg)
      | none => []
    | _, _ => []
  | _ => []

/-- Availability on entry to block `b` after its entry stores, from the set `D b`. -/
def availStart (vc : VCode) (succs preds : Array (Array Nat)) (D : Nat → Nat → Bool) (b : Nat)
    (v : Nat) : Bool :=
  D b v || (entryStored vc succs preds b).contains v

/-- Availability on entry to `sb` along an edge from `vb`, from availability `A` at the end of
`vb`: a parameter of `sb` is available iff its branch argument is; every other vreg keeps its
availability. -/
def edgeAvail (vb sb : VBlock) (A : Nat → Bool) (v : Nat) : Bool :=
  match (sb.params.toList.map Reg.homeNum).idxOf? v with
  | some k =>
    match vb.branchArgs[k]? with
    | some a => A a.homeNum
    | none => false
  | none => A v

/-- **The availability facts of the spill allocation** (V4 step 4, the dataflow invariant's VCode
part) for availability sets `D` (`D b v`: on entry to block `b`, the home of vreg `v` holds it). -/
structure SpillAvail (vc : VCode) (D : Nat → Nat → Bool) : Prop where
  /-- Every home holds its vreg on entry to the function (the register-level theorem chooses the
  initial vreg file accordingly). -/
  entry : ∀ v, D 0 v = true
  /-- Every use is available where it is read. -/
  uses : ∀ succs preds, vc.cfg = .ok (succs, preds) →
    ∀ (b : Nat) (vb : VBlock) (k : Nat) (i : MInst) (ops : Array Operand),
      vc.blocks[b]? = some vb → vb.insts[k]? = some i → i.operands = .ok ops →
      ∀ o ∈ ops.toList, o.kind = .use →
        availAt vb.insts (availStart vc succs preds D b) k o.vreg = true
  /-- Every edge delivers the availability set of its target. -/
  edges : ∀ succs preds, vc.cfg = .ok (succs, preds) →
    ∀ (b : Nat) (vb : VBlock) (ss : Array Nat) (s : Nat) (sb : VBlock),
      vc.blocks[b]? = some vb → succs[b]? = some ss → s ∈ ss.toList → vc.blocks[s]? = some sb →
      ∀ v, D s v = true →
        edgeAvail vb sb (availAt vb.insts (availStart vc succs preds D b) vb.insts.size) v = true

/-- **Step 4 of V4 (a)** (proven: `spillStep4`, `FV/Backend/Proof/SpillStep4.lean`): given a CFG,
the local facts (`SpillLocalOk`, step 3) and availability sets (`SpillAvail`), the in-states
described in the module docstring verify, so the spill allocation is `AllocChecked`. The CFG
premise is needed: `CheckedAt` asks for `vc.cfg = .ok _`, which `SpillLocalOk` and `SpillAvail`
(both quantified over the CFG) do not give (a block not ending in a terminator meets both
vacuously); the pipeline's output has a CFG (`cfg_ok_of_prepare`). -/
def SpillStep4 : Prop :=
  ∀ (vc : VCode) (D : Nat → Nat → Bool), (∃ succs preds, vc.cfg = .ok (succs, preds)) →
    SpillLocalOk vc → SpillAvail vc D → AllocChecked vc (spillAlloc vc)

end Backend.Proof.Spill
