module

public import FV.Backend.Proof.DriverCheckTy
public import FV.Concurrency.Code

@[expose] public section

/-!
# The shape of a statement's lowered code (T2h, #311, layer 2c)

Layer 2d (`IselClif.access_in_events`) places every byte of a memory statement's CLIF access in
*some* event of its lowered code's run. Semantics cannot say more: a segment that also wrote a
location back with its old value would leave every state unchanged, yet carry an extra (racy)
event. So the number and kinds of the memory instructions of each statement's code are checked
on the lowering, by translation validation, like `checkAlloc`:

* `segShape inst seg`: the memory instructions of `seg` (`memInsts`: those with memory kinds,
  `Code.akinds`) are exactly one, of the kinds of `inst`'s events under `Maps` (`load` → `ldr`
  `[plainR]`, `store` → `str` `[plainW]`, `atomic_load` → `ldar` `[acqR]`, `atomic_store` → `stlr`
  `[relW]`, `atomic_rmw`/`atomic_cas` → the LL/SC loop `[acqXR, relXW]`, `fence` → `dmb`), of the
  access size of `inst` (`memBytes`); every other statement's code has no memory instruction;
* `segShapeBl f bl`: every statement of every block, on its `lower` output (`SLow.st'.emitted`);
* **`segShapeCheck f`**: `segShapeBl` on the driver's lowering of `f` (`buildCtx`, `lowBlocks`, as
  `lowerCheckT` computes it);
* **`segShape_segT`**: the check holds on the code the validated VCode contains for the
  statement (`segT`: renamed, with the driver's result copies): renaming keeps kinds and sizes
  (`akinds_mapRegs`, `memBytes_mapRegs`) and the copies are moves.

Witness (`SegShapeWitness.lean`): a compiled function with `atomic_load`, `atomic_store`,
`atomic_rmw`, `atomic_cas`, `fence`, `load` and `store` passes the check.
-/

namespace Concurrency.SegShape

open Backend Backend.Proof Backend.Proof.Driver Code

/-- The access size of a memory instruction. -/
def memBytes : MInst → Option Nat
  | .load op .. => some op.bytes
  | .store op .. => some op.bytes
  | .loadAcquire ty .. | .storeRelease ty .. => some ty.bytes
  | .fpuLoad sz .. | .fpuStore sz .. => some sz.bytes
  | .atomicRmwLoop ty .. | .atomicCasLoop ty .. => some ty.bytes
  | _ => none

/-- The instructions with memory kinds. -/
def memInsts (seg : List MInst) : List MInst := seg.filter fun i => !(akinds i).isEmpty

/-- The kinds and access size of the memory instruction a statement's code must have. -/
def expect : Clif.Inst → Option (List AKind × Nat)
  | .load op ty .. => some ([.plainR], op.size ty)
  | .store op ty .. => some ([.plainW], op.size ty)
  | .atomicLoad ty .. => some ([.acqR], ty.bytes)
  | .atomicStore ty .. => some ([.relW], ty.bytes)
  | .atomicRmw _ ty .. | .atomicCas ty .. => some ([.acqXR, .relXW], ty.bytes)
  | .fence => some ([.dmb], 0)
  | _ => none

/-- **The shape of a statement's code**: one memory instruction of the statement's kinds and
size, or none. -/
def segShape (inst : Clif.Inst) (seg : List MInst) : Bool :=
  match expect inst with
  | some (ks, n) => match memInsts seg with
    | [i] => akinds i == ks && (ks == [.dmb] || memBytes i == some n)
    | _ => false
  | none => (memInsts seg).isEmpty

/-- The check on the driver's per-statement lowering `bl`. -/
def segShapeBl (f : Clif.Function) (bl : List BLow) : Bool :=
  (f.blocks.zip bl).all fun (B, L) =>
    (B.body.zip L.sl).all fun (stm, sl) => segShape stm.inst sl.st'.emitted.toList

/-- **The per-function check**, on the driver's lowering of `f` (as `lowerCheckT` computes it). -/
def segShapeCheck (f : Clif.Function) : Bool :=
  match buildCtx f with
  | .error _ => false
  | .ok (ctx, _, st0) =>
    match lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
        f.blocks.length with
    | none => false
    | some bl => segShapeBl f bl

theorem akinds_mapRegs (R : Reg → Reg) (i : MInst) : akinds (i.mapRegs R) = akinds i := by
  cases i <;> rfl

theorem memBytes_mapRegs (R : Reg → Reg) (i : MInst) : memBytes (i.mapRegs R) = memBytes i := by
  cases i <;> rfl

theorem memInsts_mapRegs (R : Reg → Reg) (seg : List MInst) :
    memInsts (seg.map (·.mapRegs R)) = (memInsts seg).map (·.mapRegs R) := by
  induction seg with
  | nil => rfl
  | cons i seg ih =>
    simp only [memInsts, List.map_cons, List.filter_cons, akinds_mapRegs] at ih ⊢
    split <;> simp [ih]

theorem memInsts_extraOfT (ctx : Ctx) (results : List Nat) (rss : List (List Reg)) :
    memInsts (extraOfT ctx results rss) = [] := by
  unfold memInsts extraOfT
  rw [List.filter_eq_nil_iff]
  intro i hi
  obtain ⟨⟨r, rs⟩, -, h⟩ := List.mem_filterMap.mp hi
  simp only at h
  split at h
  · cases h
  · cases h; simp [akinds]
  · cases h

theorem segShape_congr {inst : Clif.Inst} {s1 s2 : List MInst} (R : Reg → Reg)
    (h : memInsts s2 = (memInsts s1).map (·.mapRegs R)) : segShape inst s2 = segShape inst s1 := by
  unfold segShape
  rw [h]
  split
  · rcases hm : memInsts s1 with _ | ⟨i, _ | ⟨j, t⟩⟩
    · rfl
    · simp only [List.map_cons, List.map_nil, akinds_mapRegs, memBytes_mapRegs]
    · rfl
  · cases memInsts s1 <;> rfl

theorem all_zip_getElem {α β : Type} {p : α × β → Bool} {as : List α} {bs : List β}
    (h : (as.zip bs).all p = true) {j : Nat} {a : α} {b : β} (ha : as[j]? = some a)
    (hb : bs[j]? = some b) : p (a, b) = true := by
  have hz : (as.zip bs)[j]? = some (a, b) := by
    rw [List.getElem?_zip_eq_some]; exact ⟨ha, hb⟩
  exact List.all_eq_true.mp h _ (List.mem_of_getElem? hz)

/-- **The check holds on the validated code of each statement** (`segT`: the statement's
renamed `lower` output and the driver's result copies). -/
theorem segShape_segT {f : Clif.Function} {ctx : Ctx} {R : Reg → Reg} {bl : List BLow}
    (h : segShapeBl f bl = true) {bi j : Nat} {B : Clif.Block} {stm : Clif.Stmt}
    (hB : f.blocks[bi]? = some B) (hstm : B.body[j]? = some stm) {L : BLow}
    (hL : bl[bi]? = some L) {sl : SLow} (hsl : L.sl[j]? = some sl) :
    segShape stm.inst (segT f ctx R bl bi j) = true := by
  have h1 := all_zip_getElem h hB hL
  have h2 := all_zip_getElem h1 hstm hsl
  simp only [segT, hB, hL, hstm, hsl]
  rw [segShape_congr R (s1 := sl.st'.emitted.toList)]
  · exact h2
  · rw [memInsts_mapRegs, memInsts, List.filter_append]
    rw [show (extraOfT ctx stm.results sl.rss).filter (fun i => !(akinds i).isEmpty) = [] from
      memInsts_extraOfT ctx stm.results sl.rss, List.append_nil]
    rfl

end Concurrency.SegShape
