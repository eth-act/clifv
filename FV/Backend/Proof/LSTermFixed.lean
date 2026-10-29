module

public import FV.Backend.LinearScan

@[expose] public section

/-!
# The kept defs of a terminator are fixed (V4b-3, #275)

`term_kept_fixed`: every def a terminator keeps (`keptIdx`: none for a branch, whose defs are
`JTSequence`'s dead temporaries; a `Rets` and a block-ending trap define nothing; a `try_call`'s
call defines its results and payload registers in fixed registers) has a fixed-register
constraint.

The operand view of a `Rets`/`udf`/`try_call` collects only fixed defs: an invariant of the
operand visitor (`FInv`, after `Kill.KInv`), with the collector of `MInst.operands` restated
(`collect`) to keep the imports light.
-/

namespace Backend.Proof.LS

open Backend Backend.LinearScan

private abbrev OpM := StateT (Array Operand) (Except String)

/-- The operand collector of `MInst.operands`. -/
private def collect (s : OpSpec) (r : Reg) : OpM Reg := do
  match r with
  | .vreg n cls => modify (·.push ⟨n, cls, s.kind, s.pos, s.con⟩); pure r
  | _ =>
    if r.allocatable then throw s!"allocatable real register {repr r} as an operand"
    else pure r

private theorem operands_eq' (i : MInst) :
    i.operands = (do let (_, ops) ← (MInst.visitOperands collect i).run #[]; pure ops) := rfl

/-- Every collected def has a fixed-register constraint. -/
private def DefsFixed (s : Array Operand) : Prop :=
  ∀ o ∈ s.toList, o.kind = .def → ∃ p, o.con = .fixed p

/-- A step of the operand visitor keeps `DefsFixed`. -/
private def FInv {α : Type} (x : OpM α) : Prop :=
  ∀ s a s', x.run s = .ok (a, s') → DefsFixed s → DefsFixed s'

private theorem FInv.pure {α : Type} (a : α) : FInv (Pure.pure a : OpM α) := by
  intro s b s' h hs
  cases h
  exact hs

private theorem FInv.bind {α β : Type} {x : OpM α} {k : α → OpM β} (hx : FInv x)
    (hk : ∀ a, FInv (k a)) : FInv (x >>= k) := by
  intro s b s' h hs
  rw [StateT.run_bind] at h
  cases hr : x.run s with
  | error e => rw [hr] at h; cases h
  | ok p =>
    obtain ⟨a, s1⟩ := p
    rw [hr] at h
    exact hk a s1 b s' h (hx s a s1 hr hs)

private theorem FInv.push (sp : OpSpec) (r : Reg)
    (hd : sp.kind = .def → ∃ p, sp.con = .fixed p) : FInv (collect sp r) := by
  intro s a s' h hs
  cases r
  case vreg n c =>
    simp only [collect, StateT.run, modify, modifyGet, MonadStateOf.modifyGet] at h
    cases h
    intro o ho
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at ho
    rcases ho with ho | rfl
    · exact hs o ho
    · exact hd
  all_goals
    simp only [collect] at h
    split at h
    · cases h
    · cases h; exact hs

private theorem FInv.mapM {α β : Type} {F : α → OpM β} :
    ∀ (l : List α), (∀ a ∈ l, FInv (F a)) → FInv (l.mapM F)
  | [], _ => FInv.pure _
  | a :: l, h => by
    rw [List.mapM_cons]
    exact FInv.bind (h a List.mem_cons_self) fun b =>
      FInv.bind (FInv.mapM l fun a' ha' => h a' (List.mem_cons_of_mem _ ha')) fun bs => FInv.pure _

/-- Apply the visitor-invariant combinators (reducible unification only). -/
local macro "finv_steps" : tactic => `(tactic| (
  repeat'
    first
    | with_reducible refine FInv.bind (FInv.mapM _ fun a ha => ?_) fun _ => ?_
    | with_reducible refine FInv.mapM _ fun a ha => ?_
    | with_reducible refine FInv.bind (FInv.push _ _ ?_) fun _ => ?_
    | with_reducible exact FInv.pure _
    | with_reducible refine FInv.bind (FInv.pure _) fun _ => ?_))

/-- The operand visit of a non-branch terminator (`Rets`, `udf`, `try_call`) keeps `DefsFixed`. -/
private theorem finv_visit {i : MInst} (ht : i.isTerminator = true) (hb : i.isBranch = false) :
    FInv (MInst.visitOperands collect i) := by
  have huse : ∀ p : Reg, (OpSpec.fixedUse p).kind = .def → ∃ q, (OpSpec.fixedUse p).con = .fixed q :=
    fun _ hk => by cases hk
  have hdef : ∀ p : Reg, (OpSpec.fixedDef p).kind = .def → ∃ q, (OpSpec.fixedDef p).con = .fixed q :=
    fun p _ => ⟨p, rfl⟩
  have hu : OpSpec.use.kind = .def → ∃ q, OpSpec.use.con = .fixed q := fun hk => by cases hk
  cases i <;> simp only [MInst.isTerminator, MInst.isBranch, MInst.isRet, Bool.false_or,
    Bool.or_false, Bool.false_eq_true, Bool.true_eq_false, Bool.or_self] at ht hb
  case udf => exact FInv.pure _
  case rets us =>
    simp only [MInst.visitOperands]
    finv_steps
    all_goals exact huse _
  case tryCall info ti =>
    obtain ⟨dest, uses, defs⟩ := info
    cases dest <;> simp only [MInst.visitOperands] <;> finv_steps
    all_goals first | exact huse _ | exact hdef _ | exact hu

/-- The kept defs are defs at their index. -/
private theorem keptIdx_def {i : MInst} {os : Array Operand} {j : Nat} {o : Operand}
    (hj : os[j]? = some o) (hk : j ∈ keptIdx i os) : o.kind = .def := by
  have hm : j ∈ (os.toList.zipIdx.filter (·.1.kind == .def)).map (·.2) := by
    unfold keptIdx at hk
    split at hk
    · exact hk
    · exact List.mem_of_mem_take hk
  obtain ⟨⟨o', j'⟩, hf, rfl⟩ := List.mem_map.1 hm
  rw [List.mem_filter] at hf
  obtain ⟨hz, hd⟩ := hf
  rw [List.mem_zipIdx_iff_getElem?] at hz
  simp only [Array.getElem?_toList] at hz
  rw [hj] at hz
  cases hz
  simpa using hd

/-- **The kept defs of a terminator are fixed.** -/
theorem term_kept_fixed {i : MInst} {os : Array Operand} (ht : i.isTerminator = true)
    (hos : i.operands = .ok os) {j : Nat} {o : Operand} (hj : os[j]? = some o)
    (hk : j ∈ keptIdx i os) : ∃ p, o.con = .fixed p := by
  have hd := keptIdx_def hj hk
  by_cases hb : i.isBranch = true
  · have h0 : i.keptDefs = some 0 := by
      unfold MInst.keptDefs
      split
      · simp [MInst.isBranch] at hb
      · simp [MInst.isBranch] at hb
      · simp [hb]
    simp [keptIdx, h0] at hk
  · rw [operands_eq'] at hos
    cases hv : (MInst.visitOperands collect i).run #[] with
    | error e => rw [hv] at hos; cases hos
    | ok p =>
      obtain ⟨i', os'⟩ := p
      rw [hv] at hos
      cases hos
      exact finv_visit ht (by simpa using hb) #[] i' _ hv (fun o ho => by simp at ho) o
        (Array.mem_toList_iff.2 (Array.mem_of_getElem? hj)) hd

end Backend.Proof.LS
