import FV.Backend.RegallocOps

/-!
# Substituting an allocation succeeds (`MInst.assign`)

`assign_ok_of_operands`: if the operand view of an instruction is `ops`, substituting any
allocation `regs` with one register per operand (`regs.size = ops.size`) succeeds.

The operand collector (`collectOp`, one operand per vreg occurrence) and the allocation
substitution (`putOp`, one register per vreg occurrence) walk the same `MInst.visitOperands`;
`ARel` relates a collector step to a substitution step: the substitution consumes exactly as
many registers as the collector pushes operands, and succeeds when that many remain.
-/

namespace Backend.Proof

open Backend

/-- The operand collector of `MInst.operands` (`Driver.collectOp`, restated here to keep this
file independent of the driver proofs). -/
private def collectOp (s : OpSpec) (r : Reg) : StateT (Array Operand) (Except String) Reg := do
  match r with
  | .vreg n cls => modify (·.push ⟨n, cls, s.kind, s.pos, s.con⟩); pure r
  | _ =>
    if r.allocatable then throw s!"allocatable real register {repr r} as an operand"
    else pure r

private theorem operands_eq (i : MInst) :
    i.operands = (do let (_, ops) ← (MInst.visitOperands collectOp i).run #[]; pure ops) := rfl

/-- The allocation substitution of `MInst.assign`. -/
def putOp (regs : Array Reg) (_ : OpSpec) (r : Reg) : StateT Nat (Except String) Reg := do
  match r with
  | .vreg .. =>
    let k ← get
    set (k + 1)
    match regs[k]? with
    | some p => pure p
    | none => throw "fewer allocations than operands"
  | _ => pure r

theorem assign_eq (i : MInst) (regs : Array Reg) :
    i.assign regs = (do
      let (i', k) ← (MInst.visitOperands (putOp regs) i).run 0
      if k != regs.size then throw "more allocations than operands"
      pure i') := rfl

private abbrev OpM := StateT (Array Operand) (Except String)
private abbrev PutM := StateT Nat (Except String)

/-- A collector step `x` and a substitution step `y`: whenever `x` succeeds pushing `d`
operands, `y` succeeds from any counter `k` with `k + d ≤ N`, advancing it by `d`. -/
def ARel (N : Nat) {α β : Type} (x : OpM α) (y : PutM β) : Prop :=
  ∀ s a s', x.run s = .ok (a, s') → s.size ≤ s'.size ∧
    ∀ k, k + (s'.size - s.size) ≤ N → ∃ b, y.run k = .ok (b, k + (s'.size - s.size))

section
variable {N : Nat}

theorem ARel.pure {α β : Type} (a : α) (b : β) : ARel N (Pure.pure a : OpM α) (Pure.pure b) := by
  intro s c s' h
  cases h
  exact ⟨Nat.le_refl _, fun k _ => ⟨b, by simp; rfl⟩⟩

theorem ARel.bind {α β γ δ : Type} [Nonempty β] {x : OpM α} {y : PutM β} {f : α → OpM γ}
    {g : β → PutM δ} (hx : ARel N x y) (hk : ∀ a b, ARel N (f a) (g b)) :
    ARel N (x >>= f) (y >>= g) := by
  intro s c s'' h
  rw [StateT.run_bind] at h
  cases hr : x.run s with
  | error e => rw [hr] at h; cases h
  | ok p =>
    obtain ⟨a, s'⟩ := p
    rw [hr] at h
    obtain ⟨h1, hy⟩ := hx s a s' hr
    obtain ⟨h2, -⟩ := hk a (Classical.choice ‹_›) s' c s'' h
    refine ⟨Nat.le_trans h1 h2, fun k hk' => ?_⟩
    obtain ⟨b, hb⟩ := hy k (by omega)
    obtain ⟨-, hg⟩ := hk a b s' c s'' h
    obtain ⟨d, hd⟩ := hg (k + (s'.size - s.size)) (by omega)
    have he : k + (s'.size - s.size) + (s''.size - s'.size) = k + (s''.size - s.size) := by omega
    rw [he] at hd
    exact ⟨d, by rw [StateT.run_bind, hb]; exact hd⟩

theorem ARel.map {α β γ δ : Type} [Nonempty β] (f : α → γ) (g : β → δ) {x : OpM α} {y : PutM β}
    (hx : ARel N x y) : ARel N (f <$> x) (g <$> y) := by
  rw [map_eq_pure_bind, map_eq_pure_bind]
  exact ARel.bind hx fun a b => ARel.pure _ _

theorem ARel.collect (regs : Array Reg) (hN : N = regs.size) (sp sp' : OpSpec) (r : Reg) :
    ARel N (collectOp sp r) (putOp regs sp' r) := by
  intro s a s' h
  cases r
  case vreg n c =>
    simp only [collectOp, StateT.run, modify, modifyGet, MonadStateOf.modifyGet] at h
    cases h
    refine ⟨by simp, fun k hk => ?_⟩
    have hs : (s.push { vreg := n, cls := c, kind := sp.kind, pos := sp.pos, con := sp.con }).size
        - s.size = 1 := by simp
    rw [hs] at hk ⊢
    have hlt : k < regs.size := by omega
    refine ⟨regs[k], ?_⟩
    show StateT.run (putOp regs sp' (.vreg n c)) k = _
    simp [putOp, hlt]
    rfl
  all_goals
    simp only [collectOp] at h
    split at h
    · cases h
    · cases h
      exact ⟨Nat.le_refl _, fun k _ => ⟨_, by simp [putOp]; rfl⟩⟩

theorem ARel.mapM {α β : Type} [Nonempty β] {F : α → OpM β} {G : α → PutM β}
    (h : ∀ a, ARel N (F a) (G a)) : ∀ l : List α, ARel N (l.mapM F) (l.mapM G)
  | [] => ARel.pure _ _
  | a :: l => by
    rw [List.mapM_cons, List.mapM_cons]
    exact ARel.bind (h a) fun _ _ => ARel.bind (ARel.mapM h l) fun _ _ => ARel.pure _ _

theorem ARel.amode (regs : Array Reg) (hN : N = regs.size) (am : AMode) :
    ARel N (AMode.visit collectOp am) (AMode.visit (putOp regs) am) := by
  cases am <;> simp only [AMode.visit] <;>
    first
    | exact ARel.pure _ _
    | exact ARel.bind (ARel.collect regs hN _ _ _) fun _ _ => ARel.pure _ _
    | exact ARel.bind (ARel.collect regs hN _ _ _) fun _ _ =>
        ARel.bind (ARel.collect regs hN _ _ _) fun _ _ => ARel.pure _ _

theorem ARel.condBrKind (regs : Array Reg) (hN : N = regs.size) (k : CondBrKind) :
    ARel N (CondBrKind.visit collectOp k) (CondBrKind.visit (putOp regs) k) := by
  cases k <;> simp only [CondBrKind.visit] <;>
    first
    | exact ARel.pure _ _
    | exact ARel.bind (ARel.collect regs hN _ _ _) fun _ _ => ARel.pure _ _

end

/-- Apply the collector/substitution combinators. -/
macro "arel_steps" regs:term:max hN:term:max : tactic => `(tactic| (
  repeat'
    first
    | exact ARel.pure _ _
    | refine ARel.bind (ARel.collect $regs $hN _ _ _) fun _ _ => ?_
    | refine ARel.bind (ARel.amode $regs $hN _) fun _ _ => ?_
    | refine ARel.bind (ARel.condBrKind $regs $hN _) fun _ _ => ?_
    | refine ARel.bind (ARel.mapM (fun a => ?_) _) fun _ _ => ?_
    | refine ARel.mapM (fun a => ?_) _
    | refine ARel.map _ _ (ARel.collect $regs $hN _ _ _)
    | refine ARel.bind (ARel.pure _ _) fun _ _ => ?_
    | refine ARel.map _ _ ?_))

theorem arel_visit (regs : Array Reg) (i : MInst) :
    ARel regs.size (MInst.visitOperands collectOp i) (MInst.visitOperands (putOp regs) i) := by
  have hN : regs.size = regs.size := rfl
  cases i
  case call info =>
    obtain ⟨dest, uses, defs⟩ := info
    cases dest <;> simp only [MInst.visitOperands] <;> arel_steps regs hN
  case tryCall info ti =>
    obtain ⟨dest, uses, defs⟩ := info
    cases dest <;> simp only [MInst.visitOperands] <;> arel_steps regs hN
  all_goals simp only [MInst.visitOperands]
  all_goals arel_steps regs hN

/-- **Substituting an allocation** with one register per operand succeeds. -/
theorem assign_ok_of_operands {i : MInst} {ops : Array Operand} {regs : Array Reg}
    (h : i.operands = .ok ops) (hs : regs.size = ops.size) : ∃ i', i.assign regs = .ok i' := by
  rw [operands_eq] at h
  cases hr : (MInst.visitOperands collectOp i).run #[] with
  | error e => rw [hr] at h; cases h
  | ok p =>
    obtain ⟨i₀, ops'⟩ := p
    rw [hr] at h
    cases h
    obtain ⟨-, hy⟩ := arel_visit regs i #[] i₀ ops hr
    obtain ⟨i', hi'⟩ := hy 0 (by simp [hs])
    refine ⟨i', ?_⟩
    rw [assign_eq, StateT.run] at *
    simp only [Array.size_empty, Nat.sub_zero, Nat.zero_add] at hi'
    rw [hi']
    simp [hs, bind, Except.bind, pure, Except.pure]

end Backend.Proof
