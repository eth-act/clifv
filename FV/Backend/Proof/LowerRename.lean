import FV.Backend.Proof.LowerSeq

/-!
# Vreg renaming (M7 driver: alias resolution)

`lowerFunction` resolves the value aliases at the end (`MInst.mapRegs (resolve …)`). A
class-preserving vreg renaming `g` (real registers fixed) renames the operand view
(`operands_mapRegs`); with a renaming-invariant semantics, a straight-line run of the renamed
code from `ρ` simulates the run of the original code from `ρ ∘ g` (`seqRun_rename_*`), as long as
every register read is either written by the code itself or not clobbered by it.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- `g` renames virtual registers (`vreg n c ↦ vreg (gn n) c`) and fixes real registers. -/
structure VRenaming (g : Reg → Reg) (gn : Nat → Nat) : Prop where
  vreg : ∀ n c, g (.vreg n c) = .vreg (gn n) c
  real : ∀ r, (∀ n c, r ≠ .vreg n c) → g r = r

/-- Rename an operand's vreg. -/
def rnOp (gn : Nat → Nat) (o : Operand) : Operand := { o with vreg := gn o.vreg }

/-- The operand collector of `MInst.operands`. -/
def collectOp (s : OpSpec) (r : Reg) : StateT (Array Operand) (Except String) Reg := do
  match r with
  | .vreg n cls => modify (·.push ⟨n, cls, s.kind, s.pos, s.con⟩); pure r
  | _ =>
    if r.allocatable then throw s!"allocatable real register {repr r} as an operand"
    else pure r

theorem operands_eq (i : MInst) :
    i.operands = (do let (_, ops) ← (MInst.visitOperands collectOp i).run #[]; pure ops) := rfl

variable {g : Reg → Reg} {gn : Nat → Nat}

theorem collectOp_rename (hg : VRenaming g gn) (sp : OpSpec) (r : Reg) (s : Array Operand) :
    (collectOp sp (g r)).run (s.map (rnOp gn)) =
      ((collectOp sp r).run s).map (fun p => (g p.1, p.2.map (rnOp gn))) := by
  cases r
  case vreg n c =>
    rw [hg.vreg]
    simp [collectOp, StateT.run, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      Except.map, pure, StateT.pure, Except.pure, bind, StateT.bind, Except.bind, rnOp,
      Array.map_push, hg.vreg]
  all_goals
    first
    | rw [hg.real (.x _) (fun _ _ h => by cases h)]
    | rw [hg.real .xzr (fun _ _ h => by cases h)]
    | rw [hg.real .sp (fun _ _ h => by cases h)]
    | rw [hg.real (.v _) (fun _ _ h => by cases h)]
    simp only [collectOp]
    split <;> simp [StateT.run, Except.map, pure, StateT.pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw, StateT.lift, Except.bind, bind, hg.real (.x _) (fun _ _ h => by cases h),
      hg.real .xzr (fun _ _ h => by cases h), hg.real .sp (fun _ _ h => by cases h),
      hg.real (.v _) (fun _ _ h => by cases h)]

/-! ## Simulation of the operand visitor under renaming -/

abbrev OpM := StateT (Array Operand) (Except String)

/-- `y` is `x` renamed: from the renamed state it computes `f` of `x`'s result and the renamed
state (or the same error). -/
def Sim (gn : Nat → Nat) {α β : Type} (f : α → β) (x : OpM α) (y : OpM β) : Prop :=
  ∀ s, y.run (s.map (rnOp gn)) = (x.run s).map (fun p => (f p.1, p.2.map (rnOp gn)))

theorem Sim.bind {α β γ δ : Type} {f : α → β} {h : γ → δ} {x : OpM α} {y : OpM β}
    {k : α → OpM γ} {k' : β → OpM δ}
    (hx : Sim gn f x y) (hk : ∀ a, Sim gn h (k a) (k' (f a))) : Sim gn h (x >>= k) (y >>= k') := by
  intro s
  simp only [StateT.run_bind, hx s]
  cases hr : x.run s with
  | error e => rfl
  | ok p =>
    obtain ⟨a, s'⟩ := p
    exact hk a s'

theorem Sim.pure {α β : Type} {f : α → β} (a : α) (b : β) (h : b = f a) :
    Sim gn f (Pure.pure a : OpM α) (Pure.pure b) := by
  intro s; subst h; rfl

theorem Sim.collect (hg : VRenaming g gn) (sp : OpSpec) (r : Reg) :
    Sim gn g (collectOp sp r) (collectOp sp (g r)) := fun s => collectOp_rename hg sp r s

theorem Sim.mapM {α β γ δ : Type} {φ : α → β} {ψ : γ → δ} {F : α → OpM γ} {F' : β → OpM δ}
    (hF : ∀ a, Sim gn ψ (F a) (F' (φ a))) :
    ∀ l : List α, Sim gn (List.map ψ) (l.mapM F) ((l.map φ).mapM F') := by
  intro l
  induction l with
  | nil => exact Sim.pure _ _ rfl
  | cons a l ih =>
    simp only [List.mapM_cons, List.map_cons]
    exact Sim.bind (hF a) fun c => Sim.bind ih fun cs => Sim.pure _ _ rfl

theorem Sim.amode (hg : VRenaming g gn) (am : AMode) :
    Sim gn (AMode.mapRegs g) (AMode.visit collectOp am) (AMode.visit collectOp (am.mapRegs g)) := by
  cases am <;> simp only [AMode.visit, AMode.mapRegs] <;>
    first
    | exact Sim.pure _ _ rfl
    | exact Sim.bind (Sim.collect hg _ _) fun a => Sim.pure _ _ rfl
    | exact Sim.bind (Sim.collect hg _ _) fun a => Sim.bind (Sim.collect hg _ _) fun b =>
        Sim.pure _ _ rfl

theorem Sim.condBrKind (hg : VRenaming g gn) (k : CondBrKind) :
    Sim gn (CondBrKind.mapRegs g) (CondBrKind.visit collectOp k)
      (CondBrKind.visit collectOp (k.mapRegs g)) := by
  cases k <;> simp only [CondBrKind.visit, CondBrKind.mapRegs] <;>
    first
    | exact Sim.pure _ _ rfl
    | exact Sim.bind (Sim.collect hg _ _) fun a => Sim.pure _ _ rfl

theorem Sim.visit (hg : VRenaming g gn) (i : MInst) :
    Sim gn (MInst.mapRegs g) (MInst.visitOperands collectOp i)
      (MInst.visitOperands collectOp (i.mapRegs g)) := by
  cases i with
  | call info =>
    obtain ⟨dest, uses, defs⟩ := info
    have hu : Sim gn (List.map fun (x : Reg × Reg) => (g x.1, x.2))
        (uses.mapM fun x => do let r ← collectOp (OpSpec.fixedUse x.snd) x.fst; Pure.pure (r, x.snd))
        ((uses.map fun (x : Reg × Reg) => (g x.1, x.2)).mapM
          fun x => do let r ← collectOp (OpSpec.fixedUse x.snd) x.fst; Pure.pure (r, x.snd)) := by
      refine Sim.mapM ?_ uses
      intro a; obtain ⟨v, p⟩ := a
      exact Sim.bind (Sim.collect hg _ v) fun b => Sim.pure _ _ rfl
    have hd : Sim gn (List.map fun (x : Reg × Reg) => (x.1, g x.2))
        (defs.mapM fun x => do let r ← collectOp (OpSpec.fixedDef x.fst) x.snd; Pure.pure (x.fst, r))
        ((defs.map fun (x : Reg × Reg) => (x.1, g x.2)).mapM
          fun x => do let r ← collectOp (OpSpec.fixedDef x.fst) x.snd; Pure.pure (x.fst, r)) := by
      refine Sim.mapM ?_ defs
      intro a; obtain ⟨p, v⟩ := a
      exact Sim.bind (Sim.collect hg _ v) fun b => Sim.pure _ _ rfl
    cases dest with
    | reg r =>
      simp only [MInst.visitOperands, MInst.mapRegs]
      exact Sim.bind (Sim.collect hg _ r) fun a =>
        Sim.bind (Sim.pure (f := fun d => match d with | .reg r => CallDest.reg (g r) | d => d)
          (CallDest.reg a) _ rfl) fun _ =>
        Sim.bind hu fun _ => Sim.bind hd fun _ => Sim.pure _ _ rfl
    | sym n =>
      simp only [MInst.visitOperands, MInst.mapRegs]
      exact Sim.bind (Sim.pure (f := fun d => match d with | .reg r => CallDest.reg (g r) | d => d)
          (CallDest.sym n) _ rfl) fun _ =>
        Sim.bind hu fun _ => Sim.bind hd fun _ => Sim.pure _ _ rfl
  | args ds =>
    simp only [MInst.visitOperands, MInst.mapRegs]
    refine Sim.bind (Sim.mapM (φ := fun (x : Reg × Reg) => (g x.1, x.2))
      (ψ := fun (x : Reg × Reg) => (g x.1, x.2)) ?_ ds) fun us => Sim.pure _ _ rfl
    intro a; obtain ⟨v, p⟩ := a
    exact Sim.bind (Sim.collect hg _ v) fun b => Sim.pure _ _ rfl
  | rets us =>
    simp only [MInst.visitOperands, MInst.mapRegs]
    refine Sim.bind (Sim.mapM (φ := fun (x : Reg × Reg) => (g x.1, x.2))
      (ψ := fun (x : Reg × Reg) => (g x.1, x.2)) ?_ us) fun us => Sim.pure _ _ rfl
    intro a; obtain ⟨v, p⟩ := a
    exact Sim.bind (Sim.collect hg _ v) fun b => Sim.pure _ _ rfl
  | atomicRmwLoop ty op fl a o1 o2 s1 s2 =>
    -- the visit has a fixed-def conditional on `op == .xchg`
    simp only [MInst.visitOperands, MInst.mapRegs]
    split <;> rename_i s2 <;>
      repeat
        first
        | exact Sim.pure _ _ rfl
        | refine Sim.bind (Sim.collect hg _ _) fun _ => ?_
  | _ =>
    simp only [MInst.visitOperands, MInst.mapRegs]
    repeat
      first
      | exact Sim.pure _ _ rfl
      | refine Sim.bind (Sim.collect hg _ _) fun _ => ?_
      | refine Sim.bind (Sim.amode hg _) fun _ => ?_
      | refine Sim.bind (Sim.condBrKind hg _) fun _ => ?_

/-- **The operand view of a renamed instruction** is the renamed operand view. -/
theorem operands_mapRegs (hg : VRenaming g gn) (i : MInst) :
    (i.mapRegs g).operands = (i.operands).map (·.map (rnOp gn)) := by
  rw [operands_eq, operands_eq]
  have h := Sim.visit hg i #[]
  rw [show (#[] : Array Operand).map (rnOp gn) = #[] by simp] at h
  rw [h]
  cases (MInst.visitOperands collectOp i).run #[] with
  | error e => rfl
  | ok p => rfl

theorem isUse_rnOp (o : Operand) : (rnOp gn o).isUse = o.isUse := rfl
theorem isDef_rnOp (o : Operand) : (rnOp gn o).isDef = o.isDef := rfl
theorem isEarly_rnOp (o : Operand) : (rnOp gn o).isEarly = o.isEarly := rfl
theorem isLate_rnOp (o : Operand) : (rnOp gn o).isLate = o.isLate := rfl

/-! ## Straight-line runs of renamed code -/

section
variable {V W : Type}

/-- `ρ₀` (original code) and `ρ` (renamed code) agree on every vreg that is written by the code
(`D`) or whose image is not written. -/
def Agree (gn : Nat → Nat) (D : Nat → Prop) (ρ₀ ρ : Nat → V) : Prop :=
  ∀ n, (D n ∨ ¬ D (gn n)) → ρ₀ n = ρ (gn n)

theorem Agree.writeV {D : Nat → Prop} (hD : ∀ d, D d → gn d = d) :
    ∀ {dv : List (Operand × V)} {ρ₀ ρ : Nat → V}, Agree gn D ρ₀ ρ → (∀ p ∈ dv, D p.1.vreg) →
    Agree gn D (writeV ρ₀ dv) (writeV ρ (dv.map fun p => (rnOp gn p.1, p.2))) := by
  intro dv
  induction dv with
  | nil => intro _ _ h _; exact h
  | cons p dv ih =>
    intro ρ₀ ρ h hdv
    simp only [Backend.Proof.writeV, List.foldl_cons, List.map_cons] at ih ⊢
    apply ih _ (fun q hq => hdv q (List.mem_cons_of_mem _ hq))
    intro n hn
    have hp := hdv p (by simp)
    have hfix := hD _ hp
    simp only [upd, rnOp, hfix]
    by_cases e : n = p.1.vreg
    · subst e; simp [hfix]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false e)]
      by_cases e' : gn n = p.1.vreg
      · exfalso
        rcases hn with hn | hn
        · rw [hD _ hn] at e'; exact e e'
        · exact hn (e' ▸ hp)
      · rw [ite_eq_right_of_eq_false _ _ (eq_false e')]; exact h n hn

theorem filter_map_rn (l : List Operand) (P : Operand → Bool) (hP : ∀ o, P (rnOp gn o) = P o) :
    (l.map (rnOp gn)).filter P = (l.filter P).map (rnOp gn) := by
  induction l with
  | nil => rfl
  | cons o l ih =>
    simp only [List.map_cons, List.filter_cons, hP]
    split <;> simp [ih]

theorem vuses_rename {D : Nat → Prop} {ops : Array Operand} {ρ₀ ρ : Nat → V}
    (h : Agree gn D ρ₀ ρ) (hu : ∀ o ∈ ops.toList, o.isUse = true → D o.vreg ∨ ¬ D (gn o.vreg)) :
    vuses (ops.map (rnOp gn)) ρ = vuses ops ρ₀ := by
  simp only [vuses, Array.toList_map]
  rw [filter_map_rn _ _ (fun _ => rfl), List.map_map]
  apply List.map_congr_left
  intro o ho
  have := (List.mem_filter.mp ho)
  simp only [Function.comp, rnOp]
  exact (h o.vreg (hu o this.1 this.2)).symm

theorem zip_map_left {α β γ : Type} (f : α → γ) :
    ∀ (l : List α) (m : List β), (l.map f).zip m = (l.zip m).map fun p => (f p.1, p.2)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: l, b :: m => by simp [zip_map_left f l m]

theorem filter_map_pair {β : Type} (l : List (Operand × β)) (P : Operand → Bool)
    (hP : ∀ o, P (rnOp gn o) = P o) :
    (l.map fun p => (rnOp gn p.1, p.2)).filter (fun p => P p.1) =
      (l.filter fun p => P p.1).map fun p => (rnOp gn p.1, p.2) := by
  induction l with
  | nil => rfl
  | cons o l ih =>
    simp only [List.map_cons, List.filter_cons, hP]
    split <;> simp [ih]

theorem vdefUpd_rename {D : Nat → Prop} (hD : ∀ d, D d → gn d = d) {ops : Array Operand}
    {outs : List V} {ρ₀ ρ : Nat → V} (h : Agree gn D ρ₀ ρ)
    (hd : ∀ o ∈ ops.toList, o.isDef = true → D o.vreg) :
    Agree gn D (vdefUpd ops outs ρ₀) (vdefUpd (ops.map (rnOp gn)) outs ρ) := by
  have hdefs : ∀ p ∈ (ops.toList.filter Operand.isDef).zip outs, D p.1.vreg := by
    intro p hp
    have := List.mem_filter.mp (List.of_mem_zip hp).1
    exact hd _ this.1 this.2
  simp only [vdefUpd, Array.toList_map]
  rw [filter_map_rn _ _ (fun _ => rfl), zip_map_left,
    filter_map_pair _ Operand.isEarly (fun _ => rfl), filter_map_pair _ Operand.isLate (fun _ => rfl)]
  exact Agree.writeV hD (Agree.writeV hD h fun p hp => hdefs p (List.mem_filter.mp hp).1)
    fun p hp => hdefs p (List.mem_filter.mp hp).1

theorem defs_length_rn (ops : Array Operand) :
    ((ops.map (rnOp gn)).toList.filter Operand.isDef).length =
      (ops.toList.filter Operand.isDef).length := by
  simp only [Array.toList_map]
  rw [filter_map_rn _ _ (fun _ => rfl), List.length_map]

/-- **Renamed straight-line code.** If every def of `ms` is in `D` (fixed by the renaming) and
every use is in `D` or has an image outside `D`, the renamed code from `ρ` does what the code
does from any `ρ₀` agreeing with `ρ ∘ gn` there. -/
theorem seqRun_rename {sem : ISem V W} (hg : VRenaming g gn) (hsem : ∀ i, sem (i.mapRegs g) = sem i)
    {D : Nat → Prop} (hD : ∀ d, D d → gn d = d) :
    ∀ {ms : List MInst} {ρ₀ ρ : Nat → V} {w : W},
    (∀ m ∈ ms, ∀ d ∈ vdefs m, D d) → (∀ m ∈ ms, ∀ u ∈ vuseNums m, D u ∨ ¬ D (gn u)) →
    Agree gn D ρ₀ ρ →
    (∀ {ρ₀' w'}, seqRun sem ms ρ₀ w = some (.fall ρ₀' w') →
      ∃ ρ', seqRun sem (ms.map (·.mapRegs g)) ρ w = some (.fall ρ' w') ∧ Agree gn D ρ₀' ρ') ∧
    (∀ {k i ops ρ₁ w₁ outs w₂ ctl},
      seqRun sem ms ρ₀ w = some (.stop k i ops ρ₁ w₁ outs w₂ ctl) →
      ∃ ρ₁', seqRun sem (ms.map (·.mapRegs g)) ρ w =
          some (.stop k (i.mapRegs g) (ops.map (rnOp gn)) ρ₁' w₁ outs w₂ ctl) ∧
        Agree gn D ρ₁ ρ₁' ∧ Agree gn D (vdefUpd ops outs ρ₁) (vdefUpd (ops.map (rnOp gn)) outs ρ₁')) := by
  intro ms
  induction ms with
  | nil =>
    intro ρ₀ ρ w _ _ hA
    refine ⟨fun h => ?_, fun h => by simp [seqRun] at h⟩
    simp only [seqRun, Option.some.injEq, SeqEnd.fall.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ρ, rfl, hA⟩
  | cons i ms ih =>
    intro ρ₀ ρ w hdefs huses hA
    have hdi : ∀ o ∈ (i.operands.toOption.getD #[]).toList, o.isDef = true → D o.vreg := by
      intro o ho hd
      cases hop : i.operands with
      | error => simp [hop, Except.toOption] at ho
      | ok ops =>
        simp only [hop, Except.toOption, Option.getD_some] at ho
        exact hdefs i (by simp) o.vreg (by simp [vdefs, hop]; exact ⟨o, ⟨by simpa using ho, hd⟩, rfl⟩)
    have hui : ∀ o ∈ (i.operands.toOption.getD #[]).toList, o.isUse = true →
        D o.vreg ∨ ¬ D (gn o.vreg) := by
      intro o ho hu
      cases hop : i.operands with
      | error => simp [hop, Except.toOption] at ho
      | ok ops =>
        simp only [hop, Except.toOption, Option.getD_some] at ho
        exact huses i (by simp) o.vreg (by simp [vuseNums, hop]; exact ⟨o, ⟨by simpa using ho, hu⟩, rfl⟩)
    have hdefs' := fun m hm => hdefs m (List.mem_cons_of_mem _ hm)
    have huses' := fun m hm => huses m (List.mem_cons_of_mem _ hm)
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨ops, outs, w₁, hops, hsm, hlen, hrest⟩ := seqRun_cons_fall h
      simp only [hops, Except.toOption, Option.getD_some] at hdi hui
      have hA' := vdefUpd_rename (outs := outs) hD hA hdi
      obtain ⟨ρ', hr, hA''⟩ := (ih hdefs' huses' hA').1 hrest
      refine ⟨ρ', ?_, hA''⟩
      simp only [List.map_cons, seqRun, operands_mapRegs hg, hops, Except.map, hsem,
        vuses_rename hA hui, hsm, defs_length_rn, hlen, ite_true, hr, Option.map_some, SeqEnd.succ]
    · rcases seqRun_cons_stop h with
        ⟨rfl, rfl, hops, rfl, rfl, hsm, hlen, hne⟩ |
        ⟨k', ops₀, outs₀, w₃, rfl, hops₀, hsm₀, hlen₀, hrest⟩
      · simp only [hops, Except.toOption, Option.getD_some] at hdi hui
        refine ⟨ρ, ?_, hA, vdefUpd_rename hD hA hdi⟩
        simp only [List.map_cons, seqRun, operands_mapRegs hg, hops, Except.map, hsem,
          vuses_rename hA hui, hsm, defs_length_rn, hlen, ite_true]
        all_goals (cases ctl <;> first | exact absurd rfl hne | rfl)
      · simp only [hops₀, Except.toOption, Option.getD_some] at hdi hui
        have hA' := vdefUpd_rename (outs := outs₀) hD hA hdi
        obtain ⟨ρ₁', hr, hA1, hA2⟩ := (ih hdefs' huses' hA').2 hrest
        refine ⟨ρ₁', ?_, hA1, hA2⟩
        simp only [List.map_cons, seqRun, operands_mapRegs hg, hops₀, Except.map, hsem,
          vuses_rename hA hui, hsm₀, defs_length_rn, hlen₀, ite_true, hr, Option.map_some,
          SeqEnd.succ]

end

end Backend.Proof.Driver
