import FV.Backend.Proof.LowerRename
import FV.Backend.Proof.IselFlowExt

/-!
# Register classes of instructions (V4 classes)

`RegCls cls r`: a vreg `r = vreg n c` has the class `cls[n]` records (real registers always).
`InstCls cls m`: every operand of `m` does (`ClassesOk`'s instruction part). `RegsFrom P m`:
the registers of `m` are among those `P` allows (every renaming fixing them fixes `m`).

* `instCls_mapRegs`: an instruction whose registers have their classes keeps `InstCls` under a
  renaming that keeps classes (alias resolution), by the operand visitor (`keeps_visit`);
* `regsFrom_ofV`: the registers of `MInst.ofV v` are registers of `v`.
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof.Driver Backend.Proof.Flow

/-! ## Classes of registers and instructions -/

/-- Does the vreg `r` have the class `cls` records (real registers: yes)? -/
def regOk (cls : Array RegClass) : Reg → Bool
  | .vreg n c => cls[n]? == some c
  | _ => true

/-- `r` has the class `cls` records. -/
def RegCls (cls : Array RegClass) (r : Reg) : Prop := regOk cls r = true

theorem regCls_vreg {cls : Array RegClass} {n : Nat} {c : RegClass} :
    RegCls cls (.vreg n c) ↔ cls[n]? = some c := by
  simp [RegCls, regOk]

theorem regCls_real {cls : Array RegClass} {r : Reg} (h : ∀ n c, r ≠ .vreg n c) : RegCls cls r := by
  cases r <;> simp_all [RegCls, regOk]

theorem regCls_append {cls : Array RegClass} (ext : Array RegClass) {r : Reg} (h : RegCls cls r) :
    RegCls (cls ++ ext) r := by
  cases r with
  | vreg n c =>
    rw [regCls_vreg] at h ⊢
    rw [Array.getElem?_append_left (Array.getElem?_eq_some_iff.mp h).1]
    exact h
  | _ => exact regCls_real (fun _ _ h => by cases h)

/-- An operand has the class `cls` records for its vreg. -/
def OpOk (cls : Array RegClass) (o : Operand) : Prop := cls[o.vreg]? = some o.cls

/-- Every operand of `m` has the class `cls` records. -/
def InstCls (cls : Array RegClass) (m : MInst) : Prop :=
  ∀ ops, m.operands = .ok ops → ∀ o ∈ ops.toList, OpOk cls o

/-- The registers of `m` are among those `P` allows. -/
def RegsFrom (P : Reg → Prop) (m : MInst) : Prop :=
  ∀ g : Reg → Reg, (∀ r, P r → g r = r) → m.mapRegs g = m

theorem RegsFrom.mono {P Q : Reg → Prop} {m : MInst} (h : RegsFrom P m) (hPQ : ∀ r, P r → Q r) :
    RegsFrom Q m := fun g hg => h g fun r hr => hg r (hPQ r hr)

/-! ## The operand visitor keeps `OpOk` -/

/-- The visitor computation `x` only pushes operands meeting `OpOk`. -/
def Keeps (cls : Array RegClass) {α : Type} (x : OpM α) : Prop :=
  ∀ s a s', x.run s = .ok (a, s') → (∀ o ∈ s.toList, OpOk cls o) → ∀ o ∈ s'.toList, OpOk cls o

variable {cls : Array RegClass}

theorem Keeps.pure {α : Type} (a : α) : Keeps cls (Pure.pure a : OpM α) := by
  intro s b s' h hs
  cases h
  exact hs

theorem Keeps.bind {α β : Type} {x : OpM α} {k : α → OpM β} (hx : Keeps cls x)
    (hk : ∀ a, Keeps cls (k a)) : Keeps cls (x >>= k) := by
  intro s b s' h hs
  rw [StateT.run_bind] at h
  cases hr : x.run s with
  | error e => rw [hr] at h; cases h
  | ok p =>
    rw [hr] at h
    exact hk p.1 p.2 b s' h (hx s p.1 p.2 hr hs)

theorem Keeps.collect {sp : OpSpec} {r : Reg} (h : RegCls cls r) : Keeps cls (collectOp sp r) := by
  intro s a s' hr hs
  cases r
  case vreg n c =>
    simp only [collectOp, StateT.run, modify, modifyGet, MonadStateOf.modifyGet, bind, StateT.bind,
      pure, StateT.pure, Except.bind, Except.pure] at hr
    cases hr
    intro o ho
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at ho
    rcases ho with ho | rfl
    · exact hs o ho
    · exact regCls_vreg.mp h
  all_goals
    simp only [collectOp] at hr
    split at hr
    · cases hr
    · simp only [StateT.run, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨-, rfl⟩ := hr
      exact hs

theorem Keeps.mapM {α β : Type} {F : α → OpM β} :
    ∀ (l : List α), (∀ a ∈ l, Keeps cls (F a)) → Keeps cls (l.mapM F)
  | [], _ => Keeps.pure _
  | a :: l, h => by
    rw [List.mapM_cons]
    exact Keeps.bind (h a List.mem_cons_self) fun _ =>
      Keeps.bind (Keeps.mapM l fun b hb => h b (List.mem_cons_of_mem _ hb)) fun _ => Keeps.pure _

theorem Keeps.mapM_map {α β γ : Type} {F : α → OpM β} {φ : γ → α} {l : List γ}
    (hF : ∀ c, Keeps cls (F (φ c))) : Keeps cls ((l.map φ).mapM F) :=
  Keeps.mapM _ fun a ha => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp ha
    exact hF c

variable {g : Reg → Reg}

theorem Keeps.amode (hg : ∀ r, RegCls cls (g r)) (am : AMode) :
    Keeps cls (AMode.visit collectOp (am.mapRegs g)) := by
  cases am <;> simp only [AMode.visit, AMode.mapRegs] <;>
    first
    | exact Keeps.pure _
    | exact Keeps.bind (Keeps.collect (hg _)) fun _ => Keeps.pure _
    | exact Keeps.bind (Keeps.collect (hg _)) fun _ => Keeps.bind (Keeps.collect (hg _)) fun _ =>
        Keeps.pure _

theorem Keeps.condBrKind (hg : ∀ r, RegCls cls (g r)) (k : CondBrKind) :
    Keeps cls (CondBrKind.visit collectOp (k.mapRegs g)) := by
  cases k <;> simp only [CondBrKind.visit, CondBrKind.mapRegs] <;>
    first
    | exact Keeps.pure _
    | exact Keeps.bind (Keeps.collect (hg _)) fun _ => Keeps.pure _

/-- One step of a visitor proof. -/
macro "keeps_step" hg:term : tactic => `(tactic| first
  | exact Keeps.pure _
  | refine Keeps.bind (Keeps.collect ($hg _)) fun _ => ?_
  | refine Keeps.bind (Keeps.amode $hg _) fun _ => ?_
  | refine Keeps.bind (Keeps.condBrKind $hg _) fun _ => ?_
  | refine Keeps.bind (Keeps.mapM_map fun c => Keeps.bind (Keeps.collect ($hg _)) fun _ =>
      Keeps.pure _) fun _ => ?_
  | refine Keeps.bind (Keeps.pure _) fun _ => ?_)

/-- **The operand visitor of a renamed instruction** pushes only operands of the classes `cls`
records, when the renaming maps every register to one of its class. -/
theorem keeps_visit (hg : ∀ r, RegCls cls (g r)) (i : MInst) :
    Keeps cls (MInst.visitOperands collectOp (i.mapRegs g)) := by
  cases i
  case call info | tryCall info _ =>
    obtain ⟨dest, uses, defs⟩ := info
    cases dest <;> simp only [MInst.visitOperands, MInst.mapRegs] <;> repeat keeps_step hg
  all_goals simp only [MInst.visitOperands, MInst.mapRegs]
  all_goals repeat keeps_step hg

/-- `InstCls` of an instruction renamed into registers of their classes. -/
theorem instCls_of_map (hg : ∀ r, RegCls cls (g r)) (i : MInst) : InstCls cls (i.mapRegs g) := by
  intro ops hops o ho
  rw [operands_eq] at hops
  cases hr : (MInst.visitOperands collectOp (i.mapRegs g)).run #[] with
  | error e => rw [hr] at hops; cases hops
  | ok p =>
    rw [hr] at hops
    cases hops
    exact keeps_visit hg i #[] p.1 p.2 hr (fun o ho => by simp at ho) o ho

/-! ## Composition of renamings -/

theorem amode_mapRegs_comp (f g : Reg → Reg) (am : AMode) :
    (am.mapRegs g).mapRegs f = am.mapRegs (f ∘ g) := by
  cases am <;> rfl

theorem condBr_mapRegs_comp (f g : Reg → Reg) (k : CondBrKind) :
    (k.mapRegs g).mapRegs f = k.mapRegs (f ∘ g) := by
  cases k <;> rfl

theorem mapRegs_comp (f g : Reg → Reg) (i : MInst) :
    (i.mapRegs g).mapRegs f = i.mapRegs (f ∘ g) := by
  cases i with
  | call info =>
    obtain ⟨dest, uses, defs⟩ := info
    cases dest <;> simp [MInst.mapRegs, List.map_map, Function.comp_def]
  | tryCall info ti =>
    obtain ⟨dest, uses, defs⟩ := info
    cases dest <;> simp [MInst.mapRegs, List.map_map, Function.comp_def]
  | args ds => simp [MInst.mapRegs, List.map_map, Function.comp_def]
  | rets us => simp [MInst.mapRegs, List.map_map, Function.comp_def]
  | _ => simp [MInst.mapRegs, amode_mapRegs_comp, condBr_mapRegs_comp]

/-- Registers of their classes go to registers of their classes, the rest to `xzr`. -/
def fixG (cls : Array RegClass) (r : Reg) : Reg := if regOk cls r then r else .xzr

theorem fixG_cls (r : Reg) : RegCls cls (fixG cls r) := by
  unfold fixG
  split
  · assumption
  · exact regCls_real (fun _ _ h => by cases h)

/-- **`InstCls` after a class-keeping renaming** of an instruction whose registers have their
classes. -/
theorem instCls_mapRegs {m : MInst} (h : RegsFrom (RegCls cls) m) {R : Reg → Reg}
    (hR : ∀ r, RegCls cls r → RegCls cls (R r)) : InstCls cls (m.mapRegs R) := by
  have hm : m.mapRegs (fixG cls) = m := h _ fun r hr => by simp [fixG, show regOk cls r = true from hr]
  rw [← hm, mapRegs_comp]
  exact instCls_of_map (fun r => hR _ (fixG_cls r)) m

theorem instCls_of {m : MInst} (h : RegsFrom (RegCls cls) m) : InstCls cls m := by
  have := instCls_mapRegs h (R := id) fun _ h => h
  rwa [show m.mapRegs id = m from by
    have := mapRegs_comp id (fixG cls) m
    exact h id fun _ _ => rfl] at this

/-! ## `MInst.ofV` -/

theorem reg?_eq {v : V} {r : Reg} : v.reg? = some r ↔ v = .reg r := by
  cases v <;> simp [V.reg?]

theorem regsIn_data {ty : Isle.TypeId} {k : Nat} {fs : List V} : (V.data ty k fs).regsIn = regsInL fs := by
  simp [V.regsIn]

theorem amode?_fix {v : V} {am : AMode} (h : v.amode? = some am) {g : Reg → Reg}
    (hg : ∀ r ∈ v.regsIn, g r = r) : am.mapRegs g = am := by
  unfold V.amode? at h
  obtain ⟨⟨k, fs⟩, he, h2⟩ := bind_some_ex h
  rw [enumOf_eq he] at hg
  clear h he
  split at h2
  all_goals
    repeat' (first | (obtain ⟨_, _, h2⟩ := bind_some_ex h2) | split at h2)
  all_goals first
    | (cases h2; done)
    | (simp only [pure, Option.some.injEq] at h2
       subst h2
       try simp only [reg?_eq] at *
       subst_vars
       simp_all [V.regsIn, AMode.mapRegs])

theorem condBrKind?_fix {v : V} {k : CondBrKind} (h : v.condBrKind? = some k) {g : Reg → Reg}
    (hg : ∀ r ∈ v.regsIn, g r = r) : k.mapRegs g = k := by
  unfold V.condBrKind? at h
  obtain ⟨⟨k', fs⟩, he, h2⟩ := bind_some_ex h
  rw [enumOf_eq he] at hg
  clear h he
  split at h2
  all_goals
    repeat' (first | (obtain ⟨_, _, h2⟩ := bind_some_ex h2) | split at h2)
  all_goals first
    | (cases h2; done)
    | (simp only [pure, Option.some.injEq] at h2
       subst h2
       try simp only [reg?_eq] at *
       subst_vars
       simp_all [V.regsIn, CondBrKind.mapRegs])

theorem callInfo?_eq {v : V} {c : CallInfo} : v.callInfo? = some c ↔ v = .op (.callInfo c) := by
  cases v with
  | op o => cases o <;> simp [V.callInfo?]
  | _ => simp [V.callInfo?]

theorem callInfo_fix {c : CallInfo} {g : Reg → Reg}
    (hg : ∀ r ∈ (V.op (.callInfo c)).regsIn, g r = r) :
    ({ c with
      dest := match c.dest with
        | .reg r => .reg (g r)
        | d => d
      uses := c.uses.map fun (v, p) => (g v, p)
      defs := c.defs.map fun (p, v) => (p, g v) } : CallInfo) = c := by
  obtain ⟨dest, uses, defs⟩ := c
  simp only [V.regsIn, opRegs, pairRegs, List.mem_append, List.mem_flatMap, List.mem_cons,
    List.mem_nil_iff, or_false] at hg
  have hu : uses.map (fun (x : Reg × Reg) => (g x.1, x.2)) = uses := by
    conv => rhs; rw [← List.map_id uses]
    exact List.map_congr_left fun x hx => by rw [hg x.1 (.inl (.inr ⟨x, hx, .inl rfl⟩))]; rfl
  have hd : defs.map (fun (x : Reg × Reg) => (x.1, g x.2)) = defs := by
    conv => rhs; rw [← List.map_id defs]
    exact List.map_congr_left fun x hx => by rw [hg x.2 (.inr ⟨x, hx, .inr rfl⟩)]; rfl
  cases dest with
  | reg r =>
    have := hg r (.inl (.inl (by simp)))
    simp only [this, CallInfo.mk.injEq, true_and]
    exact ⟨hu, hd⟩
  | sym n =>
    simp only [CallInfo.mk.injEq, true_and]
    exact ⟨hu, hd⟩

theorem callInfo_fix' {c : CallInfo} {g : Reg → Reg}
    (hg : ∀ r, r ∈ opRegs (.callInfo c) → g r = r) :
    ({ c with
      dest := match c.dest with
        | .reg r => .reg (g r)
        | d => d
      uses := c.uses.map fun (v, p) => (g v, p)
      defs := c.defs.map fun (p, v) => (p, g v) } : CallInfo) = c := callInfo_fix hg

set_option maxHeartbeats 4000000 in
/-- **The registers of `MInst.ofV v`** are registers of `v`. -/
theorem regsFrom_ofV {v : V} {m : MInst} (h : MInst.ofV v = some m) :
    RegsFrom (· ∈ v.regsIn) m := by
  unfold MInst.ofV at h
  obtain ⟨⟨k, fs⟩, he, h2⟩ := bind_some_ex h
  rw [enumOf_eq he]
  clear h he
  revert h2
  revert m
  apply ofV_split _ (fun k fs (r : Option MInst) => ∀ m, r = some m →
    RegsFrom (· ∈ (V.data tyMInst k fs).regsIn) m)
  all_goals
    intros
    rename_i m hm
    try simp only at hm
    repeat' (first | (obtain ⟨_, _, hm⟩ := bind_some_ex hm) | split at hm)
    all_goals first
      | (cases hm; done)
      | (simp only [pure, Option.some.injEq] at hm
         subst hm
         intro g hg
         try simp only [reg?_eq, callInfo?_eq] at *
         subst_vars
         have amf := fun {v : V} {am : AMode} (h : v.amode? = some am) => amode?_fix (g := g) h
         have ckf := fun {v : V} {k : CondBrKind} (h : v.condBrKind? = some k) =>
           condBrKind?_fix (g := g) h
         simp only [V.regsIn, regsInL_cons, regsInL_nil, List.mem_append, List.mem_singleton,
           List.append_nil] at hg
         first
         | (simp only [MInst.mapRegs, MInst.call.injEq]; exact callInfo_fix' hg)
         | (simp only [MInst.mapRegs]
            have key := amf ‹V.amode? _ = some _›
            rw [key (fun r hr => hg r (by simp [hr]))]
            try simp_all)
         | (simp only [MInst.mapRegs]
            have key := ckf ‹V.condBrKind? _ = some _›
            rw [key (fun r hr => hg r (by simp [hr]))]
            try simp_all)
         | simp_all [MInst.mapRegs])

end Backend.Proof.Spill
