import FV.Backend.Proof.SpillLocalPipe
import FV.Backend.Proof.IselCtlTry
import FV.Backend.Proof.IselCtlBrTable

/-!
# The spill allocator's facts on the control forms (V4 (a), step 3: `CtlSpillHyp`)

`CtlShape N m`: the shapes of the control forms (`MInst.isCtl`) the lowering emits, with the
register lists of the ABI (`gen_call_args`/`gen_call_rets`: fixed argument/return registers
x0..x8, pairwise distinct; `Rets`: x0..x7) and fresh defs (pairwise distinct, numbered `≥ N`,
above every value's vreg). `spillInstOk_of_ctlShape`: every such shape meets `SpillInstOk`, and
its defs are `≥ N` (`ctlShape_defs`), so that the alias renaming (which only renames values'
vregs) keeps `SpillInstOk` (`spillInstOk_mapRegs`). The driver's own control forms: `Args`
(`spillInstOk_args`), the `tryCall` replacing the call a `try_call` rule emits last
(`spillInstOk_tryCall_of_call`, without `clobberAll`: a `try_call`'s signature is `system_v`).
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof Backend.Proof.Driver

/-! ## Argument/return registers -/

/-- A fixed argument/return register: `x k`, `k ≤ 8`. -/
def ArgReg (r : Reg) : Prop := ∃ k, k ≤ 8 ∧ r = .x k

theorem x_alloc9 : ∀ k < 9, (Reg.x k).allocatable = true := by decide

theorem argReg_alloc {r : Reg} (h : ArgReg r) : r.allocatable = true ∧ r.realClass? = some .int := by
  obtain ⟨k, hk, rfl⟩ := h
  exact ⟨x_alloc9 k (by omega), rfl⟩

/-- The callee-saved int registers x19..x28: never fixed, never clobbered by a call. -/
def highRegs : List Reg := (List.range 10).map fun i => .x (19 + i)

theorem highRegs_sub : highRegs.Sublist (spillPool .int) := by
  have : spillPool .int = (List.range 16).map Reg.x ++ highRegs := by decide
  rw [this]; exact List.sublist_append_right _ _

theorem highRegs_length : highRegs.length = 10 := by decide

theorem argReg_not_high {r : Reg} (h : ArgReg r) : r ∉ highRegs := by
  obtain ⟨k, hk, rfl⟩ := h
  simp only [highRegs, List.mem_map, List.mem_range, Reg.x.injEq, not_exists, not_and]
  intro i _ he; omega

theorem aapcs_not_high : ∀ r ∈ defaultAapcsClobbers, r ∉ highRegs := by decide

/-! ## `OpsOk` of a call's operands -/

/-- `(vreg, preg)` pairs of an `Args`. -/
def argPairs (D : List (Reg × Nat)) : List (Reg × Reg) := D.map fun q => (Reg.vreg q.2 .int, q.1)

/-- The facts of a call's register lists (`L`: argument vregs and registers; `D`: return
registers and vregs), with defs numbered `≥ N`. -/
structure CallOk (N : Nat) (L : List (Nat × Reg)) (D : List (Reg × Nat)) : Prop where
  useReg : ∀ q ∈ L, ArgReg q.2
  useNodup : (L.map (·.2)).Nodup
  defReg : ∀ q ∈ D, ArgReg q.1
  defRegNodup : (D.map (·.1)).Nodup
  defNodup : (D.map (·.2)).Nodup
  fresh : ∀ q ∈ D, N ≤ q.2

theorem mem_callOps {pre : List Operand} {L : List (Nat × Reg)} {D : List (Reg × Nat)} {o : Operand}
    (h : o ∈ pre ++ (retOps L ++ callDefOps D)) :
    o ∈ pre ∨ (∃ q ∈ L, o = ⟨q.1, .int, .use, .early, .fixed q.2⟩) ∨
      ∃ q ∈ D, o = ⟨q.2, .int, .def, .late, .fixed q.1⟩ := by
  simp only [List.mem_append, retOps, callDefOps, List.mem_map] at h
  rcases h with h | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
  · exact .inl h
  · exact .inr (.inl ⟨q, hq, rfl⟩)
  · exact .inr (.inr ⟨q, hq, rfl⟩)

theorem fixedRegs_argReg {pre : List Operand} {L : List (Nat × Reg)} {D : List (Reg × Nat)}
    (hpre : ∀ o ∈ pre, o.con = .reg) (hL : ∀ q ∈ L, ArgReg q.2) (hD : ∀ q ∈ D, ArgReg q.1) :
    ∀ r ∈ fixedRegs (pre ++ (retOps L ++ callDefOps D)).toArray, ArgReg r := by
  intro r hr
  simp only [fixedRegs, List.mem_filterMap] at hr
  obtain ⟨o, ho, hr⟩ := hr
  rcases mem_callOps (by simpa using ho) with ho | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
  · rw [hpre o ho] at hr; cases hr
  · cases hr; exact hL q hq
  · cases hr; exact hD q hq

/-- **`OpsOk` of a call-like operand list**: an optional `reg` use (the callee), fixed uses in
distinct argument registers, fixed defs in distinct registers outside the clobbers, with
distinct vregs; clobbers outside x19..x28. -/
theorem opsOk_call {pre : List Operand} {L : List (Nat × Reg)} {D : List (Reg × Nat)}
    {clob : List Reg} {N : Nat}
    (hpre : pre = [] ∨ ∃ t, pre = [tgtOp t]) (hc : CallOk N L D)
    (hcD : ∀ q ∈ D, q.1 ∉ clob) (hcs : ∀ r ∈ clob, r ∉ highRegs) :
    OpsOk (pre ++ (retOps L ++ callDefOps D)).toArray clob := by
  have hpreR : ∀ o ∈ pre, o.con = .reg ∧ o.kind = .use ∧ o.pos = .early ∧ o.cls = .int := by
    rcases hpre with rfl | ⟨t, rfl⟩
    · simp
    · intro o ho; simp at ho; subst ho; exact ⟨rfl, rfl, rfl, rfl⟩
  have hlen : pre.length ≤ 1 := by rcases hpre with rfl | ⟨t, rfl⟩ <;> simp
  -- the (kind, constraint) view is injective on the list
  have hkey : ((pre ++ (retOps L ++ callDefOps D)).map fun o => (o.kind, o.con)).Nodup := by
    rw [List.map_append, List.map_append, List.nodup_append, List.nodup_append]
    have h1 : (pre.map fun o => (o.kind, o.con)).Nodup := by
      rcases hpre with rfl | ⟨t, rfl⟩ <;> simp
    have h2 : ((retOps L).map fun o => (o.kind, o.con)) = L.map fun q => (OpKind.use, Constraint.fixed q.2) := by
      simp [retOps]
    have h3 : ((callDefOps D).map fun o => (o.kind, o.con)) = D.map fun q => (OpKind.def, Constraint.fixed q.1) := by
      simp [callDefOps]
    rw [h2, h3]
    refine ⟨h1, ⟨?_, ?_, ?_⟩, ?_⟩
    · have := List.Pairwise.map (S := (· ≠ ·)) (fun r => (OpKind.use, Constraint.fixed r))
        (fun a b h e => h (by simp at e; exact e)) hc.useNodup
      simp only [List.map_map, Function.comp_def] at this; exact this
    · have := List.Pairwise.map (S := (· ≠ ·)) (fun r => (OpKind.def, Constraint.fixed r))
        (fun a b h e => h (by simp at e; exact e)) hc.defRegNodup
      simp only [List.map_map, Function.comp_def] at this; exact this
    · intro a ha b hb he
      simp only [List.mem_map] at ha hb
      obtain ⟨q, -, rfl⟩ := ha; obtain ⟨q', -, rfl⟩ := hb
      simp at he
    · intro a ha b hb he
      simp only [List.mem_map] at ha
      obtain ⟨o, ho, rfl⟩ := ha
      have hr := (hpreR o ho).1
      simp only [List.mem_append, List.mem_map] at hb
      rcases hb with ⟨q, -, rfl⟩ | ⟨q, -, rfl⟩ <;> simp [hr] at he
  have hnd : (pre ++ (retOps L ++ callDefOps D)).Nodup :=
    List.Pairwise.of_map (fun o => (o.kind, o.con)) (fun a b h e => h (by rw [e])) hkey
  have hmem := fun (o : Operand) (ho : o ∈ (pre ++ (retOps L ++ callDefOps D)).toArray.toList) =>
    mem_callOps (pre := pre) (L := L) (D := D) (by simpa using ho)
  have hfix := fixedRegs_argReg (fun o ho => (hpreR o ho).1) hc.useReg hc.defReg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o ho h
    rcases hmem o ho with ho | ⟨q, -, rfl⟩ | ⟨q, -, rfl⟩
    · rw [(hpreR o ho).1] at h; cases h
    · cases h
    · cases h
  · intro o ho h
    rcases hmem o ho with ho | ⟨q, -, rfl⟩ | ⟨q, -, rfl⟩
    · exact (hpreR o ho).2.2.1
    · rfl
    · cases h
  · intro o ho p h
    rcases hmem o ho with ho | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · rw [(hpreR o ho).1] at h; cases h
    · cases h; exact argReg_alloc (hc.useReg q hq)
    · cases h; exact argReg_alloc (hc.defReg q hq)
  · intro o ho o' ho' p hu hu' h h'
    rcases hmem o ho with ho | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · rw [(hpreR o ho).1] at h; cases h
    · rcases hmem o' ho' with ho' | ⟨q', hq', rfl⟩ | ⟨q', hq', rfl⟩
      · rw [(hpreR o' ho').1] at h'; cases h'
      · injection h with h; injection h' with h'
        exact congrArg Prod.fst (inj_of_nodup_map hc.useNodup hq hq' (h.trans h'.symm))
      · cases hu'
    · cases hu
  · intro j j' o o' p hj hj' hd hd' h h'
    have ho := hmem o (List.mem_of_getElem? hj)
    have ho' := hmem o' (List.mem_of_getElem? hj')
    have he : o = o' := by
      rcases ho with ho | ⟨q, -, rfl⟩ | ⟨q, hq, rfl⟩
      · rw [(hpreR o ho).2.1] at hd; cases hd
      · cases hd
      rcases ho' with ho' | ⟨q', -, rfl⟩ | ⟨q', hq', rfl⟩
      · rw [(hpreR o' ho').2.1] at hd'; cases hd'
      · cases hd'
      injection h with h; injection h' with h'
      rw [inj_of_nodup_map hc.defRegNodup hq hq' (h.trans h'.symm)]
    subst he
    have hlt : j < (pre ++ (retOps L ++ callDefOps D)).toArray.toList.length :=
      (List.getElem?_eq_some_iff.mp hj).1
    exact (List.Nodup.getElem?_inj hlt (by simpa using hnd)).mp (hj.trans hj'.symm)
  · intro o ho p hd h
    rcases hmem o ho with ho | ⟨q, -, rfl⟩ | ⟨q, hq, rfl⟩
    · rw [(hpreR o ho).2.1] at hd; cases hd
    · cases hd
    · cases h; exact hcD q hq
  · intro o ho hd hp
    rcases hmem o ho with ho | ⟨q, -, rfl⟩ | ⟨q, -, rfl⟩
    · rw [(hpreR o ho).2.1] at hd; cases hd
    · cases hd
    · cases hp
  · intro j o i hj h
    rcases hmem o (List.mem_of_getElem? hj) with ho | ⟨q, -, rfl⟩ | ⟨q, -, rfl⟩
    · rw [(hpreR o ho).1] at h; cases h
    · cases h
    · cases h
  · intro c
    have hn : nScratch c (pre ++ (retOps L ++ callDefOps D)).toArray.toList ≤ 1 := by
      unfold nScratch
      have : ((pre ++ (retOps L ++ callDefOps D)).toArray.toList.filter
          fun o => scratch o.con && o.cls == c) =
          pre.filter fun o => scratch o.con && o.cls == c := by
        simp only [List.toList_toArray, List.filter_append]
        have e1 : (retOps L).filter (fun o => scratch o.con && o.cls == c) = [] := by
          rw [List.filter_eq_nil_iff]; intro o ho
          simp only [retOps, List.mem_map] at ho; obtain ⟨q, -, rfl⟩ := ho; simp [scratch]
        have e2 : (callDefOps D).filter (fun o => scratch o.con && o.cls == c) = [] := by
          rw [List.filter_eq_nil_iff]; intro o ho
          simp only [callDefOps, List.mem_map] at ho; obtain ⟨q, -, rfl⟩ := ho; simp [scratch]
        rw [e1, e2]; simp
      rw [this]
      exact Nat.le_trans (List.length_filter_le _ _) hlen
    cases c with
    | float =>
      have : nScratch .float (pre ++ (retOps L ++ callDefOps D)).toArray.toList = 0 := by
        unfold nScratch
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro o ho
        rcases hmem o ho with ho | ⟨q, -, rfl⟩ | ⟨q, -, rfl⟩
        · simp [(hpreR o ho).2.2.2]
        · simp [scratch]
        · simp [scratch]
      omega
    | int =>
      have hsub : highRegs.Sublist (freeRegs (pre ++ (retOps L ++ callDefOps D)).toArray clob .int) := by
        unfold freeRegs
        have := highRegs_sub.filter fun r =>
          !(fixedRegs (pre ++ (retOps L ++ callDefOps D)).toArray ++ clob).contains r
        rw [List.filter_eq_self.mpr] at this
        · exact this
        · intro r hr
          simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.contains_eq_mem, decide_eq_false_iff_not,
            List.mem_append, not_or]
          exact ⟨fun h => argReg_not_high (hfix r h) hr, fun h => hcs r h hr⟩
      have := hsub.length_le
      rw [highRegs_length] at this
      omega
  · have : (((pre ++ (retOps L ++ callDefOps D)).toArray.toList.filter (·.kind == .def)).map (·.vreg)) =
        D.map (·.2) := by
      simp only [List.toList_toArray, List.filter_append]
      have e0 : pre.filter (·.kind == .def) = [] := by
        rw [List.filter_eq_nil_iff]; intro o ho; simp [(hpreR o ho).2.1]
      have e1 : (retOps L).filter (·.kind == .def) = [] := by
        rw [List.filter_eq_nil_iff]; intro o ho
        simp only [retOps, List.mem_map] at ho; obtain ⟨q, -, rfl⟩ := ho; simp
      have e2 : (callDefOps D).filter (·.kind == .def) = callDefOps D := by
        rw [List.filter_eq_self]; intro o ho
        simp only [callDefOps, List.mem_map] at ho; obtain ⟨q, -, rfl⟩ := ho; rfl
      rw [e0, e1, e2]; simp [callDefOps]
    rw [this]; exact hc.defNodup

/-! ## Calls, `tryCall`, `Args` -/

theorem clob_call (dest : CallDest) (L : List (Nat × Reg)) (D : List (Reg × Nat)) :
    (∀ q ∈ D, q.1 ∉ (MInst.call ⟨dest, retPairs L, callDefs D⟩).clobbers) ∧
    ∀ r ∈ (MInst.call ⟨dest, retPairs L, callDefs D⟩).clobbers, r ∉ highRegs := by
  refine ⟨fun q hq h => ?_, fun r hr => aapcs_not_high r (List.mem_filter.mp hr).1⟩
  simp only [MInst.clobbers, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.any_eq_false] at h
  exact h.2 (q.1, .vreg q.2 .int) (by simp only [callDefs, List.mem_map]; exact ⟨q, hq, rfl⟩)
    (by simp)

theorem spillInstOk_callSym {N : Nat} (nm : String) {L : List (Nat × Reg)} {D : List (Reg × Nat)}
    (hc : CallOk N L D) : SpillInstOk (.call ⟨.sym nm, retPairs L, callDefs D⟩) :=
  ⟨_, operands_call_sym nm L D,
    (List.nil_append (retOps L ++ callDefOps D)) ▸
      opsOk_call (pre := []) (.inl rfl) hc (clob_call _ L D).1 (clob_call _ L D).2,
    fun _ h => by cases h⟩

theorem spillInstOk_callReg {N : Nat} (t : Nat) {L : List (Nat × Reg)} {D : List (Reg × Nat)}
    (hc : CallOk N L D) : SpillInstOk (.call ⟨.reg (.vreg t .int), retPairs L, callDefs D⟩) :=
  ⟨_, operands_call_reg t L D,
    opsOk_call (pre := [tgtOp t]) (.inr ⟨t, rfl⟩) hc (clob_call _ L D).1 (clob_call _ L D).2,
    fun _ h => by cases h⟩

/-- **The `tryCall` replacing a call** (without `clobberAll`) has the call's facts. -/
theorem spillInstOk_tryCall_of_call {c : CallInfo} {ti : TryInfo} (hcl : ti.clobberAll = false)
    (h : SpillInstOk (.call c)) : SpillInstOk (.tryCall c ti) := by
  obtain ⟨ops, hops, hok, -⟩ := h
  have hcl' : (MInst.tryCall c ti).clobbers = (MInst.call c).clobbers := by
    simp [MInst.clobbers, hcl]
  exact ⟨ops, (operands_tryCall_call c ti).trans hops, hcl' ▸ hok, fun _ h => by cases h⟩

theorem mapM_argPairs (D : List (Reg × Nat)) : ∀ (s : Array Operand),
    ((argPairs D).mapM
      (fun (x : Reg × Reg) => do let r ← collectOp (OpSpec.fixedDef x.2) x.1; pure (r, x.2))).run s =
      .ok (argPairs D, s ++ (callDefOps D).toArray) := by
  induction D with
  | nil => intro s; simp [argPairs, callDefOps] <;> rfl
  | cons q D ih =>
    intro s
    simp only [argPairs, callDefOps, List.map_cons, List.mapM_cons, StateT.run_bind] at ih ⊢
    have h1 : (collectOp (OpSpec.fixedDef q.1) (Reg.vreg q.2 .int)).run s =
        .ok (Reg.vreg q.2 .int, s.push ⟨q.2, .int, .def, .late, .fixed q.1⟩) := rfl
    rw [h1, except_ok_bind, StateT.run_pure, except_pure, except_ok_bind, ih, except_ok_bind,
      StateT.run_pure, except_pure]
    simp

theorem operands_args (D : List (Reg × Nat)) :
    (MInst.args (argPairs D)).operands = .ok (callDefOps D).toArray := by
  rw [operands_eq]
  simp only [MInst.visitOperands, StateT.run_bind, mapM_argPairs]
  simp [bind, Except.bind, StateT.run, pure, StateT.pure, Except.pure]

/-- **`Args`** of distinct vregs in distinct argument registers. -/
theorem spillInstOk_args {D : List (Reg × Nat)} (hD : ∀ q ∈ D, ArgReg q.1)
    (hr : (D.map (·.1)).Nodup) (hv : (D.map (·.2)).Nodup) : SpillInstOk (.args (argPairs D)) := by
  have hc : CallOk 0 [] D := ⟨by simp, by simp, hD, hr, hv, fun _ _ => Nat.zero_le _⟩
  have := opsOk_call (pre := []) (clob := []) (.inl rfl) hc (by simp) (by simp)
  simp only [List.nil_append, retOps, List.map_nil] at this
  exact ⟨_, operands_args D, this, fun _ h => by cases h⟩

/-! ## The other control forms -/

/-- The register of a `cbz`/`cbnz`/trap condition is an int vreg. -/
def KindOk : CondBrKind → Prop
  | .zero r _ | .notZero r _ => ∃ n, r = .vreg n .int
  | .cond _ => True

/-- **The control shapes the lowering emits** (fresh defs `≥ N`). -/
inductive CtlShape (N : Nat) : MInst → Prop
  | callSym (nm : String) (L : List (Nat × Reg)) (D : List (Reg × Nat)) :
      CallOk N L D → CtlShape N (.call ⟨.sym nm, retPairs L, callDefs D⟩)
  | callReg (t : Nat) (L : List (Nat × Reg)) (D : List (Reg × Nat)) :
      CallOk N L D → CtlShape N (.call ⟨.reg (.vreg t .int), retPairs L, callDefs D⟩)
  | rets (ns : List (Nat × Reg)) : (∀ q ∈ ns, ∃ k, k < 8 ∧ q.2 = .x k) → (ns.map (·.2)).Nodup →
      CtlShape N (.rets (retPairs ns))
  | condBr (a b : Label) (k : CondBrKind) : KindOk k → CtlShape N (.condBr a b k)
  | trapIf (k : CondBrKind) (c : Clif.TrapCode) : KindOk k → CtlShape N (.trapIf k c)
  | tbb (kd : TestBitAndBranchKind) (a b : Label) (n bit : Nat) :
      CtlShape N (.testBitAndBranch kd a b (.vreg n .int) bit)
  | udf (c : Clif.TrapCode) : CtlShape N (.udf c)
  | emitIsland (k : Nat) : CtlShape N (.emitIsland k)
  | jump (l : Label) : CtlShape N (.jump l)
  | got (n : Nat) (nm : String) : N ≤ n → CtlShape N (.loadExtNameGot (.vreg n .int) nm)
  | near (n : Nat) (nm : String) (o : Int) : N ≤ n →
      CtlShape N (.loadExtNameNear (.vreg n .int) nm o)
  | jt (d : Label) (ts : List Label) (r t1 t2 : Nat) : t1 ≠ t2 → N ≤ t1 → N ≤ t2 →
      CtlShape N (.jtSequence d ts (.vreg r .int) (.vreg t1 .int) (.vreg t2 .int))
  | rmw (t : CTy) (op : AtomicRmwLoopOp) (fl : Clif.MemFlags) (p x d d1 d2 : Nat) :
      d ≠ d1 → d ≠ d2 → d1 ≠ d2 → N ≤ d → N ≤ d1 → N ≤ d2 →
      CtlShape N (.atomicRmwLoop t op fl (.vreg p .int) (.vreg x .int) (.vreg d .int)
        (.vreg d1 .int) (.vreg d2 .int))
  | cas (t : CTy) (fl : Clif.MemFlags) (p e x d d1 : Nat) : d ≠ d1 → N ≤ d → N ≤ d1 →
      CtlShape N (.atomicCasLoop t fl (.vreg p .int) (.vreg e .int) (.vreg x .int) (.vreg d .int)
        (.vreg d1 .int))
  | tls (nm : String) (d t : Nat) : d ≠ t → N ≤ d → N ≤ t →
      CtlShape N (.elfTlsGetAddr nm (.vreg d .int) (.vreg t .int))

theorem spillInstOk_kind (k : CondBrKind) (hk : KindOk k) (i : MInst)
    (hops : i.operands = (match k with
      | .zero (.vreg n .int) _ | .notZero (.vreg n .int) _ => .ok #[⟨n, .int, .use, .early, .reg⟩]
      | _ => .ok #[]))
    (hr : ∀ us, i ≠ .rets us) (hc : i.clobbers = []) : SpillInstOk i := by
  rcases k with ⟨r, s⟩ | ⟨r, s⟩ | c
  all_goals first
    | (obtain ⟨n, rfl⟩ := hk
       refine ⟨_, hops, hc ▸ opsOk_simple (by simp) (by simp) (by simp) (by simp), fun us h => absurd h (hr us)⟩)
    | exact ⟨_, hops, hc ▸ opsOk_simple (by simp) (by simp) (by simp) (by simp), fun us h => absurd h (hr us)⟩

/-- **Every control shape meets `SpillInstOk`.** -/
theorem spillInstOk_of_ctlShape {N : Nat} {m : MInst} (h : CtlShape N m) : SpillInstOk m := by
  cases h with
  | callSym nm L D hc => exact spillInstOk_callSym nm hc
  | callReg t L D hc => exact spillInstOk_callReg t hc
  | rets ns hr hnd => exact spillInstOk_rets hr hnd
  | condBr a b k hk =>
    exact spillInstOk_kind k hk _ (by rcases k with ⟨r, s⟩ | ⟨r, s⟩ | c <;>
      (try obtain ⟨n, rfl⟩ := hk) <;> rfl) (fun _ h => by cases h) rfl
  | trapIf k c hk =>
    exact spillInstOk_kind k hk _ (by rcases k with ⟨r, s⟩ | ⟨r, s⟩ | c <;>
      (try obtain ⟨n, rfl⟩ := hk) <;> rfl) (fun _ h => by cases h) rfl
  | tbb kd a b n bit => spill_form
  | udf c => spill_form
  | emitIsland k => spill_form
  | jump l => exact spillInstOk_jump l
  | got n nm _ => spill_form
  | near n nm o _ => spill_form
  | jt d ts r t1 t2 h _ _ => exact spillInstOk_jtSequence d ts h
  | rmw t op fl p x d d1 d2 h1 h2 h3 _ _ _ => exact spillInstOk_rmwLoop t op fl h1 h2 h3
  | cas t fl p e x d d1 h _ _ => exact spillInstOk_casLoop t fl h
  | tls nm d t h _ _ => exact spillInstOk_elfTls nm h

/-- **The defs of a control shape are `≥ N`.** -/
theorem ctlShape_defs {N : Nat} {m : MInst} (h : CtlShape N m) :
    ∀ ops, m.operands = .ok ops → ∀ o ∈ ops.toList, o.kind = .def → N ≤ o.vreg := by
  intro ops hops o ho hd
  cases h with
  | callSym nm L D hc =>
    rw [operands_call_sym] at hops; cases hops
    rcases mem_callOps (pre := []) (by simpa using ho) with ho | ⟨q, -, rfl⟩ | ⟨q, hq, rfl⟩
    · cases ho
    · cases hd
    · exact hc.fresh q hq
  | callReg t L D hc =>
    rw [operands_call_reg] at hops; cases hops
    rcases mem_callOps (pre := [tgtOp t]) (by simpa using ho) with ho | ⟨q, -, rfl⟩ | ⟨q, hq, rfl⟩
    · simp at ho; subst ho; cases hd
    · cases hd
    · exact hc.fresh q hq
  | rets ns _ _ =>
    rw [operands_rets] at hops; cases hops
    simp only [retOps, List.toList_toArray, List.mem_map] at ho
    obtain ⟨q, -, rfl⟩ := ho; cases hd
  | condBr a b k hk =>
    rcases k with ⟨r, s⟩ | ⟨r, s⟩ | c <;> (try obtain ⟨n, rfl⟩ := hk) <;> cases hops <;>
      simp at ho <;> subst ho <;> cases hd
  | trapIf k c hk =>
    rcases k with ⟨r, s⟩ | ⟨r, s⟩ | c <;> (try obtain ⟨n, rfl⟩ := hk) <;> cases hops <;>
      simp at ho <;> subst ho <;> cases hd
  | tbb kd a b n bit => cases hops; simp at ho; subst ho; cases hd
  | udf c => cases hops; simp at ho
  | emitIsland k => cases hops; simp at ho
  | jump l => cases hops; simp at ho
  | got n nm hn => cases hops; simp at ho; subst ho; exact hn
  | near n nm o' hn => cases hops; simp at ho; subst ho; exact hn
  | jt d ts r t1 t2 _ h1 h2 =>
    cases hops; simp at ho; rcases ho with rfl | rfl | rfl
    · cases hd
    · exact h1
    · exact h2
  | rmw t op fl p x d d1 d2 _ _ _ h1 h2 h3 =>
    cases hops; simp [OpSpec.fixedUse, OpSpec.fixedDef] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl
    · cases hd
    · cases hd
    · exact h1
    · exact h2
    · exact h3
  | cas t fl p e x d d1 _ h1 h2 =>
    cases hops; simp [OpSpec.fixedUse, OpSpec.fixedDef] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl
    · cases hd
    · cases hd
    · cases hd
    · exact h1
    · exact h2
  | tls nm d t _ h1 h2 =>
    cases hops; simp [OpSpec.fixedDef, OpSpec.earlyDef] at ho
    rcases ho with rfl | rfl
    · exact h1
    · exact h2

/-! ## Renaming -/

theorem clobbers_mapRegs (R : Reg → Reg) (m : MInst) : (m.mapRegs R).clobbers = m.clobbers := by
  cases m <;> simp [MInst.mapRegs, MInst.clobbers, List.any_map, Function.comp_def]

theorem nScratch_rn (gn : Nat → Nat) (c : RegClass) (l : List Operand) :
    nScratch c (l.map (rnOp gn)) = nScratch c l := by
  unfold nScratch
  rw [List.filter_map, List.length_map]
  rfl

theorem fixedRegs_rn (gn : Nat → Nat) (ops : Array Operand) :
    fixedRegs (ops.map (rnOp gn)) = fixedRegs ops := by
  unfold fixedRegs
  rw [Array.toList_map, List.filterMap_map]
  rfl

/-- **A vreg renaming that fixes the defs keeps `SpillInstOk`.** -/
theorem spillInstOk_mapRegs {R : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming R gn) {m : MInst}
    (h : SpillInstOk m)
    (hfix : ∀ ops, m.operands = .ok ops → ∀ o ∈ ops.toList, o.kind = .def → gn o.vreg = o.vreg) :
    SpillInstOk (m.mapRegs R) := by
  obtain ⟨ops, hops, hok, hret⟩ := h
  have hfx := hfix ops hops
  refine ⟨ops.map (rnOp gn), by rw [operands_mapRegs hg, hops]; rfl, ?_, ?_⟩
  · rw [clobbers_mapRegs]
    have hmem : ∀ o' ∈ (ops.map (rnOp gn)).toList, ∃ o ∈ ops.toList, o' = rnOp gn o := by
      intro o' ho'
      rw [Array.toList_map, List.mem_map] at ho'
      obtain ⟨o, ho, rfl⟩ := ho'
      exact ⟨o, ho, rfl⟩
    have hget : ∀ j : Nat, (ops.map (rnOp gn)).toList[j]? = (ops.toList[j]?).map (rnOp gn) := by
      intro j; rw [Array.toList_map, List.getElem?_map]
    refine ⟨fun o' ho' => ?_, fun o' ho' => ?_, fun o' ho' => ?_, fun o' ho' o'' ho'' p => ?_,
      fun j j' o' o'' p hj hj' => ?_, fun o' ho' => ?_, fun o' ho' => ?_, fun j o' i hj => ?_,
      fun c => ?_, ?_⟩
    · obtain ⟨o, ho, rfl⟩ := hmem o' ho'; exact hok.noStack o ho
    · obtain ⟨o, ho, rfl⟩ := hmem o' ho'; exact hok.useEarly o ho
    · obtain ⟨o, ho, rfl⟩ := hmem o' ho'; exact hok.fixedReg o ho
    · obtain ⟨o, ho, rfl⟩ := hmem o' ho'
      obtain ⟨o2, ho2, rfl⟩ := hmem o'' ho''
      intro hu hu' h1 h2
      show gn o.vreg = gn o2.vreg
      rw [hok.fixedUse o ho o2 ho2 p hu hu' h1 h2]
    · rw [hget] at hj hj'
      obtain ⟨o, hj0, rfl⟩ := Option.map_eq_some_iff.mp hj
      obtain ⟨o2, hj1, rfl⟩ := Option.map_eq_some_iff.mp hj'
      exact hok.fixedDefs j j' o o2 p hj0 hj1
    · obtain ⟨o, ho, rfl⟩ := hmem o' ho'; exact hok.fixedDefClob o ho
    · obtain ⟨o, ho, rfl⟩ := hmem o' ho'; exact hok.earlyDef o ho
    · rw [hget] at hj
      obtain ⟨o, hj0, rfl⟩ := Option.map_eq_some_iff.mp hj
      intro hc
      obtain ⟨h1, h2, oi, hoi, h3, h4, h5, h6⟩ := hok.reuse j o i hj0 hc
      refine ⟨h1, h2, rnOp gn oi, by rw [hget, hoi]; rfl, h3, h4, h5, fun j' o2 hj2 hc2 => ?_⟩
      rw [hget] at hj2
      obtain ⟨o3, hj3, rfl⟩ := Option.map_eq_some_iff.mp hj2
      exact h6 j' o3 hj3 hc2
    · unfold freeRegs
      rw [fixedRegs_rn, Array.toList_map, nScratch_rn]
      exact hok.enough c
    · have e : ((ops.map (rnOp gn)).toList.filter (·.kind == .def)).map (·.vreg) =
          (ops.toList.filter (·.kind == .def)).map (·.vreg) := by
        rw [Array.toList_map, List.filter_map, List.map_map]
        show List.map _ (List.filter (fun o => o.kind == .def) ops.toList) = _
        apply List.map_congr_left
        intro o ho
        have ho' := List.mem_filter.mp ho
        exact hfx o ho'.1 (by simpa using ho'.2)
      rw [e]; exact hok.defsNodup
  · intro us hus o' ho'
    cases m <;> simp only [MInst.mapRegs] at hus <;> try cases hus
    rename_i us0
    rw [Array.toList_map, List.mem_map] at ho'
    obtain ⟨o, ho, rfl⟩ := ho'
    exact hret us0 rfl o ho

end Backend.Proof.Spill
