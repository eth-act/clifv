import FV.E2E.RegLevelOp
import FV.Backend.Proof.LowerLemmas

/-!
# `Args` on the machine (M6)

`Args` emits no code: its defs are the incoming argument registers. `lowerRFunc` checks
(`ctlCheck`) that `Args` is instruction 0 of block 0 with (int vreg, argument register) pairs,
that before it block 0 only has moves into memory, and that no edge enters block 0. Then, while
instruction 0 of block 0 is pending, the store holds the world's argument registers (`AInv`), so
`MStep`'s writes of the `Args` defs change nothing (`realizes_args`).
-/

namespace Backend.Proof

open Backend E2E Backend.Proof.Driver

/-! ## What `ctlCheck` gives -/

theorem ctlCheck_inst {vc : VCode} {rf : RFunc} (h : ctlCheck vc rf = true) {b k : Nat}
    {vb : VBlock} {i : MInst} (hvb : vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i) :
    ctlInstOk b k i = true := by
  simp only [ctlCheck, Bool.and_eq_true, List.all_eq_true] at h
  have h1 := h.1.1 (vb, b) (List.mem_zipIdx_iff_getElem?.mpr (by simpa using hvb))
  exact h1 (i, k) (List.mem_zipIdx_iff_getElem?.mpr (by simpa using hi))

theorem isVregInt_iff {r : Reg} (h : r.isVregInt = true) : ∃ n, r = .vreg n .int := by
  cases r with
  | vreg n c => cases c <;> simp_all [Reg.isVregInt]
  | _ => simp [Reg.isVregInt] at h

theorem ctlCheck_args {vc : VCode} {rf : RFunc} (h : ctlCheck vc rf = true) {b k : Nat}
    {vb : VBlock} {ds : List (Reg × Reg)} (hvb : vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.args ds)) :
    b = 0 ∧ k = 0 ∧ ∀ p ∈ ds, (∃ n, p.1 = .vreg n .int) ∧ p.2.isArgReg = true := by
  have h2 := ctlCheck_inst h hvb hi
  simp only [ctlInstOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h2
  exact ⟨h2.1.1, h2.1.2, fun p hp => ⟨isVregInt_iff (h2.2 p hp).1, (h2.2 p hp).2⟩⟩

theorem ctlCheck_succ {vc : VCode} {rf : RFunc} (h : ctlCheck vc rf = true) {b j s : Nat}
    (hs : succOf vc b j = some s) : s ≠ 0 := by
  simp only [ctlCheck, Bool.and_eq_true] at h
  have h3 := h.2
  unfold succOf at hs
  split at hs
  · rename_i ss ps hcfg
    rw [hcfg] at h3
    simp only [Array.all_eq_true', bne_iff_ne, ne_eq] at h3
    cases hb : ss[b]? with
    | none => simp [hb] at hs
    | some l =>
      simp only [hb, Option.bind_some] at hs
      exact h3 l (Array.mem_of_getElem? hb) s (Array.mem_of_getElem? hs)
  · cases hs

theorem mem_takeWhile_pred {α : Type} {p : α → Bool} : ∀ {l : List α} {x : α},
    x ∈ l.takeWhile p → p x = true
  | [], _, h => by simp at h
  | a :: l, x, h => by
    simp only [List.takeWhile_cons] at h
    split at h
    · rename_i ha
      rcases List.mem_cons.mp h with rfl | h
      · exact ha
      · exact mem_takeWhile_pred h
    · simp at h

/-- An item of block 0 followed (later) by `op 0` is a move into memory. -/
theorem ctlCheck_before {vc : VCode} {rf : RFunc} (h : ctlCheck vc rf = true)
    {items : Array RItem} (hit : rf.blocks[0]? = some items) {pre its : List RItem} {it : RItem}
    (hsp : items.toList = pre ++ it :: its) (hop : ∃ a, RItem.op 0 a ∈ its) :
    it.isMove = true ∧ it.regDst = false := by
  simp only [ctlCheck, Bool.and_eq_true, List.all_eq_true, hit, Option.getD_some] at h
  obtain ⟨⟨-, hT, hD⟩, -⟩ := h
  have hsplit := List.takeWhile_append_dropWhile (p := RItem.isMove) (l := items.toList)
  have hget : items.toList[pre.length]? = some it := by rw [hsp]; simp
  by_cases hlt : pre.length < (items.toList.takeWhile RItem.isMove).length
  · have hT' : (items.toList.takeWhile RItem.isMove)[pre.length]? = some it := by
      rw [← hsplit, List.getElem?_append_left hlt] at hget; exact hget
    have hm := List.mem_of_getElem? hT'
    exact ⟨mem_takeWhile_pred hm, by simpa using hT it hm⟩
  · exfalso
    obtain ⟨a, ha⟩ := hop
    have hits : its = items.toList.drop (pre.length + 1) := by rw [hsp]; simp
    have hdrop : items.toList.drop (pre.length + 1) =
        (items.toList.dropWhile RItem.isMove).drop
          (pre.length + 1 - (items.toList.takeWhile RItem.isMove).length) := by
      conv => lhs; rw [← hsplit]
      rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append]
    rw [hits, hdrop, show pre.length + 1 - (items.toList.takeWhile RItem.isMove).length =
      1 + (pre.length - (items.toList.takeWhile RItem.isMove).length) by omega,
      ← List.drop_drop] at ha
    have := hD _ ((List.drop_sublist _ _).subset ha)
    simp [RItem.isOp0] at this

/-! ## The invariant -/

/-- The store holds the world's argument registers `A`. -/
def ArgsOk (A : Reg → Prop) (m : Loc → CV) (w : Arm.ArmState) : Prop :=
  ∀ r, A r → m (.reg r) = regVal w r

/-- While instruction 0 of block 0 is pending, the store holds the argument registers the entry
`Args` reads (`VCode.EntryArg`). -/
def AInv (R : RL) : MConf CV Arm.ArmState → Prop
  | .run ⟨b, its, m, w⟩ => b = 0 → (∃ a, RItem.op 0 a ∈ its) → ArgsOk R.vc.EntryArg m w
  | _ => True

theorem upd_other {α β : Type} [DecidableEq α] {f : α → β} {a b : α} {x : β} (h : b ≠ a) :
    upd f a x b = f b := by simp [upd, h]

/-- `AInv` is kept by every step of the allocated code from a `Q` state. -/
theorem aInv_step {R : RL} (hR : R.Wf) {s : Arm.ArmState} {c c' : MConf CV Arm.ArmState}
    (hq : Q R s c) (hA : AInv R c) (h : MStep R.vc R.sem ckeep R.rf c c') : AInv R c' := by
  have hck := (lowerRFunc_ok hR.alloc).2.2.2
  cases h with
  | @move b src dst its m w =>
    intro hb hop
    subst hb
    obtain ⟨j, vb, items, pre, -, -, -, -, -, -, hit, hsplit, -⟩ := hq
    obtain ⟨hmv, hrd⟩ := ctlCheck_before hck hit hsplit hop
    have hA' := hA rfl (by obtain ⟨a, ha⟩ := hop; exact ⟨a, List.mem_cons_of_mem _ ha⟩)
    intro r hr
    have hne : Loc.reg r ≠ dst := by
      intro e; subst e; simp [RItem.regDst] at hrd
    rw [upd_other hne]
    exact hA' r hr
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 c' hvb hi hops hsz hsem hlen hho hcl hn =>
    cases hn with
    | next =>
      intro hb hop
      subst hb
      obtain ⟨j, vb0, items, pre, -, -, -, -, -, -, hit, hsplit, -⟩ := hq
      have := (ctlCheck_before hck hit hsplit hop).1
      simp [RItem.isMove] at this
    | goto _ hs _ =>
      intro hb
      exact absurd hb (ctlCheck_succ hck hs)
    | ret => trivial
    | halt => trivial

/-! ## `Args` realised by no code -/

theorem writeM_self {m : Loc → CV} :
    ∀ (dl : List ((Operand × Loc) × CV)), (∀ p ∈ dl, p.2 = m p.1.2) → writeM m dl = m
  | [], _ => rfl
  | p :: dl, h => by
    simp only [writeM, List.foldl_cons]
    have e : upd m p.1.2 p.2 = m := by
      funext l; simp only [upd]; split
      · subst_vars; exact h p (by simp)
      · rfl
    rw [e]
    exact writeM_self dl (fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem args_defs_self {m : Loc → CV} {w : Arm.ArmState} :
    ∀ (ns : List (Nat × Reg)) (al : List Loc), al.length = ns.length →
      (∀ p ∈ (argOps ns).zip al, ∀ r, p.1.con = .fixed r → p.2 = .reg r) →
      (∀ q ∈ ns, m (.reg q.2) = regVal w q.2) →
      ∀ p ∈ ((argOps ns).zip al).zip (ns.map fun q => regVal w q.2), p.2 = m p.1.2
  | [], _, _, _, _ => by simp
  | q :: ns, [], hl, _, _ => by simp at hl
  | q :: ns, l :: al, hl, hfix, hm => by
    intro p hp
    simp only [argOps, List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · have := hfix (⟨q.1, .int, .def, .late, .fixed q.2⟩, l) (by simp [argOps]) q.2 rfl
      simp only at this ⊢
      rw [this, hm q (by simp)]
    · exact args_defs_self ns al (by simpa using hl)
        (fun p hp r hr => hfix p (by
          simp only [argOps, List.map_cons, List.zip_cons_cons]; exact List.mem_cons_of_mem _ hp) r hr)
        (fun q' hq' => hm q' (by simp [hq'])) p hp

theorem argOps_isDef (ns : List (Nat × Reg)) : ∀ o ∈ argOps ns, o.isDef = true ∧ o.isEarly = false ∧
    o.isLate = true ∧ o.isUse = false := by
  intro o ho
  simp only [argOps, List.mem_map] at ho
  obtain ⟨q, -, rfl⟩ := ho
  simp [Operand.isDef, Operand.isEarly, Operand.isLate, Operand.isUse]

theorem argPairs_of {ds : List (Reg × Reg)} (h : ∀ p ∈ ds, ∃ n, p.1 = .vreg n .int) :
    ∃ ns : List (Nat × Reg), ds = argPairs ns ∧ ns.map (·.2) = ds.map (·.2) := by
  induction ds with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons p ds ih =>
    obtain ⟨ns, h1, h2⟩ := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    obtain ⟨n, hn⟩ := h p (by simp)
    refine ⟨(n, p.2) :: ns, ?_, by simp [h2]⟩
    obtain ⟨r, q⟩ := p
    simp only at hn
    subst hn
    simp [argPairs, h1]

theorem assign_args {ds : List (Reg × Reg)} {regs : Array Reg} {i' : MInst}
    (h : (MInst.args ds).assign regs = .ok i') : ∃ ds', i' = .args ds' := by
  unfold MInst.assign at h
  simp only [MInst.visitOperands, StateT.run_bind, StateT.run_pure] at h
  generalize StateT.run _ 0 = X at h
  cases X with
  | error e => cases h
  | ok v =>
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · simp only [Except.ok.injEq] at h
      exact ⟨_, h.symm⟩

/-- **`Args` on the machine**: no code; the store is unchanged. -/
theorem realizes_args {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {c' : MConf CV Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) (hA : AInv R (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {ds : List (Reg × Reg)}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.args ds))
    (h : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c') :
    Q R s c' := by
  have hck := (lowerRFunc_ok hR.alloc).2.2.2
  obtain ⟨rfl, rfl, hds⟩ := ctlCheck_args hck hvb hi
  obtain ⟨ns, rfl, hns⟩ := argPairs_of (fun p hp => (hds p hp).1)
  have hops := operands_args ns
  obtain ⟨j, vb0, items, pre, code, ls, ps1, ps2, T, hvb0, hit, hsplit, hchk, hcode, hls, htr, hdrop,
    hpc, hst⟩ := hq
  rw [hvb] at hvb0; cases hvb0
  have hAO := hA rfl ⟨allocs, by simp⟩
  cases h with
  | @op b k allocs its m w vb' i ops outs outs' w' ctl m2 c' hvb' hi' hops' hsz hsem hlen hho hcl hn =>
  rw [hvb] at hvb'; cases hvb'
  rw [hi] at hi'; cases hi'
  rw [hops] at hops'; cases hops'
  obtain rfl := hho.2.1 rfl
  have hsem' := hsem
  simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
  obtain ⟨rfl, rfl, rfl⟩ := hsem'
  cases hn with
  | next hk =>
  obtain ⟨c1, c2, hc1, hc2, rfl⟩ := itemsCode_cons hcode
  obtain ⟨regs, i0, i', rfl, hi0, hasg, hc1'⟩ := itemCode_op hc1
  rw [hi] at hi0; cases hi0
  -- the assigned `Args` is an `Args` again: no code
  obtain ⟨ds', rfl⟩ := assign_args hasg
  have hc1e : c1 = [] := by
    rcases hc1' with ⟨-, h, -⟩ | ⟨_, _, rfl⟩ | ⟨us, h, -⟩
    · exact absurd rfl (h ds')
    · rfl
    · cases h
  subst hc1e
  obtain ⟨c, wh, i2, ops2, hi2, hops2, hstat, hchk'⟩ := op_checked hchk
  rw [hi] at hi2; cases hi2
  rw [hops] at hops2; cases hops2
  obtain ⟨hsz', hloc, -, -⟩ := checkStatic_facts hstat
  -- the store is unchanged
  have hdefs : ∀ (P : Operand → Bool), (∀ o ∈ argOps ns, P o = true) →
      ((argOps ns).toArray.zip (regs.map Loc.reg)).toList.filter (fun p => P p.1) =
        ((argOps ns).toArray.zip (regs.map Loc.reg)).toList := by
    intro P hP
    rw [List.filter_eq_self]
    intro p hp
    exact hP _ (List.of_mem_zip (by simpa using hp)).1
  have hlenA : (regs.map Loc.reg).toList.length = ns.length := by
    have := hsz'; simp [argOps] at this; simpa using this.symm
  have hm2 : m2 = m := by
    have hE : ((((argOps ns).toArray.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).zip
        ((argPairs ns).map fun d => regVal w d.2)).filter (·.1.1.isEarly) = [] := by
      rw [List.filter_eq_nil_iff]
      intro p hp
      have h1 := (List.mem_filter.mp (List.of_mem_zip hp).1).1
      have h3 := (List.of_mem_zip (by simpa using h1)).1
      simpa using (argOps_isDef ns _ h3).2.1
    rw [hE] at hcl
    funext l
    exact hcl.1 l (by simp [MInst.clobbers])
  subst m2
  have hself : writeM m ((((argOps ns).toArray.zip (regs.map Loc.reg)).toList.filter (·.1.isDef)).zip
      ((argPairs ns).map fun d => regVal w d.2) |>.filter (·.1.1.isLate)) = m := by
    apply writeM_self
    intro p hp
    have hp' := (List.mem_filter.mp hp).1
    rw [hdefs _ (fun o ho => (argOps_isDef ns o ho).1)] at hp'
    simp only [Array.toList_zip, Array.toList_map] at hp'
    refine args_defs_self ns (regs.toList.map Loc.reg) (by simpa using hlenA) ?_ ?_ p
      (by simpa [argPairs, Function.comp_def] using hp')
    · intro p hp r hr
      exact (hloc p (by simpa using hp)).2 r hr
    · intro q hq
      exact hAO q.2 ⟨vb, argPairs ns, hvb, hi, .vreg q.1 .int, by
        simp only [argPairs, List.mem_map]; exact ⟨q, hq, rfl⟩⟩
  rw [hself]
  exact ⟨j, vb, items, pre ++ [.op 0 (regs.map Loc.reg)], c2, ls, ps1, ps2, T, hvb, hit,
    by rw [hsplit]; simp, hchk', hc2, by simpa [codeLinesE] using hls, htr, hdrop, hpc, hst⟩

end Backend.Proof
