import FV.E2E.RegLevelFrame
import FV.Backend.Proof.FrameLines

/-!
# The entry block in the emitted code (#553)

Since #553 the emitter lays out the blocks as Cranelift's `MachBuffer` does (`emitPlan`). The
entry block is still the first segment, its label line 0, and its first lines are the prologue's
(`entry_static`): the prologue is the first instruction of the entry block's code; when it is the
only one, its lines are the segment's last instruction's, which the branch check keeps as they are
(the entry block never forwards, `fwd?_entry`; the prologue branches nowhere,
`prologueLines_target`).
-/

namespace Link.EhCheck.Complete

set_option autoImplicit false

open Backend Backend.Proof E2E

/-! ## The entry block of the emitted code -/

/-- The prologue's lines branch nowhere. -/
theorem prologueLines_target (saves : List Reg) (size : Nat) :
    ∀ ln ∈ prologueLines saves size, ln.target? = none := by
  intro ln hl
  simp only [prologueLines, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with (((rfl | rfl) | hl) | hl) | hl
  · rfl
  · rfl
  · obtain ⟨i, rfl, a, b, rfl | rfl⟩ := mem_pushLines hl <;> rfl
  · obtain ⟨i, rfl, a, b, rfl | rfl⟩ := mem_pushLines hl <;> rfl
  · rcases mem_spAdjLines hl with ⟨i, -, rfl⟩ | hl | rfl
    · rfl
    · simp only [loadConst64, List.mem_cons, List.mem_filterMap] at hl
      rcases hl with rfl | ⟨j, _, hj⟩
      · rfl
      · split at hj
        · simp only [Option.some.injEq] at hj; subst hj; rfl
        · cases hj
    · rfl

/-- The entry block never forwards (`fwd?` finds the entry block's label at index 0). -/
theorem fwd?_entry {af : AFunc} {l : Label} {code : Array AInst}
    (h : af.blocks[0]? = some (l, code)) : af.fwd? l = none := by
  obtain ⟨bs, hb⟩ : ∃ bs, af.blocks.toList = (l, code) :: bs := by
    cases hl : af.blocks.toList with
    | nil => simp [← Array.getElem?_toList, hl] at h
    | cons e bs =>
      rw [← Array.getElem?_toList, hl] at h
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      exact ⟨bs, by rw [h]⟩
  unfold AFunc.fwd?
  rw [hb]
  simp [List.zipIdx_cons]

/-- **The entry block in the emitted code** (`RegLevelFrame.entry_block` without the
activation): its label at line 0, then the prologue's lines. -/
theorem entry_static {vc : VCode} {rf : RFunc} {af : AFunc} {k : Nat} {fa : FnAsm}
    (halloc : lowerRFunc vc rf = .ok af) (hemit : emitFunc k af = .ok fa) {vb : VBlock}
    {items : Array RItem} (hvb : vc.blocks[0]? = some vb) (hit : rf.blocks[0]? = some items) :
    ∃ code, itemsCode (RAFrame.compute vc rf) vb items.toList = .ok code ∧
      af.blocks[0]? = some (vb.label, (AInst.prologue :: code).toArray) ∧
      fa.lines.toList[0]? = some (.label (.block vb.label)) ∧
      prologueLines af.saves af.frameSize <+: fa.lines.toList.drop 1 := by
  have hframe := lowerRFunc_frame halloc
  obtain ⟨⟨-, -, -, hbl⟩, -⟩ := lowerRFunc_ok halloc
  obtain ⟨code, hcode, haf⟩ := hbl 0 vb items hvb hit
  have haf' : af.blocks[0]? = some (vb.label, (AInst.prologue :: code).toArray) := by
    simpa using haf
  obtain ⟨p, hp, hL, hseg⟩ := emit_seg hemit
  obtain ⟨i, s, o, j, ps1, psm, ps2, hs, ho, hidx, hlab, -, hj, hd, e1, e2, -, hj0⟩ :=
    hseg 0 _ _ haf'
  obtain rfl := hj0 rfl
  refine ⟨code, hcode, haf', hj, ?_⟩
  rw [show (0 : Nat) + 1 = 1 from rfl] at hd
  rw [hd]
  refine List.prefix_append_of_prefix ?_
  have hpl : ∀ ln ∈ prologueLines af.saves af.frameSize, ln.plain = true := fun ln h => by
    obtain ⟨-, -, -, hp⟩ := prologueLines_ins _ _ ln h; exact hp
  have hpro : codeLinesE ⟨k, af.slotBase⟩ af [AInst.prologue] ps1 =
      .ok (prologueLines af.saves af.frameSize, ps1) := by
    simp [codeLinesE, ainstLines, hframe, bind, Except.bind, pure, Except.pure]
  simp only [List.toList_toArray] at e1 e2
  by_cases hc : code = []
  · -- only the prologue: its lines are the segment's last instruction's, kept by the check
    subst hc
    simp only [List.dropLast_singleton, List.getLast?_singleton, Option.toList_some] at e1 e2
    simp only [codeLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at e1
    obtain ⟨hb0, rfl⟩ := e1
    rw [hpro] at e2
    simp only [Except.ok.injEq, Prod.mk.injEq] at e2
    obtain ⟨ht, -⟩ := e2
    obtain ⟨A, -, hx⟩ := segX_get hp hs ho
    rw [hidx] at hx
    obtain ⟨x', hx', hok⟩ := segChecked_of hp hx (.inl (by simp [hlab, fwd?_entry haf']))
    rw [hx] at hx'
    cases hx'
    unfold segTermOk at hok
    simp only [hidx, haf', Option.bind_some] at hok
    have hback : (#[AInst.prologue]).back? = some AInst.prologue := rfl
    rw [show (AInst.prologue :: ([] : List AInst)).toArray = #[AInst.prologue] from rfl, hback] at hok
    obtain ⟨hlen, hlo⟩ := termOk_kept (fun _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ _ _ h => by cases h) (fun _ _ h => by cases h) hok
    have hoe : o = s.term := by
      apply List.ext_getElem? 
      intro n
      cases hn : s.term[n]? with
      | none =>
        have : s.term.length ≤ n := List.getElem?_eq_none_iff.mp hn
        exact List.getElem?_eq_none_iff.mpr (by simpa [hlen] using this)
      | some y =>
        have hn' : n < o.length := by
          rw [hlen]; exact (List.getElem?_eq_some_iff.mp hn).1
        obtain ⟨z, hz⟩ : ∃ z, o[n]? = some z := ⟨_, List.getElem?_eq_getElem hn'⟩
        rw [hz]
        have hy : y ∈ prologueLines af.saves af.frameSize := by
          rw [ht]; exact List.mem_of_getElem? hn
        rcases hlo n y z hn hz with ⟨rfl, -⟩ | ⟨l, -, hyt, -⟩
        · rfl
        · rw [prologueLines_target _ _ y hy] at hyt; cases hyt
    rw [← hb0, List.nil_append, hoe, ← ht, relaxLines_plain hpl]
    exact List.prefix_refl _
  · rw [show AInst.prologue :: code = [AInst.prologue] ++ code from rfl,
      List.dropLast_append_of_ne_nil hc] at e1
    obtain ⟨l1, X, psA, h1, -, hb⟩ := codeLinesE_append _ _ _ _ _ e1
    rw [hpro] at h1
    simp only [Except.ok.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, -⟩ := h1
    rw [hb, List.append_assoc, relaxLines_append, relaxLines_plain hpl]
    exact List.prefix_append _ _

end Link.EhCheck.Complete
