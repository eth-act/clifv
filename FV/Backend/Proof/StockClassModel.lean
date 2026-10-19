import FV.Backend.Proof.StockClassCtorContracts
namespace Backend.Stock.Proof.OperandClassDraft
open Backend.Proof Backend.Proof.Spill Backend.Proof.Flow Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

private theorem stock_γC_ctor (s0 st : State) (as : List FA) (vs : List V) (term : Term) (v : V) (st' : State)
    (hvs : Holds2 (fun a s v => γC a s.base v) st as vs) (hIs : ClsIs ctx s0.base st.base) (hpre : apreC false term.id as = true)
    (h : (Stock.sem ctx).ctor term vs st = .ok (v, st')) :
    γC (actor term.id as) st'.base v ∧ ClsIs ctx s0.base st'.base := by
  have hc := stock_ctor_classes h
  have hargs : (∀ a ∈ as, a.f ≤ 1) → ∀ r ∈ regsInL vs, RegCls st'.base.classes r := fun hall r hr => by
    obtain ⟨w, hw, hrw⟩ := regsInL_mem hr
    obtain ⟨a, ha, hwa⟩ := holds2_mem hvs w hw
    exact regCls_step hc.step (hwa (hall a ha) r hrw)
  refine ⟨fun hf => ?_, ?_⟩
  · unfold actor at hf
    split at hf
    · simp at hf
    · rename_i hid
      have hall : ∀ a ∈ as, a.f ≤ 1 := fun a ha => joinAll_f hf a ha
      intro r hr
      rcases hc.regs hIs.sz r hr with h1 | h1 | ⟨x, -, hx⟩ | h1 | h1 | h1
      · exact hargs hall r h1
      · exact h1
      · exact regCls_step hc.step (hIs.vals x r hx)
      · exact absurd (beq_iff_eq.mpr h1) hid
      · exact regCls_step hc.step (hIs.try1 r h1)
      · exact regCls_step hc.step (hIs.try2 r h1)
  · obtain ⟨ms0, h0, h1⟩ := hIs.emitted
    obtain ⟨ms, h2, h3⟩ := hc.emit
    refine ⟨sz_step hc.step hIs.sz, fun x r hx => regCls_step hc.step (hIs.vals x r hx),
      fun r hr => regCls_step hc.step (hIs.try1 r hr), fun r hr => regCls_step hc.step (hIs.try2 r hr),
      ms0 ++ ms, by rw [h2, h0]; simp, fun m hm => ?_⟩
    rcases List.mem_append.mp hm with hm | hm
    · exact (h1 m hm).mono fun r hr => regCls_step hc.step hr
    · refine (h3 hIs.sz m hm).mono fun r hr => ?_
      rcases hr with ⟨hid, hr⟩ | hr
      · exact hargs (apreC_args hpre hid) r hr
      · exact hr


/-- The unchanged checked class summaries apply to actual Stock state and
constructors, with the existing complete class invariant supplied internally. -/
def stock_class_model {ctx : Ctx} (clean : Cov.Clean ctx) (s0 : State) :
    ModelC (Stock.sem ctx) false where
  γ := fun a s v => γC a s.base v
  Is := fun s => ClsIs ctx s0.base s.base
  Rs := fun s next => ClsStep s.base next.base
  rs_refl := fun s => clsStep_refl _
  rs_trans := fun _ _ _ => clsStep_trans
  rs_ctor := fun _ _ _ _ _ run => (stock_ctor_classes run).step
  top := fun _ _ h => by simp [FA.top] at h
  le := fun a b _ _ hab ha hb => by
    simp only [FA.le,Bool.and_eq_true,decide_eq_true_eq] at hab
    exact ha (Nat.le_trans hab.1 hb)
  mono := fun _ _ _ _ growth hv hf r hr => regCls_step growth (hv hf r hr)
  int := fun _ _ _ _ r hr => by simp [Stock.sem,Backend.sem,V.regsIn] at hr
  bool := fun _ _ _ r hr => by simp [Stock.sem,Backend.sem,V.regsIn] at hr
  prim := fun _ _ _ _ h _ r hr => by
    obtain ⟨t,rfl⟩ := sem_prim_eq ctx h
    simp [V.regsIn] at hr
  mkd := fun st ty k as vs h hf r hr => by
    rw [amk_f] at hf
    have member : r ∈ regsInL vs := by simpa [Stock.sem,Backend.sem,V.regsIn] using hr
    obtain ⟨w,hw,hrw⟩ := regsInL_mem member
    obtain ⟨a,ha,hwa⟩ := holds2_mem h w hw
    exact hwa (joinAll_f hf a ha) r hrw
  un := fun st a ty v k fs hv hu => by
    have eq := sem_unData_eq ctx hu
    subst eq
    intro w hw hf r hr
    exact hv hf r (by simpa [V.regsIn] using regsIn_sub_of_mem hw r hr)
  ext := fun st a term v fs hv extracted => γC_ext clean st.base a term v fs hv extracted
  ctor := fun st as vs term v next held invariant pre run =>
    stock_γC_ctor s0 st as vs term v next held invariant pre run

/-- Successful actual Stock evaluation accepted by the existing class summary
retains its full class invariant and gives the checked result class meaning. -/
theorem stock_apply_classes {ctx : Ctx} (clean : Cov.Clean ctx) {cfg : Config}
    (overlap : cfg.checkOverlap = false) {fuel ty term : Nat} {as : List FA} {a : FA}
    {vs : List V} {before after : State} {trace finalTrace : Array RuleId} {out : Option V}
    (checked : aApplyC program clsTab false ty term as = some a)
    (held : Holds2 (fun a s v => γC a s.base v) before as vs)
    (invariant : ClsIs ctx before.base before.base)
    (run : (applyTerm program (Stock.sem ctx) cfg fuel ty term vs).run (before,trace) =
      .ok (out,after,finalTrace)) :
    ClsIs ctx before.base after.base ∧ ∀ v,out = some v → γC a after.base v := by
  let model := stock_class_model clean before
  exact (soundAtC (md := model) overlap clsTab_ok fuel).apply
    ty term as a vs before trace out after finalTrace checked held invariant run

end Backend.Stock.Proof.OperandClassDraft
