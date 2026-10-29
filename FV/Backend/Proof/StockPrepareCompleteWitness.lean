module

public import FV.Backend.Proof.StockPrepareComplete
public import FV.Backend.Proof.StockPreparedForwardWitness
public import FV.Backend.Proof.StockPerEdgeCriticalAllocatorWitness
public import FV.Backend.Proof.PerEdgePrepareWitness

@[expose] public section

namespace Backend.Stock.Proof.PrepareCompleteWitness
open Backend.Proof Backend.Proof.Driver

private theorem star_last {α : Type} {r : α → α → Prop} {a c : α}
    (h : Star r a c) (different : a ≠ c) : ∃ b,Star r a b ∧ r b c := by
  induction h with
  | refl a => exact False.elim (different rfl)
  | @step a mid c first rest ih =>
    by_cases same : mid = c
    · subst same
      exact ⟨a,.refl _,first⟩
    · obtain ⟨b,prelude,last⟩ := ih same
      exact ⟨b,.step first prelude,last⟩

private theorem return_observation {W : Type} {vc : VCode} {edges : Array PerEdgePrep.EdgeRow}
    {sem : ISem CV W} {ρ : Nat → CV} {w w' : W} {values : List CV}
    (h : Star (VStepAt vc edges sem) (VConf.init ρ w) (.ret values w')) :
    ∃ us,PerEdgePrep.VRetFromAt vc edges sem ⟨0,0,ρ,w⟩ us values w' := by
  obtain ⟨last,prelude,step⟩ := star_last h (by intro eq; cases eq)
  cases last with
  | ret => cases step
  | halt => cases step
  | run state =>
    obtain ⟨b,k,regs,world⟩ := state
    cases step with
    | step block instruction operands semantics length next =>
      rename_i vb i ops outs final ctl
      cases next with
      | ret ret =>
        rename_i us
        subst i
        exact ⟨us,b,k,regs,world,vb,ops,outs,prelude,block,instruction,operands,rfl,semantics⟩

/-- Actual unreachable filtering/new critical edge/RPO with nonempty parameter
copies inhabits the generic checker completeness, live-block, effect and checked
wrapper results. No observed checker verdict is used to prove acceptance. -/
theorem generic_prepare_complete_witness :
    ∃ (vc : VCode) (edges : Array PerEdgePrep.EdgeRow) (p : EdgeVCode)
      (ss0 ps0 ss3 ps3 : Array (Array Nat)) (q : Nat),
      prepareAt vc edges = .ok p ∧ vc.blocks.size = 5 ∧
      p.code.blocks.map (·.label) = #[10,31,20,30] ∧
      vc.cfg = .ok (ss0,ps0) ∧ p.code.cfg = .ok (ss3,ps3) ∧
      PerEdgePrep.prepCheckAt vc edges p = true ∧ prepareCheckedAt vc edges = .ok p ∧
      (vc.hasTryCall || !p.code.hasTryCall) = true ∧ (vc.hasTls || !p.code.hasTls) = true ∧
      sigmaOf vc p.code 0 = some q ∧ PerEdgePrep.keptOkAt vc p.code edges p.edges ss0 ss3 0 q = true := by
  obtain ⟨p,run,labels,_⟩ := PerEdgePrepareWitness.per_edge_prepare_split_copy_witness (fun _ => 0)
  have accepted := PerEdgePrep.prepCheckAt_complete run (by decide +kernel)
    (by unfold Prep.Lbls; decide +kernel)
  have checked := PerEdgePrep.prepareCheckedAt_complete run (by decide +kernel)
    (by unfold Prep.Lbls; decide +kernel)
  have effects := PerEdgePrep.prepareAt_no_new_effects run (by decide +kernel)
    (by unfold Prep.Lbls; decide +kernel)
  obtain ⟨_,ss0,ps0,cfg0,_⟩ := PerEdgePrep.prepareAt_input_facts run
  obtain ⟨_,ss3,ps3,cfg3⟩ := PerEdgePrep.prepareAt_cfg run (by decide +kernel)
    (by unfold Prep.Lbls; decide +kernel)
  have cfg := Prep.cfg_spec cfg0
  have live := (Prep.reachable_spec (Prep.succsIn_of cfg) (by rw [cfg.size]; decide +kernel)).2.1
  obtain ⟨q,atQ,block⟩ := PerEdgePrep.live_okAt run (by decide +kernel)
    (by unfold Prep.Lbls; decide +kernel) cfg0 cfg3 (by decide +kernel) live
  exact ⟨_,_,p,ss0,ps0,ss3,ps3,q,run,rfl,labels,cfg0,cfg3,accepted,checked,effects.1,effects.2,atQ,block⟩

/-- Original-scope/dominated actual conditional Stock code passes preparation
without any supplied graph/checker certificate, and complete concrete csem
returns and typed observations are preserved for every initial world/registers. -/
theorem stock_prepare_complete_return_witness :
    ∃ (f : Clif.Function) (result : Result) (p : EdgeVCode),
      Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧
      prepareAt result.code result.edgeArgs = .ok p ∧
      0 < result.code.blocks.size ∧ Prep.Lbls result.code.blocks ∧
      PerEdgePrep.prepCheckAt result.code result.edgeArgs p = true ∧
      prepareCheckedAt result.code result.edgeArgs = .ok p ∧
      ∀ (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (w : Arm.ArmState) (ρ : Nat → CV),
        Star (VStepAt result.code result.edgeArgs (csem F ctx X)) (VConf.init ρ w) (.ret [regVal w (.x 0)] w) ∧
        Star (VStepAt p.code p.edges (csem F ctx X)) (VConf.init ρ w) (.ret [regVal w (.x 0)] w) ∧
        ∃ us,PerEdgePrep.VRetFromAt result.code result.edgeArgs (csem F ctx X) ⟨0,0,ρ,w⟩ us [regVal w (.x 0)] w ∧
          PerEdgePrep.VRetFromAt p.code p.edges (csem F ctx X) ⟨0,0,ρ,w⟩ us [regVal w (.x 0)] w := by
  obtain ⟨result,p,rf,af,lowered,scope,dominated,checked,_,_,_,runs⟩ :=
    PreparedForwardWitness.stock_prepared_return_forward_witness
  have prepare := (PerEdge.prepareCheckedAt_ok checked).1
  have domain := stock_prepare_domain lowered scope
  refine ⟨_,result,p,lowered,scope,dominated,prepare,domain.1,domain.2,
    stock_prepCheckAt_complete lowered scope prepare,stock_prepareCheckedAt_complete lowered scope prepare,?_⟩
  intro F ctx X w ρ
  have source := (runs F ctx X w ρ (fun _ => 0)).1
  have sem := (driverSem_csem F ctx X).toDriverSemG
  obtain ⟨us,observation⟩ := return_observation source
  exact ⟨source,stock_prepare_return lowered scope prepare sem source,us,observation,
    (stock_prepare_sound lowered scope prepare sem ρ w).1 us _ w observation⟩

/-- Complete original source trap and concrete csem halt/coded-trap observations
survive actual Stock preparation; acceptance is derived from original scope. -/
theorem stock_prepare_complete_halt_witness :
    ∃ (f : Clif.Function) (result : Result) (p : EdgeVCode),
      Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧
      prepareAt result.code result.edgeArgs = .ok p ∧
      PerEdgePrep.prepCheckAt result.code result.edgeArgs p = true ∧
      ∀ (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (w : Arm.ArmState) (ρ : Nat → CV),
        Star (VStepAt result.code result.edgeArgs (csem F ctx X)) (VConf.init ρ w) (.halt w) ∧
        Star (VStepAt p.code p.edges (csem F ctx X)) (VConf.init ρ w) (.halt w) ∧
        PerEdgePrep.VTrapFromAt result.code result.edgeArgs (csem F ctx X) ⟨0,0,ρ,w⟩ (.user 9) ∧
        PerEdgePrep.VTrapFromAt p.code p.edges (csem F ctx X) ⟨0,0,ρ,w⟩ (.user 9) := by
  obtain ⟨result,p,rf,af,lowered,scope,dominated,checked,_,_,_,runs⟩ :=
    PreparedForwardWitness.stock_prepared_halt_forward_witness
  have prepare := (PerEdge.prepareCheckedAt_ok checked).1
  refine ⟨_,result,p,lowered,scope,dominated,prepare,stock_prepCheckAt_complete lowered scope prepare,?_⟩
  intro F ctx X w ρ
  obtain ⟨source,_,observation,_⟩ := runs F ctx X w ρ (fun _ => 0)
  have sem := (driverSem_csem F ctx X).toDriverSemG
  exact ⟨source,stock_prepare_halt lowered scope prepare sem source,observation,
    (stock_prepare_sound lowered scope prepare sem ρ w).2 (.user 9) observation⟩

/-- The real Stock critical-edge fixture also inhabits scope-derived complete
preparation, including its reordered synthetic nodes and nonempty copies. -/
theorem stock_prepare_complete_critical_witness :
    ∃ (f : Clif.Function) (result : Result) (p : EdgeVCode),
      Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧
      prepareAt result.code result.edgeArgs = .ok p ∧
      PerEdgePrep.prepCheckAt result.code result.edgeArgs p = true ∧
      prepareCheckedAt result.code result.edgeArgs = .ok p ∧
      p.edges[0]? = some #[#[],#[]] ∧ p.edges[1]? = some #[#[Reg.vreg 192 .int]] ∧
      p.edges[2]? = some #[#[Reg.vreg 192 .int]] ∧ (p.code.blocks[1]!).label = 2 := by
  obtain ⟨result,p,rf,af,lowered,scope,dominated,prepare,e0,e1,e2,label,_⟩ :=
    PerEdgeCriticalAllocatorWitness.stock_per_edge_critical_allocator_fallback_witness
  exact ⟨_,result,p,lowered,scope,dominated,prepare,stock_prepCheckAt_complete lowered scope prepare,
    stock_prepareCheckedAt_complete lowered scope prepare,e0,e1,e2,label⟩

end Backend.Stock.Proof.PrepareCompleteWitness
