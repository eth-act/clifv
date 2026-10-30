import FV.Backend.Proof.StockFloatCheckDomain
import FV.Backend.Proof.LowerTotal
import FV.Backend.Lowering.StockScalarNI

/-!
# Completeness of the scalar route, phase 1: prechecks and context

On the original input conditions (`driverInB`, subset E, dominance) and the scalar production
syntax, every precheck of `Stock.lower` passes and `Stock.buildCtx` succeeds. Later phases run the
single block's scan and return from this context.
-/

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false

private theorem ret_of_match {t : Clif.Terminator}
    (h : (match t with | .ret _ => true | _ => false) = true) : ∃ xs, t = .ret xs := by
  cases t <;> first | exact ⟨_,rfl⟩ | cases h

private theorem narrowAbi_of_abi {p : Clif.AbiParam} (h : Scalar.abiEligible p = true) :
    Scalar.narrowAbiEligible p = true := by
  simp only [Scalar.abiEligible,Arithmetic.abiEligible,Scalar.narrowAbiEligible,Bool.and_eq_true,
    Bool.or_eq_true,beq_iff_eq] at h ⊢
  exact ⟨h.1,by rcases h.2 with h | h <;> simp [h]⟩

private theorem narrowAbi_all_of_abi {ps : List Clif.AbiParam} (h : ps.all Scalar.abiEligible = true) :
    ps.all Scalar.narrowAbiEligible = true :=
  List.all_eq_true.mpr fun p hp => narrowAbi_of_abi (List.all_eq_true.mp h p hp)

/-- The scalar production syntax fixes one block that ends in `ret`, with ordinary integer
parameters and returns of at most 64 bits. -/
theorem productionEligible_shape {f : Clif.Function} (h : Scalar.productionEligible f = true) :
    ∃ b xs, f.blocks = [b] ∧ b.term = .ret xs ∧
      f.sig.params.all Scalar.narrowAbiEligible = true ∧
      f.sig.returns.all Scalar.narrowAbiEligible = true := by
  unfold Scalar.productionEligible at h
  simp only [Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · unfold Scalar.eligible at h
    split at h
    · rename_i b hb
      simp only [Bool.and_eq_true] at h
      obtain ⟨xs,hx⟩ := ret_of_match h.1.1.2
      exact ⟨b,xs,hb,hx,narrowAbi_all_of_abi h.1.2,narrowAbi_all_of_abi h.2⟩
    · cases h
  · unfold Scalar.narrowEligible at h
    split at h
    · rename_i b hb
      simp only [Bool.and_eq_true] at h
      obtain ⟨xs,hx⟩ := ret_of_match h.1.1.2
      exact ⟨b,xs,hb,hx,h.1.2,h.2⟩
    · cases h
  · unfold Scalar.maskEligible at h
    split at h
    · rename_i b hb
      simp only [Bool.and_eq_true] at h
      obtain ⟨xs,hx⟩ := ret_of_match h.1.1.2
      exact ⟨b,xs,hb,hx,h.1.2,h.2⟩
    · cases h

private theorem mapM_ok {α β : Type} {f : α → Except String β} {g : α → β} :
    ∀ {ps : List α}, (∀ p ∈ ps, f p = .ok (g p)) → ps.mapM f = .ok (ps.map g)
  | [], _ => rfl
  | p :: ps, h => by
    rw [List.mapM_cons,h p List.mem_cons_self,mapM_ok fun q hq => h q (List.mem_cons_of_mem _ hq)]
    rfl

private theorem sigArgs_ok {s : Clif.Signature} (h : s.params.all Scalar.narrowAbiEligible = true) :
    sigParamBytes s = .ok (s.params.map (·.ty.bytes)) := by
  unfold sigParamBytes sigArgs
  apply mapM_ok
  intro p hm
  have hp := List.all_eq_true.mp h p hm
  simp only [Scalar.narrowAbiEligible,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at hp
  obtain ⟨normal,ty⟩ := hp
  have notWide : (p.ty == .i128) = false := by
    rcases ty with ((h | h) | h) | h <;> simp [h]
  simp only [notWide,Bool.false_eq_true,ite_false,normal]
  rfl

/-- Every precheck of `Stock.lower` passes: AAPCS64 calling convention, parameter placement,
no `i128` return, no `sret` parameter, and at most eight returns. -/
theorem stock_prechecks {f : Clif.Function} (hdrv : driverInB f = true)
    (hp : f.sig.params.all Scalar.narrowAbiEligible = true)
    (hr : f.sig.returns.all Scalar.narrowAbiEligible = true) :
    aapcsConv f.sig.callConv = true ∧ (∃ bytes, sigParamBytes f.sig = .ok bytes) ∧
      f.sig.returns.any (·.ty == .i128) = false ∧ f.sig.params.any (·.purpose == .sret) = false ∧
      (retRegs (sigRets f.sig).length).isSome = true := by
  simp only [driverInB,Bool.and_eq_true,decide_eq_true_eq] at hdrv
  obtain ⟨⟨conv,eight⟩,-⟩ := hdrv
  refine ⟨conv,⟨_,sigArgs_ok hp⟩,?_,?_,?_⟩
  · rw [Bool.eq_false_iff]
    intro h
    obtain ⟨r,hm,hw⟩ := List.any_eq_true.mp h
    have hn := List.all_eq_true.mp hr r hm
    simp only [Scalar.narrowAbiEligible,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at hn
    simp only [beq_iff_eq] at hw
    rcases hn.2 with ((h | h) | h) | h <;> rw [h] at hw <;> cases hw
  · rw [Bool.eq_false_iff]
    intro h
    obtain ⟨q,hm,hs⟩ := List.any_eq_true.mp h
    have hn := List.all_eq_true.mp hp q hm
    simp only [Scalar.narrowAbiEligible,Bool.and_eq_true,beq_iff_eq] at hn hs
    rw [hn.1] at hs
    cases hs
  · have none : f.sig.params.find? (·.purpose == .sret) = none := by
      rw [List.find?_eq_none]
      intro q hm
      have hn := List.all_eq_true.mp hp q hm
      simp only [Scalar.narrowAbiEligible,Bool.and_eq_true,beq_iff_eq] at hn
      simp [hn.1]
    simp only [sigRets,none,retRegs,eight,ite_true,Option.isSome_some]

/-- `Stock.buildCtx` succeeds on the scalar production shape: the baseline context (`buildCtx_ok`)
passes the float check (`buildCtx_functionE_domain`), and a single `ret` block requests no
exception reservation. -/
theorem stock_buildCtx_ok {f : Clif.Function} (hE : Compile.functionE f = true)
    (hdom : dominatedB f = true) (hdrv : driverInB f = true)
    {b : Clif.Block} {xs : List Nat} (blocks : f.blocks = [b]) (ret : b.term = .ret xs) :
    ∃ result, Stock.buildCtx f = .ok result := by
  have hssa : (valueDefs f).Nodup := by
    simp only [dominatedB,Bool.and_eq_true] at hdom; exact nodupB_sound hdom.1
  simp only [driverInB,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at hdrv
  obtain ⟨ctx,ranges,st0,hb⟩ := buildCtx_ok hE hssa fun B hB s hs => (hdrv.2 B hB).1 s hs
  rw [buildCtx_functionE_domain hE hb]
  simp only [allocationRequests,blocks,List.zipIdx_cons,List.zipIdx_nil,List.mapM_cons,
    List.mapM_nil,blockAllocationRequests,exceptionReservation,ret,bind,Except.bind,pure,
    Except.pure]
  exact ⟨_,rfl⟩

private def preFixture : Clif.Function := {
  name := "scalar_complete_pre"
  sig := { params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩], returns := [⟨.i64,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0, .i64), (1, .i64)], body := [⟨[2], .binary .iadd .i64 0 1⟩], term := .ret [2] }] }

-- witness: native_decide (one fixed dominance check only)
private theorem preFixture_dominated : dominatedB preFixture = true := by native_decide

/-- Non-vacuity: a real scalar-class function satisfies every hypothesis of phase 1. -/
theorem stock_complete_pre_witness :
    Scalar.productionEligible preFixture = true ∧ driverInB preFixture = true ∧
      Compile.functionE preFixture = true ∧ dominatedB preFixture = true ∧
      (∃ bytes, sigParamBytes preFixture.sig = .ok bytes) ∧
      ∃ result, Stock.buildCtx preFixture = .ok result := by
  have eligible : Scalar.productionEligible preFixture = true := by decide +kernel
  have drv : driverInB preFixture = true := by decide +kernel
  have hE : Compile.functionE preFixture = true := by decide +kernel
  have dom := preFixture_dominated
  obtain ⟨b,xs,blocks,ret,hp,hr⟩ := productionEligible_shape eligible
  exact ⟨eligible,drv,hE,dom,(stock_prechecks drv hp hr).2.1,stock_buildCtx_ok hE dom drv blocks ret⟩
end Backend.Stock.Proof
