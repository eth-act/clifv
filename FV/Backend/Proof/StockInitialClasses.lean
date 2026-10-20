import FV.Backend.Proof.StockAliasBounds
import FV.Backend.Proof.SpillClsChain

namespace Backend.Stock.Proof.InitialClassesDraft
open Backend.Proof Backend.Proof.Spill Isle Isle.Aarch64
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- Every real initial allocation slot, including exception reservations and
physical placeholders, has its actual recorded integer class. -/
theorem stock_allocate_classes (values instructions : Nat) (requests : List AllocationRequest) :
    (allocateRequests values instructions requests).base.classes =
      Array.replicate (allocateRequests values instructions requests).base.nextVreg .int := by
  unfold allocateRequests
  apply List.foldlRecOn (motive := fun a : Allocation =>
    a.base.classes = Array.replicate a.base.nextVreg .int) requests Allocation.step
  · rfl
  · intro a consistent request _
    cases request with
    | value x =>
      simp only [Allocation.step,LState.fresh]
      rw [consistent,Array.replicate_succ]
    | exception i rets pays =>
      simp only [Allocation.step]
      rw [consistent,Array.replicate_append_replicate]
      simp only [Nat.add_assoc]

/-- The successful source-context build supplies initial class consistency for
mapped source registers and every reserved return/payload register internally. -/
theorem stock_build_classes {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {st : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,st)) :
    Sz st.base ∧
    (∀ x r,ctx.valueReg? x = some r → RegCls st.base.classes r) ∧
    (∀ (i : Nat) (rs : List Reg × List Reg),st.tryRegs[i]? = some rs → ∀ r ∈ rs.1 ++ rs.2,RegCls st.base.classes r) := by
  obtain ⟨original,old,requests,_,_,same⟩ := buildCtx_allocation build
  have state := congrArg (fun q : Ctx × Array (Nat × Nat) × State => q.2.2) same
  change st = _ at state
  have classes : st.base.classes = Array.replicate st.base.nextVreg .int := by
    rw [state]
    exact stock_allocate_classes original.valTy.size original.insts.size requests
  have allocated := buildCtx_allocated build
  refine ⟨allocated.2.2.2.2,?_,?_⟩
  · intro x r mapped
    obtain ⟨n,shape,_⟩ := allocated.2.2.1 x r mapped
    subst r
    have below := allocated.1 x n mapped
    rw [regCls_vreg,classes]
    simp only [Array.getElem?_replicate,below,↓reduceIte]
  · intro i rs slot r member
    obtain ⟨n,shape,below⟩ := buildCtx_reservedBelow build i rs slot r member
    subst r
    rw [regCls_vreg,classes]
    simp only [Array.getElem?_replicate,below,↓reduceIte]

/-- Overwritten and out-of-range reservations do not weaken the allocation
invariant; the witness also contains real source and reserved registers. -/
theorem stock_allocate_classes_witness :
    let a := allocateRequests 2 1 [.value 0,.exception 0 1 2,.exception 0 2 1,.value 1]
    a.valReg[0]? = some (some (.vreg 192 .int)) ∧
    a.tryRegs[0]? = some ([.vreg 196 .int,.vreg 197 .int],[.vreg 198 .int]) ∧
    a.valReg[1]? = some (some (.vreg 199 .int)) ∧ a.base.nextVreg = 200 ∧
    a.base.classes = Array.replicate a.base.nextVreg .int :=
  ⟨rfl,rfl,rfl,rfl,stock_allocate_classes _ _ _⟩

/-- Actual successful source-context construction inhabits all initial class
premises; the reservation witness separately exercises nonempty payloads. -/
theorem stock_build_classes_witness :
    ∃ f ctx ranges st,Stock.buildCtx f = .ok (ctx,ranges,st) ∧
      Sz st.base ∧ (∀ x r,ctx.valueReg? x = some r → RegCls st.base.classes r) ∧
      (∀ (i : Nat) (rs : List Reg × List Reg),st.tryRegs[i]? = some rs → ∀ r ∈ rs.1 ++ rs.2,RegCls st.base.classes r) := by
  obtain ⟨build,_,_,_⟩ := buildCtx_allocated_witness
  exact ⟨_,_,_,_,build,stock_build_classes build⟩

end Backend.Stock.Proof.InitialClassesDraft
