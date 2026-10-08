import FV.Backend.Proof.StockValues

/-! Invariants of the stock driver's actual dense initial allocation. -/

namespace Backend.Stock.Proof

def AllocationValid (a : Allocation) : Prop :=
  firstUserVreg ≤ a.base.nextVreg ∧
  (∀ (x : Nat) (r : Reg), (a.valReg[x]?).join = some r →
    ∃ n, r = Reg.vreg n .int ∧ firstUserVreg ≤ n ∧ n < a.base.nextVreg) ∧
  (∀ (x y : Nat) (r : Reg), (a.valReg[x]?).join = some r →
    (a.valReg[y]?).join = some r → x = y) ∧
  a.base.classes.size = a.base.nextVreg

private theorem initial_valid (values instructions : Nat) :
    AllocationValid (Allocation.initial values instructions) := by
  refine ⟨Nat.le_refl _, ?_, ?_, ?_⟩
  · intro x r h
    by_cases hx : x < values <;> simp [Allocation.initial, hx] at h
  · intro x y r h
    by_cases hx : x < values <;> simp [Allocation.initial, hx] at h
  · simp [Allocation.initial]

private theorem step_value_lookup (a : Allocation) (x y : Nat) :
    ((a.step (.value x)).valReg[y]?).join =
      if y = x then if x < a.valReg.size then some (.vreg a.base.nextVreg .int)
        else none else (a.valReg[y]?).join := by
  simp only [Allocation.step, LState.fresh, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds]
  by_cases he : y = x
  · subst y
    by_cases hx : x < a.valReg.size <;> simp [hx]
  · simp [he, Ne.symm he]

private theorem value_valid {a : Allocation} (h : AllocationValid a) (x : Nat) :
    AllocationValid (a.step (.value x)) := by
  rcases h with ⟨hstart, hrange, hinj, hsize⟩
  refine ⟨by simpa [Allocation.step, LState.fresh] using Nat.le_succ_of_le hstart, ?_, ?_, ?_⟩
  · intro y r hy
    rw [step_value_lookup] at hy
    by_cases he : y = x
    · subst y
      simp only [eq_self, ite_true] at hy
      split at hy
      · cases hy
        exact ⟨a.base.nextVreg, rfl, hstart, Nat.lt_succ_self _⟩
      · cases hy
    · rw [ite_eq_right he] at hy
      obtain ⟨n, rfl, hlo, hhi⟩ := hrange y r hy
      exact ⟨n, rfl, hlo, Nat.lt_succ_of_lt hhi⟩
  · intro y z r hy hz
    rw [step_value_lookup] at hy hz
    by_cases he : y = x
    · subst y
      simp only [eq_self, ite_true] at hy
      split at hy
      · cases hy
        by_cases hz' : z = x
        · exact hz'.symm
        · rw [ite_eq_right hz'] at hz
          obtain ⟨n, hn, _, hlt⟩ := hrange z _ hz
          cases hn
          exact False.elim (Nat.lt_irrefl _ hlt)
      · cases hy
    · rw [ite_eq_right he] at hy
      by_cases hz' : z = x
      · subst z
        simp only [eq_self, ite_true] at hz
        split at hz
        · cases hz
          obtain ⟨n, hn, _, hlt⟩ := hrange y _ hy
          cases hn
          exact False.elim (Nat.lt_irrefl _ hlt)
        · cases hz
      · rw [ite_eq_right hz'] at hz
        exact hinj y z r hy hz
  · simpa [Allocation.step, LState.fresh] using congrArg Nat.succ hsize

private theorem exception_valid {a : Allocation} (h : AllocationValid a)
    (i rets pays : Nat) : AllocationValid (a.step (.exception i rets pays)) := by
  rcases h with ⟨hstart, hrange, hinj, hsize⟩
  refine ⟨by dsimp [Allocation.step]; omega, ?_, hinj, ?_⟩
  · intro x r hx
    obtain ⟨n, rfl, hlo, hhi⟩ := hrange x r hx
    refine ⟨n, rfl, hlo, ?_⟩
    dsimp [Allocation.step]
    omega
  · simp only [Allocation.step, Array.size_append, Array.size_replicate, hsize]
    omega

theorem allocation_valid (values instructions : Nat) (requests : List AllocationRequest) :
    AllocationValid (allocateRequests values instructions requests) := by
  change AllocationValid (requests.foldl Allocation.step (Allocation.initial values instructions))
  apply List.foldlRecOn (motive := AllocationValid) requests Allocation.step
  · exact initial_valid values instructions
  · intro a h request _
    cases request with
    | value x => exact value_valid h x
    | exception i rets pays => exact exception_valid h i rets pays

private theorem fold_next (requests : List AllocationRequest) (a : Allocation) :
    (requests.foldl Allocation.step a).base.nextVreg =
      a.base.nextVreg + (requests.map AllocationRequest.count).sum := by
  induction requests generalizing a with
  | nil => simp
  | cons request rest ih =>
    rw [List.foldl_cons, ih]
    cases request <;> simp [Allocation.step, LState.fresh, AllocationRequest.count, Nat.add_assoc]

/-- All allocations, including separately reserved exception registers, consume
the exact contiguous register-number range beginning at 192. -/
theorem allocation_next (values instructions : Nat) (requests : List AllocationRequest) :
    (allocateRequests values instructions requests).base.nextVreg =
      firstUserVreg + (requests.map AllocationRequest.count).sum :=
  fold_next requests (Allocation.initial values instructions)

private theorem step_size (a : Allocation) (request : AllocationRequest) :
    (a.step request).valReg.size = a.valReg.size := by
  cases request <;> simp [Allocation.step]

private theorem step_domain (a : Allocation) (request : AllocationRequest) (x : Nat)
    (hx : x < a.valReg.size) :
    ((a.step request).valReg[x]?).join.isSome = true ↔
      (a.valReg[x]?).join.isSome = true ∨ request = .value x := by
  cases request with
  | value y =>
    rw [step_value_lookup]
    by_cases he : x = y
    · subst y
      simp [hx]
    · simp [he, Ne.symm he]
  | exception i rets pays => simp [Allocation.step]

private theorem fold_domain (requests : List AllocationRequest) (a : Allocation) (x : Nat)
    (hx : x < a.valReg.size) :
    ((requests.foldl Allocation.step a).valReg[x]?).join.isSome = true ↔
      (a.valReg[x]?).join.isSome = true ∨ AllocationRequest.value x ∈ requests := by
  induction requests generalizing a with
  | nil => simp
  | cons request rest ih =>
    rw [List.foldl_cons, ih (a.step request) (by simpa only [step_size] using hx),
      step_domain a request x hx]
    simp only [List.mem_cons, eq_comm, or_assoc]

/-- Every in-bounds source value is mapped exactly when layout allocation
requests it. Exception reservations never invent a source-value mapping. -/
theorem allocation_domain (values instructions : Nat) (requests : List AllocationRequest)
    (x : Nat) (hx : x < values) :
    ((allocateRequests values instructions requests).valReg[x]?).join.isSome = true ↔
      AllocationRequest.value x ∈ requests := by
  have h := fold_domain requests (Allocation.initial values instructions) x
    (by simpa [Allocation.initial] using hx)
  simpa [allocateRequests, Allocation.initial, hx] using h

private theorem block_requests_values {f : Clif.Function} {ranges : Array (Nat × Nat)}
    {b : Clif.Block} {bi : Nat} {requests : List AllocationRequest}
    (hb : blockAllocationRequests f ranges b bi = .ok requests) :
    requests.filterMap AllocationRequest.value? = blockValues b := by
  cases he : exceptionReservation f ranges bi b.term with
  | error e => simp [blockAllocationRequests, he, bind, Except.bind] at hb
  | ok extra =>
    simp [blockAllocationRequests, he, bind, Except.bind] at hb
    subst requests
    cases extra <;>
      simp [AllocationRequest.value?, blockValues, List.filterMap_flatMap, List.filterMap_map,
        Function.comp_def, List.filterMap_cons]

private theorem mapM_projection {α β γ : Type} (fn : α → Except String β)
    (project : β → γ) (reference : α → γ)
    (hproject : ∀ a b, fn a = .ok b → project b = reference a) :
    ∀ (xs : List α) (ys : List β), xs.mapM fn = .ok ys → ys.map project = xs.map reference := by
  intro xs
  induction xs with
  | nil => intro ys h; simp at h; subst ys; rfl
  | cons a rest ih =>
    intro ys h
    rw [List.mapM_cons] at h
    cases ha : fn a with
    | error e => simp [ha, bind, Except.bind] at h
    | ok b =>
      cases hr : rest.mapM fn with
      | error e => simp [ha, hr, bind, Except.bind] at h
      | ok bs =>
        simp [ha, hr, bind, Except.bind] at h
        subst ys
        simp only [List.map_cons, hproject a b ha, ih bs hr]

/-- The request stream covers exactly the source parameters and statement
results, in layout order; exception reservations contribute no source IDs. -/
theorem allocationRequests_values {f : Clif.Function} {ranges : Array (Nat × Nat)}
    {requests : List AllocationRequest} (hb : allocationRequests f ranges = .ok requests) :
    requests.filterMap AllocationRequest.value? = f.blocks.flatMap blockValues := by
  cases hc : f.blocks.zipIdx.mapM (fun (b, bi) => blockAllocationRequests f ranges b bi) with
  | error e => simp [allocationRequests, hc, bind, Except.bind] at hb
  | ok chunks =>
    have he : chunks.flatten = requests := by simpa [allocationRequests, hc] using hb
    rw [← he, List.filterMap_flatten]
    have hm := mapM_projection
      (fun (p : Clif.Block × Nat) => blockAllocationRequests f ranges p.1 p.2)
      (List.filterMap AllocationRequest.value?) (fun p => blockValues p.1)
      (fun p qs h => block_requests_values h) f.blocks.zipIdx chunks hc
    rw [hm]
    change (List.map (blockValues ∘ Prod.fst) f.blocks.zipIdx).flatten =
      (List.map blockValues f.blocks).flatten
    rw [← List.map_map, List.zipIdx_map_fst]

private theorem mem_value_filterMap (requests : List AllocationRequest) (x : Nat) :
    AllocationRequest.value x ∈ requests ↔ x ∈ requests.filterMap AllocationRequest.value? := by
  rw [List.mem_filterMap]
  constructor
  · intro h
    exact ⟨.value x, h, rfl⟩
  · rintro ⟨q, hq, he⟩
    cases q with
    | value y => cases he; exact hq
    | exception i rets pays => cases he

def CtxAllocated (ctx : Ctx) (st : State) : Prop :=
  ValueRegsBelow ctx st.base.nextVreg ∧ ValueMapInjective ctx ∧
  (∀ (x : Nat) (r : Reg), ctx.valueReg? x = some r →
    ∃ n, r = .vreg n .int ∧ firstUserVreg ≤ n) ∧
  firstUserVreg ≤ st.base.nextVreg ∧ st.base.classes.size = st.base.nextVreg

private theorem finish_allocated (ctx : Ctx) (ranges : Array (Nat × Nat))
    (a : Allocation) (ha : AllocationValid a) :
    CtxAllocated (finishCtx ctx ranges a).1 (finishCtx ctx ranges a).2.2 := by
  rcases ha with ⟨hstart, hrange, hinj, hsize⟩
  refine ⟨?_, ?_, ?_, hstart, hsize⟩
  · intro x n hx
    obtain ⟨m, hm, _, hhi⟩ := hrange x (.vreg n .int) hx
    cases hm
    exact hhi
  · intro x y n hx hy
    exact hinj x y (.vreg n .int) hx hy
  · intro x r hx
    obtain ⟨n, hn, hlo, _⟩ := hrange x r hx
    exact ⟨n, hn, hlo⟩

/-- A successful stock context is the original DFG context with its register
map replaced by this exact layout allocation. Source data and ranges are kept. -/
theorem buildCtx_allocation {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {st : State}
    (hb : Stock.buildCtx f = .ok (ctx, ranges, st)) :
    ∃ original st0 requests,
      Backend.buildCtx f = .ok (original, ranges, st0) ∧
      allocationRequests f ranges = .ok requests ∧
      (ctx, ranges, st) = finishCtx original ranges
        (allocateRequests original.valTy.size original.insts.size requests) := by
  cases hold : Backend.buildCtx f with
  | error e => simp [Stock.buildCtx, hold, bind, Except.bind] at hb
  | ok q =>
    obtain ⟨original, ranges0, st0⟩ := q
    cases hreq : allocationRequests f ranges0 with
    | error e => simp [Stock.buildCtx, hold, hreq, bind, Except.bind] at hb
    | ok requests =>
      have he : finishCtx original ranges0
          (allocateRequests original.valTy.size original.insts.size requests) =
          (ctx, ranges, st) := by
        simpa [Stock.buildCtx, hold, hreq] using hb
      have hrg : ranges0 = ranges := congrArg (fun q => q.2.1) he
      subst ranges0
      exact ⟨original, st0, requests, rfl, hreq, he.symm⟩

/-- Every initial value register returned by the driver is virtual, outside
stock's physical placeholders, below the first temporary, and unique. -/
theorem buildCtx_allocated {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {st : State}
    (hb : Stock.buildCtx f = .ok (ctx, ranges, st)) : CtxAllocated ctx st := by
  obtain ⟨original, _, requests, _, _, he⟩ := buildCtx_allocation hb
  have hf := finish_allocated original ranges
    (allocateRequests original.valTy.size original.insts.size requests)
    (allocation_valid _ _ _)
  have hc := congrArg (fun q => q.1) he
  have hs := congrArg (fun q => q.2.2) he
  rw [← hc, ← hs] at hf
  exact hf

/-- Requests are indexed by source IDs, so the initial demand table has one
entry for every source value, including holes in sparse source numbering. -/
theorem buildCtx_demand_size {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {st : State}
    (hb : Stock.buildCtx f = .ok (ctx, ranges, st)) :
    st.demand.size = ctx.valTy.size := by
  obtain ⟨original, _, requests, _, _, he⟩ := buildCtx_allocation hb
  have hsize : ∀ (rs : List AllocationRequest) (a : Allocation),
      (rs.foldl Allocation.step a).valReg.size = a.valReg.size := by
    intro rs
    induction rs with
    | nil => intro a; rfl
    | cons r rs ih => intro a; rw [List.foldl_cons, ih, step_size]
  have hs := congrArg (fun q => q.2.2.demand.size) he
  have hc := congrArg (fun q => q.1.valTy.size) he
  rw [hs, hc]
  simpa only [finishCtx, Array.size_replicate, allocateRequests,
    Allocation.initial] using hsize requests (Allocation.initial original.valTy.size original.insts.size)

/-- Within the validated source value table, the driver's map covers exactly
the declared parameters/results. Sparse source IDs need no identity mapping. -/
theorem buildCtx_value_domain {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {st : State}
    (hb : Stock.buildCtx f = .ok (ctx, ranges, st)) (x : Nat) (hx : x < ctx.valTy.size) :
    (ctx.valueReg? x).isSome = true ↔ x ∈ f.blocks.flatMap blockValues := by
  obtain ⟨original, _, requests, _, hreq, he⟩ := buildCtx_allocation hb
  have hc := congrArg (fun q => q.1) he
  dsimp only at hc
  rw [hc] at hx ⊢
  change x < original.valTy.size at hx
  change ((allocateRequests original.valTy.size original.insts.size requests).valReg[x]?).join.isSome =
    true ↔ x ∈ f.blocks.flatMap blockValues
  rw [allocation_domain original.valTy.size original.insts.size requests x hx,
    ← allocationRequests_values hreq]
  exact mem_value_filterMap requests x

private def requests : List AllocationRequest :=
  [.value 7, .exception 1 2 1, .value 2, .value 7, .value 50]

private def allocation : Allocation := allocateRequests 8 2 requests

theorem allocation_valid_witness :
    AllocationValid allocation ∧
    (allocation.valReg[7]?).join = some (.vreg 197 .int) ∧
    (allocation.valReg[2]?).join = some (.vreg 196 .int) ∧
    allocation.tryRegs[1]! =
      ([.vreg 193 .int, .vreg 194 .int], [.vreg 195 .int]) ∧
    allocation.base.nextVreg = 199 :=
  ⟨allocation_valid _ _ _, rfl, rfl, rfl, rfl⟩

theorem allocation_next_witness :
    allocation.base.nextVreg = firstUserVreg + (requests.map AllocationRequest.count).sum ∧
    (requests.map AllocationRequest.count).sum = 7 :=
  ⟨allocation_next _ _ _, rfl⟩

theorem allocation_domain_witness :
    ((allocation.valReg[7]?).join.isSome = true ↔ AllocationRequest.value 7 ∈ requests) ∧
    (allocation.valReg[7]?).join.isSome = true ∧
    (allocation.valReg[1]?).join = none :=
  ⟨allocation_domain 8 2 requests 7 (by decide), rfl, rfl⟩

private def fixture : Clif.Function := {
  name := "dense_context"
  sig := { params := [⟨.i64, .none, .normal⟩], returns := [⟨.i64, .none, .normal⟩] }
  blocks := [
    { id := 7, params := [(7, .i64)], term := .jump ⟨9, [7]⟩ },
    { id := 9, params := [(2, .i64)], term := .ret [2] }] }

private def fixtureResult : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx fixture).toOption.getD (sinkCtx, #[], sinkState)

private theorem fixture_build : Stock.buildCtx fixture = .ok fixtureResult := rfl

theorem allocationRequests_values_witness :
    allocationRequests fixture fixtureResult.2.1 = .ok [.value 7, .value 2] ∧
    ([AllocationRequest.value 7, .value 2].filterMap AllocationRequest.value? =
      fixture.blocks.flatMap blockValues) ∧
    fixture.blocks.flatMap blockValues = [7, 2] :=
  ⟨rfl, allocationRequests_values (show allocationRequests fixture fixtureResult.2.1 =
    .ok [.value 7, .value 2] from rfl), rfl⟩

theorem buildCtx_allocation_witness :
    Stock.buildCtx fixture = .ok fixtureResult ∧
    (∃ original st0 requests,
      Backend.buildCtx fixture = .ok (original, fixtureResult.2.1, st0) ∧
      allocationRequests fixture fixtureResult.2.1 = .ok requests ∧
      fixtureResult = finishCtx original fixtureResult.2.1
        (allocateRequests original.valTy.size original.insts.size requests)) ∧
    fixtureResult.1.valueReg? 7 = some (.vreg 192 .int) ∧
    fixtureResult.1.valueReg? 2 = some (.vreg 193 .int) :=
  ⟨fixture_build, buildCtx_allocation fixture_build, rfl, rfl⟩

theorem buildCtx_allocated_witness :
    Stock.buildCtx fixture = .ok fixtureResult ∧
    CtxAllocated fixtureResult.1 fixtureResult.2.2 ∧
    fixtureResult.2.2.base.nextVreg = 194 ∧
    fixtureResult.1.valueReg? 0 = none :=
  ⟨fixture_build, buildCtx_allocated fixture_build, rfl, rfl⟩

theorem buildCtx_demand_size_witness :
    Stock.buildCtx fixture = .ok fixtureResult ∧
    fixtureResult.2.2.demand.size = fixtureResult.1.valTy.size ∧
    fixtureResult.2.2.demand.size = 8 :=
  ⟨fixture_build, buildCtx_demand_size fixture_build, rfl⟩

theorem buildCtx_value_domain_witness :
    ((fixtureResult.1.valueReg? 2).isSome = true ↔
      2 ∈ fixture.blocks.flatMap blockValues) ∧
    fixtureResult.1.valueReg? 2 = some (.vreg 193 .int) ∧
    fixtureResult.1.valueReg? 0 = none :=
  ⟨buildCtx_value_domain fixture_build 2 (by decide), rfl, rfl⟩

end Backend.Stock.Proof
