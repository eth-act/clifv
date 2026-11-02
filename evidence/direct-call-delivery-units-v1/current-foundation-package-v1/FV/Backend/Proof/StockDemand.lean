import FV.Backend.Proof.StockValues
import FV.Backend.Proof.LowerLemmas

/-!
Register requests used by returns, calls and their ABI helpers. List requests
preserve order and multiplicity: requesting a value twice increments its demand
twice, even though demanded-value availability only records membership.
-/

namespace Backend.Stock.Proof

open Backend.Proof Isle Isle.Aarch64

/-- Marking requests modifies only demand. Keeping the other state fields in one
equation also preserves colors, sunk definitions, aliases and emitted code. -/
theorem markList_state (st : State) (vs : List Nat) :
    vs.foldl State.mark st =
      { st with demand := vs.foldl (fun ds x => ds.modify x (· + 1)) st.demand } := by
  induction vs generalizing st with
  | nil => rfl
  | cons x xs ih => simpa only [List.foldl_cons, State.mark] using ih (st.mark x)

/-- Counts reflect every request, including duplicate source operands. The bound
is on the queried value; out-of-bounds requests to other values are harmless. -/
theorem markList_demand (st : State) (vs : List Nat) (x : Nat)
    (hx : x < st.demand.size) :
    (vs.foldl State.mark st).demand[x]! = st.demand[x]! + vs.count x := by
  induction vs generalizing st with
  | nil => simp
  | cons y ys ih =>
    rw [List.foldl_cons, ih (st.mark y) (by simpa only [State.mark, Array.size_modify] using hx)]
    by_cases he : y = x
    · subst y
      rw [(mark_demand st x hx).1, List.count_cons_self]
      omega
    · rw [mark_other st y x (Ne.symm he), List.count_cons_of_ne he]

theorem demanded_markList_iff (st : State) (vs : List Nat) (x : Nat)
    (hx : x < st.demand.size) :
    Demanded (vs.foldl State.mark st) x ↔ x ∈ vs ∨ Demanded st x := by
  rw [Demanded, markList_demand st vs x hx]
  by_cases hz : st.demand[x]! = 0
  · simp [Demanded, hz, List.count_eq_zero]
  · simp [Demanded, hz]

/-- The availability obligation for a list request is precisely the requested
values together with the values already demanded. -/
theorem ValuesHeld.markList {ctx : Ctx} {fr : Clif.Frame} {ρ : Nat → CV}
    {st : State} {vs : List Nat} (h : ValuesHeld (Demanded st) ctx fr ρ)
    (hbounds : ∀ x ∈ vs, x < st.demand.size)
    (havail : ∀ x ∈ vs, ValueHeld ctx fr ρ x) :
    ValuesHeld (Demanded (vs.foldl State.mark st)) ctx fr ρ := by
  induction vs generalizing st with
  | nil => exact h
  | cons x xs ih =>
    simp only [List.foldl_cons]
    apply ih (h.mark (hbounds x (by simp)) (havail x (by simp)))
    · intro y hy
      simpa only [State.mark, Array.size_modify] using hbounds y (by simp [hy])
    · intro y hy
      exact havail y (by simp [hy])

private theorem requestGuard_iff (ctx : Ctx) (st : State) (vs : List Nat) :
    vs.any (fun x => (ctx.defInst? x).any (fun i => st.sunk[i]!)) = false ↔
      ∀ x ∈ vs, DemandAllowed ctx st x := by
  simp only [List.any_eq_false, Bool.not_eq_true, Option.any_eq_false, DemandAllowed]

/-- The implicit-use helper has the same sunk-definition guard as explicit
register requests, without requiring a register mapping. -/
theorem stock_mark_value_used (ctx : Ctx) (st : State) (x : Nat)
    (hsafe : DemandAllowed ctx st x) :
    Stock.externCtor ctx T.mark_value_used [.value x] st = .ok (.op .unit, st.mark x) := by
  cases hd : ctx.defInst? x with
  | none => simp [Stock.externCtor, T.mark_value_used, hd]
  | some i => simp [Stock.externCtor, T.mark_value_used, hd, hsafe i hd]

private theorem vector_shape (ctx : Ctx) (st : State) (vs : List Nat) :
    Stock.externCtor ctx T.put_in_regs_vec [.values vs] st =
      if vs.any (fun x => (ctx.defInst? x).any (fun i => st.sunk[i]!)) then
        .unmodeled "demand for sunk instruction"
      else match vs.mapM ctx.valueReg? with
        | some rs => .ok (.regsVec (rs.map fun r => [r]), vs.foldl State.mark st)
        | none => .unmodeled "put_in_regs_vec" := by
  have hlegacy : Backend.externCtor ctx T.put_in_regs_vec [.values vs]
      (vs.foldl State.mark st).base =
      match vs.mapM ctx.valueReg? with
      | some rs => .ok (.regsVec (rs.map fun r => [r]), (vs.foldl State.mark st).base)
      | none => .unmodeled "put_in_regs_vec" := rfl
  have hdelegate : (match Backend.externCtor ctx T.put_in_regs_vec [.values vs]
      (vs.foldl State.mark st).base with
      | .ok (v, b) => .ok (v, { vs.foldl State.mark st with base := b })
      | .fail => .fail | .unmodeled e => .unmodeled e) =
      (match vs.mapM ctx.valueReg? with
      | some rs => .ok (.regsVec (rs.map fun r => [r]), vs.foldl State.mark st)
      | none => .unmodeled "put_in_regs_vec" : ExtResult (V × State)) := by
    rw [hlegacy]
    cases vs.mapM ctx.valueReg? <;> rfl
  simp only [T.put_in_regs_vec] at hdelegate
  change (if _ then _ else _) = _
  split
  · rfl
  · exact hdelegate

/-- Successful vector requests certify their guard, ordered register map, result
and complete final state. This is an equivalence over the actual stock helper. -/
theorem stock_put_in_regs_vec_iff (ctx : Ctx) (st : State) (vs : List Nat)
    (v : V) (st' : State) :
    Stock.externCtor ctx T.put_in_regs_vec [.values vs] st = .ok (v, st') ↔
      (∀ x ∈ vs, DemandAllowed ctx st x) ∧
      ∃ rs, vs.mapM ctx.valueReg? = some rs ∧
        v = .regsVec (rs.map fun r => [r]) ∧ st' = vs.foldl State.mark st := by
  rw [vector_shape, ← requestGuard_iff]
  cases hg : vs.any (fun x => (ctx.defInst? x).any (fun i => st.sunk[i]!)) <;>
    cases hm : vs.mapM ctx.valueReg? <;> simp [eq_comm]

theorem stock_put_in_regs_vec (ctx : Ctx) (st : State) (vs : List Nat) (rs : List Reg)
    (hsafe : ∀ x ∈ vs, DemandAllowed ctx st x)
    (hmap : vs.mapM ctx.valueReg? = some rs) :
    Stock.externCtor ctx T.put_in_regs_vec [.values vs] st =
      .ok (.regsVec (rs.map fun r => [r]), vs.foldl State.mark st) :=
  (stock_put_in_regs_vec_iff ctx st vs _ _).mpr ⟨hsafe, rs, hmap, rfl, rfl⟩

theorem stock_put_in_regs_vec_sunk (ctx : Ctx) (st : State) (vs : List Nat)
    (x i : Nat) (hx : x ∈ vs) (hd : ctx.defInst? x = some i) (hsunk : st.sunk[i]! = true) :
    Stock.externCtor ctx T.put_in_regs_vec [.values vs] st =
      .unmodeled "demand for sunk instruction" := by
  have hg : vs.any (fun x => (ctx.defInst? x).any (fun i => st.sunk[i]!)) = true := by
    apply List.any_eq_true.mpr
    exact ⟨x, hx, by simp [hd, hsunk]⟩
  rw [vector_shape, hg]
  rfl

theorem stock_put_in_regs_vec_unmapped (ctx : Ctx) (st : State) (vs : List Nat)
    (hsafe : ∀ x ∈ vs, DemandAllowed ctx st x) (hmap : vs.mapM ctx.valueReg? = none) :
    Stock.externCtor ctx T.put_in_regs_vec [.values vs] st =
      .unmodeled "put_in_regs_vec" := by
  rw [vector_shape, (requestGuard_iff ctx st vs).mpr hsafe, hmap]
  rfl

/-- Read an integer virtual register; materialized source values always use this
case. The other cases cannot occur in the availability proofs. -/
def registerView (ρ : Nat → CV) : Reg → CV
  | .vreg n .int => ρ n
  | _ => 0

private theorem mapM_regs_spec {ctx : Ctx} {vs : List Nat} {rs : List Reg}
    (hm : vs.mapM ctx.valueReg? = some rs) :
    vs.length = rs.length ∧
      ∀ (j : Nat) x r, vs[j]? = some x → rs[j]? = some r → ctx.valueReg? x = some r := by
  induction vs generalizing rs with
  | nil =>
    simp only [List.mapM_nil, pure] at hm
    cases hm
    exact ⟨rfl, by simp⟩
  | cons x xs ih =>
    cases hx : ctx.valueReg? x with
    | none => simp [List.mapM_cons, hx] at hm
    | some r =>
      cases ht : xs.mapM ctx.valueReg? with
      | none => simp [List.mapM_cons, hx, ht] at hm
      | some tail =>
        simp only [List.mapM_cons, hx, ht, pure] at hm
        cases hm
        obtain ⟨hl, hget⟩ := ih ht
        refine ⟨by simp [hl], ?_⟩
        intro j y s hy hs
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hy hs
          subst y s
          exact hx
        | succ j => exact hget j y s hy hs

/-- Source values read in list order are held by the corresponding mapped
registers. Repeated source operands retain their repeated entries. -/
theorem requested_values_hold {ctx : Ctx} {fr : Clif.Frame} {ρ : Nat → CV}
    {vs : List Nat} {vals : List Clif.Val} {rs : List Reg}
    (hheld : ValuesHeld (fun x => x ∈ vs) ctx fr ρ)
    (hvals : fr.getMany vs = .ok vals) (hmap : vs.mapM ctx.valueReg? = some rs) :
    AllHold vals (rs.map (registerView ρ)) := by
  obtain ⟨hvl, hvs⟩ := Backend.Proof.Driver.getMany_spec hvals
  obtain ⟨hrl, hrs⟩ := mapM_regs_spec hmap
  refine ⟨by simp only [List.length_map]; omega, ?_⟩
  intro j v a hv ha
  rw [List.getElem?_map] at ha
  cases hreg : rs[j]? with
  | none => simp [hreg] at ha
  | some r =>
    rw [hreg] at ha
    cases ha
    have hj : j < vs.length := by
      have h := (List.getElem?_eq_some_iff.mp hv).1
      omega
    have hx : vs[j]? = some vs[j] := List.getElem?_eq_getElem hj
    obtain ⟨v', hsource, hval⟩ := hvs j vs[j] hx
    have he := Option.some.inj (hval.symm.trans hv)
    subst v'
    obtain ⟨n, hn, hold⟩ := hheld vs[j] (List.getElem_mem hj) v hsource
    have hregmap := hrs j vs[j] r hx hreg
    have he := Option.some.inj (hregmap.symm.trans hn)
    subst r
    exact hold

/-- A successful helper's demanded set supplies all values read by its returned
register vector. This exposes the semantic obligation used by calls/returns
without reverting to a source-ID-indexed register file. -/
theorem stock_put_in_regs_vec_hold {ctx : Ctx} {st st' : State} {fr : Clif.Frame}
    {ρ : Nat → CV} {vs : List Nat} {vals : List Clif.Val} {rss : List (List Reg)}
    (hcall : Stock.externCtor ctx T.put_in_regs_vec [.values vs] st = .ok (.regsVec rss, st'))
    (hbounds : ∀ x ∈ vs, x < st.demand.size)
    (hheld : ValuesHeld (Demanded st') ctx fr ρ) (hvals : fr.getMany vs = .ok vals) :
    ∃ rs : List Reg, rss = rs.map (fun r => [r]) ∧ AllHold vals (rs.map (registerView ρ)) := by
  obtain ⟨_, rs, hm, ho, hs⟩ := (stock_put_in_regs_vec_iff ctx st vs _ st').mp hcall
  cases ho
  subst st'
  refine ⟨rs, rfl, requested_values_hold ?_ hvals hm⟩
  apply hheld.mono
  intro x hx
  exact (demanded_markList_iff st vs x (hbounds x hx)).mpr (Or.inl hx)

/-! Concrete witnesses include duplicate requests, an out-of-bounds mark, a
defined producer, sparse vreg numbers and rejection after that producer sinks. -/

private theorem request_safe : ∀ x ∈ [1, 0, 1], DemandAllowed sinkCtx sinkState x := by
  intro x hx i hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · change none = some i at hd; cases hd
  · change some 0 = some i at hd
    cases hd
    rfl
  · change none = some i at hd; cases hd

private def requestFrame : Clif.Frame := {
  func := sinkCtx.func
  regs := fun | 0 => some (.ofInt .i8 7) | 1 => some (.ofInt .i64 7) | _ => none
  slots := []
  body := []
  term := .ret [1, 0, 1] }

private theorem request_held : ValuesHeld (fun _ => True) sinkCtx requestFrame (fun _ => 7) := by
  intro x _ v hv
  cases x with
  | zero =>
    change some (Clif.Val.ofInt .i8 7) = some v at hv
    cases hv
    exact ⟨192, rfl, by unfold VHolds; decide⟩
  | succ x =>
    cases x with
    | zero =>
      change some (Clif.Val.ofInt .i64 7) = some v at hv
      cases hv
      exact ⟨193, rfl, by unfold VHolds; decide⟩
    | succ x => change none = some v at hv; cases hv

theorem markList_state_witness :
    [1, 99, 0, 1].foldl State.mark sinkState =
      { sinkState with demand := #[1, 2] } ∧
    ([1, 99, 0, 1].foldl State.mark sinkState).base = sinkState.base ∧
    ([1, 99, 0, 1].foldl State.mark sinkState).color = some 2 ∧
    ([1, 99, 0, 1].foldl State.mark sinkState).sunk = #[false] := by
  refine ⟨?_, rfl, rfl, rfl⟩
  rw [markList_state]
  rfl

theorem markList_demand_witness :
    ([1, 99, 0, 1].foldl State.mark sinkState).demand[1]! =
      sinkState.demand[1]! + ([1, 99, 0, 1] : List Nat).count 1 ∧
    ([1, 99, 0, 1].foldl State.mark sinkState).demand[1]! = 2 ∧
    ([1, 99, 0, 1].foldl State.mark sinkState).demand[0]! = 1 ∧
    ([1, 99, 0, 1].foldl State.mark sinkState).demand[99]! = 0 :=
  ⟨markList_demand sinkState _ 1 (by decide), rfl, rfl, rfl⟩

theorem demanded_markList_iff_witness :
    (Demanded ([1, 1].foldl State.mark (sinkState.mark 0)) 0 ↔
      0 ∈ ([1, 1] : List Nat) ∨ Demanded (sinkState.mark 0) 0) ∧
    Demanded ([1, 1].foldl State.mark (sinkState.mark 0)) 0 ∧
    Demanded ([1, 1].foldl State.mark (sinkState.mark 0)) 1 ∧
    ¬Demanded (sinkState.mark 0) 1 :=
  ⟨demanded_markList_iff (sinkState.mark 0) _ 0 (by decide),
    by unfold Demanded; decide, by unfold Demanded; decide, by unfold Demanded; decide⟩

theorem ValuesHeld.markList_witness :
    ValuesHeld (Demanded sinkState) sinkCtx requestFrame (fun _ => 7) ∧
    (∀ x ∈ [1, 0, 1], ValueHeld sinkCtx requestFrame (fun _ => 7) x) ∧
    ValuesHeld (Demanded ([1, 0, 1].foldl State.mark sinkState))
      sinkCtx requestFrame (fun _ => 7) := by
  have h := request_held.mono (fewer := Demanded sinkState) (fun _ _ => trivial)
  have ha := fun x (_ : x ∈ [1, 0, 1]) => request_held x trivial
  refine ⟨h, ha, h.markList ?_ ha⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> decide

theorem stock_mark_value_used_witness :
    DemandAllowed sinkCtx sinkState 0 ∧
    Stock.externCtor sinkCtx T.mark_value_used [.value 0] sinkState =
      .ok (.op .unit, sinkState.mark 0) ∧ (sinkState.mark 0).demand[0]! = 1 := by
  have hs := request_safe 0 (by simp)
  exact ⟨hs, stock_mark_value_used _ _ _ hs, rfl⟩

theorem stock_put_in_regs_vec_iff_witness :
    (Stock.externCtor sinkCtx T.put_in_regs_vec [.values [1, 0, 1]] sinkState =
      .ok (.regsVec [[.vreg 193 .int], [.vreg 192 .int], [.vreg 193 .int]],
        [1, 0, 1].foldl State.mark sinkState)) ∧
    (∀ x ∈ [1, 0, 1], DemandAllowed sinkCtx sinkState x) ∧
    [1, 0, 1].mapM sinkCtx.valueReg? = some [.vreg 193 .int, .vreg 192 .int, .vreg 193 .int] := by
  exact ⟨(stock_put_in_regs_vec_iff _ _ _ _ _).mpr ⟨request_safe, _, rfl, rfl, rfl⟩,
    request_safe, rfl⟩

theorem stock_put_in_regs_vec_witness :
    Stock.externCtor sinkCtx T.put_in_regs_vec [.values [1, 0, 1]] sinkState =
      .ok (.regsVec [[.vreg 193 .int], [.vreg 192 .int], [.vreg 193 .int]],
        [1, 0, 1].foldl State.mark sinkState) ∧
    ([1, 0, 1].foldl State.mark sinkState).demand = #[1, 2] :=
  ⟨stock_put_in_regs_vec _ _ _ _ request_safe rfl, rfl⟩

theorem stock_put_in_regs_vec_sunk_witness :
    sinkNext.sunk[0]! = true ∧
    Stock.externCtor sinkCtx T.put_in_regs_vec [.values [1, 0, 1]] sinkNext =
      .unmodeled "demand for sunk instruction" :=
  ⟨rfl, stock_put_in_regs_vec_sunk _ _ _ 0 0 (by simp) rfl rfl⟩

theorem stock_put_in_regs_vec_unmapped_witness :
    [1, 2].mapM sinkCtx.valueReg? = none ∧
    Stock.externCtor sinkCtx T.put_in_regs_vec [.values [1, 2]] sinkState =
      .unmodeled "put_in_regs_vec" := by
  refine ⟨rfl, stock_put_in_regs_vec_unmapped _ _ _ ?_ rfl⟩
  intro x hx i hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> change none = some i at hd <;> cases hd

theorem requested_values_hold_witness :
    requestFrame.getMany [1, 0, 1] =
      .ok [Clif.Val.ofInt .i64 7, .ofInt .i8 7, .ofInt .i64 7] ∧
    AllHold [Clif.Val.ofInt .i64 7, .ofInt .i8 7, .ofInt .i64 7]
      ([Reg.vreg 193 .int, .vreg 192 .int, .vreg 193 .int].map (registerView (fun _ => 7))) :=
  ⟨rfl, requested_values_hold (vs := [1, 0, 1]) (request_held.mono (fun _ _ => trivial)) rfl rfl⟩

theorem stock_put_in_regs_vec_hold_witness :
    Stock.externCtor sinkCtx T.put_in_regs_vec [.values [1, 0, 1]] sinkState =
      .ok (.regsVec [[.vreg 193 .int], [.vreg 192 .int], [.vreg 193 .int]],
        [1, 0, 1].foldl State.mark sinkState) ∧
    ∃ rs : List Reg,
      [[Reg.vreg 193 .int], [.vreg 192 .int], [.vreg 193 .int]] = rs.map (fun r => [r]) ∧
      AllHold [Clif.Val.ofInt .i64 7, .ofInt .i8 7, .ofInt .i64 7]
        (rs.map (registerView (fun _ => 7))) := by
  have hc := stock_put_in_regs_vec_witness.1
  refine ⟨hc, stock_put_in_regs_vec_hold hc ?_ ValuesHeld.markList_witness.2.2 rfl⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> decide

end Backend.Stock.Proof
