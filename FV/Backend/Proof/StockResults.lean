import FV.Backend.Proof.StockValues
import FV.Backend.Proof.IselFamAluBIconst
import FV.Backend.Proof.IselLcf
import FV.Backend.Proof.LowerAlias

/-!
Result binding for the stock scan. Virtual results update the actual alias array
without copies; value availability reads source mappings through a fixed final
renaming. This does not yet establish the final renaming for a whole function.
-/

namespace Backend.Stock.Proof

open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 4096

theorem setAlias_virtual (st : State) (n d : Nat) (c : RegClass) :
    st.setAlias (.vreg n c) (.vreg d c) =
      .ok { st with alias := aliasStep st.alias (n, d) } := by
  simp [State.setAlias, aliasStep]

theorem setAlias_virtual_get (st : State) (n d : Nat) :
    ∃ next, st.setAlias (.vreg n .int) (.vreg d .int) = .ok next ∧
      next.base = st.base ∧ next.demand = st.demand ∧ next.sunk = st.sunk ∧
      (∀ k, (next.alias[k]?).join = if k = n then some d else (st.alias[k]?).join) ∧
      st.alias.size ≤ next.alias.size ∧ n < next.alias.size := by
  refine ⟨_, setAlias_virtual st n d .int, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · exact aliasStep_get st.alias (n, d)
  · exact (aliasStep_size st.alias (n, d)).1
  · exact (aliasStep_size st.alias (n, d)).2

/-- The driver's actual alias chase reaches a fresh result and leaves that
result fixed. This discharges the result equation for a single fresh binding. -/
theorem resolve_bound_fresh {st next : State} {n d : Nat} {c : RegClass}
    (hb : st.setAlias (.vreg n c) (.vreg d c) = .ok next)
    (hnd : n < d) (hsize : st.alias.size ≤ d) :
    Backend.lowerFunction.resolve next.alias (next.alias.size + 1) (.vreg n c) = .vreg d c ∧
    ∀ fuel, Backend.lowerFunction.resolve next.alias fuel (.vreg d c) = .vreg d c := by
  rw [setAlias_virtual] at hb
  cases hb
  let a := aliasStep st.alias (n, d)
  have hn : (a[n]?).join = some d := by
    exact (aliasStep_get st.alias (n, d) n).trans (by simp)
  have hd : (a[d]?).join = none := by
    rw [aliasStep_get]
    simp only [Nat.ne_of_gt hnd, ite_false, Array.getElem?_eq_none hsize, Option.join_none]
  have terminal (fuel : Nat) : Backend.lowerFunction.resolve a fuel (.vreg d c) = .vreg d c := by
    cases fuel <;> simp only [Backend.lowerFunction.resolve, hd]
  refine ⟨?_, terminal⟩
  have hs := (aliasStep_size st.alias (n, d)).2
  obtain ⟨k, hk⟩ : ∃ k, a.size + 1 = k + 2 := ⟨a.size - 1, by dsimp only [a]; omega⟩
  change Backend.lowerFunction.resolve a (a.size + 1) (.vreg n c) = .vreg d c
  rw [hk]
  simp only [Backend.lowerFunction.resolve, hn, hd]

/-- Ordered virtual bindings, including repeated destinations, agree exactly
with the driver's alias fold and leave every other state field unchanged. -/
theorem bindResults_virtual (ctx : Ctx) (st : State) (xs : List (Nat × Nat × Nat))
    (hm : ∀ p ∈ xs, ctx.valueReg? p.1 = some (.vreg p.2.1 .int)) :
    bindResults ctx (xs.map fun p => (p.1, [.vreg p.2.2 .int])) st =
      .ok ({ st with alias := (xs.map (·.2)).foldl aliasStep st.alias }, #[]) := by
  have aux : ∀ (xs : List (Nat × Nat × Nat)) (st : State) (extra : Array MInst),
      (∀ p ∈ xs, ctx.valueReg? p.1 = some (.vreg p.2.1 .int)) →
      (xs.map fun p => (p.1, [Reg.vreg p.2.2 .int])).foldlM
        (fun (s : State × Array MInst) (pair : Nat × List Reg) => do
          let (st, extra) := s
          let (v, rs) := pair
          let some vr := ctx.valueReg? v | throw s!"unknown value v{v}"
          match rs with
          | [r@(.vreg ..)] => pure (← st.setAlias vr r, extra)
          | [r] => pure (st, extra.push (.mov .size64 vr r))
          | _ => throw "multi-register result") (st, extra) =
        (Except.ok ({ st with alias := (xs.map (·.2)).foldl aliasStep st.alias }, extra) :
          Except String (State × Array MInst)) := by
    intro xs
    induction xs with
    | nil => intro st extra _; rfl
    | cons p ps ih =>
      intro st extra hm
      rw [List.map_cons, List.foldlM_cons]
      simp only [hm p (List.mem_cons_self ..)]
      simp only [setAlias_virtual, bind, Except.bind, pure, Except.pure]
      exact ih { st with alias := aliasStep st.alias p.2 } extra
        (fun q hq => hm q (List.mem_cons_of_mem _ hq))
  exact aux xs st #[] hm

theorem bindResults_physical (ctx : Ctx) (st : State) (x : Nat) (vr r : Reg)
    (hm : ctx.valueReg? x = some vr) (hp : r.isVirtual = false) :
    bindResults ctx [(x, [r])] st = .ok (st, #[.mov .size64 vr r]) := by
  cases r <;> simp [Reg.isVirtual] at hp <;> simp [bindResults, hm, List.foldlM]

theorem bindResults_reject_multi (ctx : Ctx) (st : State) (x : Nat) (vr : Reg)
    (rs : List Reg) (hm : ctx.valueReg? x = some vr) (hlen : rs.length ≠ 1) :
    bindResults ctx [(x, rs)] st = .error "multi-register result" := by
  cases rs with
  | nil => simp [bindResults, hm, List.foldlM]; rfl
  | cons r rs =>
    cases rs with
    | nil => exact False.elim (hlen rfl)
    | cons r' rs => simp [bindResults, hm, List.foldlM]; rfl

/-- A fresh selected-code result becomes available at its mapped source value
through the final alias renaming. Other defined, demanded values are preserved
when their resolved registers lie below the fresh definition range. -/
theorem ValuesHeld.resolvedResult {needed : Nat → Prop} {ctx : Ctx} {fr : Clif.Frame}
    {ρ ρ' : Nat → CV} {gn : Nat → Nat} {x n d limit : Nat} {v : Clif.Val}
    {ms : List MInst} {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (h : ValuesHeld needed ctx fr (fun k => ρ (gn k)))
    (hmap : ctx.valueReg? x = some (.vreg n .int)) (hresult : gn n = d)
    (hvalue : VHolds v (ρ' d))
    (hbelow : ∀ y m, needed y → y ≠ x → ctx.valueReg? y = some (.vreg m .int) →
      (fr.regs y).isSome = true → gn m < limit)
    (hdefs : ∀ mi ∈ ms, ∀ e ∈ vdefs mi, limit ≤ e)
    (hrun : PRun F isem ms ρ ρ') :
    ValuesHeld needed ctx (withValue fr x v) (fun k => ρ' (gn k)) := by
  intro y hy value hv
  by_cases he : y = x
  · subst y
    simp only [withValue, eq_self, ite_true] at hv
    cases hv
    exact ⟨n, hmap, by change VHolds v (ρ' (gn n)); rw [hresult]; exact hvalue⟩
  · simp only [withValue, ite_eq_right he] at hv
    obtain ⟨m, hm, hold⟩ := h y hy value hv
    have hb := hbelow y m hy he hm (by rw [hv]; rfl)
    obtain ⟨w', hr, _⟩ := hrun Arm.ArmState.default
    have keep := seqRun_fall_frame
      (n := gn m) (fun mi hmi hmem => Nat.not_le_of_lt hb (hdefs mi hmi _ hmem)) hr
    exact ⟨m, hm, by change VHolds value (ρ' (gn m)); rw [keep]; exact hold⟩

private def aliasInput : State :=
  { sinkState with alias := aliasStep #[] (191, 193), demand := #[1, 1] }

private def virtualBindings : List (Nat × Nat × Nat) :=
  [(0, 192, 194), (1, 193, 195), (0, 192, 196)]

private def aliasOutput : State :=
  { aliasInput with alias := (virtualBindings.map (·.2)).foldl aliasStep aliasInput.alias }

private theorem bindings_mapped :
    ∀ p ∈ virtualBindings, sinkCtx.valueReg? p.1 = some (.vreg p.2.1 .int) := by
  intro p hp
  simp only [virtualBindings, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> rfl

theorem setAlias_virtual_witness :
    aliasInput.setAlias (.vreg 192 .int) (.vreg 194 .int) =
      .ok { aliasInput with alias := aliasStep aliasInput.alias (192, 194) } ∧
    ((aliasStep aliasInput.alias (192, 194))[192]?).join = some 194 ∧
    ((aliasStep aliasInput.alias (192, 194))[191]?).join = some 193 :=
  ⟨setAlias_virtual _ _ _ _, rfl, rfl⟩

theorem setAlias_virtual_get_witness :
    ∃ next, aliasInput.setAlias (.vreg 192 .int) (.vreg 194 .int) = .ok next ∧
      next.base = aliasInput.base ∧ next.demand = #[1, 1] ∧ next.sunk = aliasInput.sunk ∧
      (∀ k, (next.alias[k]?).join = if k = 192 then some 194 else (aliasInput.alias[k]?).join) ∧
      aliasInput.alias.size ≤ next.alias.size ∧ 192 < next.alias.size :=
  setAlias_virtual_get aliasInput 192 194

theorem resolve_bound_fresh_witness :
    ∃ next, aliasInput.setAlias (.vreg 192 .int) (.vreg 194 .int) = .ok next ∧
      Backend.lowerFunction.resolve next.alias (next.alias.size + 1) (.vreg 192 .int) =
        .vreg 194 .int ∧
      (∀ fuel, Backend.lowerFunction.resolve next.alias fuel (.vreg 194 .int) = .vreg 194 .int) ∧
      (next.alias[191]?).join = some 193 := by
  have hb := setAlias_virtual aliasInput 192 194 .int
  have hr := resolve_bound_fresh hb (by decide) (by decide)
  exact ⟨_, hb, hr.1, hr.2, rfl⟩

theorem bindResults_virtual_witness :
    (∀ p ∈ virtualBindings, sinkCtx.valueReg? p.1 = some (.vreg p.2.1 .int)) ∧
    bindResults sinkCtx [(0, [.vreg 194 .int]), (1, [.vreg 195 .int]), (0, [.vreg 196 .int])]
      aliasInput = .ok (aliasOutput, #[]) ∧
    (aliasOutput.alias[192]?).join = some 196 ∧
    (aliasOutput.alias[193]?).join = some 195 ∧
    (aliasOutput.alias[191]?).join = some 193 ∧
    aliasOutput.base = aliasInput.base ∧ aliasOutput.demand = #[1, 1] :=
  ⟨bindings_mapped, bindResults_virtual _ _ _ bindings_mapped, rfl, rfl, rfl, rfl, rfl⟩

theorem bindResults_physical_witness :
    sinkCtx.valueReg? 0 = some (.vreg 192 .int) ∧
    bindResults sinkCtx [(0, [.x 0])] aliasInput =
      .ok (aliasInput, #[.mov .size64 (.vreg 192 .int) (.x 0)]) :=
  ⟨rfl, bindResults_physical _ _ _ _ _ rfl rfl⟩

theorem bindResults_reject_multi_witness :
    bindResults sinkCtx [(0, [])] aliasInput = .error "multi-register result" ∧
    bindResults sinkCtx [(0, [.vreg 194 .int, .vreg 195 .int])] aliasInput =
      .error "multi-register result" :=
  ⟨bindResults_reject_multi _ _ _ _ _ rfl (by decide),
    bindResults_reject_multi _ _ _ _ _ rfl (by decide)⟩

private def pendingFrame : Clif.Frame := {
  func := sinkCtx.func
  regs := fun x => if x = 1 then some (.ofInt .i64 11) else none
  slots := [], body := [], term := .ret [0] }

private def incomingRF (n : Nat) : CV := if n = 193 then 11 else 0

private def resultRename (n : Nat) : Nat := if n = 192 then 194 else n

private theorem pendingHeld :
    ValuesHeld (Demanded aliasInput) sinkCtx pendingFrame (fun k => incomingRF (resultRename k)) := by
  intro x _ v hv
  by_cases he : x = 1
  · subst x
    change some (Clif.Val.ofInt .i64 11) = some v at hv
    cases hv
    exact ⟨193, rfl, by unfold VHolds; decide⟩
  · simp [pendingFrame, he] at hv

private theorem pendingBelow :
    ∀ y m, Demanded aliasInput y → y ≠ 0 → sinkCtx.valueReg? y = some (.vreg m .int) →
      (pendingFrame.regs y).isSome = true → resultRename m < 194 := by
  intro y m _ _ hm hv
  have hy : y = 1 := by
    apply Classical.byContradiction
    intro hne
    simp [pendingFrame, hne] at hv
  subst y
  change some (Reg.vreg 193 .int) = some (Reg.vreg m .int) at hm
  cases hm
  decide

private theorem selfRefines : Refines (fun _ => True) ispec :=
  fun _ _ _ _ w' _ h => ⟨w', h, SameWorld.refl _ _⟩

theorem ValuesHeld.resolvedResult_witness :
    ∃ ms ρ',
      PRun (fun _ => True) ispec ms incomingRF ρ' ∧
      (∀ mi ∈ ms, ∀ e ∈ vdefs mi, 194 ≤ e) ∧
      ValuesHeld (Demanded aliasInput) sinkCtx
        (withValue pendingFrame 0 (.ofInt .i8 9)) (fun k => ρ' (resultRename k)) ∧
      VHolds (Clif.Val.ofInt .i8 9) (ρ' 194) ∧ ρ' 193 = 11 ∧ ρ' 192 = 0 ∧
      ¬VHolds (Clif.Val.ofInt .i8 9) (ρ' 192) := by
  have mat := imm_case_movz selfRefines (w := 8) (i := 9)
    (mw := ⟨9, 0⟩) (Or.inl rfl) rfl aliasInput.base
  obtain ⟨ms, d, hd, hshape, hrun⟩ := mat
  change V.reg (.vreg 194 .int) = V.reg (.vreg d .int) at hd
  cases hd
  obtain ⟨ρ', X, hr, hx, hX, _⟩ := hrun incomingRF
  have hv : VHolds (Clif.Val.ofInt .i8 9) (ρ' 194) := by
    apply vholds_of_lo64 (by decide) hx
    exact hX
  have hdefs : ∀ mi ∈ ms, ∀ e ∈ vdefs mi, 194 ≤ e :=
    fun mi hmi e he => (hshape.defs mi hmi e he).1
  have held := pendingHeld.resolvedResult (x := 0) (n := 192) (d := 194)
    rfl rfl hv pendingBelow hdefs hr
  obtain ⟨w', hs, _⟩ := hr Arm.ArmState.default
  have keep (k : Nat) (hk : k < 194) : ρ' k = incomingRF k :=
    seqRun_fall_frame (fun mi hmi he => Nat.not_le_of_lt hk (hdefs mi hmi _ he)) hs
  have h192 : ρ' 192 = 0 := keep 192 (by decide)
  refine ⟨ms, ρ', hr, hdefs, held, hv, keep 193 (by decide), h192, ?_⟩
  rw [h192]
  unfold VHolds
  decide

end Backend.Stock.Proof
