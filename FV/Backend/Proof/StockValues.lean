import FV.Backend.Proof.StockProjection
import FV.Backend.Proof.LowerSeq

/-!
Value availability with explicit source-to-vreg mapping. Stock's initial vregs
are dense layout allocations; a CLIF value ID is not its register number.
The simulation can restrict availability to values demanded by selected code.
These relations and frame lemmas do not yet prove the whole-function simulation.
-/

namespace Backend.Stock.Proof

open Backend.Proof Backend.Proof.Driver Isle Isle.Aarch64

attribute [local irreducible] runTerm Isle.Aarch64.program

/-- A defined source value has a mapped virtual register holding its low bits. -/
def ValueHeld (ctx : Ctx) (fr : Clif.Frame) (ρ : Nat → CV) (x : Nat) : Prop :=
  ∀ v, fr.regs x = some v →
    ∃ n, ctx.valueReg? x = some (.vreg n .int) ∧ VHolds v (ρ n)

/-- Only `needed` source values must be materialized. The relation still requires
a register mapping for each available value in that subset. -/
def ValuesHeld (needed : Nat → Prop) (ctx : Ctx) (fr : Clif.Frame) (ρ : Nat → CV) : Prop :=
  ∀ x, needed x → ValueHeld ctx fr ρ x

def Demanded (st : State) (x : Nat) : Prop := st.demand[x]! ≠ 0

/-- Bounds refer to register numbers, rather than the source IDs indexing the map. -/
def ValueRegsBelow (ctx : Ctx) (limit : Nat) : Prop :=
  ∀ x n, ctx.valueReg? x = some (.vreg n .int) → n < limit

def sourceView (ctx : Ctx) (ρ : Nat → CV) (x : Nat) : CV :=
  match ctx.valueReg? x with
  | some (.vreg n .int) => ρ n
  | _ => 0

def ValueMapInjective (ctx : Ctx) : Prop :=
  ∀ x y n, ctx.valueReg? x = some (.vreg n .int) →
    ctx.valueReg? y = some (.vreg n .int) → x = y

def withValue (fr : Clif.Frame) (x : Nat) (v : Clif.Val) : Clif.Frame :=
  { fr with regs := fun y => if y = x then some v else fr.regs y }

theorem ValuesHeld.read {needed : Nat → Prop} {ctx : Ctx} {fr : Clif.Frame}
    {ρ : Nat → CV} (h : ValuesHeld needed ctx fr ρ) {x n : Nat} {v : Clif.Val}
    (hn : needed x) (hv : fr.regs x = some v)
    (hr : ctx.valueReg? x = some (.vreg n .int)) : VHolds v (ρ n) := by
  obtain ⟨m, hm, hvalue⟩ := h x hn v hv
  have he := Option.some.inj (hm.symm.trans hr)
  cases he
  exact hvalue

theorem ValuesHeld.mono {needed fewer : Nat → Prop} {ctx : Ctx} {fr : Clif.Frame}
    {ρ : Nat → CV} (h : ValuesHeld needed ctx fr ρ)
    (hsubset : ∀ x, fewer x → needed x) : ValuesHeld fewer ctx fr ρ :=
  fun x hx => h x (hsubset x hx)

theorem ValuesHeld.sourceView {ctx : Ctx} {fr : Clif.Frame} {ρ : Nat → CV}
    (h : ValuesHeld (fun _ => True) ctx fr ρ) : ValsHeld fr (Backend.Stock.Proof.sourceView ctx ρ) := by
  intro x v hv
  obtain ⟨n, hn, hvalue⟩ := h x trivial v hv
  simpa only [Backend.Stock.Proof.sourceView, hn] using hvalue

theorem ValuesHeld.of_sourceView {needed : Nat → Prop} {ctx : Ctx} {fr : Clif.Frame}
    {ρ : Nat → CV} (h : ValsHeld fr (Backend.Stock.Proof.sourceView ctx ρ))
    (hmapped : ∀ x, needed x → ∀ v, fr.regs x = some v →
      ∃ n, ctx.valueReg? x = some (.vreg n .int)) : ValuesHeld needed ctx fr ρ := by
  intro x hx v hv
  obtain ⟨n, hn⟩ := hmapped x hx v hv
  refine ⟨n, hn, ?_⟩
  simpa only [Backend.Stock.Proof.sourceView, hn] using h x v hv

theorem ValuesHeld.keep {needed : Nat → Prop} {ctx : Ctx} {fr : Clif.Frame}
    {ρ ρ' : Nat → CV} (h : ValuesHeld needed ctx fr ρ)
    (hkeep : ∀ x n, needed x → ctx.valueReg? x = some (.vreg n .int) → ρ' n = ρ n) :
    ValuesHeld needed ctx fr ρ' := by
  intro x hx v hv
  obtain ⟨n, hn, hvalue⟩ := h x hx v hv
  exact ⟨n, hn, by rw [hkeep x n hx hn]; exact hvalue⟩

theorem ValuesHeld.fresh {needed : Nat → Prop} {ctx : Ctx} {fr : Clif.Frame}
    {ρ ρ' : Nat → CV} {limit : Nat} (h : ValuesHeld needed ctx fr ρ)
    (hbelow : ValueRegsBelow ctx limit) (hkeep : ∀ n, n < limit → ρ' n = ρ n) :
    ValuesHeld needed ctx fr ρ' :=
  h.keep (fun x n _ hn => hkeep n (hbelow x n hn))

/-- Straight-line selected code writing fresh registers preserves all previously
materialized source values, independent of the instruction semantics/world. -/
theorem ValuesHeld.seqRun {W : Type} {isem : ISem CV W} {needed : Nat → Prop}
    {ctx : Ctx} {fr : Clif.Frame} {ρ ρ' : Nat → CV} {w w' : W} {limit : Nat}
    {ms : List MInst} (h : ValuesHeld needed ctx fr ρ) (hbelow : ValueRegsBelow ctx limit)
    (hdefs : ∀ m ∈ ms, ∀ n ∈ vdefs m, limit ≤ n)
    (hrun : seqRun isem ms ρ w = some (.fall ρ' w')) : ValuesHeld needed ctx fr ρ' := by
  apply h.fresh hbelow
  intro n hn
  exact seqRun_fall_frame (fun m hm hmem => Nat.not_le_of_lt hn (hdefs m hm n hmem)) hrun

theorem ValuesHeld.updateResult {needed : Nat → Prop} {ctx : Ctx} {fr : Clif.Frame}
    {ρ ρ' : Nat → CV} {x n : Nat} {v : Clif.Val} (h : ValuesHeld needed ctx fr ρ)
    (hmap : ctx.valueReg? x = some (.vreg n .int)) (hvalue : VHolds v (ρ' n))
    (hkeep : ∀ y m, needed y → y ≠ x →
      ctx.valueReg? y = some (.vreg m .int) → ρ' m = ρ m) :
    ValuesHeld needed ctx (withValue fr x v) ρ' := by
  intro y hy value hv
  by_cases he : y = x
  · subst y
    simp only [withValue, ite_true, eq_self] at hv
    cases hv
    exact ⟨n, hmap, hvalue⟩
  · simp only [withValue, ite_eq_right he] at hv
    obtain ⟨m, hm, hold⟩ := h y hy value hv
    exact ⟨m, hm, by rw [hkeep y m hy he hm]; exact hold⟩

/-- For an injective initial map, installing one result cannot overwrite any
other source value. No equality between source IDs and vreg numbers is needed. -/
theorem ValuesHeld.writeResult {needed : Nat → Prop} {ctx : Ctx} {fr : Clif.Frame}
    {ρ : Nat → CV} {x n : Nat} {v : Clif.Val} {result : CV}
    (h : ValuesHeld needed ctx fr ρ) (hinj : ValueMapInjective ctx)
    (hmap : ctx.valueReg? x = some (.vreg n .int)) (hvalue : VHolds v result) :
    ValuesHeld needed ctx (withValue fr x v) (fun m => if m = n then result else ρ m) := by
  apply h.updateResult hmap (by simpa only [eq_self, ite_true] using hvalue)
  intro y m _ hne hm
  have hmn : m ≠ n := by
    intro he
    subst m
    exact hne (hinj y x n hm hmap)
  exact ite_eq_right hmn

/-- Guard used by register-demand helpers: a sunk definition cannot be demanded
again. Values with no DFG definition (e.g. parameters) satisfy it immediately. -/
def DemandAllowed (ctx : Ctx) (st : State) (x : Nat) : Prop :=
  ∀ i, ctx.defInst? x = some i → st.sunk[i]! = false

theorem mark_demand (st : State) (x : Nat) (hx : x < st.demand.size) :
    (st.mark x).demand[x]! = st.demand[x]! + 1 ∧
    (st.mark x).base = st.base ∧ (st.mark x).demand.size = st.demand.size := by
  have hm : x < (st.demand.modify x (· + 1)).size := by simpa only [Array.size_modify] using hx
  refine ⟨?_, rfl, Array.size_modify⟩
  change (st.demand.modify x (· + 1))[x]! = st.demand[x]! + 1
  rw [_root_.getElem!_pos (st.demand.modify x (· + 1)) x hm, Array.getElem_modify_self _ hm, _root_.getElem!_pos st.demand x hx]

/-- Demanding one value leaves every other selected-code use count unchanged,
including queries outside the demand array. -/
theorem mark_other (st : State) (x y : Nat) (hne : y ≠ x) :
    (st.mark x).demand[y]! = st.demand[y]! := by
  change (st.demand.modify x (· + 1))[y]! = st.demand[y]!
  by_cases hy : y < st.demand.size
  · have hm : y < (st.demand.modify x (· + 1)).size := by
      simpa only [Array.size_modify] using hy
    rw [_root_.getElem!_pos _ y hm, Array.getElem_modify_of_ne (Ne.symm hne),
      _root_.getElem!_pos _ y hy]
  · simp [getElem!_def, Array.getElem?_modify, Array.getElem?_eq_none (Nat.le_of_not_lt hy)]

/-- A successful in-bounds demand adds precisely that value to the set of
values whose selected code needs a register. -/
theorem demanded_mark_iff (st : State) (x y : Nat) (hx : x < st.demand.size) :
    Demanded (st.mark x) y ↔ y = x ∨ Demanded st y := by
  by_cases he : y = x
  · subst y
    have hn := (mark_demand st x hx).1
    simp only [Demanded, hn, Nat.add_one_ne_zero, ne_eq, not_false_eq_true, eq_self, true_or]
  · rw [Demanded, mark_other st x y he]
    simp only [he, false_or, Demanded]

/-- Register demand is valid only when the newly requested value is available.
The backward simulation must discharge this premise from the producer's code. -/
theorem ValuesHeld.mark {ctx : Ctx} {fr : Clif.Frame} {ρ : Nat → CV}
    {st : State} {x : Nat} (h : ValuesHeld (Demanded st) ctx fr ρ)
    (hx : x < st.demand.size) (havail : ValueHeld ctx fr ρ x) :
    ValuesHeld (Demanded (st.mark x)) ctx fr ρ := by
  intro y hy
  rcases (demanded_mark_iff st x y hx).mp hy with rfl | hold
  · exact havail
  · exact h y hold

theorem stock_put_in_reg (ctx : Ctx) (st : State) (x : Nat) (r : Reg)
    (hr : ctx.valueReg? x = some r) (hsafe : DemandAllowed ctx st x) :
    Stock.externCtor ctx T.put_in_reg [.value x] st = .ok (.reg r, st.mark x) := by
  have hlegacy : Backend.externCtor ctx T.put_in_reg [.value x] (st.mark x).base =
      match ctx.valueReg? x with
      | some r => .ok (.reg r, (st.mark x).base)
      | none => .unmodeled s!"put_in_reg v{x}" := rfl
  have hdelegate : (match Backend.externCtor ctx T.put_in_reg [.value x] (st.mark x).base with
      | .ok (v, b) => .ok (v, { st.mark x with base := b })
      | .fail => .fail | .unmodeled e => .unmodeled e) =
      (.ok (.reg r, st.mark x) : ExtResult (V × State)) := by
    rw [hlegacy, hr]
  simp only [T.put_in_reg] at hdelegate
  have hshape : Stock.externCtor ctx T.put_in_reg [.value x] st =
      match ctx.defInst? x with
      | some i => if st.sunk[i]! then .unmodeled s!"demand for sunk instruction {i}"
        else .ok (.reg r, st.mark x)
      | none => .ok (.reg r, st.mark x) := by
    cases hd : ctx.defInst? x <;>
      simp [Stock.externCtor, T.put_in_reg, TId.mark_value_used, hd] <;>
        first | exact hdelegate | (split <;> first | rfl | exact hdelegate)
  rw [hshape]
  cases hd : ctx.defInst? x with
  | none => rfl
  | some i => simp only [hsafe i hd, Bool.false_eq_true, ite_false]

/-- Extended operands demand their CLIF source just like ordinary register operands. -/
theorem stock_put_extended_in_reg (ctx : Ctx) (st : State) (x : Nat) (e : ExtendOp) (r : Reg)
    (hr : ctx.valueReg? x = some r) (hsafe : DemandAllowed ctx st x) :
    Stock.externCtor ctx T.put_extended_in_reg [.op (.extended x e)] st = .ok (.reg r, st.mark x) := by
  have hlegacy : Backend.externCtor ctx T.put_extended_in_reg [.op (.extended x e)] (st.mark x).base =
      match ctx.valueReg? x with
      | some r => .ok (.reg r, (st.mark x).base)
      | none => .unmodeled "put_extended_in_reg" := rfl
  have hdelegate : (match Backend.externCtor ctx T.put_extended_in_reg [.op (.extended x e)] (st.mark x).base with
      | .ok (v, b) => .ok (v, { st.mark x with base := b })
      | .fail => .fail | .unmodeled e => .unmodeled e) =
      (.ok (.reg r, st.mark x) : ExtResult (V × State)) := by
    rw [hlegacy, hr]
  simp only [T.put_extended_in_reg] at hdelegate
  have hshape : Stock.externCtor ctx T.put_extended_in_reg [.op (.extended x e)] st =
      match ctx.defInst? x with
      | some i => if st.sunk[i]! then .unmodeled s!"demand for sunk instruction {i}"
        else .ok (.reg r, st.mark x)
      | none => .ok (.reg r, st.mark x) := by
    cases hd : ctx.defInst? x <;>
      simp [Stock.externCtor, T.put_extended_in_reg, TId.mark_value_used, hd] <;>
        first | exact hdelegate | (split <;> first | rfl | exact hdelegate)
  rw [hshape]
  cases hd : ctx.defInst? x with
  | none => rfl
  | some i => simp only [hsafe i hd, Bool.false_eq_true, ite_false]

theorem stock_put_in_regs (ctx : Ctx) (st : State) (x : Nat) (r : Reg)
    (hr : ctx.valueReg? x = some r) (hsafe : DemandAllowed ctx st x) :
    Stock.externCtor ctx T.put_in_regs [.value x] st = .ok (.regs [r], st.mark x) := by
  have hlegacy : Backend.externCtor ctx T.put_in_regs [.value x] (st.mark x).base =
      match ctx.valueReg? x with
      | some r => .ok (.regs [r], (st.mark x).base)
      | none => .unmodeled s!"put_in_regs v{x}" := rfl
  have hdelegate : (match Backend.externCtor ctx T.put_in_regs [.value x] (st.mark x).base with
      | .ok (v, b) => .ok (v, { st.mark x with base := b })
      | .fail => .fail | .unmodeled e => .unmodeled e) =
      (.ok (.regs [r], st.mark x) : ExtResult (V × State)) := by
    rw [hlegacy, hr]
  simp only [T.put_in_regs] at hdelegate
  have hshape : Stock.externCtor ctx T.put_in_regs [.value x] st =
      match ctx.defInst? x with
      | some i => if st.sunk[i]! then .unmodeled s!"demand for sunk instruction {i}"
        else .ok (.regs [r], st.mark x)
      | none => .ok (.regs [r], st.mark x) := by
    cases hd : ctx.defInst? x <;>
      simp [Stock.externCtor, T.put_in_regs, TId.mark_value_used, hd] <;>
        first | exact hdelegate | (split <;> first | rfl | exact hdelegate)
  rw [hshape]
  cases hd : ctx.defInst? x with
  | none => rfl
  | some i => simp only [hsafe i hd, Bool.false_eq_true, ite_false]

/-! Concrete mapped registers 192/193 are deliberately different from their
source IDs 0/1. A real one-instruction VCode run writes temporary 194. -/

private def valueFrame : Clif.Frame := {
  func := sinkCtx.func
  regs := fun | 0 => some (.ofInt .i8 7) | 1 => some (.ofInt .i64 11) | _ => none
  slots := []
  body := []
  term := .ret [0] }

private def valueRF (n : Nat) : CV := if n = 192 then 7 else 11

private theorem valueHeld : ValuesHeld (fun _ => True) sinkCtx valueFrame valueRF := by
  intro x _ v hv
  cases x with
  | zero =>
    change some (Clif.Val.ofInt .i8 7) = some v at hv
    cases hv
    exact ⟨192, rfl, by unfold VHolds; decide⟩
  | succ x =>
    cases x with
    | zero =>
      change some (Clif.Val.ofInt .i64 11) = some v at hv
      cases hv
      exact ⟨193, rfl, by unfold VHolds; decide⟩
    | succ x => change none = some v at hv; cases hv

private theorem mappingCases {x n : Nat}
    (h : sinkCtx.valueReg? x = some (.vreg n .int)) :
    (x = 0 ∧ n = 192) ∨ (x = 1 ∧ n = 193) := by
  cases x with
  | zero => change some (Reg.vreg 192 .int) = some (Reg.vreg n .int) at h; cases h; exact .inl ⟨rfl, rfl⟩
  | succ x =>
    cases x with
    | zero => change some (Reg.vreg 193 .int) = some (Reg.vreg n .int) at h; cases h; exact .inr ⟨rfl, rfl⟩
    | succ x =>
      have hb : sinkCtx.valReg.size ≤ x + 2 := by change 2 ≤ x + 2; omega
      simp only [Ctx.valueReg?, Array.getElem?_eq_none hb, Option.join_none] at h
      cases h

private theorem mappingBelow : ValueRegsBelow sinkCtx 194 := by
  intro x n h
  rcases mappingCases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

private theorem mappingInjective : ValueMapInjective sinkCtx := by
  intro x y n hx hy
  rcases mappingCases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases mappingCases hy with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> first | rfl | cases h

private def freshRF (n : Nat) : CV := if n = 194 then 99 else valueRF n

private theorem freshRF_keep (n : Nat) (hn : n < 194) : freshRF n = valueRF n :=
  ite_eq_right (Nat.ne_of_lt hn)

theorem ValuesHeld.read_witness :
    ValuesHeld (fun _ => True) sinkCtx valueFrame valueRF ∧
    sinkCtx.valueReg? 0 = some (.vreg 192 .int) ∧
    VHolds (Clif.Val.ofInt .i8 7) (valueRF 192) :=
  ⟨valueHeld, rfl, valueHeld.read (x := 0) trivial rfl rfl⟩

theorem ValuesHeld.mono_witness :
    ValuesHeld (fun x => x = 0) sinkCtx valueFrame valueRF ∧
    ValuesHeld (Demanded { sinkState with demand := #[1, 0] }) sinkCtx valueFrame valueRF :=
  ⟨valueHeld.mono (fun _ _ => trivial), valueHeld.mono (fun _ _ => trivial)⟩

theorem ValuesHeld.sourceView_witness :
    ValuesHeld (fun _ => True) sinkCtx valueFrame valueRF ∧
    ValsHeld valueFrame (Backend.Stock.Proof.sourceView sinkCtx valueRF) ∧
    Backend.Stock.Proof.sourceView sinkCtx valueRF 0 = 7 ∧ valueRF 0 = 11 :=
  ⟨valueHeld, valueHeld.sourceView, rfl, rfl⟩

theorem ValuesHeld.of_sourceView_witness :
    ValsHeld valueFrame (Backend.Stock.Proof.sourceView sinkCtx valueRF) ∧
    ValuesHeld (fun _ => True) sinkCtx valueFrame valueRF :=
  ⟨valueHeld.sourceView, ValuesHeld.of_sourceView valueHeld.sourceView
    (fun x hx v hv => let ⟨n, hn, _⟩ := valueHeld x hx v hv; ⟨n, hn⟩)⟩

theorem ValuesHeld.keep_witness :
    ValuesHeld (fun _ => True) sinkCtx valueFrame freshRF ∧ freshRF 194 = 99 :=
  ⟨valueHeld.keep (fun x n _ hn => freshRF_keep n (mappingBelow x n hn)), rfl⟩

theorem ValuesHeld.fresh_witness :
    ValueRegsBelow sinkCtx 194 ∧ ValuesHeld (fun _ => True) sinkCtx valueFrame freshRF ∧
    freshRF 194 ≠ valueRF 194 :=
  ⟨mappingBelow, valueHeld.fresh mappingBelow freshRF_keep, by decide⟩

private def copyInst : MInst := .mov .size64 (.vreg 194 .int) (.vreg 192 .int)

private def copyOps : Array Operand := copyInst.operands.toOption.getD #[]

private def copySem : ISem CV Unit := fun _ uses w => some (uses.take 1, w, .next)

private def copyRF : Nat → CV := vdefUpd copyOps [7] valueRF

theorem ValuesHeld.seqRun_witness :
    ValueRegsBelow sinkCtx 194 ∧
    (∀ m ∈ [copyInst], ∀ n ∈ vdefs m, 194 ≤ n) ∧
    Backend.Proof.seqRun copySem [copyInst] valueRF () = some (.fall copyRF ()) ∧
    ValuesHeld (fun _ => True) sinkCtx valueFrame copyRF := by
  have hdefs : ∀ m ∈ [copyInst], ∀ n ∈ vdefs m, 194 ≤ n := by
    intro m hm n hn
    simp only [List.mem_singleton] at hm
    subst m
    have hd : vdefs copyInst = [194] := rfl
    have hn' : n = 194 := by simpa only [hd, List.mem_singleton] using hn
    subst n
    exact Nat.le_refl _
  have hrun : Backend.Proof.seqRun copySem [copyInst] valueRF () = some (.fall copyRF ()) := by rfl
  exact ⟨mappingBelow, hdefs, hrun, valueHeld.seqRun mappingBelow hdefs hrun⟩

private def resultRF (n : Nat) : CV := if n = 192 then 9 else valueRF n

theorem ValuesHeld.updateResult_witness :
    ValuesHeld (fun _ => True) sinkCtx (withValue valueFrame 0 (.ofInt .i8 9)) resultRF ∧
    (withValue valueFrame 0 (.ofInt .i8 9)).regs 0 = some (.ofInt .i8 9) := by
  refine ⟨valueHeld.updateResult (x := 0) (n := 192) rfl (by unfold VHolds; decide) ?_, rfl⟩
  intro y m _ hne hm
  rcases mappingCases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact False.elim (hne rfl)
  · rfl

theorem ValuesHeld.writeResult_witness :
    ValueMapInjective sinkCtx ∧
    ValuesHeld (fun _ => True) sinkCtx (withValue valueFrame 0 (.ofInt .i8 9)) resultRF :=
  ⟨mappingInjective, valueHeld.writeResult mappingInjective (x := 0) (n := 192) rfl (by unfold VHolds; decide)⟩

theorem mark_demand_witness :
    (sinkState.mark 0).demand[0]! = sinkState.demand[0]! + 1 ∧
    (sinkState.mark 0).base = sinkState.base ∧
    (sinkState.mark 0).demand.size = sinkState.demand.size ∧
    (sinkState.mark 0).demand[1]! = sinkState.demand[1]! :=
  ⟨(mark_demand sinkState 0 (by decide)).1, (mark_demand sinkState 0 (by decide)).2.1,
    (mark_demand sinkState 0 (by decide)).2.2, rfl⟩

private theorem allowDefinition : DemandAllowed sinkCtx sinkState 0 := by
  intro i hi
  change some 0 = some i at hi
  cases hi
  rfl

theorem mark_other_witness :
    (sinkState.mark 0).demand[0]! = 1 ∧
    (sinkState.mark 0).demand[1]! = sinkState.demand[1]! ∧
    (sinkState.mark 0).demand[2]! = sinkState.demand[2]! :=
  ⟨rfl, mark_other sinkState 0 1 (by decide), mark_other sinkState 0 2 (by decide)⟩

theorem demanded_mark_iff_witness :
    (Demanded (sinkState.mark 0) 0 ↔ 0 = 0 ∨ Demanded sinkState 0) ∧
    Demanded (sinkState.mark 0) 0 ∧ ¬Demanded sinkState 0 ∧
    ¬Demanded (sinkState.mark 0) 1 :=
  ⟨demanded_mark_iff sinkState 0 0 (by decide), by unfold Demanded; decide,
    by unfold Demanded; decide, by unfold Demanded; decide⟩

theorem ValuesHeld.mark_witness :
    ValuesHeld (Demanded sinkState) sinkCtx valueFrame valueRF ∧
    ValueHeld sinkCtx valueFrame valueRF 0 ∧
    ValuesHeld (Demanded (sinkState.mark 0)) sinkCtx valueFrame valueRF ∧
    Demanded (sinkState.mark 0) 0 := by
  have hold := valueHeld.mono (fewer := Demanded sinkState) (fun _ _ => trivial)
  have havail := valueHeld 0 trivial
  exact ⟨hold, havail, hold.mark (by decide) havail, by unfold Demanded; decide⟩

theorem stock_put_in_reg_witness :
    DemandAllowed sinkCtx sinkState 0 ∧
    Stock.externCtor sinkCtx T.put_in_reg [.value 0] sinkState =
      .ok (.reg (.vreg 192 .int), sinkState.mark 0) ∧
    (sinkState.mark 0).demand[0]! = 1 :=
  ⟨allowDefinition, stock_put_in_reg _ _ _ _ rfl allowDefinition, rfl⟩

theorem stock_put_in_regs_witness :
    DemandAllowed sinkCtx sinkState 0 ∧
    Stock.externCtor sinkCtx T.put_in_regs [.value 0] sinkState =
      .ok (.regs [.vreg 192 .int], sinkState.mark 0) ∧
    (sinkState.mark 0).demand[0]! = 1 :=
  ⟨allowDefinition, stock_put_in_regs _ _ _ _ rfl allowDefinition, rfl⟩

theorem stock_put_extended_in_reg_witness :
    DemandAllowed sinkCtx sinkState 0 ∧
    Stock.externCtor sinkCtx T.put_extended_in_reg [.op (.extended 0 .uxtw)] sinkState =
      .ok (.reg (.vreg 192 .int), sinkState.mark 0) ∧
    (sinkState.mark 0).demand[0]! = 1 :=
  ⟨allowDefinition, stock_put_extended_in_reg _ _ _ _ _ rfl allowDefinition, rfl⟩

end Backend.Stock.Proof
