import FV.Backend.Proof.StockAcquireReadQueueCut

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Original source-slot order implies strict metadata color order for actual source events. -/
theorem source_slot_colors_order {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {initial : LState} (built : Backend.buildCtx f = .ok (ctx,ranges,initial))
    (first second : Nat) (firstSource : some first ∈ sourceColorEvents ctx ranges)
    (secondSource : some second ∈ sourceColorEvents ctx ranges) (before : first < second) :
    (sourceMetadata ctx ranges).entryColor[first]! < (sourceMetadata ctx ranges).entryColor[second]! := by
  by_cases increasing : (sourceMetadata ctx ranges).entryColor[first]! < (sourceMetadata ctx ranges).entryColor[second]!
  · exact increasing
  have opposite := Nat.le_of_not_gt increasing
  rcases Nat.eq_or_lt_of_le opposite with same | reverse
  · have equal := source_color_equal_slots built second first secondSource firstSource same
    omega
  · have wrongOrder := source_color_order_reflects_slots built second first secondSource firstSource reverse
    omega

def PositiveColorOrder (colors : Array Nat) : Prop :=
  ∀ first second,colors[first]! ≠ 0 → colors[second]! ≠ 0 → first < second → colors[first]! < colors[second]!

/-- Successful actual source construction supplies strict order for every positive metadata slot. -/
theorem source_metadata_positive_order {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {initial : LState} (built : Backend.buildCtx f = .ok (ctx,ranges,initial)) :
    PositiveColorOrder (sourceMetadata ctx ranges).entryColor := by
  intro first second firstPositive secondPositive before
  exact source_slot_colors_order built first second
    (source_color_positive_member ctx ranges first firstPositive)
    (source_color_positive_member ctx ranges second secondPositive) before

/-- The reference cut follows original colored positions without consuming deferred reads. -/
def referenceCut (colors : Array Nat) (cut inst : Nat) : Nat :=
  if colors[inst]! = 0 then cut else colors[inst]!

def ColorTailBound (colors : Array Nat) (cut : Nat) (indices : List Nat) : Prop :=
  ∀ inst ∈ indices,colors[inst]! ≠ 0 → colors[inst]! ≤ cut

/-- Strict reverse source order derives each later reference-cut bound internally. -/
theorem referenceCut_tail_bound {colors : Array Nat} (ordered : PositiveColorOrder colors)
    {cut inst : Nat} {indices : List Nat} (reverse : (inst::indices).Pairwise (fun first second => second < first))
    (bounded : ColorTailBound colors cut (inst::indices)) :
    referenceCut colors cut inst ≤ cut ∧ ColorTailBound colors (referenceCut colors cut inst) indices := by
  by_cases quiet : colors[inst]! = 0
  · simp only [referenceCut,quiet,ite_true]
    refine ⟨Nat.le_refl _,?_⟩
    intro target member positive
    exact bounded target (List.mem_cons_of_mem _ member) positive
  · simp only [referenceCut,quiet,ite_false]
    refine ⟨bounded inst (List.mem_cons_self ..) quiet,?_⟩
    intro target member positive
    have before := (List.pairwise_cons.mp reverse).1 target member
    exact Nat.le_of_lt (ordered target inst positive quiet before)

/-- An actual source terminator bounds every earlier source effect in its block. -/
theorem source_event_tail_bound {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {initial : LState} (built : Backend.buildCtx f = .ok (ctx,ranges,initial)) (terminal : Nat)
    (terminalSource : some terminal ∈ sourceColorEvents ctx ranges) {indices : List Nat}
    (earlier : ∀ inst ∈ indices,inst < terminal) :
    ColorTailBound (sourceMetadata ctx ranges).entryColor
      (sourceMetadata ctx ranges).entryColor[terminal]! indices := by
  intro inst member positive
  exact Nat.le_of_lt (source_slot_colors_order built inst terminal
    (source_color_positive_member ctx ranges inst positive) terminalSource (earlier inst member))

end Backend.Stock.Proof.Acquire810
