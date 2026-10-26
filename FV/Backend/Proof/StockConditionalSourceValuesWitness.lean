import FV.Backend.Proof.StockOriginalConditionPrefix
import FV.Backend.Proof.StockConditionalSourceValues
import FV.Backend.Proof.StockConditionalTargetsWitness

namespace Backend.Stock.Proof.ConditionalValues.SourceWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarSelect
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

def function : Clif.Function := {
  name := "stock_per_successor_migration"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64)],term := .brif 7 ⟨1,[7]⟩ ⟨2,[7]⟩},
    {id := 1,params := [(31,.i64)],term := .ret [31]}, {id := 2,params := [(47,.i64)],term := .ret [47]}] }
private def built : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx function).toOption.getD (sinkCtx,#[],sinkState)
private def ctx : Ctx := Driver.termCtx built.1 0
  (.data 152 5 [.data 151 1 [],.value 7,.blockCalls [0,1]])
private def before : State := built.2.2
private def frame (word : BitVec Clif.Ty.i64.width) : Clif.Frame := {
  func := function,regs := fun key => if key = 7 then some ⟨.i64,word⟩ else none,
  slots := [],body := [],term := function.blocks[0]!.term }
private def registers (word : BitVec Clif.Ty.i64.width) (key : Nat) : CV :=
  if key = 192 then word.setWidth 128 else 0
private theorem scope : LowerScope function := lowerScope_of rfl
private theorem build : Stock.buildCtx function = .ok built := rfl
private theorem inv : MappedCtxInv function ctx :=
  (buildCtx_mappedInv scope build).termCtx (by rfl) _
private theorem typed : ctx.valueType? 7 = some (.int 64) := rfl
private theorem getter (word : BitVec Clif.Ty.i64.width) : (frame word).getAs 7 .i64 = .ok word := rfl
private theorem dfg (word : BitVec Clif.Ty.i64.width) : DFGCons ctx (frame word) := by
  constructor
  · intro key index info inst value defined found source pure read
    by_cases same : key = 7
    · subst key
      change none = some index at defined
      cases defined
    · simp [frame,same] at read
  · intro key ty value type read
    by_cases same : key = 7
    · subst key
      rw [typed] at type
      cases type
      change some ⟨.i64,word⟩ = some value at read
      cases read
      rfl
    · simp [frame,same] at read
private theorem reads_typed (word : BitVec Clif.Ty.i64.width) {key : Nat} {ty : Clif.Ty} {bits : BitVec ty.width}
    (read : (frame word).getAs key ty = .ok bits) : ctx.valueType? key = some (.int ty.width) := by
  have source := getAs_ok read
  by_cases same : key = 7
  · subst key
    change some (⟨.i64,word⟩ : Clif.Val) = some (⟨ty,bits⟩ : Clif.Val) at source
    cases source
    exact typed
  · simp [frame,same] at source
private theorem held (word : BitVec Clif.Ty.i64.width) (state : State) :
    ValuesHeld (Demanded state) ctx (frame word) (fun key => registers word (aliasNum #[] key)) := by
  intro key _ value read
  by_cases same : key = 7
  · subst key
    change some ⟨.i64,word⟩ = some value at read
    cases read
    refine ⟨192,rfl,?_⟩
    have identity : aliasNum #[] 192 = 192 := by apply chaseF_none; rfl
    change VHolds ⟨.i64,word⟩ (registers word (aliasNum #[] 192))
    rw [identity]
    change (word.setWidth 128).setWidth 64 = word
    rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
    exact BitVec.setWidth_eq _
  · simp [frame,same] at read
private theorem extent : ∀ key r,ctx.valueReg? key = some r → key < before.demand.size := by
  intro key r mapped
  have size : ctx.valReg.size = before.demand.size := rfl
  by_cases inside : key < before.demand.size
  · exact inside
  · have empty : ctx.valReg[key]? = none := Array.getElem?_eq_none (by rw [size]; omega)
    simp [Ctx.valueReg?,empty] at mapped
private theorem separated (word : BitVec Clif.Ty.i64.width) {value : Nat} {ty : Clif.Ty} {bits : BitVec ty.width}
    (read : (frame word).getAs value ty = .ok bits) (key : Nat)
    (mapped : ctx.valueReg? value = some (.vreg key .int)) : aliasNum #[] key ≠ before.base.nextVreg := by
  have source := getAs_ok read
  by_cases same : value = 7
  · subst value
    have mapping : ctx.valueReg? 7 = some (.vreg 192 .int) := rfl
    rw [mapping] at mapped
    cases mapped
    have identity : aliasNum #[] 192 = 192 := by apply chaseF_none; rfl
    rw [identity]
    decide
  · simp [frame,same] at source
private def Observed (term : Nat) : Prop :=
  (((applyTerm program (Stock.sem ctx) {} 1001 123 term [.value 7]).run (before,#[])).toOption.bind
    (fun result => result.1)).isSome = true
section Kernel
attribute [local semireducible] Isle.Aarch64.program
private theorem observed650 : Observed 650 := by unfold Observed; decide +kernel
private theorem observed651 : Observed 651 := by unfold Observed; decide +kernel
end Kernel
private theorem actual {term : Nat} (observed : Observed term) :
    ∃ raw middle trace,ApplyInternal program (Stock.sem ctx) {} 1000 123 term [.value 7]
      (before,#[]) raw (middle,trace) := by
  unfold Observed at observed
  cases run : (applyTerm program (Stock.sem ctx) {} 1001 123 term [.value 7]).run (before,#[]) with
  | error error => rw [run] at observed; cases observed
  | ok result =>
    obtain ⟨output,middle,trace⟩ := result
    cases output with
    | none => rw [run] at observed; cases observed
    | some raw => exact ⟨raw,middle,trace,run⟩

/-- A complete original conditional source and arbitrary64-bit inputs inhabit
the new original650 companion/source-truth bridge. -/
theorem original_source_companion_witness (word : BitVec Clif.Ty.i64.width) :
    (∃ result,Stock.lower function = .ok result) ∧
    ∃ raw middle trace producer condition booleanTrace,
      ApplyInternal program (Stock.sem ctx) {} 1000 123 650 [.value 7]
        (before,#[]) raw (middle,trace) ∧
      ApplyInternal program (Stock.sem ctx) {} 119 27 715 [raw] (middle,trace)
        (.reg (middle.base.fresh .int).1)
        ({middle with base := (((middle.base.fresh .int).2.emit producer).emit
          (.cset (middle.base.fresh .int).1 condition))},booleanTrace) ∧
      BooleanExecution (fun _ => True) ispec #[] (word != 0) before
        {middle with base := (((middle.base.fresh .int).2.emit producer).emit
          (.cset (middle.base.fresh .int).1 condition))}
        (.reg (middle.base.fresh .int).1) (registers word) := by
  obtain ⟨result,_,_,_,run,_⟩ := ConditionalTargetsWitness.stock_selected_brif_targets_witness
  obtain ⟨raw,middle,trace,emitter⟩ := actual observed650
  obtain ⟨producer,condition,booleanTrace,_,_,_,_,_,companion,execution⟩ :=
    original_boolean_companion inv (dfg word) (getter word) (reads_typed word) (by decide) emitter
      refines_ispec (by simp [before]) extent (held word middle) (separated word)
  exact ⟨⟨result,run⟩,raw,middle,trace,producer,condition,booleanTrace,emitter,companion,execution⟩

/-- The actual original nonzero emitter and constructed715 companion separately
inhabit the reused width-dispatched source-value theorem. -/
theorem nonzero_source_companion_witness (word : BitVec Clif.Ty.i64.width) :
    ∃ raw middle trace producer condition booleanTrace,
      ApplyInternal program (Stock.sem ctx) {} 1000 123 651 [.value 7]
        (before,#[]) raw (middle,trace) ∧
      ApplyInternal program (Stock.sem ctx) {} 119 27 715 [raw] (middle,trace)
        (.reg (middle.base.fresh .int).1)
        ({middle with base := (((middle.base.fresh .int).2.emit producer).emit
          (.cset (middle.base.fresh .int).1 condition))},booleanTrace) ∧
      BooleanExecution (fun _ => True) ispec #[] (word != 0) before
        {middle with base := (((middle.base.fresh .int).2.emit producer).emit
          (.cset (middle.base.fresh .int).1 condition))}
        (.reg (middle.base.fresh .int).1) (registers word) := by
  obtain ⟨raw,middle,trace,emitter⟩ := actual observed651
  have shape := stock_select_nonzero_actual_condition_shape inv (cty := .i64) (by decide)
    (by decide) typed emitter
  obtain ⟨producer,condition,booleanTrace,_,_,_,_,companion⟩ :=
    stock_select_condition_boolean_companion ctx shape middle trace
  have execution := nonzero_boolean_values inv (cty := .i64) (by decide)
    (dfg word) (getter word) typed (by decide) (by decide) emitter companion
    refines_ispec (by simp [before]) extent (held word _)
  exact ⟨raw,middle,trace,producer,condition,booleanTrace,emitter,companion,execution⟩


/-- The complete original conditional source also inhabits the derived real
prefix bound, for every input word, without an alias-inequality premise. -/
theorem original_prefix_witness (word : BitVec Clif.Ty.i64.width) :
    ∃ raw middle trace code,
      ApplyInternal program (Stock.sem ctx) {} 1000 123 650 [.value 7]
        (before,#[]) raw (middle,trace) ∧ Frag before.base middle.base code := by
  obtain ⟨raw,middle,trace,emitter⟩ := actual observed650
  obtain ⟨code,fragment⟩ := original_prefix inv (dfg word) (getter word) (reads_typed word) (by decide) emitter
  exact ⟨raw,middle,trace,code,emitter,fragment⟩

end Backend.Stock.Proof.ConditionalValues.SourceWitness
