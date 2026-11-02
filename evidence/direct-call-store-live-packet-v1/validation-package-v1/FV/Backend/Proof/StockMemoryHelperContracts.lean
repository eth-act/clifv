import FV.Backend.Proof.StockMemoryHelperProjection
import FV.Backend.Proof.IselMemHelpers

/-! Draft contracts for the next memory batch. Current production gates exclude it. -/
namespace Backend.Stock.Proof.MemoryHelpers
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false

inductive IntegerLoad where
  | unsigned8 | signed8 | unsigned16 | signed16 | unsigned32 | signed32 | unsigned64

def IntegerLoad.term : IntegerLoad → Nat
  | .unsigned8 => 529 | .signed8 => 530 | .unsigned16 => 531 | .signed16 => 532
  | .unsigned32 => 533 | .signed32 => 534 | .unsigned64 => 535

def IntegerLoad.tag : IntegerLoad → Nat
  | .unsigned8 => 10 | .signed8 => 11 | .unsigned16 => 12 | .signed16 => 13
  | .unsigned32 => 14 | .signed32 => 15 | .unsigned64 => 16

/-- Every integer load helper returns its fresh register and emits its decoded load.
All Stock scheduling fields remain unchanged. -/
theorem integer_load_contract (kind : IntegerLoad) (ctx : Ctx) {cfg : Config}
    (overlap : cfg.checkOverlap = false) {fuel : Nat} (enough : 40 ≤ fuel)
    {address flags : V} {st next : State} {before trace : Array RuleId} {out : V}
    (run : ApplyInternal program (Stock.sem ctx) cfg fuel 27 kind.term
      [address,flags] (st,before) out (next,trace)) :
    ∃ instruction,
      MInst.ofV (.data 58 kind.tag [.reg (st.base.fresh .int).1,address,flags]) =
        some instruction ∧
      out = .reg (st.base.fresh .int).1 ∧
      next = {st with base := (st.base.fresh .int).2.emit instruction} := by
  have member : kind.term ∈ helperIds := by cases kind <;> decide
  have projected := integer_helper_success ctx overlap member [address,flags] run
  have legacy : ∃ instruction,
      MInst.ofV (.data 58 kind.tag [.reg (st.base.fresh .int).1,address,flags]) =
        some instruction ∧
      out = .reg (st.base.fresh .int).1 ∧
      next.base = (st.base.fresh .int).2.emit instruction := by
    cases kind
    · exact uload8_helper_ok data_program ctx overlap enough projected.1
    · exact sload8_helper_ok data_program ctx overlap enough projected.1
    · exact uload16_helper_ok data_program ctx overlap enough projected.1
    · exact sload16_helper_ok data_program ctx overlap enough projected.1
    · exact uload32_helper_ok data_program ctx overlap enough projected.1
    · exact sload32_helper_ok data_program ctx overlap enough projected.1
    · exact uload64_helper_ok data_program ctx overlap enough projected.1
  obtain ⟨instruction,decoded,value,base⟩ := legacy
  refine ⟨instruction,decoded,value,?_⟩
  calc
    next = {st with base := next.base} := projected.2
    _ = {st with base := (st.base.fresh .int).2.emit instruction} := by rw [base]

inductive IntegerStore where
  | bits8 | bits16 | bits32 | bits64

def IntegerStore.term : IntegerStore → Nat
  | .bits8 => 541 | .bits16 => 542 | .bits32 => 543 | .bits64 => 544

def IntegerStore.tag : IntegerStore → Nat
  | .bits8 => 17 | .bits16 => 18 | .bits32 => 19 | .bits64 => 20

/-- Every integer store helper returns its exact side-effect payload.
The enclosing root emits the payload; the helper preserves the complete state. -/
theorem integer_store_contract (kind : IntegerStore) (ctx : Ctx) {cfg : Config}
    (overlap : cfg.checkOverlap = false) {fuel : Nat} (enough : 40 ≤ fuel)
    {address flags value : V} {st next : State} {before trace : Array RuleId} {out : V}
    (run : ApplyInternal program (Stock.sem ctx) cfg fuel 46 kind.term
      [address,flags,value] (st,before) out (next,trace)) :
    out = .data 46 0 [.data 58 kind.tag [value,address,flags]] ∧ next = st := by
  have member : kind.term ∈ helperIds := by cases kind <;> decide
  have projected := integer_helper_success ctx overlap member [address,flags,value] run
  have legacy : out = .data 46 0 [.data 58 kind.tag [value,address,flags]] ∧
      next.base = st.base := by
    cases kind
    · exact store8_helper_ok data_program ctx overlap enough projected.1
    · exact store16_helper_ok data_program ctx overlap enough projected.1
    · exact store32_helper_ok data_program ctx overlap enough projected.1
    · exact store64_helper_ok data_program ctx overlap enough projected.1
  refine ⟨legacy.1,?_⟩
  calc
    next = {st with base := next.base} := projected.2
    _ = {st with base := st.base} := by rw [legacy.2]
    _ = st := rfl

end Backend.Stock.Proof.MemoryHelpers
