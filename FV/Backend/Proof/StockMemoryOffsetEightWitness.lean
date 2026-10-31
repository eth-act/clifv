import FV.Backend.Proof.StockMemoryOffsetEightAddress
import FV.Backend.Proof.StockMemoryIntegerLoadWitness

namespace Backend.Stock.Memory.IntegerRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Source-built contexts inhabit both positive-offset address contracts at every width. -/
theorem parameter_offset_eight_address_witness (width : Width) :
    ∃ (ctx : Ctx) (st : State),ctx.defInst? 0 = none ∧
      ctx.valueReg? 0 = some (.vreg 192 .int) ∧
      (applyTerm program (Stock.sem ctx) {} 60 89 575
        [.ty (.int width.bits),.value 0,.int 8]).run (st,#[]) =
        .ok (some (.data 89 VIdx.AMode.UnsignedOffset [.reg (.vreg 192 .int),.op (.uimm12Scaled 8)]),
          st.mark 0,#[].push rule_inst_4103.id) ∧
      (applyTerm program (Stock.sem ctx) {} 80 89 574
        [.ty (.int width.bits),.value 0,.int 8]).run (st,#[]) =
        .ok (some (.data 89 VIdx.AMode.UnsignedOffset [.reg (.vreg 192 .int),.op (.uimm12Scaled 8)]),
          st.mark 0,(#[].push rule_inst_4103.id).push rule_inst_4038.id) := by
  obtain ⟨ctx,st,trace,parameter,mapped,prior⟩ := integer_load_rhs_witness width
  exact ⟨ctx,st,parameter,mapped,
    stock_parameter_amode_eight_width data_program width ctx rfl parameter mapped st #[] 0,
    stock_parameter_load_address_eight_width data_program width ctx rfl parameter mapped st #[] 0⟩

end Backend.Stock.Memory.IntegerRoots
