import FV.Backend.Proof.StockMemoryLoadedPointerAddress
import FV.Backend.Proof.StockMemoryLoadedPointerFixture

namespace Backend.Stock.Memory.IntegerRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000

/-- The unchanged captured function inhabits both loaded-pointer address contracts at every width. -/
theorem captured_loaded_pointer_address_witness (width : Width) :
    ∃ (ctx : Ctx) (ranges : Array (Nat × Nat)) (st : State),
      Stock.buildCtx LoadedPointerFixture.function = .ok (ctx,ranges,st) ∧
      ctx.defInst? 3 = some 4 ∧ ctx.valueReg? 3 = some (.vreg 194 .int) ∧
      (applyTerm program (Stock.sem ctx) {} 60 89 575
        [.ty (.int width.bits),.value 3,.int 0]).run (st,#[]) =
        .ok (some (.data 89 VIdx.AMode.UnsignedOffset [.reg (.vreg 194 .int),.op (.uimm12Scaled 0)]),
          st.mark 3,#[].push rule_inst_4064.id) ∧
      (applyTerm program (Stock.sem ctx) {} 80 89 574
        [.ty (.int width.bits),.value 3,.int 0]).run (st,#[]) =
        .ok (some (.data 89 VIdx.AMode.UnsignedOffset [.reg (.vreg 194 .int),.op (.uimm12Scaled 0)]),
          st.mark 3,(#[].push rule_inst_4064.id).push rule_inst_4038.id) := by
  obtain ⟨ctx,ranges,st,info,built,scope,dominated,defined,mapped,source,data,type,safe⟩ :=
    LoadedPointerFixture.captured_loaded_pointer_context_witness
  exact ⟨ctx,ranges,st,built,defined,mapped,
    stock_loaded_pointer_amode_zero_width data_program width ctx (cfg := {}) rfl
      defined source data type mapped st #[] 0 safe,
    stock_loaded_pointer_address_zero_width data_program width ctx (cfg := {}) rfl
      defined source data type mapped st #[] 0 safe⟩

/-- The same source context rejects a deliberately sunk loaded pointer at every width. -/
theorem captured_loaded_pointer_rejection_witness (width : Width) :
    ∃ (ctx : Ctx) (ranges : Array (Nat × Nat)) (st : State),
      Stock.buildCtx LoadedPointerFixture.function = .ok (ctx,ranges,st) ∧
      ctx.defInst? 3 = some 4 ∧
      (applyTerm program (Stock.sem ctx) {} 80 89 574
        [.ty (.int width.bits),.value 3,.int 0]).run
          ({st with sunk := #[false,false,false,false,true]},#[]) =
        .error (.unmodeled "demand for sunk instruction 4") := by
  obtain ⟨ctx,ranges,st,info,built,scope,dominated,defined,mapped,source,data,type,safe⟩ :=
    LoadedPointerFixture.captured_loaded_pointer_context_witness
  exact ⟨ctx,ranges,st,built,defined,
    stock_loaded_pointer_address_zero_sunk data_program width ctx (cfg := {}) rfl defined source data type
      {st with sunk := #[false,false,false,false,true]} #[] 0 rfl⟩

end Backend.Stock.Memory.IntegerRoots
