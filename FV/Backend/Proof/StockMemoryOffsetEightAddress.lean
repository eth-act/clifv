import FV.Backend.Proof.StockMemoryIntegerAddress

namespace Backend.Stock.Memory.IntegerRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

private theorem stock_sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem stock_sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl
private theorem stock_sem_i64 (ctx : Ctx) :
    (Stock.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl
private theorem stock_sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem stock_sem_i32 (ctx : Ctx) :
    (Stock.sem ctx).prim 14 "I32" = some (.ty (.int 32)) := rfl

private theorem stock_sem_i8 (ctx : Ctx) :
    (Stock.sem ctx).prim 14 "I8" = some (.ty (.int 8)) := rfl
private theorem stock_sem_i16 (ctx : Ctx) :
    (Stock.sem ctx).prim 14 "I16" = some (.ty (.int 16)) := rfl

/-- A parameter pointer selects the real unsigned offset8 addressing rule;
The nonzero scaled-offset rule precedes the defining-instruction look-throughs. -/
theorem stock_parameter_amode_eight_width {p : Program} (hp : Data p) (width : Width) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {x nreg : Nat}
    (parameter : ctx.defInst? x = none) (mapped : ctx.valueReg? x = some (.vreg nreg .int))
    (st : State) (tr : Array RuleId) (n : Nat) :
    (applyTerm p (Stock.sem ctx) cfg (n + 60) 89 575 [.ty (.int width.bits),.value x,.int 8]).run (st,tr) =
      .ok (some (.data 89 VIdx.AMode.UnsignedOffset [.reg (.vreg nreg .int),.op (.uimm12Scaled 8)]),
        st.mark x,tr.push rule_inst_4103.id) := by
  have absent := fun q => ext_def_inst_none ctx q parameter
  have demanded := stock_put_in_reg ctx st x (.vreg nreg .int) mapped
    (by intro i impossible; rw [parameter] at impossible; cases impossible)
  have widen (s : State) : Stock.externCtor ctx T.i32_into_i64 [.int 8] s = .ok (.int 8,s) := by
    rw [stock_ctor_baseOnly ctx T.i32_into_i64 _ s (by decide)]
    rfl
  have scaled (s : State) : Stock.externCtor ctx T.uimm12_scaled_from_i64 [.int 8,.ty (.int width.bits)] s =
      .ok (.op (.uimm12Scaled 8),s) := by
    rw [stock_ctor_baseOnly ctx T.uimm12_scaled_from_i64 _ s (by decide)]
    cases width <;> rfl
  have nonzero (s : State) : Stock.externCtor ctx T.uimm12_scaled_nonzero_from_i64
      [.int 8,.ty (.int width.bits)] s = .ok (.op (.uimm12Scaled 8),s) := by
    rw [stock_ctor_baseOnly ctx T.uimm12_scaled_nonzero_from_i64 _ s (by decide)]
    cases width <;> rfl
  cases width <;> simp only [Width.bits] at * <;> cases hp <;>
    isel_eval [*,Width.bits,stock_sem_i8,stock_sem_i16,stock_sem_i64,stock_sem_ctor,stock_sem_mkData,stock_sem_extract,stock_sem_i32,
    rule_inst_4103,rule_inst_4096,rule_inst_4093,rule_inst_4083,rule_inst_4081,rule_inst_4079,
    rule_inst_4077,rule_inst_4075,rule_inst_4064,widen,scaled,nonzero]

/-- The outer address selector retains the parameter pointer and the actual
unsigned-offset choice, ruling out stack and constant-folded definitions. -/
theorem stock_parameter_load_address_eight_width {p : Program} (hp : Data p) (width : Width) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {x nreg : Nat}
    (parameter : ctx.defInst? x = none) (mapped : ctx.valueReg? x = some (.vreg nreg .int))
    (st : State) (tr : Array RuleId) (n : Nat) :
    (applyTerm p (Stock.sem ctx) cfg (n + 80) 89 574 [.ty (.int width.bits),.value x,.int 8]).run (st,tr) =
      .ok (some (.data 89 VIdx.AMode.UnsignedOffset [.reg (.vreg nreg .int),.op (.uimm12Scaled 8)]),
        st.mark x,(tr.push rule_inst_4103.id).push rule_inst_4038.id) := by
  have absent := fun q => ext_def_inst_none ctx q parameter
  have child := fun q trace fuel => stock_parameter_amode_eight_width hp width ctx hc parameter mapped q trace fuel
  cases width <;> simp only [Width.bits] at * <;> cases hp <;>
    isel_eval [*,Width.bits,stock_sem_i8,stock_sem_i16,stock_sem_i64,stock_sem_extract,rule_inst_4047,rule_inst_4043,rule_inst_4040,rule_inst_4038]

end Backend.Stock.Memory.IntegerRoots
