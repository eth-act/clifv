import FV.Backend.Proof.StockMemorySelection

namespace Backend.Stock.Memory
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

/-- A parameter pointer selects the real unsigned zero-offset addressing rule;
all higher-priority defining-instruction look-throughs fail internally. -/
theorem stock_parameter_amode_zero {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {x nreg : Nat}
    (parameter : ctx.defInst? x = none) (mapped : ctx.valueReg? x = some (.vreg nreg .int))
    (st : State) (tr : Array RuleId) (n : Nat) :
    (applyTerm p (Stock.sem ctx) cfg (n + 60) 89 575 [.ty (.int 32),.value x,.int 0]).run (st,tr) =
      .ok (some (.data 89 VIdx.AMode.UnsignedOffset [.reg (.vreg nreg .int),.op (.uimm12Scaled 0)]),
        st.mark x,tr.push rule_inst_4064.id) := by
  have absent := fun q => ext_def_inst_none ctx q parameter
  have demanded := stock_put_in_reg ctx st x (.vreg nreg .int) mapped
    (by intro i impossible; rw [parameter] at impossible; cases impossible)
  have widen (s : State) : Stock.externCtor ctx T.i32_into_i64 [.int 0] s = .ok (.int 0,s) := by
    rw [stock_ctor_baseOnly ctx T.i32_into_i64 _ s (by decide)]
    rfl
  have scaled (s : State) : Stock.externCtor ctx T.uimm12_scaled_from_i64 [.int 0,.ty (.int 32)] s =
      .ok (.op (.uimm12Scaled 0),s) := by
    rw [stock_ctor_baseOnly ctx T.uimm12_scaled_from_i64 _ s (by decide)]
    rfl
  have nonzero (s : State) : Stock.externCtor ctx T.uimm12_scaled_nonzero_from_i64
      [.int 0,.ty (.int 32)] s = .fail := by
    rw [stock_ctor_baseOnly ctx T.uimm12_scaled_nonzero_from_i64 _ s (by decide)]
    rfl
  cases hp
  isel_eval [*,stock_sem_ctor,stock_sem_mkData,stock_sem_extract,stock_sem_i32,
    rule_inst_4103,rule_inst_4096,rule_inst_4093,rule_inst_4083,rule_inst_4081,rule_inst_4079,
    rule_inst_4077,rule_inst_4075,rule_inst_4064,widen,scaled,nonzero]

/-- The outer address selector retains the parameter pointer and the actual
unsigned-offset choice, ruling out stack and constant-folded definitions. -/
theorem stock_parameter_load_address {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {x nreg : Nat}
    (parameter : ctx.defInst? x = none) (mapped : ctx.valueReg? x = some (.vreg nreg .int))
    (st : State) (tr : Array RuleId) (n : Nat) :
    (applyTerm p (Stock.sem ctx) cfg (n + 80) 89 574 [.ty (.int 32),.value x,.int 0]).run (st,tr) =
      .ok (some (.data 89 VIdx.AMode.UnsignedOffset [.reg (.vreg nreg .int),.op (.uimm12Scaled 0)]),
        st.mark x,(tr.push rule_inst_4064.id).push rule_inst_4038.id) := by
  have absent := fun q => ext_def_inst_none ctx q parameter
  have child := fun q trace fuel => stock_parameter_amode_zero hp ctx hc parameter mapped q trace fuel
  cases hp
  isel_eval [*,stock_sem_extract,rule_inst_4047,rule_inst_4043,rule_inst_4040,rule_inst_4038]

end Backend.Stock.Memory
