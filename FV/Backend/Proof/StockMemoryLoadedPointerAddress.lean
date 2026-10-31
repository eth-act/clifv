import FV.Backend.Proof.StockMemoryIntegerAddress

namespace Backend.Stock.Memory.IntegerRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
attribute [local irreducible] Isle.Aarch64.program

private theorem stock_sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem stock_sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl
private theorem stock_sem_i64 (ctx : Ctx) :
    (Stock.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl
private theorem stock_sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem stock_sem_unData (ctx : Ctx) (ty t k : Nat) (vs : List V) :
    (Stock.sem ctx).unData ty (.data t k vs) = if t = ty then some (k,vs) else none :=
  Backend.Proof.sem_unData ctx ty t k vs
private theorem stock_sem_i32 (ctx : Ctx) :
    (Stock.sem ctx).prim 14 "I32" = some (.ty (.int 32)) := rfl

private theorem stock_sem_i8 (ctx : Ctx) :
    (Stock.sem ctx).prim 14 "I8" = some (.ty (.int 8)) := rfl
private theorem stock_sem_i16 (ctx : Ctx) :
    (Stock.sem ctx).prim 14 "I16" = some (.ty (.int 16)) := rfl

private theorem loaded_pointer_rule_failure {p : Program} (hp : Data p) (ctx : Ctx)
    {x i sourcePointer : Nat} {info : IInfo} {flags : Clif.MemFlags} {loadOffset : Int}
    (defined : ctx.defInst? x = some i) (source : ctx.insts[i]? = some info)
    (data : info.data = .data 152 16 [.data 151 29 [],.value sourcePointer,.op (.memFlags flags),.int loadOffset])
    (type : info.resTys.head? = some (.int 64)) {rule : Rule}
    (member : rule ∈ [rule_inst_4096,rule_inst_4093,rule_inst_4083,rule_inst_4081,rule_inst_4079,
      rule_inst_4077,rule_inst_4075,rule_inst_4047,rule_inst_4043,rule_inst_4040])
    (ty : V) (st : State) :
    matchArgs p (Stock.sem ctx) st rule.args [ty,.value x,.int 0]
      (Array.replicate rule.vars.length none) = .ok none := by
  have definition := ext_def_inst_some ctx st.base defined
  have loaded := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at loaded
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cases hp
  all_goals isel_eval [*,rule_inst_4096,rule_inst_4093,rule_inst_4083,rule_inst_4081,rule_inst_4079,
    rule_inst_4077,rule_inst_4075,rule_inst_4047,rule_inst_4043,rule_inst_4040,stock_sem_extract,stock_sem_unData]

/-- A loaded pointer selects the actual zero-offset address without folding its definition. -/
theorem stock_loaded_pointer_amode_zero_width {p : Program} (hp : Data p) (width : Width) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {x nreg : Nat}
    {i sourcePointer : Nat} {info : IInfo} {flags : Clif.MemFlags} {loadOffset : Int}
    (defined : ctx.defInst? x = some i) (source : ctx.insts[i]? = some info)
    (data : info.data = .data 152 16 [.data 151 29 [],.value sourcePointer,.op (.memFlags flags),.int loadOffset])
    (type : info.resTys.head? = some (.int 64))
    (mapped : ctx.valueReg? x = some (.vreg nreg .int))
    (st : State) (tr : Array RuleId) (n : Nat) (safe : DemandAllowed ctx st x) :
    (applyTerm p (Stock.sem ctx) cfg (n + 60) 89 575 [.ty (.int width.bits),.value x,.int 0]).run (st,tr) =
      .ok (some (.data 89 VIdx.AMode.UnsignedOffset [.reg (.vreg nreg .int),.op (.uimm12Scaled 0)]),
        st.mark x,tr.push rule_inst_4064.id) := by
  have failure_4096 := fun q => loaded_pointer_rule_failure hp ctx
    defined source data type (rule := rule_inst_4096) (by simp) (.ty (.int width.bits)) q
  have failure_4093 := fun q => loaded_pointer_rule_failure hp ctx
    defined source data type (rule := rule_inst_4093) (by simp) (.ty (.int width.bits)) q
  have failure_4083 := fun q => loaded_pointer_rule_failure hp ctx
    defined source data type (rule := rule_inst_4083) (by simp) (.ty (.int width.bits)) q
  have failure_4081 := fun q => loaded_pointer_rule_failure hp ctx
    defined source data type (rule := rule_inst_4081) (by simp) (.ty (.int width.bits)) q
  have failure_4079 := fun q => loaded_pointer_rule_failure hp ctx
    defined source data type (rule := rule_inst_4079) (by simp) (.ty (.int width.bits)) q
  have failure_4077 := fun q => loaded_pointer_rule_failure hp ctx
    defined source data type (rule := rule_inst_4077) (by simp) (.ty (.int width.bits)) q
  have failure_4075 := fun q => loaded_pointer_rule_failure hp ctx
    defined source data type (rule := rule_inst_4075) (by simp) (.ty (.int width.bits)) q
  have demanded := stock_put_in_reg ctx st x (.vreg nreg .int) mapped safe
  have widen (s : State) : Stock.externCtor ctx T.i32_into_i64 [.int 0] s = .ok (.int 0,s) := by
    rw [stock_ctor_baseOnly ctx T.i32_into_i64 _ s (by decide)]
    rfl
  have scaled (s : State) : Stock.externCtor ctx T.uimm12_scaled_from_i64 [.int 0,.ty (.int width.bits)] s =
      .ok (.op (.uimm12Scaled 0),s) := by
    rw [stock_ctor_baseOnly ctx T.uimm12_scaled_from_i64 _ s (by decide)]
    cases width <;> rfl
  have nonzero (s : State) : Stock.externCtor ctx T.uimm12_scaled_nonzero_from_i64
      [.int 0,.ty (.int width.bits)] s = .fail := by
    rw [stock_ctor_baseOnly ctx T.uimm12_scaled_nonzero_from_i64 _ s (by decide)]
    cases width <;> rfl
  cases hp
  isel_eval [*,stock_sem_i8,stock_sem_i16,stock_sem_i64,stock_sem_ctor,stock_sem_mkData,stock_sem_extract,stock_sem_unData,stock_sem_i32,
    rule_inst_4103,rule_inst_4064,widen,scaled,nonzero]

/-- The outer address selector keeps the original loaded pointer and its zero offset. -/
theorem stock_loaded_pointer_address_zero_width {p : Program} (hp : Data p) (width : Width) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {x nreg : Nat}
    {i sourcePointer : Nat} {info : IInfo} {flags : Clif.MemFlags} {loadOffset : Int}
    (defined : ctx.defInst? x = some i) (source : ctx.insts[i]? = some info)
    (data : info.data = .data 152 16 [.data 151 29 [],.value sourcePointer,.op (.memFlags flags),.int loadOffset])
    (type : info.resTys.head? = some (.int 64))
    (mapped : ctx.valueReg? x = some (.vreg nreg .int))
    (st : State) (tr : Array RuleId) (n : Nat) (safe : DemandAllowed ctx st x) :
    (applyTerm p (Stock.sem ctx) cfg (n + 80) 89 574 [.ty (.int width.bits),.value x,.int 0]).run (st,tr) =
      .ok (some (.data 89 VIdx.AMode.UnsignedOffset [.reg (.vreg nreg .int),.op (.uimm12Scaled 0)]),
        st.mark x,(tr.push rule_inst_4064.id).push rule_inst_4038.id) := by
  have failure_4047 := fun q => loaded_pointer_rule_failure hp ctx
    defined source data type (rule := rule_inst_4047) (by simp) (.ty (.int width.bits)) q
  have failure_4043 := fun q => loaded_pointer_rule_failure hp ctx
    defined source data type (rule := rule_inst_4043) (by simp) (.ty (.int width.bits)) q
  have failure_4040 := fun q => loaded_pointer_rule_failure hp ctx
    defined source data type (rule := rule_inst_4040) (by simp) (.ty (.int width.bits)) q
  have child := fun trace fuel => stock_loaded_pointer_amode_zero_width hp width ctx hc
    defined source data type mapped st trace fuel safe
  cases hp
  isel_eval [*,stock_sem_i8,stock_sem_i16,stock_sem_i64,stock_sem_extract,stock_sem_unData,rule_inst_4038]

/-- An already sunk loaded pointer makes the fallback address request fail. -/
private theorem loaded_pointer_amode_zero_sunk {p : Program} (hp : Data p) (width : Width) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {x : Nat}
    {i sourcePointer : Nat} {info : IInfo} {flags : Clif.MemFlags} {loadOffset : Int}
    (defined : ctx.defInst? x = some i) (source : ctx.insts[i]? = some info)
    (data : info.data = .data 152 16 [.data 151 29 [],.value sourcePointer,.op (.memFlags flags),.int loadOffset])
    (type : info.resTys.head? = some (.int 64))
    (st : State) (tr : Array RuleId) (n : Nat) (sunk : st.sunk[i]! = true) :
    (applyTerm p (Stock.sem ctx) cfg (n + 60) 89 575 [.ty (.int width.bits),.value x,.int 0]).run (st,tr) =
      .error (.unmodeled s!"demand for sunk instruction {i}") := by
  have failure_4096 := fun q => loaded_pointer_rule_failure hp ctx
    defined source data type (rule := rule_inst_4096) (by simp) (.ty (.int width.bits)) q
  have failure_4093 := fun q => loaded_pointer_rule_failure hp ctx
    defined source data type (rule := rule_inst_4093) (by simp) (.ty (.int width.bits)) q
  have failure_4083 := fun q => loaded_pointer_rule_failure hp ctx
    defined source data type (rule := rule_inst_4083) (by simp) (.ty (.int width.bits)) q
  have failure_4081 := fun q => loaded_pointer_rule_failure hp ctx
    defined source data type (rule := rule_inst_4081) (by simp) (.ty (.int width.bits)) q
  have failure_4079 := fun q => loaded_pointer_rule_failure hp ctx
    defined source data type (rule := rule_inst_4079) (by simp) (.ty (.int width.bits)) q
  have failure_4077 := fun q => loaded_pointer_rule_failure hp ctx
    defined source data type (rule := rule_inst_4077) (by simp) (.ty (.int width.bits)) q
  have failure_4075 := fun q => loaded_pointer_rule_failure hp ctx
    defined source data type (rule := rule_inst_4075) (by simp) (.ty (.int width.bits)) q
  have demanded : Stock.externCtor ctx T.put_in_reg [.value x] st =
      .unmodeled s!"demand for sunk instruction {i}" := by
    simp [Stock.externCtor,T.put_in_reg,defined,sunk]
  have widen (s : State) : Stock.externCtor ctx T.i32_into_i64 [.int 0] s = .ok (.int 0,s) := by
    rw [stock_ctor_baseOnly ctx T.i32_into_i64 _ s (by decide)]
    rfl
  have scaled (s : State) : Stock.externCtor ctx T.uimm12_scaled_from_i64 [.int 0,.ty (.int width.bits)] s =
      .ok (.op (.uimm12Scaled 0),s) := by
    rw [stock_ctor_baseOnly ctx T.uimm12_scaled_from_i64 _ s (by decide)]
    cases width <;> rfl
  have nonzero (s : State) : Stock.externCtor ctx T.uimm12_scaled_nonzero_from_i64
      [.int 0,.ty (.int width.bits)] s = .fail := by
    rw [stock_ctor_baseOnly ctx T.uimm12_scaled_nonzero_from_i64 _ s (by decide)]
    cases width <;> rfl
  cases hp
  isel_eval [*,stock_sem_i8,stock_sem_i16,stock_sem_i64,stock_sem_ctor,stock_sem_mkData,stock_sem_extract,stock_sem_unData,stock_sem_i32,
    rule_inst_4103,rule_inst_4064,widen,scaled,nonzero]

/-- The actual address helper rejects a sunk loaded pointer without a runtime certificate. -/
theorem stock_loaded_pointer_address_zero_sunk {p : Program} (hp : Data p) (width : Width) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {x : Nat}
    {i sourcePointer : Nat} {info : IInfo} {flags : Clif.MemFlags} {loadOffset : Int}
    (defined : ctx.defInst? x = some i) (source : ctx.insts[i]? = some info)
    (data : info.data = .data 152 16 [.data 151 29 [],.value sourcePointer,.op (.memFlags flags),.int loadOffset])
    (type : info.resTys.head? = some (.int 64))
    (st : State) (tr : Array RuleId) (n : Nat) (sunk : st.sunk[i]! = true) :
    (applyTerm p (Stock.sem ctx) cfg (n + 80) 89 574 [.ty (.int width.bits),.value x,.int 0]).run (st,tr) =
      .error (.unmodeled s!"demand for sunk instruction {i}") := by
  have failure_4047 := fun q => loaded_pointer_rule_failure hp ctx
    defined source data type (rule := rule_inst_4047) (by simp) (.ty (.int width.bits)) q
  have failure_4043 := fun q => loaded_pointer_rule_failure hp ctx
    defined source data type (rule := rule_inst_4043) (by simp) (.ty (.int width.bits)) q
  have failure_4040 := fun q => loaded_pointer_rule_failure hp ctx
    defined source data type (rule := rule_inst_4040) (by simp) (.ty (.int width.bits)) q
  have child := fun trace fuel => loaded_pointer_amode_zero_sunk hp width ctx hc
    defined source data type st trace fuel sunk
  cases hp
  isel_eval [*,stock_sem_i8,stock_sem_i16,stock_sem_i64,stock_sem_extract,stock_sem_unData,rule_inst_4038]

end Backend.Stock.Memory.IntegerRoots
