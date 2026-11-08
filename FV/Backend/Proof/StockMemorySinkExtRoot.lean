import FV.Backend.Proof.StockMemoryExtLoadSelection
import FV.Backend.Proof.StockSinkProvenance
import FV.Backend.Proof.StockCastBaseValues

/-! Stock's `uextend_load`/`sextend_load` roots (rules 815/824) on an extension
whose operand is the single result of an original plain load. The match binds the
load's own type, pointer, flags and offset; the right-hand side sinks the load and
emits one extending load from the load's address. Rule 810 does the same for an
extension of an `atomic_load` result: it emits one acquiring load (`Source`). -/
namespace Backend.Stock.Memory.SinkExtend
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Memory.ExtendedRoots (Kind)
open Backend.Stock.Proof.MemoryHelpers
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

/-- Sign of the extension that a sunk load implements. -/
def signed : Kind → Bool
  | .signed8 | .signed16 | .signed32 => true
  | .unsigned8 | .unsigned16 | .unsigned32 => false

/-- Type of the original plain load. -/
def loadTy : Kind → Clif.Ty
  | .unsigned8 | .signed8 => .i8
  | .unsigned16 | .signed16 => .i16
  | .unsigned32 | .signed32 => .i32

/-- The extension opcode of the consumer. -/
def extendOp (kind : Kind) : Clif.ExtendOp := ScalarCast.extendOp (signed kind)

/-- The root that sinks the load into its extension. -/
def root (kind : Kind) : Rule := if signed kind then rule_lower_1359 else rule_lower_1300

/-- The type dispatch of `aarch64_uload`/`aarch64_sload` for the load type. -/
def dispatch : Kind → Rule
  | .unsigned8 => rule_lower_1307 | .unsigned16 => rule_lower_1308 | .unsigned32 => rule_lower_1309
  | .signed8 => rule_lower_1366 | .signed16 => rule_lower_1367 | .signed32 => rule_lower_1368

/-- Encoded consumer opcode (`Uextend`/`Sextend`). -/
def extendTag (kind : Kind) : Nat := ScalarCast.extendOpcode (signed kind)

/-- The bound environment of a matched sink root. -/
abbrev rootEnv (bits x y j : Nat) (flags : Clif.MemFlags) : Isle.Interp.Env V :=
  ((((((Array.replicate 7 none).setIfInBounds 4 (some (V.value y))).setIfInBounds 0
    (some (V.ty (CTy.int bits)))).setIfInBounds 1 (some (V.value x))).setIfInBounds 2
    (some (V.op (.memFlags flags)))).setIfInBounds 3 (some (V.int 0))).setIfInBounds 5
    (some (V.inst j))

private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (ty t k : Nat) (fs : List V) :
    (Stock.sem ctx).unData ty (.data t k fs) = if t = ty then some (k,fs) else none :=
  Backend.Proof.sem_unData ctx ty t k fs
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_i8 (ctx : Ctx) : (Stock.sem ctx).prim 14 "I8" = some (.ty (.int 8)) := rfl
private theorem sem_i16 (ctx : Ctx) : (Stock.sem ctx).prim 14 "I16" = some (.ty (.int 16)) := rfl
private theorem sem_i32 (ctx : Ctx) : (Stock.sem ctx).prim 14 "I32" = some (.ty (.int 32)) := rfl
private theorem sem_i64 (ctx : Ctx) : (Stock.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl
private theorem sem_mkData (ctx : Ctx) (ty tag : Nat) (args : List V) :
    (Stock.sem ctx).mkData ty tag args = .data ty tag args := rfl

/-- The sink root matches an extension of an eligible plain-load result. The match
retains the scheduling state and binds the load's type, pointer, flags and offset. -/
theorem stock_match_sink_extend {p : Program} (hp : Data p) (kind : Kind) (ctx : Ctx) {cfg : Config}
    {i j x y w : Nat} {info load : IInfo} {flags : Clif.MemFlags}
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w)) (fits : w ≤ 64)
    (data : info.data = .data 152 29 [.data 151 (extendTag kind) [],.value y])
    (defined : ctx.defInst? y = some j) (loaded : ctx.insts[j]? = some load)
    (loadType : load.resTys.head? = some (.int (loadTy kind).width))
    (loadData : load.data = .data 152 16 [.data 151 29 [],.value x,.op (.memFlags flags),.int 0])
    (little : flags.endianness ≠ some .big) (st : State)
    (eligible : Stock.source ctx st y = some (j,true)) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) cfg (n+5) (root kind) [.inst i]).run (st,tr) =
      .ok (some (rootEnv (loadTy kind).width x y j flags),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  have inner := ext_inst_data_value ctx st.base loaded
  rw [loadData,loadType,Option.getD_some] at inner
  have definition := ext_def_inst_some ctx st.base defined
  have size := ext_fits_in_64' ctx st.base (.int w)
  have endian := (ext_little_or_native_endian_iff ctx st.base flags [.op (.memFlags flags)]).mpr ⟨little,rfl⟩
  have sinkable : Stock.externCtor ctx T.is_sinkable_inst [.value y] st = .ok (.inst j,st) := by
    change (match Stock.source ctx st y with
      | some (j,true) => ExtResult.ok (V.inst j,st)
      | _ => ExtResult.fail) = _
    rw [eligible]
  have bits : CTy.bits (.int w) = w := rfl
  simp only [bits,fits,decide_true,ite_true] at size
  cases kind <;> simp only [root,signed,extendTag,ScalarCast.extendOpcode,loadTy,Clif.Ty.width] at * <;> cases hp <;>
    isel_eval [*,rule_lower_1300,rule_lower_1359,sem_extract,sem_unData,sem_eq,sem_ctor]

private theorem output_run {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (st : State) (tr : Array RuleId) (n : Nat) (r : Reg) :
    (applyTerm p (Stock.sem ctx) cfg (n+10) 25 172 [.reg r]).run (st,tr) =
      .ok (some (.regsVec [[r]]),st,tr.push rule_prelude_lower_105.id) := by
  have value : ∀ q,Stock.externCtor ctx T.value_reg [.reg r] q = .ok (.regs [r],q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.value_reg _ q (by decide)]; rfl
  have output : ∀ q,Stock.externCtor ctx T.output [.regs [r]] q = .ok (.regsVec [[r]],q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.output _ q (by decide)]; rfl
  cases hp
  isel_eval [*,rule_prelude_lower_105,sem_ctor]

/-- The state after the root sinks the load at `j`. -/
abbrev sunkState (st : State) (j : Nat) : State :=
  { st with color := some st.entryColor[j]!, sunk := st.sunk.set! j true }

/-- The sink root's right-hand side sinks the load, records the pointer demand and
emits the extending load from the load's own address into one fresh register. -/
theorem stock_sink_extend_rhs {p : Program} (hp : Data p) (kind : Kind) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {j x y nreg : Nat}
    (parameter : ctx.defInst? x = none) (mapped : ctx.valueReg? x = some (.vreg nreg .int))
    (flags : Clif.MemFlags) (st : State)
    (sink : Stock.externCtor ctx T.sink_inst [.inst j] st = .ok (.op .unit,sunkState st j))
    (tr : Array RuleId) (n : Nat) :
    ∃ trace,(evalExpr p (Stock.sem ctx) cfg (n+120) (root kind).rhs
      (rootEnv (loadTy kind).width x y j flags)).run (st,tr) =
        .ok (some (.regsVec [[(st.base.fresh .int).1]]),
          {((sunkState st j).mark x) with base := ((st.base.fresh .int).2.emit
            (.load kind.loadOp (st.base.fresh .int).1 (.unsignedOffset (.vreg nreg .int) 0) flags))},trace) := by
  have address := fun q trace fuel =>
    IntegerRoots.stock_parameter_load_address_width hp kind.width ctx hc parameter mapped q trace fuel
  have load := fun q trace fuel => integer_load_forward kind.helper hp ctx hc q trace fuel
    (.data 89 VIdx.AMode.UnsignedOffset [.reg (.vreg nreg .int),.op (.uimm12Scaled 0)])
    (.op (.memFlags flags))
    (.load kind.loadOp (q.base.fresh .int).1 (.unsignedOffset (.vreg nreg .int) 0) flags)
    (by cases kind <;> rfl)
  have output := fun q trace fuel r => output_run hp ctx hc q trace fuel r
  have offset (q : State) : Stock.externCtor ctx T.offset32_to_i32 [.int 0] q =
      .ok (.int 0,q) := by
    rw [stock_ctor_baseOnly ctx T.offset32_to_i32 _ q (by decide)]
    rfl
  have t16 : (V.ty (CTy.int 16) == V.ty (CTy.int 8)) = false := by decide
  have t32 : (V.ty (CTy.int 32) == V.ty (CTy.int 8)) = false := by decide
  have t32' : (V.ty (CTy.int 32) == V.ty (CTy.int 16)) = false := by decide
  refine ⟨((((tr.push rule_inst_4064.id).push rule_inst_4038.id).push kind.helper.ruleId).push
    (dispatch kind).id).push rule_prelude_lower_105.id,?_⟩
  cases kind <;> simp only [Kind.width,IntegerRoots.Width.bits,Kind.helper,Kind.loadOp,root,signed,
    loadTy,Clif.Ty.width,IntegerLoad.term,IntegerLoad.ruleId,dispatch] at * <;> cases hp <;>
    isel_eval [*,rule_lower_1300,rule_lower_1359,rule_lower_1307,rule_lower_1308,rule_lower_1309,
      rule_lower_1366,rule_lower_1367,rule_lower_1368,sem_ctor,sem_eq,sem_i8,sem_i16,sem_i32,sem_i64] <;> rfl

/-- A successful right-hand side has executed its leading sink: Stock's sink of
the load succeeded from the matched state. -/
theorem stock_sink_extend_rhs_sinks (kind : Kind) (ctx : Ctx) {bits x y j : Nat}
    {flags : Clif.MemFlags} {st next : State} {tr tr' : Array RuleId} {out : V} {n : Nat}
    (run : (evalExpr program (Stock.sem ctx) {} (n+8) (root kind).rhs
      (rootEnv bits x y j flags)).run (st,tr) = .ok (some out,next,tr')) :
    Stock.externCtor ctx T.sink_inst [.inst j] st = .ok (.op .unit,sunkState st j) := by
  have shape : ∃ body,(root kind).rhs = .let 25 [(6,13,.term 13 236 [.var 18 5])] body := by
    cases kind <;> exact ⟨_,rfl⟩
  obtain ⟨body,shape⟩ := shape
  rw [shape,evalExpr.eq_6,evalBinds.eq_3] at run
  simp only [evalExpr.eq_7,evalArgs.eq_3,evalExpr.eq_2,evalArgs.eq_2,isel_monad,applyTerm.eq_2,
    data_program.t236,T.sink_inst,Stock.sem] at run
  cases call : Stock.externCtor ctx T.sink_inst [.inst j] st with
  | fail => simp only [T.sink_inst] at call; rw [call] at run; simp only [isel_monad] at run; cases run
  | unmodeled e => simp only [T.sink_inst] at call; rw [call] at run; simp only [isel_monad] at run; cases run
  | ok pair =>
    obtain ⟨v,s⟩ := pair
    obtain ⟨_,_,_,unit,state⟩ := sink_accepted call
    subst unit
    subst state
    rfl

/-! ## The source load

Rule 810 (`lower.isle` 1272) folds an extension of an `atomic_load` result in the same way
as rules 815/824 fold a plain load: the extension sinks the atomic load and emits one
acquiring load (`ldarb`/`ldarh`/`ldar w`), which zero-extends. -/

/-- The original load whose single result the extension consumes. -/
inductive Source where
  /-- A plain `load` at offset zero (rules 815/824). -/
  | plain
  /-- An `atomic_load` (rule 810, zero extensions only). -/
  | acquire
  deriving DecidableEq

/-- The original load instruction of `ty` through the pointer `x`. -/
def Source.load : Source → Clif.Ty → Clif.MemFlags → Nat → Clif.Inst
  | .plain,ty,flags,x => .load .load ty flags x 0
  | .acquire,ty,flags,x => .atomicLoad ty flags x

/-- The extensions that a source admits: rule 810 folds only zero extensions. -/
def Source.admits : Source → Kind → Bool
  | .plain,_ => true
  | .acquire,kind => !signed kind

/-- The root that folds the source load into its extension. -/
def Source.root : Source → Kind → Rule
  | .plain,kind => SinkExtend.root kind
  | .acquire,_ => rule_lower_1272

/-- The one instruction that the root emits into `dst` through the pointer vreg `nreg`. -/
def Source.emitted : Source → Kind → Reg → Nat → Clif.MemFlags → MInst
  | .plain,kind,dst,nreg,flags => .load kind.loadOp dst (.unsignedOffset (.vreg nreg .int) 0) flags
  | .acquire,kind,dst,nreg,flags => .loadAcquire (.int (loadTy kind).width) dst (.vreg nreg .int) flags

/-- The bound environment of a matched rule 810: the result type, the extended value,
its type, the atomic load's flags and the atomic load itself. -/
abbrev acquireEnv (w bits y j : Nat) (flags : Clif.MemFlags) : Isle.Interp.Env V :=
  (((((Array.replicate 5 none).setIfInBounds 0 (some (V.ty (CTy.int w)))).setIfInBounds 3
    (some (V.value y))).setIfInBounds 1 (some (V.ty (CTy.int bits)))).setIfInBounds 2
    (some (V.op (.memFlags flags)))).setIfInBounds 4 (some (V.inst j))

/-- Rule 810 matches a zero extension of an eligible atomic-load result. The match
retains the scheduling state and binds the operand's type and the load's flags. -/
theorem stock_match_acquire_extend {p : Program} (hp : Data p) (kind : Kind) (ctx : Ctx)
    {cfg : Config} {i j x y w : Nat} {info load : IInfo} {flags : Clif.MemFlags}
    (unsigned : signed kind = false)
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w)) (fits : w ≤ 64)
    (data : info.data = .data 152 29 [.data 151 (extendTag kind) [],.value y])
    (typed : ctx.valueType? y = some (.int (loadTy kind).width))
    (defined : ctx.defInst? y = some j) (loaded : ctx.insts[j]? = some load)
    (loadData : load.data = .data 152 17 [.data 151 158 [],.value x,.op (.memFlags flags)])
    (little : flags.endianness ≠ some .big) (st : State)
    (eligible : Stock.source ctx st y = some (j,true)) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) cfg (n+5) rule_lower_1272 [.inst i]).run (st,tr) =
      .ok (some (acquireEnv w (loadTy kind).width y j flags),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  have inner := ext_inst_data_value ctx st.base loaded
  rw [loadData] at inner
  have definition := ext_def_inst_some ctx st.base defined
  have valueType := ext_value_type ctx st.base typed
  have size := ext_fits_in_64' ctx st.base (.int w)
  have endian := (ext_little_or_native_endian_iff ctx st.base flags [.op (.memFlags flags)]).mpr ⟨little,rfl⟩
  have sinkable : Stock.externCtor ctx T.is_sinkable_inst [.value y] st = .ok (.inst j,st) := by
    change (match Stock.source ctx st y with
      | some (j,true) => ExtResult.ok (V.inst j,st)
      | _ => ExtResult.fail) = _
    rw [eligible]
  have bits : CTy.bits (.int w) = w := rfl
  simp only [bits,fits,decide_true,ite_true] at size
  cases kind <;> simp only [signed,Bool.true_eq_false] at unsigned <;>
    simp only [signed,extendTag,ScalarCast.extendOpcode,loadTy,Clif.Ty.width] at * <;> cases hp <;>
    isel_eval [*,rule_lower_1272,sem_extract,sem_unData,sem_eq,sem_ctor]

/-- The `load_acquire` helper allocates one fresh register and emits one acquiring load
of `bits` from the pointer vreg; every scheduling field is unchanged. -/
theorem acquire_helper_forward {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (overlap : cfg.checkOverlap = false) (st : State) (trace : Array RuleId) (fuel bits nreg : Nat)
    (flags : Clif.MemFlags) :
    (applyTerm p (Stock.sem ctx) cfg (fuel+20) 27 422
      [.ty (.int bits),.op (.memFlags flags),.reg (.vreg nreg .int)]).run (st,trace) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := ((st.base.fresh .int).2.emit
          (.loadAcquire (.int bits) (st.base.fresh .int).1 (.vreg nreg .int) flags))},
        trace.push rule_inst_3028.id) := by
  have temp (s : State) : Stock.externCtor ctx T.temp_writable_reg [.ty (.int 64)] s =
      .ok (.reg (s.base.fresh .int).1,{s with base := (s.base.fresh .int).2}) := rfl
  have reg (r : Reg) (s : State) : Stock.externCtor ctx T.writable_reg_to_reg [.reg r] s =
      .ok (.reg r,s) := rfl
  have emit (s : State) : Stock.externCtor ctx T.emit
      [.data 58 42 [.ty (.int bits),.reg (st.base.fresh .int).1,.reg (.vreg nreg .int),
        .op (.memFlags flags)]] s =
        .ok (.op .unit,{s with base := (s.base.emit
          (.loadAcquire (.int bits) (st.base.fresh .int).1 (.vreg nreg .int) flags))}) := by
    rw [stock_ctor_baseOnly ctx T.emit _ s (by decide)]
    rfl
  cases hp
  isel_eval [*,rule_inst_3028,sem_ctor,sem_mkData,sem_i64,temp,reg,emit]

/-- `sink_atomic_load` on an installed atomic load through a parameter pointer sinks the
load and returns the pointer's register, marking the pointer demanded. -/
theorem sink_atomic_load_forward {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (overlap : cfg.checkOverlap = false) {j x nreg : Nat} {load : IInfo} {flags : Clif.MemFlags} (loaded : ctx.insts[j]? = some load)
    (loadData : load.data = .data 152 17 [.data 151 158 [],.value x,.op (.memFlags flags)])
    (parameter : ctx.defInst? x = none) (mapped : ctx.valueReg? x = some (.vreg nreg .int))
    (st : State) (sink : Stock.externCtor ctx T.sink_inst [.inst j] st = .ok (.op .unit,sunkState st j))
    (trace : Array RuleId) (fuel : Nat) :
    (applyTerm p (Stock.sem ctx) cfg (fuel+20) 27 564 [.inst j]).run (st,trace) =
      .ok (some (.reg (.vreg nreg .int)),(sunkState st j).mark x,trace.push rule_inst_3905.id) := by
  have inner := ext_inst_data_value ctx st.base loaded
  rw [loadData] at inner
  have demanded := stock_put_in_reg ctx (sunkState st j) x (.vreg nreg .int) mapped
    (by intro i impossible; rw [parameter] at impossible; cases impossible)
  cases hp
  isel_eval [*,rule_inst_3905,sem_extract,sem_unData,sem_eq,sem_ctor]

/-- Rule 810's right-hand side sinks the atomic load, demands the pointer and emits one
acquiring load from the pointer's register into one fresh register. -/
theorem stock_acquire_extend_rhs {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {j x y nreg w bits : Nat} {load : IInfo} {flags : Clif.MemFlags}
    (loaded : ctx.insts[j]? = some load)
    (loadData : load.data = .data 152 17 [.data 151 158 [],.value x,.op (.memFlags flags)])
    (parameter : ctx.defInst? x = none) (mapped : ctx.valueReg? x = some (.vreg nreg .int))
    (st : State) (sink : Stock.externCtor ctx T.sink_inst [.inst j] st = .ok (.op .unit,sunkState st j))
    (tr : Array RuleId) (n : Nat) :
    (evalExpr p (Stock.sem ctx) cfg (n+120) rule_lower_1272.rhs (acquireEnv w bits y j flags)).run (st,tr) =
      .ok (some (.regsVec [[(st.base.fresh .int).1]]),
        {((sunkState st j).mark x) with base := ((st.base.fresh .int).2.emit
          (.loadAcquire (.int bits) (st.base.fresh .int).1 (.vreg nreg .int) flags))},
        ((tr.push rule_inst_3905.id).push rule_inst_3028.id).push rule_prelude_lower_105.id) := by
  have sunk := fun q fuel => sink_atomic_load_forward hp ctx hc loaded loadData parameter mapped st sink q fuel
  have acquire := fun q trace fuel => acquire_helper_forward hp ctx hc q trace fuel bits nreg flags
  have output := fun q trace fuel r => output_run hp ctx hc q trace fuel r
  cases hp
  isel_eval [*,rule_lower_1272,sem_ctor] <;> rfl

/-- A successful rule-810 right-hand side has executed its sink of the atomic load:
Stock's sink of the load succeeded from the matched state. -/
theorem stock_acquire_extend_rhs_sinks {ctx : Ctx} {j x y w bits : Nat} {load : IInfo}
    {flags : Clif.MemFlags} (loaded : ctx.insts[j]? = some load)
    (loadData : load.data = .data 152 17 [.data 151 158 [],.value x,.op (.memFlags flags)])
    {st next : State} {tr tr' : Array RuleId} {out : V} {n : Nat}
    (run : (evalExpr program (Stock.sem ctx) {} (n+40) rule_lower_1272.rhs
      (acquireEnv w bits y j flags)).run (st,tr) = .ok (some out,next,tr')) :
    Stock.externCtor ctx T.sink_inst [.inst j] st = .ok (.op .unit,sunkState st j) := by
  rw [sink_ctor_eq]
  split
  · rename_i bad
    exfalso
    have failed : Stock.externCtor ctx T.sink_inst [.inst j] st =
        .unmodeled s!"invalid sink of instruction {j}" := by
      simp only [sink_ctor_eq,bad,ite_true]
    have inner := ext_inst_data_value ctx st.base loaded
    rw [loadData] at inner
    have hp := data_program
    cases hp
    revert run
    isel_eval [*,rule_lower_1272,rule_inst_3905,sem_ctor,sem_extract,sem_unData,sem_eq]
    intro impossible
    cases impossible
  · rfl

end Backend.Stock.Memory.SinkExtend
