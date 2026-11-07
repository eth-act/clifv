import FV.Backend.Proof.StockMemorySinkExtRecord
import FV.Backend.Proof.LowerDecide

/-! Non-vacuity on Cranelift's `load-extends.clif` filetest functions
`%load_uextend_i8_i32` and `%load_sextend_i16_i64`: their default (trapping) loads
inhabit the source class, the original-scope Stock driver succeeds, and the
whole-driver sink step applies with rule 815 or 824. The same holds for the
`atomic_load.clif` functions `%atomic_load_i8_i64` and `%atomic_load_i32_i64` with
rule 810: the atomic load is sunk into one acquiring load. -/
namespace Backend.Stock.Memory.SinkExtend
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Memory.ExtendedRoots (Kind)
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.lower

/-- The filetest block: `v1 = <load>.<in> v0; v2 = <op>.<out> v1; return v2`. -/
private def block (src : Source) (kind : Kind) (out : Clif.Ty) : Clif.Block :=
  { id := 0, params := [(0,.i64)],
    body := [⟨[1],src.load (loadTy kind) {} 0⟩,⟨[2],.extend (extendOp kind) out 1⟩],
    term := .ret [2] }

/-- The filetest function with signature `(i64) -> <out>`. -/
private def fixture (src : Source) (kind : Kind) (out : Clif.Ty) : Clif.Function :=
  { name := "load_extend",
    sig := { params := [⟨.i64,.none,.normal⟩], returns := [⟨out,.none,.normal⟩] },
    blocks := [block src kind out] }

private def lowers (src : Source) (kind : Kind) (out : Clif.Ty) : Bool :=
  match Stock.lower (fixture src kind out) with
  | .ok result => result.blockScans.size == 1
  | .error _ => false

section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.lower
private theorem lowers_uextend : lowers .plain .unsigned8 .i32 = true := by decide +kernel
private theorem lowers_sextend : lowers .plain .signed16 .i64 = true := by decide +kernel
private theorem lowers_acquire8 : lowers .acquire .unsigned8 .i64 = true := by decide +kernel
private theorem lowers_acquire32 : lowers .acquire .unsigned32 .i64 = true := by decide +kernel
private theorem scope_uextend : lowerScopeB (fixture .plain .unsigned8 .i32) = true := by decide +kernel
private theorem scope_sextend : lowerScopeB (fixture .plain .signed16 .i64) = true := by decide +kernel
private theorem scope_acquire8 : lowerScopeB (fixture .acquire .unsigned8 .i64) = true := by decide +kernel
private theorem scope_acquire32 : lowerScopeB (fixture .acquire .unsigned32 .i64) = true := by
  decide +kernel
end Kernel

private theorem dominated (src : Source) (kind : Kind) (out : Clif.Ty) :
    Dominated (fixture src kind out) := by
  constructor
  · change ([0,1,2] : List Nat).Nodup; decide
  · intro ctx ranges st build bi b found
    have bound : bi < 1 := by have h := lt_of_getElem? found; simpa [fixture] using h
    have zero : bi = 0 := by omega
    subst bi
    simp [fixture] at found
    subst b
    constructor
    · intro j stm present
      cases j with
      | zero =>
        simp [block] at present
        subst stm
        intro x member
        have zero : x = 0 := by cases src <;> simpa [Source.load,Driver.instArgs] using member
        subst x
        simp [availOf,fixture,block,defsBefore,defsFrom]
      | succ j =>
        cases j with
        | zero =>
          simp [block] at present
          subst stm
          intro x member
          have one : x = 1 := by simpa [Driver.instArgs] using member
          subst x
          simp [availOf,fixture,block,defsBefore,defsFrom]
        | succ j => simp [block] at present
    · intro x member
      have two : x = 2 := by
        simpa [abiTerm,Driver.termArgs,sretRet,sigRets,fixture,block] using member
      subst x
      simp [availOf,fixture,block,defsBefore,defsFrom]
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := fixture src kind out) (ctx := ctx) (gn := id)).cand tl x available
    have length : (fixture src kind out).blocks.length = 1 := rfl
    omega

private theorem shape (kind : Kind) (out : Clif.Ty) (small : narrow out = true) :
    Shape kind (fixture .plain kind out) (block .plain kind out) 0 1 2 out {} :=
  ⟨rfl,rfl,rfl,small,by simp [block],by simp [fixture,sigRets]⟩

private theorem acquireShape (kind : Kind) (out : Clif.Ty) (small : narrow out = true)
    (unsigned : signed kind = false) :
    SourceShape .acquire kind (fixture .acquire kind out) (block .acquire kind out) 0 1 2 out {} :=
  ⟨rfl,rfl,rfl,small,by simp [block],by simp [fixture,sigRets],by simp [Source.admits,unsigned]⟩

private theorem instance_of (src : Source) (kind : Kind) (out : Clif.Ty)
    (lowered : lowers src kind out = true) (scope : lowerScopeB (fixture src kind out) = true) :
    ∃ (result : Result) (event : BlockScanEvent),
      Stock.lower (fixture src kind out) = .ok result ∧ LowerScope (fixture src kind out) ∧
      Dominated (fixture src kind out) ∧ event ∈ result.blockScans.toList := by
  unfold lowers at lowered
  cases run : Stock.lower (fixture src kind out) with
  | error e => rw [run] at lowered; cases lowered
  | ok result =>
    rw [run] at lowered
    have size : result.blockScans.size = 1 := by simpa using lowered
    exact ⟨result,result.blockScans[0],rfl,lowerScope_of scope,dominated src kind out,
      Array.mem_toList_iff.mpr (Array.getElem_mem (by omega))⟩

/-- `%load_uextend_i8_i32`: the actual original-scope driver selects rule 815,
emits one `ldrb`-style unsigned 8-bit load and skips the load's record as sunk. -/
theorem load_uextend_i8_i32_sinks :
    ∃ (f : Clif.Function) (result : Result) (event : BlockScanEvent) (b : Clif.Block),
      Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧
      Shape .unsigned8 f b 0 1 2 .i32 {} ∧ event ∈ result.blockScans.toList ∧
      ∃ (extend load : ScanRecord) (scanned : BlockScan) (step : Step) (nreg : Nat),
        scanned.records = [extend,load] ∧ step.rules.getLast? = some 815 ∧
        extend.output.emitted = #[.load .uload8 ((scanState extend.input 1).base.fresh .int).1
          (.unsignedOffset (.vreg nreg .int) 0) {}] ∧
        extend.output.state.sunk = #[true,false,false] ∧
        load.output.step = some ⟨0,0,.sunk,load.input,load.input,[],[],#[]⟩ := by
  obtain ⟨result,event,run,scope,dominated,events⟩ :=
    instance_of .plain .unsigned8 .i32 lowers_uextend scope_uextend
  have form := shape .unsigned8 .i32 rfl
  obtain ⟨_,extend,load,scanned,step,nreg,_,records,_,_,_,_,_,_,_,_,last,code,sunk,skipped⟩ :=
    stock_lower_sink_extend_record .unsigned8 run scope dominated form events
  exact ⟨_,result,event,_,run,scope,dominated,form,events,extend,load,scanned,step,nreg,records,
    last,code,sunk,by rw [skipped]⟩

/-- `%load_sextend_i16_i64`: the actual driver selects rule 824 and emits one
signed 16-bit load (`ldrsh`); the load's record is skipped as sunk. -/
theorem load_sextend_i16_i64_sinks :
    ∃ (f : Clif.Function) (result : Result) (event : BlockScanEvent) (b : Clif.Block),
      Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧
      Shape .signed16 f b 0 1 2 .i64 {} ∧ event ∈ result.blockScans.toList ∧
      ∃ (extend load : ScanRecord) (scanned : BlockScan) (step : Step) (nreg : Nat),
        scanned.records = [extend,load] ∧ step.rules.getLast? = some 824 ∧
        extend.output.emitted = #[.load .sload16 ((scanState extend.input 1).base.fresh .int).1
          (.unsignedOffset (.vreg nreg .int) 0) {}] ∧
        extend.output.state.sunk = #[true,false,false] ∧
        load.output.step = some ⟨0,0,.sunk,load.input,load.input,[],[],#[]⟩ := by
  obtain ⟨result,event,run,scope,dominated,events⟩ :=
    instance_of .plain .signed16 .i64 lowers_sextend scope_sextend
  have form := shape .signed16 .i64 rfl
  obtain ⟨_,extend,load,scanned,step,nreg,_,records,_,_,_,_,_,_,_,_,last,code,sunk,skipped⟩ :=
    stock_lower_sink_extend_record .signed16 run scope dominated form events
  exact ⟨_,result,event,_,run,scope,dominated,form,events,extend,load,scanned,step,nreg,records,
    last,code,sunk,by rw [skipped]⟩

/-- `%atomic_load_i8_i64`: the actual original-scope driver selects rule 810, emits one
acquiring byte load (`ldarb`) from the pointer and skips the atomic load's record as sunk. -/
theorem atomic_load_i8_i64_sinks :
    ∃ (f : Clif.Function) (result : Result) (event : BlockScanEvent) (b : Clif.Block),
      Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧
      SourceShape .acquire .unsigned8 f b 0 1 2 .i64 {} ∧ event ∈ result.blockScans.toList ∧
      ∃ (extend load : ScanRecord) (scanned : BlockScan) (step : Step) (nreg : Nat),
        scanned.records = [extend,load] ∧ step.rules.getLast? = some 810 ∧
        extend.output.emitted = #[.loadAcquire (.int 8) ((scanState extend.input 1).base.fresh .int).1
          (.vreg nreg .int) {}] ∧
        extend.output.state.sunk = #[true,false,false] ∧
        load.output.step = some ⟨0,0,.sunk,load.input,load.input,[],[],#[]⟩ := by
  obtain ⟨result,event,run,scope,dominated,events⟩ :=
    instance_of .acquire .unsigned8 .i64 lowers_acquire8 scope_acquire8
  have form := acquireShape .unsigned8 .i64 rfl rfl
  obtain ⟨_,extend,load,scanned,step,nreg,_,records,_,_,_,_,_,_,_,_,last,code,sunk,skipped⟩ :=
    stock_lower_source_extend_record .acquire .unsigned8 run scope dominated form events
  exact ⟨_,result,event,_,run,scope,dominated,form,events,extend,load,scanned,step,nreg,records,
    last,code,sunk,by rw [skipped]⟩

/-- `%atomic_load_i32_i64`: rule 810 folds the zero extension into one 32-bit acquiring
load (`ldar w`), which clears the upper bits; the atomic load's record is skipped as sunk. -/
theorem atomic_load_i32_i64_sinks :
    ∃ (f : Clif.Function) (result : Result) (event : BlockScanEvent) (b : Clif.Block),
      Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧
      SourceShape .acquire .unsigned32 f b 0 1 2 .i64 {} ∧ event ∈ result.blockScans.toList ∧
      ∃ (extend load : ScanRecord) (scanned : BlockScan) (step : Step) (nreg : Nat),
        scanned.records = [extend,load] ∧ step.rules.getLast? = some 810 ∧
        extend.output.emitted = #[.loadAcquire (.int 32) ((scanState extend.input 1).base.fresh .int).1
          (.vreg nreg .int) {}] ∧
        extend.output.state.sunk = #[true,false,false] ∧
        load.output.step = some ⟨0,0,.sunk,load.input,load.input,[],[],#[]⟩ := by
  obtain ⟨result,event,run,scope,dominated,events⟩ :=
    instance_of .acquire .unsigned32 .i64 lowers_acquire32 scope_acquire32
  have form := acquireShape .unsigned32 .i64 rfl rfl
  obtain ⟨_,extend,load,scanned,step,nreg,_,records,_,_,_,_,_,_,_,_,last,code,sunk,skipped⟩ :=
    stock_lower_source_extend_record .acquire .unsigned32 run scope dominated form events
  exact ⟨_,result,event,_,run,scope,dominated,form,events,extend,load,scanned,step,nreg,records,
    last,code,sunk,by rw [skipped]⟩

end Backend.Stock.Memory.SinkExtend
