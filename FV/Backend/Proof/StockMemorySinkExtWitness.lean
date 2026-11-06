import FV.Backend.Proof.StockMemorySinkExtRecord
import FV.Backend.Proof.LowerDecide

/-! Non-vacuity on Cranelift's `load-extends.clif` filetest functions
`%load_uextend_i8_i32` and `%load_sextend_i16_i64`: their default (trapping) loads
inhabit the source class, the original-scope Stock driver succeeds, and the
whole-driver sink step applies with rule 815 or 824. -/
namespace Backend.Stock.Memory.SinkExtend
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Memory.ExtendedRoots (Kind)
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.lower

/-- The filetest block: `v1 = load.<in> v0; v2 = <op>.<out> v1; return v2`. -/
private def block (kind : Kind) (out : Clif.Ty) : Clif.Block :=
  { id := 0, params := [(0,.i64)],
    body := [⟨[1],.load .load (loadTy kind) {} 0 0⟩,⟨[2],.extend (extendOp kind) out 1⟩],
    term := .ret [2] }

/-- The filetest function with signature `(i64) -> <out>`. -/
private def fixture (kind : Kind) (out : Clif.Ty) : Clif.Function :=
  { name := "load_extend",
    sig := { params := [⟨.i64,.none,.normal⟩], returns := [⟨out,.none,.normal⟩] },
    blocks := [block kind out] }

private def lowers (kind : Kind) (out : Clif.Ty) : Bool :=
  match Stock.lower (fixture kind out) with
  | .ok result => result.blockScans.size == 1
  | .error _ => false

section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.lower
private theorem lowers_uextend : lowers .unsigned8 .i32 = true := by decide +kernel
private theorem lowers_sextend : lowers .signed16 .i64 = true := by decide +kernel
private theorem scope_uextend : lowerScopeB (fixture .unsigned8 .i32) = true := by decide +kernel
private theorem scope_sextend : lowerScopeB (fixture .signed16 .i64) = true := by decide +kernel
end Kernel

private theorem dominated (kind : Kind) (out : Clif.Ty) : Dominated (fixture kind out) := by
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
        have zero : x = 0 := by simpa [Driver.instArgs] using member
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
    have bound := (inFix_fixOk (f := fixture kind out) (ctx := ctx) (gn := id)).cand tl x available
    have length : (fixture kind out).blocks.length = 1 := rfl
    omega

private theorem shape (kind : Kind) (out : Clif.Ty) (small : narrow out = true) :
    Shape kind (fixture kind out) (block kind out) 0 1 2 out {} :=
  ⟨rfl,rfl,rfl,small,by simp [block],by simp [fixture,sigRets]⟩

private theorem instance_of (kind : Kind) (out : Clif.Ty) (small : narrow out = true)
    (lowered : lowers kind out = true) (scope : lowerScopeB (fixture kind out) = true) :
    ∃ (result : Result) (event : BlockScanEvent),
      Stock.lower (fixture kind out) = .ok result ∧ LowerScope (fixture kind out) ∧
      Dominated (fixture kind out) ∧ Shape kind (fixture kind out) (block kind out) 0 1 2 out {} ∧
      event ∈ result.blockScans.toList := by
  unfold lowers at lowered
  cases run : Stock.lower (fixture kind out) with
  | error e => rw [run] at lowered; cases lowered
  | ok result =>
    rw [run] at lowered
    have size : result.blockScans.size = 1 := by simpa using lowered
    exact ⟨result,result.blockScans[0],rfl,lowerScope_of scope,dominated kind out,
      shape kind out small,Array.mem_toList_iff.mpr (Array.getElem_mem (by omega))⟩

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
  obtain ⟨result,event,run,scope,dominated,form,events⟩ :=
    instance_of .unsigned8 .i32 rfl lowers_uextend scope_uextend
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
  obtain ⟨result,event,run,scope,dominated,form,events⟩ :=
    instance_of .signed16 .i64 rfl lowers_sextend scope_sextend
  obtain ⟨_,extend,load,scanned,step,nreg,_,records,_,_,_,_,_,_,_,_,last,code,sunk,skipped⟩ :=
    stock_lower_sink_extend_record .signed16 run scope dominated form events
  exact ⟨_,result,event,_,run,scope,dominated,form,events,extend,load,scanned,step,nreg,records,
    last,code,sunk,by rw [skipped]⟩

end Backend.Stock.Memory.SinkExtend
