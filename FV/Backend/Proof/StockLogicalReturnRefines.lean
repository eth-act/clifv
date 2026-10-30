import FV.Backend.Proof.StockLogicalBodyRefines
import FV.Backend.Proof.StockPureReturnRefines
import FV.Backend.Proof.StockArithmeticEntryRefines

/-! Complete original-entry-to-return simulation for ordinary logical/mixed bodies.
The source class extends the preserved Mixed class; the old theorems remain intact. -/
namespace Backend.Stock.Proof.LogicalBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem family_pure {inst : Clif.Inst} (family : Family inst) : pureInst inst = true := by
  rcases family with ⟨subtract,ty,x,y,rfl⟩ | ⟨ty,c,x,y,rfl⟩ | ⟨kind,ty,x,y,rfl⟩
  all_goals rfl

/-- Actual source execution and the actual emitted logical/mixed body/return reach
an ABI-correct return in Stock's returned VCode. Source steps, terminal definedness,
caller/frame transport and segment placement are all derived internally. -/
theorem actual_logical_return_refines_at {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body, Family stm.inst)
    {xs : List Nat} (ret : b.term = .ret xs)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {s : Clif.State}
    (func : s.frame.func = f) (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (terminal : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx event.block 0 s.frame)
    {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel s = .returned vals mem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR)
    {label : Nat} {vb : VBlock} {pre post : Array MInst}
    (placed : result.code.blocks[label]? = some vb)
    (code : vb.insts = pre ++ event.output.code.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) ++ post) :
    ∀ ρ w, GuardedScanRel f result event.ctx event.block MR event.output.state
      (0,s.frame,s.mem) ρ w →
      RunOkABI f result.code isem MR s.frame.slots ⟨label,pre.size,ρ,w⟩ (.returned vals mem) := by
  obtain ⟨term,body,split,bodyRun⟩ := actual_logical_body_refines run scope dominated blocks family events
    refines stable (env := env) (cp := cp)
  exact PureBody.actual_pure_return_refines_at run scope dominated abi blocks
    (fun stm member => family_pure (family stm member)) ret events split func callers remaining
    terminal defined returned refines stable bodyRun placed code

/-- Compatibility variant retaining existential body placement. -/
theorem actual_logical_return_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body, Family stm.inst)
    {xs : List Nat} (ret : b.term = .ret xs)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {s : Clif.State}
    (func : s.frame.func = f) (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (terminal : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx event.block 0 s.frame)
    {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel s = .returned vals mem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) :
    ∃ label k, ∀ ρ w, GuardedScanRel f result event.ctx event.block MR event.output.state
      (0,s.frame,s.mem) ρ w →
      RunOkABI f result.code isem MR s.frame.slots ⟨label,k,ρ,w⟩ (.returned vals mem) := by
  obtain ⟨label,vb,pre,post,placed,code⟩ := stock_lower_block_scan_code run events
  exact ⟨label,pre.size,actual_logical_return_refines_at run scope dominated abi blocks family ret
    events func callers remaining terminal defined returned refines stable placed code⟩

/-- Original function entry derives the frame, caller and source-definedness
premises of the actual logical/mixed return simulation. -/
theorem actual_logical_entered_return_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body, Family stm.inst)
    {xs : List Nat} (ret : b.term = .ret xs)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {args : List Clif.Val} {cm0 cm : Clif.Mem} {fr : Clif.Frame}
    (entered : Clif.enterFunc f args cm0 = .ok (fr,cm))
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals mem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) :
    ∃ label k, ∀ ρ w, GuardedScanRel f result event.ctx event.block MR event.output.state
      (0,fr,cm) ρ w →
      RunOkABI f result.code isem MR fr.slots ⟨label,k,ρ,w⟩ (.returned vals mem) := by
  obtain ⟨b',regs,entry,types,paramTypes,set,slots,frame⟩ := Opt.enterFunc_ok entered
  have same : b' = b := by
    have found : some b = some b' := by simpa only [Clif.Function.entry?,blocks,List.head?_cons] using entry
    exact Option.some.inj found.symm
  subst b'
  obtain ⟨term,body,split,families⟩ := actual_logical_families run scope blocks family events
  have bound := (List.getElem?_eq_some_iff.mp split.block).1
  rw [blocks] at bound
  have zero : event.block = 0 := by simpa using bound
  have defined : SourceDefinedAt f result.ctx event.block 0 fr := by
    rw [zero]
    exact source_defined_enterFunc dominated result.ctx entered
  apply actual_logical_return_refines run scope dominated abi blocks family ret events
    (s := ⟨fr,[],cm⟩) (by rw [frame]) rfl
    (by rw [frame]) (by rw [frame]) defined returned refines stable

/-- Complete original-entry-to-return simulation of arbitrary single-block
select/add/sub/logical bodies in the actual Stock VCode. ABI materialization, omitted parameter
values, final aliases, source execution and machine PC placement are derived
internally. The allocation checker may choose the proof-selected initial file. -/
theorem actual_logical_entry_return_refines_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body, Family stm.inst)
    {xs : List Nat} (ret : b.term = .ret xs)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals mem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ, RunOkABI f result.code isem MR fr.slots ⟨0,0,ρ,w⟩ (.returned vals mem) := by
  exact PureBody.actual_pure_entry_return_refines_frame run scope dominated abi blocks
    (fun stm member => family_pure (family stm member)) ret entered returned refines driver memorySem stable
    (fun event events => actual_logical_body_refines run scope dominated blocks family events refines stable)
    memory arguments

/-- Executable-entry compatibility variant; retains the original statement. -/
theorem actual_logical_entry_return_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body, Family stm.inst)
    {xs : List Nat} (ret : b.term = .ret xs)
    {args : List Clif.Val} {cm0 cm : Clif.Mem} {fr : Clif.Frame}
    (entered : Clif.enterFunc f args cm0 = .ok (fr,cm))
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals mem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ, RunOkABI f result.code isem MR fr.slots ⟨0,0,ρ,w⟩ (.returned vals mem) := by
  exact actual_logical_entry_return_refines_frame run scope dominated abi blocks family ret (SourceEntry.of_enterFunc entered) returned refines driver memorySem stable memory arguments


end Backend.Stock.Proof.LogicalBody
