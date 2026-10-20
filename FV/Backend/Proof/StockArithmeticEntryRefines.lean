import FV.Backend.Proof.StockEntryPrelude
import FV.Backend.Proof.StockArithmeticReturnRefines

namespace Backend.Stock.Proof.ArithmeticBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

private theorem return_inbounds {vc : VCode} {isem : Backend.Proof.Sem}
    {vs : VState CV Arm.ArmState} {us : List (Reg × Reg)} {vals : List CV} {w : Arm.ArmState}
    (ret : VRetFrom vc isem vs us vals w) {block : VBlock}
    (placed : vc.blocks[vs.b]? = some block) : vs.k < block.insts.size := by
  obtain ⟨b,k,ρ,w₁,vb,ops,outs,path,atBlock,instruction,_⟩ := ret
  cases path with
  | refl =>
    have same : block = vb := Option.some.inj (placed.symm.trans atBlock)
    subst vb
    exact (Array.getElem?_eq_some_iff.mp instruction).1
  | step first rest =>
    cases first with
    | step found instruction operands semantics length next =>
      have same : block = _ := Option.some.inj (placed.symm.trans found)
      subst same
      exact (Array.getElem?_eq_some_iff.mp instruction).1

/-- Complete original-entry-to-return simulation of arbitrary single-block
add/sub bodies in the actual Stock VCode. ABI materialization, omitted parameter
values, final aliases, source execution and machine PC placement are derived
internally. The allocation checker may choose the proof-selected initial file. -/
theorem actual_arithmetic_entry_return_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body, ∃ subtract : Bool, ∃ ty x y,
      stm.inst = .binary (if subtract then .isub else .iadd) ty x y)
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
  obtain ⟨event,vb,pre,body,ρ',w',events,zero,placed,pieces,execution,mem',values,same,
    after,bodyCode⟩ := stock_lower_entry_prelude_refines run scope dominated entered driver
      memorySem stable memory arguments
  have code : vb.insts = pre ++ event.output.code.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) ++ after := by
    rw [pieces,bodyCode,Array.append_assoc]
  obtain ⟨b',regs,entry,argTypes,paramTypes,set,slots,frame⟩ := Opt.enterFunc_ok entered
  have sameBlock : b' = b := by
    have found : some b = some b' := by
      simpa only [Clif.Function.entry?,blocks,List.head?_cons] using entry
    exact Option.some.inj found.symm
  subst b'
  have defined : SourceDefinedAt f result.ctx event.block 0 fr := by
    rw [zero]
    exact source_defined_enterFunc dominated result.ctx entered
  have held := stock_lower_entered_values_guarded run scope dominated events entered values
    event.output.state w' mem'
  have finished := actual_arithmetic_return_refines_at run scope dominated abi blocks family ret events
    (s := ⟨fr,[],cm⟩) (by rw [frame]) rfl (by rw [frame]) (by rw [frame])
    defined returned refines stable placed code ρ' w' held
  have room : pre.size < vb.insts.size := by
    obtain ⟨us,outs,world,cm',reached,_⟩ := finished
    exact return_inbounds reached placed
  have segment : SegAt vb 0 pre.toList := by
    intro k bound
    have inside : k < pre.size := by simpa only [Array.length_toList] using bound
    rw [Nat.zero_add,pieces,Array.getElem?_append_left inside]
    simp [inside]
  have path := seqRun_fall_star (vc := result.code) (sem := isem) placed segment
    (by simpa only [Nat.zero_add,Array.length_toList] using room) execution
  refine ⟨entrySeed event.ctx fr,RunOkABI.prefix path ?_⟩
  simpa only [Nat.zero_add,Array.length_toList] using finished

end Backend.Stock.Proof.ArithmeticBody
