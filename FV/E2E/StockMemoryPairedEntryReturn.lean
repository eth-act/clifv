import FV.E2E.StockMemoryPairedEntry

namespace E2E.StockMemory
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private theorem return_inbounds {W : Type} {vc : VCode} {isem : ISem CV W}
    {vs : VState CV W} {us : List (Reg × Reg)} {vals : List CV} {w : W}
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

/-- Compose actual register ABI entry, an ordinary paired source body and its
placed ABI return, starting at instruction zero with one shared virtual file. -/
theorem actual_ordinary_paired_entry_return_refines_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body, OrdinaryBody.OrdinaryInst stm.inst)
    {xs : List Nat} (ret : b.term = .ret xs)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals mem)
    (registerOnly : ∀ loc ∈ locsOf f.sig,∃ pin,loc = .reg pin)
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n a,Γ.syms n = some a → X.sym n 0 = BitVec.ofNat 64 a)
    (tls : XTls Γ.F X)
    (bodyProvider : ∀ (event : BlockScanEvent), event ∈ result.blockScans.toList →
      ∃ (term : ScanRecord) (body : BlockScan), SourceBodySplit f event b term body ∧
        ∀ s s', SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block + ·)) s s' →
        ∀ ρ w, PairedScanRel f result event.ctx event.block Γ c D event.output.state s ρ w → ∃ ρ' w',
          seqRun (pairSem (csem Γ.F fc X)) (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ w =
            some (.fall ρ' w') ∧
          PairedScanRel f result event.ctx event.block Γ c D term.output.state s' ρ' w')
    {w w' : Arm.ArmState} (memory : MRP Γ f c D fr.slots cm (w,w'))
    (arguments : ArgsAtEntry Γ.F f.sig args w) (otherArguments : ArgsAtEntry Γ.F f.sig args w')
    (registers : ∀ pin v,(.reg pin,v) ∈ (locsOf f.sig).zip args → regVal w' pin = regVal w pin) :
    RunOkABI f result.code (pairSem (csem Γ.F fc X)) (MRP Γ f c D) fr.slots
      ⟨0,0,entrySeed result.ctx fr,(w,w')⟩ (.returned vals mem) := by
  obtain ⟨event,vb,pre,body,ρ',events,zero,placed,pieces,execution,values,after,bodyCode⟩ :=
    stock_lower_entry_prelude_paired_frame run scope dominated entered registerOnly slot symbols memory arguments otherArguments registers
  have code : vb.insts = pre ++ event.output.code.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) ++ after := by
    rw [pieces,bodyCode,Array.append_assoc]
  have entryFacts := entered
  obtain ⟨b',regs,entry,argTypes,paramTypes,set,frame⟩ := entryFacts
  have sameBlock : b' = b := by
    have found : some b = some b' := by
      simpa only [Clif.Function.entry?,blocks,List.head?_cons] using entry
    exact Option.some.inj found.symm
  subst b'
  have defined : SourceDefinedAt f result.ctx event.block 0 fr := by
    rw [zero]
    exact source_defined_entry_frame dominated result.ctx entered
  have held : PairedScanRel f result event.ctx event.block Γ c D event.output.state
      (0,fr,cm) ρ' (w,w') := by
    exact ⟨stock_lower_entered_values_guarded_frame run scope dominated events entered values
      event.output.state w memory.1,
      stock_lower_entered_values_guarded_frame run scope dominated events entered values
      event.output.state w' memory.2.1,memory.2.2⟩
  obtain ⟨term,body,split,bodyRun⟩ := bodyProvider event events
  have finished := actual_ordinary_paired_return_refines_at run scope dominated abi family ret events split
    (s := ⟨fr,[],cm⟩) (by rw [frame]) rfl (by rw [frame]) (by rw [frame])
    defined returned (fc := fc) tls bodyRun placed code ρ' (w,w') held
  have room : pre.size < vb.insts.size := by
    obtain ⟨us,outs,world,cm',reached,_⟩ := finished
    exact return_inbounds reached placed
  have segment : SegAt vb 0 pre.toList := by
    intro k bound
    have inside : k < pre.size := by simpa only [Array.length_toList] using bound
    rw [Nat.zero_add,pieces,Array.getElem?_append_left inside]
    simp [inside]
  have path := seqRun_fall_star (vc := result.code) (sem := pairSem (csem Γ.F fc X)) placed segment
    (by simpa only [Nat.zero_add,Array.length_toList] using room) execution
  have seed : entrySeed event.ctx fr = entrySeed result.ctx fr := by
    classical
    let make (lookup : Nat → Option Reg) (key : Nat) : CV :=
      if h : ∃ pair : Nat × Clif.Val,
          lookup pair.1 = some (.vreg key .int) ∧ fr.regs pair.1 = some pair.2 then
        (Classical.choose h).2.bits.setWidth 128
      else 0
    change make event.ctx.valueReg? = make result.ctx.valueReg?
    rw [funext (stock_lower_record_context run scope events).2.1]
  rw [← seed]
  apply RunOkABI.prefix path
  simpa only [Nat.zero_add,Array.length_toList] using finished


end E2E.StockMemory
