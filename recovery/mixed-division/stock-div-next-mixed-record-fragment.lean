namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Every real mixed-body record is either a previously proved scalar record
or a retained, bound division record. The actual driver derives these cases. -/
inductive MixedDivRecord (f : Clif.Function) (ctx : Ctx) (bi : Nat) (r : ScanRecord) : Prop where
  | scalar {j : Nat} {b : Clif.Block} {stm : Clif.Stmt} {info : IInfo}
      (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
      (current : r.inst = blockStart f bi+j)
      (source : ctx.insts[r.inst]? = some info) (clif : info.clif = some stm.inst)
      (family : HighMulBody.Family stm.inst)
      (actual : PureBody.SourceRecord f ctx bi r) : MixedDivRecord f ctx bi r
  | division {j : Nat} {b : Clif.Block} {stm : Clif.Stmt} {step : Step} {info : IInfo}
      {op : Clif.DivOp} {ty : Clif.Ty} {x y z a : Nat}
      (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
      (current : r.inst = blockStart f bi+j)
      (source : ctx.insts[r.inst]? = some info) (clif : info.clif = some (.div op ty x y))
      (results : info.results = [z]) (statementResults : stm.results = [z])
      (mapped : ctx.valueReg? z = some (.vreg a .int))
      (recorded : r.output.step = some step) (emitted : step.decision = .emitted) :
      MixedDivRecord f ctx bi r

/-- Existing complete scalar handlers and the generic division handler compose
through one guarded original-source relation. -/
theorem MixedDivRecord.fall_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    (classified : MixedDivRecord f event.ctx event.block record)
    (sourceFamily : ∀ b ∈ f.blocks,∀ stm ∈ b.body,CastComplete.MemoryFormat stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
      (GuardedScanRel f result event.ctx event.block MR) record := by
  cases classified with
  | scalar block statement current source clif family actual =>
    exact QuietSourceColors.highmul_source_record_fall_refines run scope dominated events records
      block statement current family actual sourceFamily refines driver stable
  | division block statement current source clif results statementResults mapped recorded emitted =>
    exact stock_lower_div_scan_fall_refines run scope dominated events records
      block statement current _ source clif results statementResults mapped recorded emitted refines stable

/-- A real source trap is impossible at a pure prefix record; at a division,
the complete source bridge gives the real selected guard's coded halt. -/
theorem MixedDivRecord.trap_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    (classified : MixedDivRecord f event.ctx event.block record)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} :
    ScanTrapRefines (LocalBody.IndexedSourceTrap env cp f event.ctx event.block)
      isem result.final.alias (GuardedScanRel f result event.ctx event.block MR) record := by
  cases classified with
  | @scalar j b stm info block statement current source clif family actual =>
    intro s code failed ρ w held
    obtain ⟨indexed,info',inst,rest,found,original,remaining,trapped⟩ := failed
    have sameInfo : info' = info := Option.some.inj (found.symm.trans source)
    subst info'
    have sameInst : inst = stm.inst := Option.some.inj (original.symm.trans clif)
    subst inst
    rw [LocalBody.local_outcome (LocalBody.LocalInst.of_pure (HighMulBody.family_pure family))] at trapped
    exact False.elim (HighMulBody.highmul_inst_notrap family s.2.1 s.2.2 code trapped)
  | @division j b stm step info op ty x y z a block statement current source clif results statementResults mapped recorded emitted =>
    intro s code failed ρ w held
    obtain ⟨indexed,info',inst,rest,found,original,remaining,trapped⟩ := failed
    have sameInfo : info' = info := Option.some.inj (found.symm.trans source)
    subst info'
    have sameInst : inst = .div op ty x y := Option.some.inj (original.symm.trans clif)
    subst inst
    have position : s.1 = j := Nat.add_left_cancel (indexed.symm.trans current)
    obtain ⟨func,dfg,memory,values⟩ := held
    rw [position] at dfg values
    obtain ⟨d,output,bounds,trap⟩ := ScalarDiv.stock_lower_div_source_trap run scope dominated events
      records block statement current source clif results mapped recorded emitted refines dfg values trapped
    exact trap w

end Backend.Stock.Proof
#print axioms Backend.Stock.Proof.MixedDivRecord.fall_refines
#print axioms Backend.Stock.Proof.MixedDivRecord.trap_refines
