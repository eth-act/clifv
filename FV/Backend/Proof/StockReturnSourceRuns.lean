import FV.Backend.Proof.StockReturnHelpers
import FV.Backend.Proof.StockReturnArity
import FV.Backend.Proof.StockSourceDefined

/-! Execute the actual revised return helper against successful original source
returns. Source arity and implicit reads are derived internally; return pins
follow the actual ABI, while all legacy return contracts remain unchanged. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

private theorem mapped_virtual {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) :
    ∀ {xs : List Nat} {rs : List Reg},xs.mapM ctx.valueReg? = some rs →
      ∃ ns : List Nat,rs = ns.map (fun n => Reg.vreg n .int)
  | [],rs,map => by simp at map; subst rs; exact ⟨[],rfl⟩
  | x :: xs,rs,map => by
    simp only [List.mapM_cons,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,
      Option.some.injEq] at map
    obtain ⟨r,lookup,tail,rest,rfl⟩ := map
    obtain ⟨n,rfl⟩ := inv.valueReg x r lookup
    obtain ⟨ns,equal⟩ := mapped_virtual inv rest
    exact ⟨n :: ns,by rw [equal]; rfl⟩

private theorem zip_retPairs (ns : List Nat) (ps : List Reg) :
    ((ns.map (fun n => Reg.vreg n .int)).zip ps) = retPairs (ns.zip ps) := by
  simp [retPairs,List.zip_map_left,Prod.map]

private theorem resolved_rets (aliases : Array (Option Nat)) (ns : List Nat) (ps : List Reg) :
    (MInst.rets (retPairs (ns.zip ps))).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) =
      .rets (retPairs ((ns.map (aliasNum aliases)).zip ps)) := by
  simp [MInst.mapRegs,retPairs,List.zip_map_left,List.map_map,Function.comp_def,Prod.map,resolve_vreg,aliasNum]

/-- Real return-helper machine execution uses the actual mapped/final-alias
registers and ABI pins, including x8. Successful original source execution and
original entry/source invariants derive request arity and all ABI reads. -/
theorem stock_lower_return_source_run {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {xs : List Nat} (ret : b.term = .ret xs)
    {env : Clif.Env} {cp : Clif.Program} {s : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem}
    (func : s.frame.func = f) (callers : s.callers = [])
    (done : Clif.stepTerm env cp s (.ret xs) = .done vals cm)
    (defined : SourceDefinedAt f result.ctx event.block b.body.length s.frame)
    {fuel : Nat} (enough : 60 ≤ fuel) {st next : State} {tr trace : Array RuleId} {out : V}
    (helper : ApplyInternal program (Stock.sem event.ctx) {} fuel 25 294 [.values (xs ++ sretRet f)]
      (st,tr) out (next,trace))
    {ρ : Nat → CV} (held : ValuesHeld (fun x => x ∈ xs ++ sretRet f) event.ctx s.frame
      (fun key => ρ (aliasNum result.final.alias key)))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) :
    ∃ (rs ps : List Reg) (extra : List Clif.Val),
      (xs ++ sretRet f).mapM event.ctx.valueReg? = some rs ∧
      returnPins f rs.length = some ps ∧ ps.length = rs.length ∧
      s.frame.getMany (xs ++ sretRet f) = .ok (vals ++ extra) ∧
      next = {(xs ++ sretRet f).foldl State.mark st with
        base := ((xs ++ sretRet f).foldl State.mark st).base.emit (.rets (rs.zip ps))} ∧
      out = .regsVec [] ∧
      ∀ world,MR s.frame.slots s.mem world → ∃ ops world',
        seqRun isem [(.rets (rs.zip ps) : MInst).mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))] ρ world =
          some (.stop 0 ((.rets (rs.zip ps) : MInst).mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) ops ρ world [] world' .ret) ∧
        AllHold (vals ++ extra) (vuses ops ρ) ∧ MR s.frame.slots s.mem world' := by
  obtain ⟨rs,ps,safe,mapped,pins,state,output⟩ := stock_lower_return_observed data_program rfl enough helper
  have inv := (stock_lower_record_context run scope events).1
  rw [inv.func] at pins
  obtain ⟨extra,read⟩ := stock_lower_return_abi_read run dominated events block ret callers done defined
  have values := requested_values_hold held read mapped
  have sourceCount := (getMany_ok read).1
  have registerCount : (vals ++ extra).length = rs.length := by simpa only [List.length_map] using values.1
  have pinCount : ps.length = rs.length := by
    by_cases implicit : (sigRets f.sig).any (·.purpose == .sret) = true
    · have arity := (stock_lower_sret_source_arity run abi events block ret implicit func done).2.2
      have equal : rs.length = 1 := by omega
      simp only [returnPins,implicit,ite_true,Option.some.injEq] at pins
      rw [← pins,List.length_singleton,equal]
    · have ordinary : (sigRets f.sig).any (·.purpose == .sret) = false := Bool.eq_false_iff.mpr implicit
      simp only [returnPins,ordinary,Bool.false_eq_true,ite_false] at pins
      obtain ⟨_,same⟩ := retRegs_eq pins
      rw [same,List.length_map,List.length_range]
  refine ⟨rs,ps,extra,mapped,pins,pinCount,read,state,output,?_⟩
  intro world memory
  obtain ⟨ns,registers⟩ := mapped_virtual inv mapped
  have lengths : ns.length = ps.length := by rw [registers,List.length_map] at pinCount; exact pinCount.symm
  let pairs : List (Nat × Reg) := (ns.map (aliasNum result.final.alias)).zip ps
  have code : (.rets (rs.zip ps) : MInst).mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)) = .rets (retPairs pairs) := by
    rw [registers,zip_retPairs,resolved_rets]
  obtain ⟨world',executed,worldEq⟩ := seqRun_one_stop refines (operands_rets pairs) (ρ := ρ) (w := world) (ctl := .ret)
    (by decide) (ispec_rets _ _ world) (by rw [List.toList_toArray,filter_isDef_retOps]; rfl)
  refine ⟨(retOps pairs).toArray,world',?_,?_,stable _ _ _ _ (SameWorld.nf worldEq) memory⟩
  · simpa only [code] using executed
  · rw [vuses_retOps]
    have fst : pairs.map (·.1) = ns.map (aliasNum result.final.alias) :=
      List.map_fst_zip (by simp only [List.length_map]; omega)
    have uses : pairs.map (fun q => ρ q.1) = rs.map (registerView (fun key => ρ (aliasNum result.final.alias key))) := by
      rw [show (fun q : Nat × Reg => ρ q.1) = ρ ∘ (·.1) from rfl,← List.map_map,fst,registers]
      simp only [List.map_map,Function.comp_def,registerView]
    rw [uses]
    exact values
end Backend.Stock.Proof
