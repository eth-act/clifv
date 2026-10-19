import FV.Backend.Proof.StockCallStoreSem
import FV.Backend.Proof.StockDemand
namespace Backend.Stock.Proof.GotStoreSemDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
open ExplicitCallSemDraft ExplicitCallExecutionDraft CallStoreSemDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

private theorem mapped_arguments {ctx : Ctx} {fr : Clif.Frame} {ρ : Nat → CV}
    {args ns : List Nat} {vals : List Clif.Val}
    (held : ValuesHeld (fun x => x ∈ args) ctx fr ρ) (read : fr.getMany args = .ok vals)
    (mapping : args.mapM ctx.valueReg? = some (ns.map fun n => Reg.vreg n .int)) :
    ns.length = vals.length ∧
      ∀ (j : Nat) (v : Clif.Val) (n : Nat),vals[j]? = some v → ns[j]? = some n → VHolds v (ρ n) := by
  have all := requested_values_hold held read mapping
  simp only [List.map_map,Function.comp_def,registerView] at all
  refine ⟨by simpa using all.1.symm,?_⟩
  intro j v n atValue atReg
  apply all.2 j v (ρ n) atValue
  simp only [List.getElem?_map,atReg,Option.map_some]

/-- An actual successful original direct source call supplies argument and
return typing, the external implementation, and returned memory. Its mapped
argument stores then execute before the real explicit-result call; callee
AllHold and output length derive from the ORIGINAL external contract. -/
theorem stock_source_got_stores_execution {Rd F : BitVec 64 → Prop} {asm : FnCtx} {X : ExtSem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} {f : Clif.Function} {ctx : Ctx}
    (stable : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (memory : MemRefinesR Rd F sb syms (csem F asm X)) {outB : Nat} (outgoing : OutArgsOk F outB MR)
    (external : XCallsOk env (f.externs.map (·.2)) MR X)
    {fn : Nat} {args ns : List Nat} {ext : Clif.ExtFunc}
    (declared : f.extern? fn = some ext) (stackOk : SigStackOk ext.sig outB)
    {bytes : List Nat} {locs : List ArgLoc} {stack base target : Nat}
    (byteRun : sigParamBytes ext.sig = .ok bytes) (locations : sigArgLocs ext.sig = .ok (locs,stack))
    (mapping : args.mapM ctx.valueReg? = some (ns.map fun n => Reg.vreg n .int))
    {fr : Clif.Frame} {ρ : Nat → CV} {cm cm' : Clif.Mem} {w : Arm.ArmState} {rvals : List Clif.Val}
    (far : ext.colocated = false) (fresh : ∀ n ∈ ns,n ≠ target)
    (frame : fr.func = f) (held : ValuesHeld (fun x => x ∈ args) ctx fr ρ) (related : MR fr.slots cm w)
    (source : instOutcome env cp fr cm (.call fn args) = .ok (rvals,cm')) :
    ∃ outs w',seqRun (explicitCallSem (csem F asm X))
        (((stackEnts ((locs.zip ns).zip bytes)).map argStore) ++
          [.loadExtNameGot (.vreg target .int) ext.name,.call ⟨.reg (.vreg target .int),retPairs (regPairsOf ((locs.zip ns).zip bytes)),callDefs (outDefs base ext.sig.returns.length)⟩]) ρ w =
          some (.fall (writeV (upd ρ target (ofX (X.sym ext.name 0))) ((callDefOps (outDefs base ext.sig.returns.length)).zip outs)) w') ∧
      outs.length = ext.sig.returns.length ∧ AllHold rvals outs ∧
      ResultsHeld base fr (outRegs' base ext.sig.returns.length) rvals
        (writeV (upd ρ target (ofX (X.sym ext.name 0))) ((callDefOps (outDefs base ext.sig.returns.length)).zip outs)) ∧ MR fr.slots cm' w' := by
  obtain ⟨actual,vals,g,found,read,typed,implementation,returned,resultTypes⟩ := instOutcome_call_ok source
  rw [frame,declared] at found
  cases found
  obtain ⟨count,values⟩ := mapped_arguments held read mapping
  have mem := stock_explicit_call_mem_refines memory
  obtain ⟨atCall,stores,relatedCall,arguments⟩ := argsAt_after_stores stable mem outgoing stackOk byteRun locations typed count values related
  have member : ext ∈ f.externs.map (·.2) := List.mem_map.mpr ⟨(fn,ext),lookup_mem declared,rfl⟩
  have length : rvals.length = ext.sig.returns.length := by
    have types := congrArg List.length resultTypes
    simpa [Clif.AbiParam.tys] using types
  let ρ₁ := upd ρ target (ofX (X.sym ext.name 0))
  have unchanged : (regPairsOf ((locs.zip ns).zip bytes)).map (ρ₁ ·.1) =
      (regPairsOf ((locs.zip ns).zip bytes)).map (ρ ·.1) := by
    apply List.map_congr_left
    intro q member
    have ne := fresh q.1 (map_zip_args (mem_args_of_regPairs (List.mem_map_of_mem member)))
    simp only [ρ₁,upd,if_neg ne]
  have targetValue : ρ₁ target = ofX (X.sym ext.name 0) := by simp [ρ₁,upd]
  have load : explicitCallSem (csem F asm X) (.loadExtNameGot (.vreg target .int) ext.name) [] atCall =
      some ([ofX (X.sym ext.name 0)],atCall,.next) := rfl
  have loaded := seqRun_got (F := F) (ρ := ρ) load
  obtain ⟨outs,w',call,size,returnedValues,relatedAfter⟩ := stock_explicit_direct_call_return
    (F := F) (ctx := asm) (dest := .reg (.vreg target .int))
    (us := retPairs (regPairsOf ((locs.zip ns).zip bytes)))
    (ds := callDefs (outDefs base ext.sig.returns.length))
    (uses := ρ₁ target :: (regPairsOf ((locs.zip ns).zip bytes)).map (ρ₁ ·.1))
    external member implementation (.inr ⟨.vreg target .int,rfl,far,by rw [targetValue,unchanged]⟩)
    (by simp [callDefs,outDefs]) (arguments atCall (SameWorldNF.refl F atCall)) relatedCall returned length
  have size' : outs.length = ext.sig.returns.length := by simpa [callDefs,outDefs] using size
  have executed := seqRun_call_reg (ρ := ρ₁) call (by simpa [outDefs] using size')
  have results := CallResultValuesDraft.stock_resultsHeld_call_prefix (fr := fr) (ρ := ρ₁) (b := base) returnedValues.prefixHold
  rw [length] at results
  refine ⟨outs,w',?_,size',returnedValues,results,relatedAfter⟩
  exact seqRun_append_fall' _ stores (seqRun_append_fall' _ loaded executed)
end Backend.Stock.Proof.GotStoreSemDraft
