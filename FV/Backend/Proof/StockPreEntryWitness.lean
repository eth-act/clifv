import FV.Backend.Proof.StockPreEntryState
import FV.Backend.Proof.PerEdgeSpillEntrySaves
import FV.Backend.Proof.StockEntryGoodWitness
import FV.Backend.Proof.PerEdgeSpillJumpWitness

namespace Backend.Stock.Proof.PreEntryWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgeSpill
open Backend.Stock.Proof.SpillEntryFixture Backend.Stock.Proof.IndexedInstFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

private theorem last_ok (indirect : Bool) : SpillInstOk (last indirect) := by
  have callOk : CallOk 0 [] [(.x 0,retV indirect),(.x 1,retV indirect+2)] := by
    constructor
    · intro q h; cases h
    · exact List.nodup_nil
    · intro q h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl | rfl
      · exact ⟨0,by decide,rfl⟩
      · exact ⟨1,by decide,rfl⟩
    · change ([Reg.x 0,Reg.x 1] : List Reg).Nodup; decide +kernel
    · cases indirect <;> decide +kernel
    · intro q _; exact Nat.zero_le _
  exact spillInstOk_tryCall_of_call rfl (spillInstOk_callReg (retV indirect+8) callOk)

/-- Complete direct/indirect TryCall sources inhabit canonical entry-prefix
execution on both normal and handler routes, alongside real function-entry
saves and actual predecessor inclusion. Original source and checked/physical
stages are retained; these are checker-state witnesses. -/
theorem stock_preEntry_unique_witness (indirect handler : Bool) :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc)
      (succs preds : Array (Array Nat)) (vb tb : VBlock)
      (post body : Nat → Nat → Bool) (out e : AState),
      Stock.lower (function indirect) = .ok result ∧ LowerScope (function indirect) ∧
      Dominated (function indirect) ∧ ArityOk (function indirect) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      p.code.cfg = .ok (succs,preds) ∧ p.code.blocks[0]? = some vb ∧
      p.code.blocks[target handler]? = some tb ∧
      GoodAt p.code p.edges (post 0) out ∧
      EdgeTransferAt (spillCtxAt p.code p.edges succs) p.edges 0 (target handler) (index handler)
        (args indirect handler) tb out e ∧
      (preEntryStateAt p.code p.edges succs preds post body (target handler)).le e = true ∧
      Spill.Runs (spillCtxAt p.code p.edges succs) tb 0
        (spillEntryStoresAt (spillHomesAt p.code p.edges) p.code succs preds (target handler) ++
         spillEntryCopiesAt (spillHomesAt p.code p.edges) p.code p.edges succs preds (target handler))
        (preEntryStateAt p.code p.edges succs preds post body (target handler))
        (fun k a => k = 0 ∧ GoodAt p.code p.edges (body (target handler)) a ∧
          (bodyStateAt p.code p.edges (body (target handler))).le a = true) ∧
      Spill.Runs (spillCtxAt p.code p.edges succs) vb 0 spillSaves (entryState (stateSizeAt p.code p.edges))
        (fun k a => k = 0 ∧ GoodAt p.code p.edges (fun _ => false) a ∧
          (bodyStateAt p.code p.edges (fun _ => false)).le a = true) := by
  obtain ⟨result,p,rf,af,c,vb,tb,out,oldEdge,final,preds,run,scope,dominated,arity,raw,fallback,accepted,physical,
    code,allocated,cfg,block,targetBlock,placed,sourceChecked,postGood,live,availability,transfer,checked,finalGood,least⟩ :=
    EntryGoodWitness.stock_entry_return_blocks_witness indirect handler
  have layout := indexed_inst_layout run raw
  obtain ⟨fixture⟩ := try_fixture indirect
  have metadata := (by
    have same := Except.ok.inj (run.symm.trans fixture.lowered)
    have sameP := Except.ok.inj (raw.symm.trans (same ▸ fixture.prepare))
    subst sameP
    exact fixture.metadata : Metadata indirect p)
  obtain ⟨count,atLast,normalParams,handlerParams,edgeRow,cfgOption,rest⟩ := metadata
  have cfgFixed : p.code.cfg = .ok (#[#[2,1],#[],#[]],#[#[],#[0],#[0]]) := by
    cases actual : p.code.cfg <;> simp_all [Except.toOption]
  have sameCfg := Prod.mk.inj (Except.ok.inj (cfg.symm.trans cfgFixed))
  have succsFixed : c.succs = #[#[2,1],#[],#[]] := sameCfg.1
  have predsFixed : preds = #[#[],#[0],#[0]] := sameCfg.2
  have atLast' : vb.insts.back? = some (last indirect) := by
    have same : p.code.blocks[0]! = vb := by rw [getElem!_def,block]
    rw [same] at atLast
    exact atLast
  let post : Nat → Nat → Bool := fun _ => availInst (last indirect) (availAt (firstInstructions indirect) (fun _ => false) 2)
  let body : Nat → Nat → Bool := fun _ v => v == (retV indirect + if handler then 5 else 3) || v == ordinaryV indirect
  change GoodAt p.code p.edges (post 0) out at postGood
  change EntryAvailAt p.code vb (index handler) (args indirect handler) tb (post 0) (body (target handler)) at availability
  obtain ⟨ops,operands,valid,_⟩ := last_ok indirect
  have successors : c.succs[0]? = some #[2,1] := by rw [succsFixed]; rfl
  have edge : (#[2,1] : Array Nat)[index handler]? = some (target handler) := by cases handler <;> rfl
  have pred : preds[target handler]? = some #[0] := by rw [predsFixed]; cases handler <;> rfl
  have atArgs : (#[args indirect true,args indirect false] : Array (Array Reg))[index handler]? = some (args indirect handler) := by cases handler <;> rfl
  have notEntry : target handler ≠ 0 := by cases handler <;> decide
  have entry := stock_preEntryStateAt_unique_runs run scope dominated.ssa raw cfg notEntry block targetBlock
    successors edge pred edgeRow atArgs atLast' operands valid (post := post) (body := body) rfl availability
  obtain ⟨prepared,raw',_,_,arguments,parameters⟩ := stock_prepare_copy_metadata run scope dominated.ssa
  have same := Except.ok.inj (raw.symm.trans raw')
  subst prepared
  have arity' := stock_prepare_edge_arity run scope dominated.ssa raw c.succs preds cfg 0 (index handler)
    (target handler) #[2,1] _ _ tb successors edge edgeRow atArgs targetBlock
  have newTransfer := edgeAt_of_metadata (c := spillCtxAt p.code p.edges c.succs) rfl block targetBlock edgeRow atArgs arity'
    (arguments 0 _ _ _ edgeRow atArgs) (parameters _ _ targetBlock) out
  have inclusion := preEntryStateAt_unique_le (body := body) cfg notEntry block targetBlock successors edge pred edgeRow atArgs postGood live newTransfer
  have nonempty : vb.insts.size ≠ 0 := by
    have same : p.code.blocks[0]! = vb := by rw [getElem!_def,block]
    have instructions := layout.1
    rw [same] at instructions
    rw [instructions]; cases indirect <;> decide
  have saved : (spillCtxAt p.code p.edges c.succs).rf.saved = calleeSaved := by
    unfold spillCtxAt spillAllocAt; split <;> rfl
  exact ⟨result,p,rf,af,c.succs,preds,vb,tb,post,body,out,_,run,scope,dominated,arity,raw,fallback,accepted,physical,
    cfg,block,targetBlock,postGood,newTransfer,inclusion,entry,spill_entry_saves_runs saved nonempty⟩

/-- The shared-predecessor branch is inhabited by the complete checked cyclic
source. Its finite body candidate contains two available loop values. This
witness concerns the canonical state branch; shared-edge execution is a
separate remaining obligation. -/
theorem stock_preEntry_shared_witness :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc)
      (succs preds : Array (Array Nat)) (body : Nat → Nat → Bool),
      Stock.lower IndexedSpillFixture.function = .ok result ∧ LowerScope IndexedSpillFixture.function ∧
      Dominated IndexedSpillFixture.function ∧ prepareAt result.code result.edgeArgs = .ok p ∧
      rf = spillAllocAt p.code p.edges ∧ checkAllocAt p.code p.edges rf = .ok () ∧
      lowerRFunc p.code rf = .ok af ∧ p.code.cfg = .ok (succs,preds) ∧
      preds[1]? = some #[0,3] ∧ body 1 194 = true ∧ body 1 195 = true ∧
      (preEntryStateAt p.code p.edges succs preds (fun _ _ => false) body 1).le
        (bodyStateAt p.code p.edges (body 1)) = true := by
  obtain ⟨result,p,rf,af,tb,succs,preds,run,scope,dominated,raw,fallback,accepted,physical,cfg,
    successor,predecessors,targetBlock,copies,installed⟩ := SpillJumpWitness.stock_spill_jump_route_witness
  let body : Nat → Nat → Bool := fun _ v => v == 194 || v == 195
  have shared : ∀ b,preds[1]? ≠ some #[b] := by
    intro b eq
    rw [predecessors] at eq
    have size := congrArg Array.size (Option.some.inj eq)
    change 2 = 1 at size
    omega
  have inclusion := preEntryStateAt_shared_le (post := fun _ _ => false) (succs := succs) (preds := preds)
    (body := body) (target := 1) (by decide) shared (bodyStateAt_good p.code p.edges (body 1))
  exact ⟨result,p,rf,af,succs,preds,body,run,scope,dominated,raw,fallback,accepted,physical,cfg,
    predecessors,rfl,rfl,inclusion⟩

end Backend.Stock.Proof.PreEntryWitness
