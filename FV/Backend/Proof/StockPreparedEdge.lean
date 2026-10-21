import FV.Backend.Proof.PerEdgeSpillEntrySymbols

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgeSpill
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Every actual selected prepared Stock edge passes its copy checks and has
the exact parameter-symbol transfer under original scope/SSA. Source block,
vector classes, target distinctness and edge arity are derived internally. -/
theorem stock_prepared_edge_transfer {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup)
    {p : EdgeVCode} (raw : prepareAt result.code result.edgeArgs = .ok p)
    {c : CheckCtx} (code : c.vc = p.code) {ps : Array (Array Nat)}
    (cfg : p.code.cfg = .ok (c.succs,ps))
    {b target j : Nat} {ss : Array Nat} {row : Array (Array Reg)} {args : Array Reg} {tb : VBlock}
    (successors : c.succs[b]? = some ss) (edge : ss[j]? = some target)
    (atRow : p.edges[b]? = some row) (atArgs : row[j]? = some args) (targetBlock : p.code.blocks[target]? = some tb)
    (out : AState) : EdgeTransferAt c p.edges b target j args tb out
      ((c.edgeForget b target out).parCopy (tb.params.toList.map Reg.homeNum) (args.toList.map Reg.homeNum)) := by
  obtain ⟨prepared,raw',_,_,arguments,parameters⟩ := stock_prepare_copy_metadata run scope ssa
  have same := Except.ok.inj (raw.symm.trans raw')
  subst prepared
  have arity := stock_prepare_edge_arity run scope ssa raw c.succs ps cfg b j target ss row args tb
    successors edge atRow atArgs targetBlock
  have bBound : b < p.code.blocks.size := by
    rw [← (Prep.cfg_spec cfg).size]
    exact (Array.getElem?_eq_some_iff.mp successors).1
  exact edgeAt_of_metadata code (Array.getElem?_eq_getElem bBound) targetBlock atRow atArgs arity
    (arguments b j row args atRow atArgs) (parameters target tb targetBlock) out

/-- Complete edge-checker acceptance for every actual prepared Stock CFG
successor. Selected vector/target existence and metadata are all derived;
there is no supplied row, vector, block or edge-arity certificate. -/
theorem stock_prepared_all_edge_transfer {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup)
    {p : EdgeVCode} (raw : prepareAt result.code result.edgeArgs = .ok p)
    {c : CheckCtx} (code : c.vc = p.code) {ps : Array (Array Nat)}
    (cfg : p.code.cfg = .ok (c.succs,ps))
    {b target j : Nat} {ss : Array Nat} (successors : c.succs[b]? = some ss) (edge : ss[j]? = some target)
    (out : AState) : ∃ (args : Array Reg) (tb : VBlock) (e : AState),
      p.edges[b]?.bind (·[j]?) = some args ∧ p.code.blocks[target]? = some tb ∧
      EdgeTransferAt c p.edges b target j args tb out e := by
  obtain ⟨nonempty,labels⟩ := stock_prepare_domain run scope
  obtain ⟨_,ss0,ps0,cfg0,_⟩ := PerEdgePrep.prepareAt_input_facts raw
  obtain ⟨args,tb,atArgs,targetBlock,_⟩ := PerEdgePrep.prepareAt_edge_arguments raw nonempty labels cfg0
    (stock_lower_edge_arity run scope ssa ss0 ps0 cfg0) cfg successors edge
  cases atRow : p.edges[b]? with
  | none => rw [atRow] at atArgs; cases atArgs
  | some row =>
    have selected : row[j]? = some args := by simpa only [atRow,Option.bind_some] using atArgs
    exact ⟨args,tb,_,selected,targetBlock,stock_prepared_edge_transfer run scope ssa raw code cfg successors edge atRow selected targetBlock out⟩

/-- Actual Stock successor-entry stores/copies follow the real edge's parameter
renaming. All arity/class/distinctness/storage premises are derived internally;
predecessor static/availability facts remain internal proof obligations. -/
theorem stock_spill_entry_symbols_runs {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup)
    {p : EdgeVCode} (raw : prepareAt result.code result.edgeArgs = .ok p)
    {c : CheckCtx} (code : c.vc = p.code) (allocated : c.rf = spillAllocAt p.code p.edges)
    {ps : Array (Array Nat)} (cfg : p.code.cfg = .ok (c.succs,ps))
    {b target j : Nat} {ss : Array Nat} {row : Array (Array Reg)} {args : Array Reg} {vb tb : VBlock}
    (source : p.code.blocks[b]? = some vb) (targetBlock : p.code.blocks[target]? = some tb)
    (successors : c.succs[b]? = some ss) (edge : ss[j]? = some target) (pred : ps[target]? = some #[b])
    (atRow : p.edges[b]? = some row) (atArgs : row[j]? = some args)
    (static : ∀ T ops,vb.insts.back? = some T → T.operands = .ok ops → OpsOk ops T.clobbers)
    {out : AState} (incoming : IncomingArgSymbolsAt p.code p.edges vb j args (c.edgeForget b target out))
    (saved : ∀ r ∈ calleeSaved,Sym.entry r ∈ out.get (.save r))
    (stateSize : out.size = stateSizeAt p.code p.edges) :
    ∃ e,EdgeTransferAt c p.edges b target j args tb out e ∧
      Spill.Runs c tb 0 (spillEntryStoresAt (spillHomesAt p.code p.edges) p.code c.succs ps target ++
        spillEntryCopiesAt (spillHomesAt p.code p.edges) p.code p.edges c.succs ps target) e fun k final =>
        k = 0 ∧ final.size = stateSizeAt p.code p.edges ∧
        (∀ (i : Nat) (ar p' : Reg),args[i]? = some ar → tb.params[i]? = some p' →
          Sym.vreg p'.homeNum ∈ final.get (spillHomeAt (spillHomesAt p.code p.edges) p'.homeNum p'.homeCls)) ∧
        (∀ r ∈ calleeSaved,Sym.entry r ∈ final.get (.save r)) ∧
        ∀ l,(∀ cl,l ≠ .reg (spillScratch cl)) →
          (∀ i cl,l ≠ .stack ((spillHomesAt p.code p.edges).size+i) cl) →
          (∀ p' ∈ tb.params.toList,l ≠ spillHomeAt (spillHomesAt p.code p.edges) p'.homeNum p'.homeCls) →
          (∀ x ∈ termEdgeDefs vb j,spillHomeAt (spillHomesAt p.code p.edges) x.1.vreg x.1.cls ≠ l) →
          final.get l = e.get l := by
  have transfer := stock_prepared_edge_transfer run scope ssa raw code cfg successors edge atRow atArgs targetBlock out
  obtain ⟨prepared,raw',_,_,arguments,parameters⟩ := stock_prepare_copy_metadata run scope ssa
  have same := Except.ok.inj (raw.symm.trans raw')
  subst prepared
  have argShape := arguments b j row args atRow atArgs
  have paramShape := parameters target tb targetBlock
  have arity := stock_prepare_edge_arity run scope ssa raw c.succs ps cfg b j target ss row args tb
    successors edge atRow atArgs targetBlock
  have classes : ∀ (i : Nat) (ar p' : Reg),args[i]? = some ar → tb.params[i]? = some p' →
      ∃ v w cl,ar = .vreg v cl ∧ p' = .vreg w cl := by
    intro i ar p' arAt pAt
    obtain ⟨v,rfl⟩ := argShape ar (Array.mem_toList_iff.mpr (Array.mem_of_getElem? arAt))
    obtain ⟨w,rfl⟩ := paramShape.1 p' (Array.mem_toList_iff.mpr (Array.mem_of_getElem? pAt))
    exact ⟨v,w,.int,rfl,rfl⟩
  have slots : c.rf.spillSlots = (spillHomesAt p.code p.edges).size + maxArgsAt p.edges := by
    rw [allocated]; exact (spillAllocAt_storage _ _).1
  exact ⟨_,transfer,spill_entry_symbols_runs slots cfg source targetBlock successors edge pred atRow atArgs static arity classes
    paramShape.2 transfer incoming saved stateSize⟩

end Backend.Stock.Proof
