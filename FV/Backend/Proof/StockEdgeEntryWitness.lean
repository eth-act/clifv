import FV.Backend.Proof.StockPreparedEdge
import FV.Backend.Proof.PerEdgeSpillInstFixture
import FV.Backend.Proof.PerEdgeSpillCycleFixture

namespace Backend.Stock.Proof.EdgeEntryWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgeSpill
open Backend.Stock.Proof.SpillEntryFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

private def livePairs (indirect handler : Bool) : List (Operand × Loc) :=
  let first := (⟨retV indirect,.int,.def,.late,.fixed (.x 0)⟩,Loc.reg (.x 0))
  if handler then [first,(⟨retV indirect+2,.int,.def,.late,.fixed (.x 1)⟩,Loc.reg (.x 1))] else [first]
private theorem live_pairs {vb : VBlock} {indirect handler : Bool}
    (atLast : vb.insts.back? = some (last indirect)) : termEdgeDefs vb (index handler) = livePairs indirect handler := by
  unfold termEdgeDefs
  rw [atLast]
  cases indirect <;> cases handler <;> decide +kernel
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

private theorem home_eq {h : SpillHomesAt} {v n : Nat}
    (found : homeLookup h (spillHomeKeyAt v .int) = some n) : spillHomeAt h v .int = .stack n .int := by
  unfold homeLookup at found
  simp only [spillHomeAt,found,Option.getD_some]
private theorem different_homes {p : EdgeVCode} {v w n m : Nat}
    (left : homeLookup (spillHomesAt p.code p.edges) (spillHomeKeyAt v .int) = some n)
    (right : homeLookup (spillHomesAt p.code p.edges) (spillHomeKeyAt w .int) = some m) (different : v ≠ w) :
    spillHomeAt (spillHomesAt p.code p.edges) v .int ≠ spillHomeAt (spillHomesAt p.code p.edges) w .int := by
  rw [home_eq left,home_eq right]
  intro same
  have equal : n = m := by injection same
  rw [← equal] at right
  have key := (spillHomesAt_spec p.code p.edges).valid.2 _ _ _ left right
  exact different (spillHomeKeyAt_injective key).1

private def content (indirect : Bool) (p : EdgeVCode) : Loc → List Sym
  | .reg (.x 0) => [.vreg (retV indirect)]
  | .reg (.x 1) => [.vreg (retV indirect+2)]
  | .save r => if r ∈ calleeSaved then [.entry r] else []
  | .stack n cl => if spillHomeAt (spillHomesAt p.code p.edges) (ordinaryV indirect) .int = .stack n cl then
      [.vreg (ordinaryV indirect)] else []
  | _ => []
private def before (indirect : Bool) (p : EdgeVCode) : AState :=
  mkState (stateSizeAt p.code p.edges) (content indirect p)

/-- Four complete original Stock TryCall pipelines inhabit real edge symbol
renaming followed by actual selected result stores/entry copies. Fresh normal
and exception symbols and a live ordinary argument reach parameter homes as
parameter symbols; every save cell survives. No source-value or universal
checker-acceptance claim is inferred from this symbolic-state witness. -/
theorem stock_edge_entry_symbols_witness (indirect handler : Bool) :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc) (c : CheckCtx)
      (vb tb : VBlock) (out e : AState) (ss ps : Array (Array Nat)),
      Stock.lower (function indirect) = .ok result ∧ LowerScope (function indirect) ∧
      Dominated (function indirect) ∧ ArityOk (function indirect) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧
      rf = spillAllocAt p.code p.edges ∧ checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      c.vc = p.code ∧ c.rf = rf ∧ c.succs = ss ∧ p.code.cfg = .ok (ss,ps) ∧
      p.code.blocks[0]? = some vb ∧ p.code.blocks[target handler]? = some tb ∧
      out.size = stateSizeAt p.code p.edges ∧
      IncomingArgSymbolsAt p.code p.edges vb (index handler) (args indirect handler) (c.edgeForget 0 (target handler) out) ∧
      EdgeTransferAt c p.edges 0 (target handler) (index handler) (args indirect handler) tb out e ∧
      Spill.Runs c tb 0 (spillEntryStoresAt (spillHomesAt p.code p.edges) p.code ss ps (target handler) ++
        spillEntryCopiesAt (spillHomesAt p.code p.edges) p.code p.edges ss ps (target handler)) e fun k final =>
        k = 0 ∧ final.size = stateSizeAt p.code p.edges ∧
        (∀ (i : Nat) (ar p' : Reg),(args indirect handler)[i]? = some ar → tb.params[i]? = some p' →
          Sym.vreg p'.homeNum ∈ final.get (spillHomeAt (spillHomesAt p.code p.edges) p'.homeNum p'.homeCls)) ∧
        ∀ r ∈ calleeSaved,Sym.entry r ∈ final.get (.save r) := by
  obtain ⟨fixture⟩ := try_fixture indirect
  rcases fixture with ⟨result,p,rf,af,run,scope,dominated,arity,raw,fallback,accepted,physical,metadata⟩
  obtain ⟨count,atLast,normalParams,handlerParams,edgeRow,cfgOption,rest⟩ := metadata
  have cfg : p.code.cfg = .ok (#[#[2,1],#[],#[]],#[#[],#[0],#[0]]) := by
    cases actual : p.code.cfg <;> simp_all [Except.toOption]
  let ss : Array (Array Nat) := #[#[2,1],#[],#[]]
  let ps : Array (Array Nat) := #[#[],#[0],#[0]]
  let c : CheckCtx := ⟨p.code,ss,rf,stateSizeAt p.code p.edges⟩
  let vb := p.code.blocks[0]!
  let tb := p.code.blocks[target handler]!
  let out := before indirect p
  have source : p.code.blocks[0]? = some vb := by
    have bound : 0 < p.code.blocks.size := by omega
    dsimp only [vb]; rw [getElem!_pos p.code.blocks 0 bound]
    exact Array.getElem?_eq_getElem bound
  have atTarget : p.code.blocks[target handler]? = some tb := by
    have bound : target handler < p.code.blocks.size := by cases handler <;> simp [target] <;> omega
    dsimp only [tb]; rw [getElem!_pos p.code.blocks _ bound]
    exact Array.getElem?_eq_getElem bound
  have defs : termEdgeDefs vb (index handler) = livePairs indirect handler := live_pairs atLast
  have retHome := (spillHomesAt_spec p.code p.edges).outgoing 0 0 0 _ _ (.vreg (retV indirect) .int) edgeRow (by rfl) (by rfl)
  have payHome := (spillHomesAt_spec p.code p.edges).outgoing 0 0 1 _ _ (.vreg (retV indirect+2) .int) edgeRow (by rfl) (by rfl)
  have ordHome := (spillHomesAt_spec p.code p.edges).outgoing 0 0 2 _ _ (.vreg (ordinaryV indirect) .int) edgeRow (by rfl) (by rfl)
  obtain ⟨nr,hr⟩ := retHome
  obtain ⟨np,hp⟩ := payHome
  obtain ⟨no,ho⟩ := ordHome
  dsimp only [Reg.homeNum,Reg.homeCls] at hr hp ho
  have retDifferent : retV indirect ≠ ordinaryV indirect := by unfold ordinaryV; omega
  have payDifferent : retV indirect+2 ≠ ordinaryV indirect := by unfold ordinaryV; omega
  have retHomeDifferent := different_homes hr ho retDifferent
  have payHomeDifferent := different_homes hp ho payDifferent
  have ordinaryHeld : Sym.vreg (ordinaryV indirect) ∈ out.get (spillHomeAt (spillHomesAt p.code p.edges) (ordinaryV indirect) .int) := by
    have nBound := (spillHomesAt_spec p.code p.edges).valid.1 _ _ ho
    have index : ∃ i,(Loc.stack no .int).index = some i ∧ i < stateSizeAt p.code p.edges :=
      ⟨_,rfl,by unfold stateSizeAt; omega⟩
    obtain ⟨i,atIndex,iBound⟩ := index
    rw [home_eq ho]
    dsimp only [out,before]
    rw [get_mkState atIndex iBound]
    simp [content,home_eq ho]
  have firstHeld : Sym.vreg (retV indirect) ∈ out.get (.reg (.x 0)) := by
    dsimp only [out,before]
    rw [get_mkState (i := 0) rfl (by unfold stateSizeAt; omega)]
    exact List.mem_singleton_self _
  have secondHeld : Sym.vreg (retV indirect+2) ∈ out.get (.reg (.x 1)) := by
    dsimp only [out,before]
    rw [get_mkState (i := 1) rfl (by unfold stateSizeAt; omega)]
    exact List.mem_singleton_self _
  have saved : ∀ r ∈ calleeSaved,Sym.entry r ∈ out.get (.save r) := by
    intro r member
    obtain ⟨i,atIndex,iBound⟩ := save_index member
    dsimp only [out,before]
    rw [get_mkState atIndex (by unfold stateSizeAt; omega)]
    simp only [content,if_pos member,List.mem_singleton]
  have forget : c.edgeForget 0 (target handler) out = if handler then out else out.remove (.vreg (retV indirect+2)) := by
    unfold CheckCtx.edgeForget
    rw [show c.vc = p.code from rfl,source]
    change (match vb.insts.back? with | some i => _ | none => _) = _
    rw [show vb.insts.back? = _ from atLast]
    cases indirect <;> cases handler
    all_goals first | rfl | skip
    all_goals change forgetOps out [⟨_,.int,.def,.late,.fixed (.x 1)⟩] = out.remove (.vreg _)
    all_goals simp [forgetOps,AState.remove,bne]
  have retained {v : Nat} {l : Loc} (held : Sym.vreg v ∈ out.get l)
      (live : handler = true ∨ v ≠ retV indirect+2) : Sym.vreg v ∈ (c.edgeForget 0 (target handler) out).get l := by
    rw [forget]
    cases handler
    · simp only [Bool.false_eq_true,ite_false,get_remove,List.mem_filter]
      refine ⟨held,?_⟩
      rcases live with impossible | different
      · cases impossible
      · simpa using different
    · exact held
  have firstAfter := retained (v := retV indirect) firstHeld (.inr (by omega))
  have ordinaryAfter := retained (v := ordinaryV indirect) ordinaryHeld (.inr (by unfold ordinaryV; omega))
  have incoming : IncomingArgSymbolsAt p.code p.edges vb (index handler) (args indirect handler)
      (c.edgeForget 0 (target handler) out) := by
    intro i ar atArg
    cases handler
    · have iBound : i < 2 := (Array.getElem?_eq_some_iff.mp atArg).1
      have choices : i = 0 ∨ i = 1 := by omega
      rcases choices with rfl | rfl
      · change some (.vreg (retV indirect) .int) = some ar at atArg
        cases atArg
        refine .inl ⟨(⟨retV indirect,.int,.def,.late,.fixed (.x 0)⟩,Loc.reg (.x 0)),?_,rfl,rfl,?_⟩
        · rw [defs]; simp [livePairs]
        · exact firstAfter
      · change some (.vreg (ordinaryV indirect) .int) = some ar at atArg
        cases atArg
        refine .inr ⟨?_,ordinaryAfter⟩
        intro x member
        rw [defs] at member
        simp only [livePairs,Bool.false_eq_true,ite_false,List.mem_singleton] at member
        subst x
        exact retHomeDifferent
    · have iBound : i < 3 := (Array.getElem?_eq_some_iff.mp atArg).1
      have choices : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases choices with rfl | rfl | rfl
      · change some (.vreg (retV indirect) .int) = some ar at atArg
        cases atArg
        refine .inl ⟨(⟨retV indirect,.int,.def,.late,.fixed (.x 0)⟩,Loc.reg (.x 0)),?_,rfl,rfl,?_⟩
        · rw [defs]; simp [livePairs]
        · exact firstAfter
      · change some (.vreg (retV indirect+2) .int) = some ar at atArg
        cases atArg
        refine .inl ⟨(⟨retV indirect+2,.int,.def,.late,.fixed (.x 1)⟩,Loc.reg (.x 1)),?_,rfl,rfl,?_⟩
        · rw [defs]; simp [livePairs]
        · exact retained secondHeld (.inl rfl)
      · change some (.vreg (ordinaryV indirect) .int) = some ar at atArg
        cases atArg
        refine .inr ⟨?_,ordinaryAfter⟩
        intro x member
        rw [defs] at member
        simp only [livePairs,ite_true,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl
        · exact retHomeDifferent
        · exact payHomeDifferent
  have static : ∀ T ops,vb.insts.back? = some T → T.operands = .ok ops → OpsOk ops T.clobbers := by
    intro T ops lastAt operands
    rw [show vb.insts.back? = _ from atLast] at lastAt
    cases lastAt
    obtain ⟨ops',operands',valid,_⟩ := last_ok indirect
    rw [operands'] at operands
    cases operands
    exact valid
  have size : out.size = stateSizeAt p.code p.edges := size_mkState _ _
  obtain ⟨e,transfer,moves⟩ := stock_spill_entry_symbols_runs run scope dominated.ssa raw (by rfl)
    (by change rf = _; exact fallback) cfg source atTarget (by rfl : ss[0]? = some #[2,1])
    (by cases handler <;> rfl) (by cases handler <;> rfl) edgeRow (by cases handler <;> rfl) static incoming saved size
  refine ⟨result,p,rf,af,c,vb,tb,out,e,ss,ps,run,scope,dominated,arity,raw,fallback,accepted,physical,
    rfl,rfl,rfl,cfg,source,atTarget,size,incoming,transfer,?_⟩
  exact moves.mono fun k a ⟨same,size,params,saved,_⟩ => ⟨same,size,params,saved⟩

/-- The complete checked cyclic Stock source instantiates edge acceptance and
symbol transfer on every actual prepared edge, retaining its two-live reversed
critical vector and all raw/checker/physical lowering stages. -/
theorem stock_cyclic_edge_transfer_witness :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc) (c : CheckCtx) (ss ps : Array (Array Nat)),
      Stock.lower IndexedSpillFixture.function = .ok result ∧ LowerScope IndexedSpillFixture.function ∧
      Dominated IndexedSpillFixture.function ∧ ArityOk IndexedSpillFixture.function ∧
      prepareAt result.code result.edgeArgs = .ok p ∧
      rf = spillAllocAt p.code p.edges ∧ checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      c.vc = p.code ∧ c.rf = rf ∧ c.succs = ss ∧ p.code.cfg = .ok (ss,ps) ∧
      p.edges[3]? = some #[#[Reg.vreg 195 .int,Reg.vreg 194 .int]] ∧
      (p.code.blocks[1]!).params = #[Reg.vreg 194 .int,Reg.vreg 195 .int] ∧
      ∀ (b target j : Nat) (succs : Array Nat),ss[b]? = some succs → succs[j]? = some target →
        ∀ out,∃ args tb e,p.edges[b]?.bind (·[j]?) = some args ∧ p.code.blocks[target]? = some tb ∧
          EdgeTransferAt c p.edges b target j args tb out e := by
  obtain ⟨fixture⟩ := IndexedSpillFixture.cycle_fixture
  rcases fixture with ⟨result,p,rf,af,run,scope,dominated,raw,fallback,accepted,physical,
    count,edgeRow,params,rest⟩
  obtain ⟨nonempty,labels⟩ := stock_prepare_domain run scope
  obtain ⟨_,ss,ps,cfg⟩ := PerEdgePrep.prepareAt_cfg raw nonempty labels
  let c : CheckCtx := ⟨p.code,ss,rf,stateSizeAt p.code p.edges⟩
  refine ⟨result,p,rf,af,c,ss,ps,run,scope,dominated,arityOk_of (by decide +kernel),raw,fallback,accepted,physical,
    rfl,rfl,rfl,cfg,edgeRow,params,?_⟩
  intro b target j succs successors edge out
  exact stock_prepared_all_edge_transfer run scope dominated.ssa raw (by rfl) cfg successors edge out

end Backend.Stock.Proof.EdgeEntryWitness
