import FV.Backend.Proof.PerEdgeSpillEntry
import FV.Backend.Proof.SpillCtlForms
import FV.Backend.Proof.StockCfgTotal
import FV.Backend.Proof.PerEdgeSpillEntryFixture

namespace Backend.Stock.Proof.SpillEntryWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.PerEdgeSpill Backend.Proof.Spill
open Backend.Stock.Proof.SpillEntryFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

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
  exact spillInstOk_tryCall_of_call rfl
    (spillInstOk_callReg (retV indirect+8) callOk)

/-- Four complete source pipelines (direct/indirect, normal/exception) inhabit
actual indexed entry placement, result stores and copies. Nonempty fresh
physical result symbols reach real parameter homes; the ordinary argument and
all save cells survive. The real global checker and physical lowering succeed. -/
theorem stock_try_spill_entry_witness (indirect handler : Bool) :
    ∃ (result : Result) (prepared : EdgeVCode) (rf : RFunc) (af : AFunc) (c : CheckCtx)
      (vb tb : VBlock) (a0 : AState) (succs preds : Array (Array Nat)),
      Stock.lower (function indirect) = .ok result ∧ LowerScope (function indirect) ∧
      Dominated (function indirect) ∧ ArityOk (function indirect) ∧
      prepareAt result.code result.edgeArgs = .ok prepared ∧
      prepareCheckedAt result.code result.edgeArgs = .ok prepared ∧
      rf = spillAllocAt prepared.code prepared.edges ∧ checkAllocAt prepared.code prepared.edges rf = .ok () ∧
      lowerRFunc prepared.code rf = .ok af ∧ c.vc = prepared.code ∧ c.rf = rf ∧ c.succs = succs ∧
      prepared.code.cfg = .ok (succs,preds) ∧
      prepared.code.blocks[0]? = some vb ∧ prepared.code.blocks[target handler]? = some tb ∧
      (∃ suffix,rf.blocks[target handler]? = some ((
        spillEntryStoresAt (spillHomesAt prepared.code prepared.edges) prepared.code succs preds (target handler) ++
        spillEntryCopiesAt (spillHomesAt prepared.code prepared.edges) prepared.code prepared.edges succs preds (target handler) ++ suffix).toArray)) ∧
      a0.size = stateSizeAt prepared.code prepared.edges ∧
      Runs c tb 0
        (spillEntryStoresAt (spillHomesAt prepared.code prepared.edges) prepared.code succs preds (target handler) ++
         spillEntryCopiesAt (spillHomesAt prepared.code prepared.edges) prepared.code prepared.edges succs preds (target handler)) a0
        (fun k' a' => k' = 0 ∧ a'.size = stateSizeAt prepared.code prepared.edges ∧
          a'.get (spillHomeAt (spillHomesAt prepared.code prepared.edges)
            (retV indirect + if handler then 5 else 3) .int) = [.vreg 900] ∧
          (handler = true → a'.get (spillHomeAt (spillHomesAt prepared.code prepared.edges)
            (retV indirect+6) .int) = [.vreg 901]) ∧
          a'.get (spillHomeAt (spillHomesAt prepared.code prepared.edges)
            (retV indirect + if handler then 7 else 4) .int) = [.vreg 902] ∧
          ∀ r,a'.get (.save r) = a0.get (.save r)) := by
  obtain ⟨f⟩ := try_fixture indirect
  rcases f with ⟨result,prepared,rf,af,lowered,scope,dominated,arity,prepare,fallback,accepted,physical,metadata⟩
  obtain ⟨count,atLast,normalParams,handlerParams,edgeRow,cfgOption,first,second,ordinary⟩ := metadata
  have cfg : prepared.code.cfg = .ok (#[#[2,1],#[],#[]],#[#[],#[0],#[0]]) := by
    cases actual : prepared.code.cfg <;> simp_all [Except.toOption]
  let succs : Array (Array Nat) := #[#[2,1],#[],#[]]
  let preds : Array (Array Nat) := #[#[],#[0],#[0]]
  let c : CheckCtx := ⟨prepared.code,succs,rf,stateSizeAt prepared.code prepared.edges⟩
  let vb := prepared.code.blocks[0]!
  let tb := prepared.code.blocks[target handler]!
  have source : prepared.code.blocks[0]? = some vb := by
    have bound : 0 < prepared.code.blocks.size := by omega
    dsimp only [vb]; rw [getElem!_pos prepared.code.blocks 0 bound]
    exact Array.getElem?_eq_getElem bound
  have targetAt : prepared.code.blocks[target handler]? = some tb := by
    have bound : target handler < prepared.code.blocks.size := by cases handler <;> simp [target] <;> omega
    dsimp only [tb]; rw [getElem!_pos prepared.code.blocks (target handler) bound]
    exact Array.getElem?_eq_getElem bound
  have targetParams : tb.params = params indirect handler := by
    cases handler
    · exact normalParams
    · exact handlerParams
  have slots : c.rf.spillSlots = (spillHomesAt prepared.code prepared.edges).size + maxArgsAt prepared.edges := by
    rw [show c.rf = rf from rfl,fallback]; exact (spillAllocAt_storage _ _).1
  have stateSize : (initial indirect prepared).size = stateSizeAt prepared.code prepared.edges := by
    simp only [initial,size_put,Array.size_replicate]
  have static : ∀ T ops,vb.insts.back? = some T → T.operands = .ok ops → OpsOk ops T.clobbers := by
    intro T ops termAt opAt
    rw [show vb.insts.back? = _ from atLast] at termAt
    cases termAt
    obtain ⟨ops',operands,valid,_⟩ := last_ok indirect
    rw [operands] at opAt
    cases opAt
    exact valid
  have sizes : (args indirect handler).size = tb.params.size := by
    rw [targetParams]; cases handler <;> rfl
  have classes : ∀ (i : Nat) (a p : Reg),(args indirect handler)[i]? = some a → tb.params[i]? = some p →
      ∃ v w cl,a = .vreg v cl ∧ p = .vreg w cl := by
    rw [targetParams]
    intro i a p left right
    cases handler
    · have bound : i < 2 := by have h := (Array.getElem?_eq_some_iff.mp left).1; exact h
      have choices : i = 0 ∨ i = 1 := by omega
      rcases choices with rfl | rfl
      all_goals cases left; cases right; exact ⟨_,_,.int,rfl,rfl⟩
    · have bound : i < 3 := by have h := (Array.getElem?_eq_some_iff.mp left).1; exact h
      have choices : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases choices with rfl | rfl | rfl
      all_goals cases left; cases right; exact ⟨_,_,.int,rfl,rfl⟩
  have distinct : (tb.params.toList.map Reg.homeNum).Nodup := by
    rw [targetParams]; cases indirect <;> cases handler <;> decide +kernel
  have edgeAt : (#[2,1] : Array Nat)[index handler]? = some (target handler) := by cases handler <;> rfl
  have predAt : preds[target handler]? = some #[0] := by cases handler <;> rfl
  have argsAt : (#[args indirect true,args indirect false] : Array (Array Reg))[index handler]? = some (args indirect handler) := by
    cases handler <;> rfl
  have entry := spill_entry_runs slots cfg source targetAt (by rfl : succs[0]? = some #[2,1]) edgeAt predAt
    edgeRow argsAt static sizes classes distinct stateSize
  have checkedPrep : prepareCheckedAt result.code result.edgeArgs = .ok prepared := by
    obtain ⟨p,raw,checked,_⟩ := stock_prepare_total lowered scope
    have same := Except.ok.inj (prepare.symm.trans raw); subst p; exact checked
  have placed := spillAllocAt_block (edges := prepared.edges) cfg targetAt
  have noSaves : ((if target handler == 0 then spillSaves else []) : List RItem) = [] := by cases handler <;> rfl
  rw [noSaves,List.nil_append,← fallback] at placed
  refine ⟨result,prepared,rf,af,c,vb,tb,initial indirect prepared,succs,preds,
    lowered,scope,dominated,arity,prepare,checkedPrep,fallback,accepted,physical,rfl,rfl,rfl,cfg,source,targetAt,
    ⟨_,by simpa only [List.append_assoc] using placed⟩,stateSize,?_⟩
  apply entry.mono
  intro k a ⟨same,size,fresh,unchanged,save⟩
  have firstDef : (⟨retV indirect,.int,.def,.late,.fixed (.x 0)⟩,Loc.reg (.x 0)) ∈ termEdgeDefs vb (index handler) := by
    unfold termEdgeDefs
    rw [show vb.insts.back? = _ from atLast]
    cases indirect <;> cases handler <;> decide +kernel
  have firstValue := fresh _ firstDef 0 (.vreg (retV indirect) .int)
    (.vreg (retV indirect + if handler then 5 else 3) .int)
    (by cases handler <;> rfl) (by rw [targetParams]; cases handler <;> rfl) rfl rfl
  refine ⟨same,size,firstValue.trans first,?_,?_,save⟩
  · intro isHandler
    subst handler
    have secondDef : (⟨retV indirect+2,.int,.def,.late,.fixed (.x 1)⟩,Loc.reg (.x 1)) ∈ termEdgeDefs vb (index true) := by
      unfold termEdgeDefs
      rw [show vb.insts.back? = _ from atLast]
      cases indirect <;> decide +kernel
    exact (fresh _ secondDef 1 (.vreg (retV indirect+2) .int) (.vreg (retV indirect+6) .int) rfl
      (by rw [targetParams]; rfl) rfl rfl).trans second
  · have nonstored : ∀ x ∈ termEdgeDefs vb (index handler),
        spillHomeAt (spillHomesAt prepared.code prepared.edges) x.1.vreg x.1.cls ≠
        spillHomeAt (spillHomesAt prepared.code prepared.edges) (ordinaryV indirect) .int := by
      intro x member
      have defs : termEdgeDefs vb (index handler) =
          if handler then [(⟨retV indirect,.int,.def,.late,.fixed (.x 0)⟩,Loc.reg (.x 0)),
            (⟨retV indirect+2,.int,.def,.late,.fixed (.x 1)⟩,Loc.reg (.x 1))]
          else [(⟨retV indirect,.int,.def,.late,.fixed (.x 0)⟩,Loc.reg (.x 0))] := by
        unfold termEdgeDefs
        rw [show vb.insts.back? = _ from atLast]
        cases indirect <;> cases handler <;> decide +kernel
      have freshNum : x.1.vreg = retV indirect ∨ x.1.vreg = retV indirect+2 := by
        rw [defs] at member
        cases handler <;> simp at member
        · cases member; exact Or.inl rfl
        · rcases member with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
      obtain ⟨n,hn⟩ := (spillHomesAt_spec prepared.code prepared.edges).code 0 vb source _
        (by
          obtain ⟨_,_,lastAt,opsAt,sub⟩ := (termEdgeDefs_sub vb (index handler)).resolve_left
            (fun empty => by rw [empty] at member; cases member)
          have pair := (mem_keptPairs (sub.subset member)).1
          exact mem_blockVregs_op (back_get lastAt).2 opsAt (spillPairs_fst _ _ ▸ List.mem_map_of_mem pair))
      let ordinaryIndex : Nat := if handler then 2 else 1
      have ordinaryAt : (args indirect handler)[ordinaryIndex]? = some (.vreg (ordinaryV indirect) .int) := by cases handler <;> rfl
      obtain ⟨m,hm⟩ := (spillHomesAt_spec prepared.code prepared.edges).outgoing 0 (index handler) ordinaryIndex
        _ _ _ edgeRow argsAt ordinaryAt
      change homeLookup (spillHomesAt prepared.code prepared.edges) (spillHomeKeyAt (ordinaryV indirect) .int) = some m at hm
      intro equal
      have stackEq : Loc.stack n x.1.cls = .stack m .int := by
        unfold homeLookup at hn hm
        simpa only [spillHomeAt,hn,hm,Option.getD_some] using equal
      injection stackEq with nm cl
      have keys := (spillHomesAt_spec prepared.code prepared.edges).valid.2 _ _ _ hn (nm.symm ▸ hm)
      have sameNum := (spillHomeKeyAt_injective keys).1
      change x.1.vreg = ordinaryV indirect at sameNum
      rcases freshNum with freshNum | freshNum
      all_goals rw [freshNum] at sameNum; unfold ordinaryV at sameNum; omega
    have ordinaryValue := unchanged (if handler then 2 else 1) (.vreg (ordinaryV indirect) .int)
      (.vreg (retV indirect + if handler then 7 else 4) .int) (by cases handler <;> rfl)
      (by rw [targetParams]; cases handler <;> rfl) nonstored
    exact ordinaryValue.trans ordinary

end Backend.Stock.Proof.SpillEntryWitness
