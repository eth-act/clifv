import FV.Backend.Proof.StockEntryGood
import FV.Backend.Proof.PerEdgeSpillInstFixture
import FV.Backend.Proof.PerEdgeSpillBlock

namespace Backend.Stock.Proof.EntryGoodWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgeSpill
open Backend.Stock.Proof.SpillEntryFixture Backend.Stock.Proof.IndexedInstFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

private def sourceA (indirect : Bool) : Nat → Bool := availAt (firstInstructions indirect) (fun _ => false) 2
private def sourceB (indirect : Bool) : Nat → Bool := availInst (last indirect) (sourceA indirect)
private def firstParam (indirect handler : Bool) : Nat := retV indirect + if handler then 5 else 3
private def wanted (indirect handler : Bool) (v : Nat) : Bool := v == firstParam indirect handler || v == ordinaryV indirect

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

private theorem static_all {indirect : Bool} {p : EdgeVCode} (count : p.code.blocks.size = 3)
    (layout : Layout indirect p) :
    ∀ (b : Nat) (vb : VBlock) (k : Nat) (i : MInst),p.code.blocks[b]? = some vb → vb.insts[k]? = some i → SpillInstOk i := by
  intro b vb k i block instruction
  have bBound : b < 3 := by have := (Array.getElem?_eq_some_iff.mp block).1; omega
  have asBang : p.code.blocks[b]! = vb := by rw [getElem!_def,block]
  have choices : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  rcases choices with rfl | rfl | rfl
  · have instructions := layout.1
    rw [asBang] at instructions
    rw [instructions] at instruction
    have kBound : k < 3 := (Array.getElem?_eq_some_iff.mp instruction).1
    have choices : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases choices with rfl | rfl | rfl
    · cases instruction; spill_form
    · cases indirect <;> cases instruction <;> spill_form
    · cases instruction; exact last_ok indirect
  · have instructions := layout.2.1
    rw [asBang] at instructions
    rw [instructions] at instruction
    have zero : k = 0 := by have := (Array.getElem?_eq_some_iff.mp instruction).1; change k < 1 at this; omega
    subst k
    cases instruction
    exact spillInstOk_rets (ns := [(retV indirect+3,.x 0)]) (by intro q h; simp only [List.mem_singleton] at h; subst q; exact ⟨0,by decide,rfl⟩) (by simp)
  · have instructions := layout.2.2.1
    rw [asBang] at instructions
    rw [instructions] at instruction
    have zero : k = 0 := by have := (Array.getElem?_eq_some_iff.mp instruction).1; change k < 1 at this; omega
    subst k
    cases instruction
    exact spillInstOk_rets (ns := [(retV indirect+5,.x 0)]) (by intro q h; simp only [List.mem_singleton] at h; subst q; exact ⟨0,by decide,rfl⟩) (by simp)

private theorem classes_all {p : EdgeVCode} (checked : classesB p = true)
    {b k : Nat} {vb : VBlock} {i : MInst} {ops : Array Operand}
    (block : p.code.blocks[b]? = some vb) (instruction : vb.insts[k]? = some i) (operands : i.operands = .ok ops) :
    ∀ o ∈ ops.toList,p.code.classes[o.vreg]? = some o.cls := by
  have blockCheck := Array.all_eq_true_iff_forall_mem.mp checked vb (Array.mem_of_getElem? block)
  have instCheck := Array.all_eq_true_iff_forall_mem.mp blockCheck i (Array.mem_of_getElem? instruction)
  rw [operands] at instCheck
  intro o member
  exact of_decide_eq_true (Array.all_eq_true_iff_forall_mem.mp instCheck o (Array.mem_toList_iff.mp member))

private def usesB (indirect : Bool) : Bool := (List.range 3).all fun k =>
  match (firstInstructions indirect)[k]? with
  | none => false
  | some i => match i.operands with
    | .error _ => false
    | .ok ops => ops.all fun o => if o.kind == .use then availAt (firstInstructions indirect) (fun _ => false) k o.vreg else true
private theorem uses_observed (indirect : Bool) : usesB indirect = true := by cases indirect <;> decide +kernel

private def livePairs (indirect handler : Bool) : List (Operand × Loc) :=
  let first := (⟨retV indirect,.int,.def,.late,.fixed (.x 0)⟩,Loc.reg (.x 0))
  if handler then [first,(⟨retV indirect+2,.int,.def,.late,.fixed (.x 1)⟩,Loc.reg (.x 1))] else [first]
private theorem live_pairs {vb : VBlock} {indirect handler : Bool}
    (atLast : vb.insts.back? = some (last indirect)) : termEdgeDefs vb (index handler) = livePairs indirect handler := by
  unfold termEdgeDefs
  rw [atLast]
  cases indirect <;> cases handler <;> decide +kernel
private theorem selected_kept {vb : VBlock} {T : MInst} {ops : Array Operand} {j : Nat} {x : Operand × Loc}
    (atLast : vb.insts.back? = some T) (operands : T.operands = .ok ops) (member : x ∈ termEdgeDefs vb j) :
    x ∈ keptPairs T (ops.zip (spillLocs ops T.clobbers)).toList := by
  obtain ⟨T',ops',last',_,operands',kept,_⟩ := termEdgeDefs_spec member
  rw [atLast] at last'
  cases last'
  rw [operands] at operands'
  cases operands'
  exact kept

/-- Complete direct/indirect normal/handler sources execute their real source
body from empty homes, then their real edge and entire return successor block.
Successor availability, live results, ordinary homes, saves and canonical state
inclusion are proved from the actual checker execution. Raw/checker/physical
pipeline stages and original source conditions are retained. -/
theorem stock_entry_return_blocks_witness (indirect handler : Bool) :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc) (c : CheckCtx)
      (vb tb : VBlock) (out e final : AState) (preds : Array (Array Nat)),
      Stock.lower (function indirect) = .ok result ∧ LowerScope (function indirect) ∧
      Dominated (function indirect) ∧ ArityOk (function indirect) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧
      rf = spillAllocAt p.code p.edges ∧ checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      c.vc = p.code ∧ c.rf = rf ∧ p.code.cfg = .ok (c.succs,preds) ∧
      p.code.blocks[0]? = some vb ∧ p.code.blocks[target handler]? = some tb ∧
      rf.blocks[0]? = some ((spillSaves ++ vb.insts.toList.zipIdx.flatMap (PerEdgeSpill.bodyItem p.code p.edges c.succs preds 0 vb)).toArray) ∧
      c.runItems vb 0 (vb.insts.toList.zipIdx.flatMap (PerEdgeSpill.bodyItem p.code p.edges c.succs preds 0 vb))
        (bodyStateAt p.code p.edges (fun _ => false)) = .ok out ∧
      GoodAt p.code p.edges (sourceB indirect) out ∧
      (∀ x ∈ termEdgeDefs vb (index handler),Sym.vreg x.1.vreg ∈ out.get x.2) ∧
      EntryAvailAt p.code vb (index handler) (args indirect handler) tb (sourceB indirect) (wanted indirect handler) ∧
      EdgeTransferAt c p.edges 0 (target handler) (index handler) (args indirect handler) tb out e ∧
      c.runBlock (target handler) e = .ok final ∧ GoodAt p.code p.edges (wanted indirect handler) final ∧
      (bodyStateAt p.code p.edges (wanted indirect handler)).le final = true := by
  obtain ⟨fixture⟩ := try_fixture indirect
  rcases fixture with ⟨result,p,rf,af,run,scope,dominated,arity,raw,fallback,accepted,physical,metadata⟩
  have layout := indexed_inst_layout run raw
  obtain ⟨count,atLast,normalParams,handlerParams,edgeRow,cfgOption,rest⟩ := metadata
  have cfg : p.code.cfg = .ok (#[#[2,1],#[],#[]],#[#[],#[0],#[0]]) := by
    cases actual : p.code.cfg <;> simp_all [Except.toOption]
  let preds : Array (Array Nat) := #[#[],#[0],#[0]]
  let c : CheckCtx := ⟨p.code,#[#[2,1],#[],#[]],rf,stateSizeAt p.code p.edges⟩
  let vb := p.code.blocks[0]!
  let tb := p.code.blocks[target handler]!
  have block : p.code.blocks[0]? = some vb := by
    have bound : 0 < p.code.blocks.size := by omega
    dsimp only [vb]; rw [getElem!_pos p.code.blocks 0 bound]
    exact Array.getElem?_eq_getElem bound
  have targetBlock : p.code.blocks[target handler]? = some tb := by
    have bound : target handler < p.code.blocks.size := by cases handler <;> simp [target] <;> omega
    dsimp only [tb]; rw [getElem!_pos p.code.blocks _ bound]
    exact Array.getElem?_eq_getElem bound
  have firsts : vb.insts = firstInstructions indirect := layout.1
  have retCode : tb.insts = #[.rets [(.vreg (firstParam indirect handler) .int,.x 0)]] := by
    cases handler
    · exact layout.2.1
    · exact layout.2.2.1
  have paramCode : tb.params = params indirect handler := by cases handler <;> assumption
  have slots : c.rf.spillSlots = (spillHomesAt p.code p.edges).size + maxArgsAt p.edges := by
    change rf.spillSlots = _; rw [fallback]; exact (spillAllocAt_storage _ _).1
  have saved : c.rf.saved = calleeSaved := by change rf.saved = _; rw [fallback]; unfold spillAllocAt; split <;> rfl
  have static := static_all count layout 0 vb
  have classes : ∀ (k : Nat) (i : MInst) (ops : Array Operand),vb.insts[k]? = some i →
      i.operands = .ok ops → ∀ o ∈ ops.toList,p.code.classes[o.vreg]? = some o.cls :=
    fun k i ops hi hops => classes_all layout.2.2.2 block hi hops
  have uses : ∀ (k : Nat) (i : MInst) (ops : Array Operand),vb.insts[k]? = some i → i.operands = .ok ops →
      ∀ o ∈ ops.toList,o.kind = .use → availAt vb.insts (fun _ => false) k o.vreg = true := by
    intro k i ops instruction operands o member use
    rw [firsts] at instruction ⊢
    have kBound : k < 3 := (Array.getElem?_eq_some_iff.mp instruction).1
    have checked := List.all_eq_true.mp (uses_observed indirect) k (List.mem_range.mpr kBound)
    rw [instruction] at checked
    dsimp only at checked
    rw [operands] at checked
    dsimp only at checked
    have useChecked := Array.all_eq_true_iff_forall_mem.mp checked o (Array.mem_toList_iff.mp member)
    simpa only [use,BEq.rfl,ite_true] using useChecked
  have preRun := spill_body_prefix_runs slots saved block (fun k i hi => static k i block hi) classes uses
    (n := 2) (succs := c.succs) (preds := preds) (by rw [firsts]; change 2 < 3; decide)
    (bodyStateAt_good p.code p.edges (fun _ => false))
  have bodyShape : vb.insts.toList.zipIdx.flatMap (PerEdgeSpill.bodyItem p.code p.edges c.succs preds 0 vb) =
      (vb.insts.toList.take 2).zipIdx.flatMap (PerEdgeSpill.bodyItem p.code p.edges c.succs preds 0 vb) ++
        spillInstAt (spillHomesAt p.code p.edges) 2 (last indirect) := by
    have noJump : jumpCopies p.code p.edges c.succs preds 0 = [] := by rfl
    rw [firsts]
    simp [firstInstructions,PerEdgeSpill.bodyItem,firsts,noJump]
  obtain ⟨ops,operands,valid,returns⟩ := last_ok indirect
  have sourceRun : Spill.Runs c vb 0
      (vb.insts.toList.zipIdx.flatMap (PerEdgeSpill.bodyItem p.code p.edges c.succs preds 0 vb))
      (bodyStateAt p.code p.edges (fun _ => false)) (fun k a => k = vb.insts.size ∧
        GoodAt p.code p.edges (sourceB indirect) a ∧
        ∀ x ∈ termEdgeDefs vb (index handler),Sym.vreg x.1.vreg ∈ a.get x.2) := by
    rw [bodyShape]
    refine Spill.Runs.append preRun fun k mid ⟨same,good⟩ => ?_
    subst k
    have atTerm : vb.insts[2]? = some (last indirect) := by rw [firsts]; rfl
    have midGood : GoodAt p.code p.edges (sourceA indirect) mid := by simpa only [sourceA,firsts] using good
    refine (spillInstAt_runs slots saved block atTerm operands valid returns (fun _ => rfl)
      (classes 2 _ ops atTerm operands) (by simpa only [sourceA,firsts] using uses 2 _ ops atTerm operands) midGood).mono ?_
    intro k final ⟨same,good,kept⟩
    exact ⟨same.trans (by rw [firsts]; rfl),good,fun x member => kept x (selected_kept atLast operands member)⟩
  obtain ⟨out,sourceChecked,postGood,live⟩ := sourceRun.run
  have installed := spillAllocAt_block (edges := p.edges) cfg block
  rw [← fallback] at installed
  have noStores : spillEntryStoresAt (spillHomesAt p.code p.edges) p.code c.succs preds 0 = [] := by rfl
  have noCopies : spillEntryCopiesAt (spillHomesAt p.code p.edges) p.code p.edges c.succs preds 0 = [] := by rfl
  have placed : rf.blocks[0]? = some ((spillSaves ++ vb.insts.toList.zipIdx.flatMap
      (PerEdgeSpill.bodyItem p.code p.edges c.succs preds 0 vb)).toArray) := by
    change rf.blocks[0]? = some (((if 0 == 0 then spillSaves else []) ++
      spillEntryStoresAt (spillHomesAt p.code p.edges) p.code c.succs preds 0 ++
      spillEntryCopiesAt (spillHomesAt p.code p.edges) p.code p.edges c.succs preds 0 ++
      vb.insts.toList.zipIdx.flatMap (PerEdgeSpill.bodyItem p.code p.edges c.succs preds 0 vb)).toArray) at installed
    simpa only [show ((0 : Nat) == 0) = true from rfl,ite_true,noStores,noCopies,List.append_nil] using installed
  have ordinaryClass : p.code.classes[ordinaryV indirect]? = some .int := by
    have inst : vb.insts[0]? = some (.movWide .movZ (.vreg (ordinaryV indirect) .int) ⟨9,0⟩ .size64) := by rw [firsts]; rfl
    have op : (MInst.movWide .movZ (.vreg (ordinaryV indirect) .int) ⟨9,0⟩ .size64).operands =
        .ok #[⟨ordinaryV indirect,.int,.def,.late,.reg⟩] := by rfl
    exact classes 0 _ _ inst op ⟨ordinaryV indirect,.int,.def,.late,.reg⟩ (by simp)
  have retAt : tb.insts[0]? = some (.rets [(.vreg (firstParam indirect handler) .int,.x 0)]) := by rw [retCode]; rfl
  have retOperands : (MInst.rets [(.vreg (firstParam indirect handler) .int,.x 0)]).operands =
      .ok #[⟨firstParam indirect handler,.int,.use,.early,.fixed (.x 0)⟩] := by rfl
  have firstClass : p.code.classes[firstParam indirect handler]? = some .int :=
    classes_all layout.2.2.2 targetBlock retAt retOperands ⟨firstParam indirect handler,.int,.use,.early,.fixed (.x 0)⟩ (by simp)
  have retClasses : ∀ os,(MInst.rets [(.vreg (firstParam indirect handler) .int,.x 0)]).operands = .ok os →
      ∀ o ∈ os.toList,p.code.classes[o.vreg]? = some o.cls :=
    fun os hops => classes_all layout.2.2.2 targetBlock retAt hops
  have retUses : ∀ os,(MInst.rets [(.vreg (firstParam indirect handler) .int,.x 0)]).operands = .ok os →
      ∀ o ∈ os.toList,o.kind = .use → wanted indirect handler o.vreg = true := by
    intro os hops o member use
    rw [retOperands] at hops
    cases hops
    have same : o = ⟨firstParam indirect handler,.int,.use,.early,.fixed (.x 0)⟩ := by simpa using member
    subst o
    simp [wanted]
  have retStatic := static_all count layout (target handler) tb 0 _ targetBlock retAt
  have ordinaryAvailable : sourceB indirect (ordinaryV indirect) = true := by cases indirect <;> decide +kernel
  have retUnavailable : sourceB indirect (retV indirect) = false := by cases indirect <;> decide +kernel
  have payUnavailable : sourceB indirect (retV indirect+2) = false := by cases indirect <;> decide +kernel
  have defs : termEdgeDefs vb (index handler) = livePairs indirect handler := live_pairs atLast
  have availability : EntryAvailAt p.code vb (index handler) (args indirect handler) tb (sourceB indirect) (wanted indirect handler) := by
    constructor
    · intro i ar arAt
      cases handler
      · have bound : i < 2 := (Array.getElem?_eq_some_iff.mp arAt).1
        have choices : i = 0 ∨ i = 1 := by omega
        rcases choices with rfl | rfl
        · change some (.vreg (retV indirect) .int) = some ar at arAt
          cases arAt
          exact .inr ⟨(⟨retV indirect,.int,.def,.late,.fixed (.x 0)⟩,Loc.reg (.x 0)),by rw [defs]; simp [livePairs],rfl,rfl⟩
        · change some (.vreg (ordinaryV indirect) .int) = some ar at arAt
          cases arAt
          exact .inl ordinaryAvailable
      · have bound : i < 3 := (Array.getElem?_eq_some_iff.mp arAt).1
        have choices : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases choices with rfl | rfl | rfl
        · change some (.vreg (retV indirect) .int) = some ar at arAt
          cases arAt
          exact .inr ⟨(⟨retV indirect,.int,.def,.late,.fixed (.x 0)⟩,Loc.reg (.x 0)),by rw [defs]; simp [livePairs],rfl,rfl⟩
        · change some (.vreg (retV indirect+2) .int) = some ar at arAt
          cases arAt
          exact .inr ⟨(⟨retV indirect+2,.int,.def,.late,.fixed (.x 1)⟩,Loc.reg (.x 1)),by rw [defs]; simp [livePairs],rfl,rfl⟩
        · change some (.vreg (ordinaryV indirect) .int) = some ar at arAt
          cases arAt
          exact .inl ordinaryAvailable
    · intro i ar arAt available
      cases handler
      · have bound : i < 2 := (Array.getElem?_eq_some_iff.mp arAt).1
        have choices : i = 0 ∨ i = 1 := by omega
        rcases choices with rfl | rfl
        · change some (.vreg (retV indirect) .int) = some ar at arAt
          cases arAt
          dsimp only [Reg.homeNum] at available
          rw [retUnavailable] at available
          cases available
        · change some (.vreg (ordinaryV indirect) .int) = some ar at arAt
          cases arAt
          exact ordinaryClass
      · have bound : i < 3 := (Array.getElem?_eq_some_iff.mp arAt).1
        have choices : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases choices with rfl | rfl | rfl
        · change some (.vreg (retV indirect) .int) = some ar at arAt
          cases arAt
          dsimp only [Reg.homeNum] at available
          rw [retUnavailable] at available
          cases available
        · change some (.vreg (retV indirect+2) .int) = some ar at arAt
          cases arAt
          dsimp only [Reg.homeNum] at available
          rw [payUnavailable] at available
          cases available
        · change some (.vreg (ordinaryV indirect) .int) = some ar at arAt
          cases arAt
          exact ordinaryClass
    · intro p' member available
      rw [paramCode] at member
      cases handler
      · simp [params] at member
        rcases member with rfl | rfl
        · exact firstClass
        · have absent : wanted indirect false (retV indirect+4) = false := by cases indirect <;> decide +kernel
          dsimp only [Reg.homeNum] at available
          rw [absent] at available
          cases available
      · simp [params] at member
        rcases member with rfl | rfl | rfl
        · exact firstClass
        · have absent : wanted indirect true (retV indirect+6) = false := by cases indirect <;> decide +kernel
          dsimp only [Reg.homeNum] at available
          rw [absent] at available
          cases available
        · have absent : wanted indirect true (retV indirect+7) = false := by cases indirect <;> decide +kernel
          dsimp only [Reg.homeNum] at available
          rw [absent] at available
          cases available
    · intro v required outside
      simp only [wanted,Bool.or_eq_true,beq_iff_eq] at required
      rcases required with rfl | rfl
      · apply False.elim (outside ?_)
        rw [paramCode]
        cases handler <;> simp [params,firstParam,Reg.homeNum]
      · exact ordinaryAvailable
  obtain ⟨e,final,transfer,checked,finalGood,least⟩ := stock_spill_return_successor_runs run scope dominated.ssa raw (by rfl)
    (by change rf = _; exact fallback) cfg block targetBlock (by rfl : c.succs[0]? = some #[2,1])
    (by cases handler <;> rfl) (by cases handler <;> rfl) edgeRow (by cases handler <;> rfl)
    atLast operands valid availability postGood live (by cases handler <;> decide) retCode retStatic retClasses retUses
  have retPreserves : availInst (.rets [(.vreg (firstParam indirect handler) .int,.x 0)]) (wanted indirect handler) = wanted indirect handler := by
    funext v
    unfold availInst
    rw [retOperands]
    rfl
  rw [retPreserves] at finalGood least
  exact ⟨result,p,rf,af,c,vb,tb,out,e,final,preds,run,scope,dominated,arity,raw,fallback,accepted,physical,
    rfl,rfl,cfg,block,targetBlock,placed,sourceChecked,postGood,live,availability,transfer,checked,finalGood,least⟩

end Backend.Stock.Proof.EntryGoodWitness
