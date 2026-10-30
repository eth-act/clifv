import FV.Backend.Proof.PerEdgeSpillBlock
import FV.Backend.Proof.SpillCtlForms
import FV.Backend.Proof.PerEdgeSpillInstFixture

namespace Backend.Stock.Proof.IndexedInstWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgeSpill
open Backend.Stock.Proof.SpillEntryFixture Backend.Stock.Proof.IndexedInstFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

private def contents (vc : VCode) (edges : Array (Array (Array Reg))) (A : Nat → Bool) : Loc → List Sym
  | .stack n cl => ((List.range vc.classes.size).filter fun v =>
      A v && decide (vc.classes[v]? = some cl) &&
        decide (homeLookup (spillHomesAt vc edges) (spillHomeKeyAt v cl) = some n)).map .vreg
  | .save r => if r ∈ calleeSaved then [.entry r] else []
  | _ => []
private def state (p : EdgeVCode) (A : Nat → Bool) : AState :=
  mkState (stateSizeAt p.code p.edges) (contents p.code p.edges A)
private theorem state_good (p : EdgeVCode) (A : Nat → Bool) : GoodAt p.code p.edges A (state p A) := by
  constructor
  · exact size_mkState _ _
  · intro v cl n available classes home
    have bound := (spillHomesAt_spec p.code p.edges).valid.1 _ _ home
    have index : ∃ i,(Loc.stack n cl).index = some i ∧ i < stateSizeAt p.code p.edges := by
      cases cl <;> exact ⟨_,rfl,by unfold stateSizeAt; omega⟩
    obtain ⟨i,atIndex,iBound⟩ := index
    rw [state,get_mkState atIndex iBound]
    simp only [contents,List.mem_map,List.mem_filter,List.mem_range,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨v,⟨(Array.getElem?_eq_some_iff.mp classes).1,⟨⟨available,classes⟩,home⟩⟩,rfl⟩
  · intro r saved
    obtain ⟨i,atIndex,iBound⟩ := save_index saved
    have bound : i < stateSizeAt p.code p.edges := by unfold stateSizeAt; omega
    rw [state,get_mkState atIndex bound]
    simp only [contents,if_pos saved,List.mem_singleton]

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

/-- Complete direct/indirect original Stock sources instantiate the new dense
instruction theorem at every actual instruction, including TryCall and both
return blocks. Actual nonempty home/save states witness its invariant; checked
allocation and physical lowering are retained. This is checker-state transport,
not source/Arm realization or universal fallback acceptance. -/
theorem stock_indexed_instructions_witness (indirect : Bool) :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc) (c : CheckCtx),
      Stock.lower (function indirect) = .ok result ∧ LowerScope (function indirect) ∧
      Dominated (function indirect) ∧ ArityOk (function indirect) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧
      rf = spillAllocAt p.code p.edges ∧ checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      c.vc = p.code ∧ c.rf = rf ∧ p.code.blocks.size = 3 ∧
      (∀ v,p.code.classes[v]? = some .int →
        (∃ n,homeLookup (spillHomesAt p.code p.edges) (spillHomeKeyAt v .int) = some n) →
        Sym.vreg v ∈ (state p (fun _ => true)).get (spillHomeAt (spillHomesAt p.code p.edges) v .int)) ∧
      ∀ (b : Nat) (vb : VBlock) (k : Nat) (i : MInst),p.code.blocks[b]? = some vb → vb.insts[k]? = some i →
        ∃ (ops : Array Operand),i.operands = .ok ops ∧ GoodAt p.code p.edges (fun _ => true) (state p (fun _ => true)) ∧
        Runs c vb k (spillInstAt (spillHomesAt p.code p.edges) k i) (state p (fun _ => true))
          (fun k' a' => k' = k+1 ∧ GoodAt p.code p.edges (availInst i (fun _ => true)) a' ∧
            ∀ x ∈ keptPairs i (ops.zip (spillLocs ops i.clobbers)).toList,Sym.vreg x.1.vreg ∈ a'.get x.2) := by
  obtain ⟨fixture⟩ := try_fixture indirect
  rcases fixture with ⟨result,p,rf,af,run,scope,dominated,arity,raw,fallback,accepted,physical,metadata⟩
  have layout := indexed_inst_layout run raw
  have facts := static_all metadata.1 layout
  have header := accepted
  unfold checkAllocAt at header
  obtain ⟨⟨ss,ps⟩,cfg,_⟩ := Except.bind_ok header
  let c : CheckCtx := ⟨p.code,ss,rf,stateSizeAt p.code p.edges⟩
  have slots : c.rf.spillSlots = (spillHomesAt p.code p.edges).size + maxArgsAt p.edges := by
    change rf.spillSlots = _; rw [fallback]; exact (spillAllocAt_storage _ _).1
  have saved : c.rf.saved = calleeSaved := by change rf.saved = _; rw [fallback]; unfold spillAllocAt; split <;> rfl
  refine ⟨result,p,rf,af,c,run,scope,dominated,arity,raw,fallback,accepted,physical,rfl,rfl,metadata.1,?_,?_⟩
  · intro v classes ⟨n,home⟩
    have eq : spillHomeAt (spillHomesAt p.code p.edges) v .int = .stack n .int := by
      unfold spillHomeAt
      change homeLookup (spillHomesAt p.code p.edges) (spillHomeKeyAt v .int) = some n at home
      unfold homeLookup at home
      rw [home]; rfl
    rw [eq]
    exact (state_good p (fun _ => true)).home v .int n rfl classes home
  · intro b vb k i block instruction
    obtain ⟨ops,operands,valid,returns⟩ := facts b vb k i block instruction
    refine ⟨ops,operands,state_good p (fun _ => true),?_⟩
    have lastTerm : k+1 = vb.insts.size → i.isTerminator = true := by
      intro lastAt
      obtain ⟨T,last,isTerm⟩ := cfg_last cfg block
      have atLast := (back_get last).2
      rw [show vb.insts.size-1=k by omega,instruction] at atLast
      cases atLast
      exact isTerm
    exact spillInstAt_runs slots saved block instruction operands valid returns lastTerm
      (classes_all layout.2.2.2 block instruction operands) (fun _ _ _ => rfl) (state_good p (fun _ => true))

private def usesB (indirect : Bool) : Bool := (List.range 3).all fun k =>
  match (firstInstructions indirect)[k]? with
  | none => false
  | some i => match i.operands with
    | .error _ => false
    | .ok ops => ops.all fun o => if o.kind == .use then availAt (firstInstructions indirect) (fun _ => false) k o.vreg else true
private theorem uses_observed (indirect : Bool) : usesB indirect = true := by cases indirect <;> decide +kernel

/-- The real two-instruction prefix establishes the callee target's availability
from empty homes, then the actual TryCall loads that target and establishes
its physical result symbols. All save cells survive. The complete original
Stock pipeline also passes the checker and physical lowering. -/
theorem stock_indexed_prefix_call_witness (indirect : Bool) :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc) (c : CheckCtx) (vb : VBlock),
      Stock.lower (function indirect) = .ok result ∧ LowerScope (function indirect) ∧
      Dominated (function indirect) ∧ ArityOk (function indirect) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧
      rf = spillAllocAt p.code p.edges ∧ checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      c.vc = p.code ∧ c.rf = rf ∧ p.code.blocks[0]? = some vb ∧ vb.insts = firstInstructions indirect ∧
      (state p (fun _ => false)).size = stateSizeAt p.code p.edges ∧
      GoodAt p.code p.edges (fun _ => false) (state p (fun _ => false)) ∧
      availAt vb.insts (fun _ => false) 2 (retV indirect+8) = true ∧
      availAt vb.insts (fun _ => false) 3 (ordinaryV indirect) = true ∧
      Runs c vb 0 ((vb.insts.toList.take 2).zipIdx.flatMap (bodyItem p.code p.edges c.succs
        #[#[],#[0],#[0]] 0 vb)) (state p (fun _ => false))
        (fun k a => k = 2 ∧ GoodAt p.code p.edges (availAt vb.insts (fun _ => false) 2) a) ∧
      (∃ suffix,rf.blocks[0]? = some ((spillSaves ++
        (vb.insts.toList.take 2).zipIdx.flatMap (bodyItem p.code p.edges c.succs #[#[],#[0],#[0]] 0 vb) ++ suffix).toArray)) ∧
      Runs c vb 0 (vb.insts.toList.zipIdx.flatMap (bodyItem p.code p.edges c.succs #[#[],#[0],#[0]] 0 vb))
        (state p (fun _ => false)) (fun k a => k = 3 ∧ GoodAt p.code p.edges (availAt vb.insts (fun _ => false) 3) a ∧
          ∀ r ∈ calleeSaved,Sym.entry r ∈ a.get (.save r)) := by
  obtain ⟨fixture⟩ := try_fixture indirect
  rcases fixture with ⟨result,p,rf,af,run,scope,dominated,arity,raw,fallback,accepted,physical,metadata⟩
  have layout := indexed_inst_layout run raw
  have cfg : p.code.cfg = .ok (#[#[2,1],#[],#[]],#[#[],#[0],#[0]]) := by
    have optionCfg := metadata.2.2.2.2.2.1
    cases actual : p.code.cfg <;> simp_all [Except.toOption]
  let c : CheckCtx := ⟨p.code,#[#[2,1],#[],#[]],rf,stateSizeAt p.code p.edges⟩
  let vb := p.code.blocks[0]!
  have block : p.code.blocks[0]? = some vb := by
    have bound : 0 < p.code.blocks.size := by rw [metadata.1]; decide
    dsimp only [vb]
    rw [getElem!_pos p.code.blocks 0 bound]
    exact Array.getElem?_eq_getElem bound
  have firsts : vb.insts = firstInstructions indirect := layout.1
  have slots : c.rf.spillSlots = (spillHomesAt p.code p.edges).size + maxArgsAt p.edges := by
    change rf.spillSlots = _; rw [fallback]; exact (spillAllocAt_storage _ _).1
  have saved : c.rf.saved = calleeSaved := by change rf.saved = _; rw [fallback]; unfold spillAllocAt; split <;> rfl
  have static := static_all metadata.1 layout 0 vb
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
  have preRun := spill_body_prefix_runs slots saved block (fun k i hi => static k i block hi)
    (classes) uses (n := 2) (succs := c.succs) (preds := #[#[],#[0],#[0]])
    (by rw [firsts]; change 2 < 3; decide) (state_good p (fun _ => false))
  have bodyShape : vb.insts.toList.zipIdx.flatMap (bodyItem p.code p.edges c.succs #[#[],#[0],#[0]] 0 vb) =
      (vb.insts.toList.take 2).zipIdx.flatMap (bodyItem p.code p.edges c.succs #[#[],#[0],#[0]] 0 vb) ++
        spillInstAt (spillHomesAt p.code p.edges) 2 (last indirect) := by
    have noJump : jumpCopies p.code p.edges c.succs #[#[],#[0],#[0]] 0 = [] := by rfl
    rw [firsts]
    simp [firstInstructions,bodyItem,firsts,noJump]
  have full : Runs c vb 0 (vb.insts.toList.zipIdx.flatMap (bodyItem p.code p.edges c.succs #[#[],#[0],#[0]] 0 vb))
      (state p (fun _ => false)) (fun k a => k = 3 ∧ GoodAt p.code p.edges (availAt vb.insts (fun _ => false) 3) a ∧
        ∀ r ∈ calleeSaved,Sym.entry r ∈ a.get (.save r)) := by
    rw [bodyShape]
    refine Runs.append preRun fun k mid ⟨same,good⟩ => ?_
    subst k
    have atLast : vb.insts[2]? = some (last indirect) := by rw [firsts]; rfl
    obtain ⟨ops,operands,valid,returns⟩ := last_ok indirect
    refine (spillInstAt_runs slots saved block atLast operands valid returns (fun _ => rfl)
      (classes 2 _ ops atLast operands) (uses 2 _ ops atLast operands) good).mono ?_
    intro k final ⟨same,good,_⟩
    have after : GoodAt p.code p.edges (availAt vb.insts (fun _ => false) 3) final := by
      rw [show 3 = 2+1 from rfl,availAt_succ atLast]; exact good
    exact ⟨same,after,after.save⟩
  have installed := spillAllocAt_block (edges := p.edges) cfg block
  rw [← fallback] at installed
  have placed : ∃ suffix,rf.blocks[0]? = some ((spillSaves ++
        (vb.insts.toList.take 2).zipIdx.flatMap (bodyItem p.code p.edges c.succs #[#[],#[0],#[0]] 0 vb) ++ suffix).toArray) := by
    refine ⟨spillInstAt (spillHomesAt p.code p.edges) 2 (last indirect),?_⟩
    have noStores : spillEntryStoresAt (spillHomesAt p.code p.edges) p.code #[#[2,1],#[],#[]] #[#[],#[0],#[0]] 0 = [] := by rfl
    have noCopies : spillEntryCopiesAt (spillHomesAt p.code p.edges) p.code p.edges #[#[2,1],#[],#[]] #[#[],#[0],#[0]] 0 = [] := by rfl
    dsimp only [c] at bodyShape ⊢
    simpa only [show (0 == 0) = true from rfl,ite_true,noStores,noCopies,
      List.append_nil,List.nil_append,bodyShape,List.append_assoc] using installed
  exact ⟨result,p,rf,af,c,vb,run,scope,dominated,arity,raw,fallback,accepted,physical,rfl,rfl,block,firsts,
    (state_good p (fun _ => false)).size,state_good p (fun _ => false),
    by rw [firsts]; cases indirect <;> decide +kernel,
    by rw [firsts]; cases indirect <;> decide +kernel,preRun,placed,full⟩

end Backend.Stock.Proof.IndexedInstWitness
