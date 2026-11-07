import FV.Backend.Proof.StockContext
import FV.Backend.Proof.StockTraversalRecordOrigin
import FV.Backend.Proof.StockScalarCompleteBlock

/-! Source-derived scheduling facts for one block `[y = load x; z = extend y]; return z`.
The metadata loop colors the load and the return, leaves the extension
uncolored, and counts exactly one use of the loaded value. The single block's
scan starts from the initial state. These facts feed Stock's sinking test. -/
namespace Backend.Stock.Memory.SinkExtend
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

private theorem unused_get (n x : Nat) : (Array.replicate n UseState.unused)[x]! = .unused := by
  simp only [getElem!_def,Array.getElem?_replicate]; split <;> simp_all <;> rfl

/-- The exact use analysis counts one use of the middle value of a three-value chain. -/
theorem useStates_chain (ctx : Ctx) {x y z : Nat} (sret : sretRet ctx.func = []) (xy : x ≠ y)
    (zy : z ≠ y) (xz : x ≠ z) (bound : y < ctx.valTy.size) :
    (useStates ctx #[[x],[y],[z]])[y]! = .once := by
  unfold useStates
  have first : (UseState.unused == UseState.multiple || UseState.once != UseState.multiple) = true := by
    decide
  have yz : y ≠ z := Ne.symm zy
  simp only [sret,List.forIn_nil,Id.run_pure,← Array.forIn_toList,List.forIn_cons,unused_get,
    UseState.inc,Array.getElem!_set!_ne _ _ _ _ xy,Array.getElem!_set!_ne _ _ _ _ yz,
    Array.getElem!_set!_ne _ _ _ _ xz,first,ite_true,pure_bind]
  simp only [Array.getElem!_set!_ne _ _ _ _ zy]
  rw [Array.getElem!_set!_self _ _ _ (by simp [bound])]

/-- The metadata loop on a load/extension block whose load is plain or atomic. -/
theorem metadata_chain_of (ctx : Ctx) (ranges : Array (Nat × Nat)) {b : Clif.Block} {x y z : Nat}
    {first : Clif.Inst} {out : Clif.Ty} {op : Clif.ExtendOp}
    (loads : (∃ ty flags,first = .load .load ty flags x 0) ∨ ∃ ty flags,first = .atomicLoad ty flags x)
    (blocks : ctx.func.blocks = [b])
    (body : b.body = [⟨[y],first⟩,⟨[z],.extend op out y⟩]) (ret : b.term = .ret [z])
    (range : ranges[0]! = (0,3)) (size : ctx.insts.size = 3) :
    (sourceMetadata ctx ranges).args = #[[x],[y],[z]] ∧
      (sourceMetadata ctx ranges).entryColor = #[1,0,2] := by
  rcases loads with ⟨ty,flags,rfl⟩ | ⟨ty,flags,rfl⟩
  all_goals
    simp only [sourceMetadata,blocks,body,ret,size,range,List.zipIdx_cons,List.zipIdx_nil,
      List.forIn_cons,List.forIn_nil,Id.run_bind,Id.run_pure,colored,mustLower,Stock.instArgs,
      Stock.termArgs]
    simp only [Bool.or_true,Bool.or_false,ite_true,ite_false,Bool.false_eq_true,Id.run_pure,
      pure_bind,Nat.add_zero,Nat.zero_add,Nat.reduceAdd,Nat.reduceSub]
    constructor <;> rfl

/-- The metadata loop on the load/extension block: operand lists and memory colors. -/
theorem metadata_chain (ctx : Ctx) (ranges : Array (Nat × Nat)) {b : Clif.Block} {x y z : Nat}
    {ty out : Clif.Ty} {flags : Clif.MemFlags} {op : Clif.ExtendOp} (blocks : ctx.func.blocks = [b])
    (body : b.body = [⟨[y],.load .load ty flags x 0⟩,⟨[z],.extend op out y⟩]) (ret : b.term = .ret [z])
    (range : ranges[0]! = (0,3)) (size : ctx.insts.size = 3) :
    (sourceMetadata ctx ranges).args = #[[x],[y],[z]] ∧
      (sourceMetadata ctx ranges).entryColor = #[1,0,2] :=
  metadata_chain_of ctx ranges (Or.inl ⟨ty,flags,rfl⟩) blocks body ret range size

/-- Successful context construction gives the block's colors, one use of the loaded
value and no sunk instruction, for a plain or an atomic load. -/
theorem initial_chain_of {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) (dominated : Dominated f)
    {b : Clif.Block} (blocks : f.blocks = [b]) {x y z : Nat} {first : Clif.Inst} {out : Clif.Ty}
    {op : Clif.ExtendOp}
    (loads : (∃ ty flags,first = .load .load ty flags x 0) ∨ ∃ ty flags,first = .atomicLoad ty flags x)
    (body : b.body = [⟨[y],first⟩,⟨[z],.extend op out y⟩]) (ret : b.term = .ret [z])
    (parameter : x ∈ b.params.map (·.1)) (noSret : sretRet f = []) :
    initial.entryColor = #[1,0,2] ∧ initial.uses[y]! = .once ∧ initial.sunk = #[false,false,false] := by
  obtain ⟨original,st0,requests,oldBuild,_,finished⟩ := buildCtx_allocation build
  have spec := ctxSpec_of oldBuild
  have found : f.blocks[0]? = some b := by rw [blocks]; rfl
  have range : ranges[0]! = (0,3) := by
    simp only [getElem!_def,spec.ranges 0 b found,blockStart,body]
    simp
  have size : original.insts.size = 3 := by
    rw [spec.facts.insts]
    simp [blockStart,blocks,body]
  have originalBlocks : original.func.blocks = [b] := by rw [spec.func]; exact blocks
  obtain ⟨args,colors⟩ := metadata_chain_of original ranges loads originalBlocks body ret range size
  have defs : valueDefs f = b.params.map (·.1) ++ [y,z] := by
    simp [valueDefs,blocks,body]
  have distinct := dominated.ssa
  rw [defs] at distinct
  have xy : x ≠ y := by
    intro same; subst same
    exact (List.nodup_append.mp distinct).2.2 x parameter x (by simp) rfl
  have xz : x ≠ z := by
    intro same; subst same
    exact (List.nodup_append.mp distinct).2.2 x parameter x (by simp) rfl
  have yz : y ≠ z := by
    intro same; subst same
    have tail := (List.nodup_append.mp distinct).2.1
    simp at tail
  have member : y ∈ valueDefs f := by rw [defs]; simp
  have bound : y < original.valTy.size := by
    have small := (spec.facts.vals y member).1
    rw [spec.facts.size.1] at small
    rw [spec.facts.size.2.2]
    exact small
  have state := congrArg (fun p : Ctx × Array (Nat × Nat) × State => p.2.2) finished
  dsimp only [finishCtx] at state
  rw [state]
  refine ⟨colors,?_,?_⟩
  · change (useStates {original with valReg := _} (sourceMetadata original ranges).args)[y]! = .once
    rw [args]
    exact useStates_chain _ (by rw [spec.func]; exact noSret) xy (Ne.symm yz) xz bound
  · change Array.replicate original.insts.size false = _
    rw [size]
    rfl

/-- Successful context construction gives the block's colors, one use of the loaded
value and no sunk instruction. -/
theorem initial_chain {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) (dominated : Dominated f)
    {b : Clif.Block} (blocks : f.blocks = [b]) {x y z : Nat} {ty out : Clif.Ty}
    {flags : Clif.MemFlags} {op : Clif.ExtendOp}
    (body : b.body = [⟨[y],.load .load ty flags x 0⟩,⟨[z],.extend op out y⟩]) (ret : b.term = .ret [z])
    (parameter : x ∈ b.params.map (·.1)) (noSret : sretRet f = []) :
    initial.entryColor = #[1,0,2] ∧ initial.uses[y]! = .once ∧ initial.sunk = #[false,false,false] :=
  initial_chain_of build dominated blocks (Or.inl ⟨ty,flags,rfl⟩) body ret parameter noSret

/-- A return-only signature has no implicit `sret` return value. -/
theorem sretRet_ordinary {f : Clif.Function}
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false) : sretRet f = [] := by
  unfold sretRet
  have same : sigRets f.sig = f.sig.returns := by
    unfold sigRets at ordinary ⊢
    cases found : f.sig.params.find? (·.purpose == .sret) with
    | none => rfl
    | some p =>
      rw [found] at ordinary
      have sret : (p.purpose == .sret) = true := List.find?_some (p := fun a : Clif.AbiParam => a.purpose == .sret) found
      cases empty : f.sig.returns.isEmpty with
      | true => simp [empty,sret] at ordinary
      | false => simp
  simp [same]

/-- The scan of a single block that returns starts from the initial state, with
the block's end color as the current memory color. -/
theorem single_event_input {f : Clif.Function} {result : Result} (run : Stock.lower f = .ok result)
    {b : Clif.Block} {xs : List Nat} (blocks : f.blocks = [b]) (ret : b.term = .ret xs)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    event.input = {result.initial with color := some result.initial.endColor[0]!} := by
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,bi,data,core,
    build,ordered,initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,
    eventEq,stateEq⟩ := stock_lower_blockScanOrigin run events
  have orderEq : result.order = singleOrder :=
    (Except.ok.inj ((blockOrder_single blocks ret).symm.trans ordered)).symm
  rw [orderEq] at parts node coreRun
  have one : (Array.range singleOrder.nodes.size).reverse.toList = [0] := rfl
  rw [one] at parts
  obtain ⟨rfl,rfl,rfl⟩ : earlier = [] ∧ label = 0 ∧ suffix = [] := by
    rcases earlier with _ | ⟨e,rest⟩
    · simp only [List.nil_append,List.cons.injEq] at parts
      exact ⟨rfl,parts.1.symm,parts.2.symm⟩
    · simp at parts
  simp only [List.foldlM_nil,pure,Except.pure,Except.ok.injEq] at prefixRun
  subst prefixRun
  have nodeZero : singleOrder.nodes[0]! = .original 0 := rfl
  rw [nodeZero] at node
  cases node
  have blockZero : f.blocks[0]! = b := by simp [blocks]
  have successors : singleOrder.successors[0]! = #[] := rfl
  rw [blockZero,successors,initial] at coreRun
  unfold lowerBlockCore at coreRun
  have emptyTargets : (#[] : Array Nat).zipIdx.toList = [] := rfl
  simp only [ret,collectOutgoing,emptyTargets,List.foldlM_nil,Bool.false_eq_true,ite_false,
    Option.map_none,Option.getD_none,bind,Except.bind,pure,Except.pure] at coreRun
  split at coreRun
  · cases coreRun
  · cases coreRun
    subst eventEq
    rfl

end Backend.Stock.Memory.SinkExtend
