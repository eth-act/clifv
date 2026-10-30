import FV.Backend.Proof.StockScalarCompletePre
import FV.Backend.Proof.AbiClass
import FV.Backend.Proof.StockContext

/-!
# Completeness of the scalar route, phase 2: one `ret` block

For a function with one block that ends in `ret`, the actual traversal is a single original
node with no successors. `Stock.lower` then succeeds as soon as that block's core lowering
(`lowerBlockCore`: the body scan) succeeds; every other step of the driver is total here.
-/

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false

/-- The traversal of a single block without successors: one original node. -/
def singleOrder : Order := { nodes := #[.original 0], successors := #[#[]] }

theorem blockOrder_single {f : Clif.Function} {b : Clif.Block} {xs : List Nat}
    (blocks : f.blocks = [b]) (ret : b.term = .ret xs) : blockOrder f = .ok singleOrder := by
  obtain ⟨id,params,cold,body,term⟩ := b
  simp only at ret
  subst ret
  unfold blockOrder
  rw [blocks]
  cbv

private theorem forIn_ne_error {ε α β : Type} {body : α → β → Except ε (ForInStep β)}
    {l : List α} {init : β} {e : ε} (hb : ∀ x ∈ l, ∀ s, ∃ s', body x s = .ok (.yield s')) :
    forIn l init body ≠ .error e := by
  obtain ⟨r,hr⟩ := forIn_ok' body l init hb
  rw [hr]
  intro h
  cases h

/-- The entry block's assembly succeeds: the signature places its parameters, and every used
parameter has a register. -/
theorem assembleOriginalBlock_entry_ok {ctx : Ctx} {f : Clif.Function} {b : Clif.Block}
    {label : Nat} {outgoing : Array (Array Reg)} {bytes : List Nat} {uses : Array UseState}
    {code : Array MInst} (hargs : ∃ locs n, sigArgLocs f.sig = .ok (locs,n))
    (params : ∀ v ∈ b.params, (ctx.valueReg? v.1).isSome = true) :
    ∃ vb, assembleOriginalBlock ctx f b 0 label #[] outgoing bytes uses code = .ok vb := by
  obtain ⟨locs,n,hlocs⟩ := hargs
  unfold assembleOriginalBlock
  simp only [beq_self_eq_true,ite_true,hlocs,bind,Except.bind,pure,Except.pure]
  split
  · rename_i err heq
    refine absurd heq (forIn_ne_error fun x hx s => ?_)
    have hv : x.1.1 ∈ b.params := (List.of_mem_zip (List.of_mem_zip hx).1).1
    obtain ⟨reg,hreg⟩ := Option.isSome_iff_exists.mp (params x.1.1 hv)
    by_cases hu : (uses[x.1.1.fst]! == UseState.unused) = true
    · exact ⟨(s.1,s.2),by simp only [hu,ite_true]⟩
    · simp only [hu,Bool.false_eq_true,ite_false,hreg]
      split <;> exact ⟨_,rfl⟩
  · split <;> exact ⟨_,rfl⟩

/-- The single original node lowers when its block core does. -/
theorem lowerNode_single {ctx : Ctx} {ranges : Array (Nat × Nat)} {f : Clif.Function}
    {bytes : List Nat} {input : DriverState} {b : Clif.Block} {xs : List Nat}
    (blocks : f.blocks = [b]) (ret : b.term = .ret xs) (noSretRet : sretRet f = [])
    (rets : sigRets f.sig = f.sig.returns)
    (hargs : ∃ locs n, sigArgLocs f.sig = .ok (locs,n))
    (params : ∀ v ∈ b.params, (ctx.valueReg? v.1).isSome = true)
    {lowered : LoweredBlockCore}
    (core : lowerBlockCore ctx singleOrder f b 0 ranges[0]!.1 ranges[0]!.2
      (instDataV "MultiAry" [opcodeV "Return", .values xs]) #[] input.state = .ok lowered) :
    ∃ d, lowerNode ctx ranges singleOrder f bytes 0 input = .ok d := by
  have h1 : (#[Node.original 0] : Array Node)[0]! = .original 0 := rfl
  have h2 : ([b] : List Clif.Block)[0]! = b := rfl
  have h3 : (#[#[]] : Array (Array Nat))[0]! = #[] := rfl
  obtain ⟨vb,hvb⟩ := assembleOriginalBlock_entry_ok (ctx := ctx) (b := b) (label := 0)
    (outgoing := lowered.outgoing) (bytes := bytes) (uses := lowered.state.uses) (code := lowered.code)
    hargs params
  simp only [singleOrder] at core
  unfold lowerNode
  simp only [singleOrder,blocks,h1,h2,h3,ret,termData,abiTerm,noSretRet,List.append_nil,rets,
    bne_self_eq_false,Bool.and_false,Bool.false_eq_true,ite_false,bind,Except.bind,pure,Except.pure,
    core,hvb]
  exact ⟨_,rfl⟩

/-- On one block that ends in `ret`, without `sret`, `Stock.lower` succeeds when the block's
core lowering succeeds from the initial state. -/
theorem stock_lower_single_ret {f : Clif.Function} (hdrv : driverInB f = true)
    (hp : f.sig.params.all Scalar.narrowAbiEligible = true)
    (hr : f.sig.returns.all Scalar.narrowAbiEligible = true)
    {b : Clif.Block} {xs : List Nat} (blocks : f.blocks = [b]) (ret : b.term = .ret xs)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (built : Stock.buildCtx f = .ok (ctx, ranges, initial))
    (params : ∀ v ∈ b.params, (ctx.valueReg? v.1).isSome = true)
    {lowered : LoweredBlockCore}
    (core : lowerBlockCore ctx singleOrder f b 0 ranges[0]!.1 ranges[0]!.2
      (instDataV "MultiAry" [opcodeV "Return", .values xs]) #[] initial = .ok lowered) :
    ∃ result, Stock.lower f = .ok result := by
  obtain ⟨conv,⟨bytes,hbytes⟩,wide,sret,eight⟩ := stock_prechecks hdrv hp hr
  have rets : sigRets f.sig = f.sig.returns := by
    have none : f.sig.params.find? (·.purpose == .sret) = none := by
      rw [List.find?_eq_none]
      intro q hm hs
      have hn := List.all_eq_true.mp hp q hm
      simp only [Scalar.narrowAbiEligible,Bool.and_eq_true,beq_iff_eq] at hn hs
      rw [hn.1] at hs
      cases hs
    simp only [sigRets,none]
  have noSretRet : sretRet f = [] := by simp only [sretRet,rets,bne_self_eq_false,Bool.false_eq_true,ite_false]
  unfold Stock.lower
  simp only [conv,Bool.not_true,Bool.false_eq_true,ite_false,hbytes,wide,sret,Bool.false_and,
    blockOrder_single blocks ret,built,bind,Except.bind,pure,Except.pure]
  have none8 : (retRegs (sigRets f.sig).length).isNone = false := by
    cases h : retRegs (sigRets f.sig).length <;> simp_all
  have range1 : (Array.range singleOrder.nodes.size).reverse.toList = [0] := rfl
  have hargs : ∃ locs n, sigArgLocs f.sig = .ok (locs,n) := sigArgLocs_ok hbytes
  obtain ⟨d,hd⟩ := lowerNode_single (bytes := bytes)
    (input := { state := initial, blocks := Array.replicate singleOrder.nodes.size default, edgeArgs := Array.replicate singleOrder.nodes.size #[], schedule := #[], scans := #[], blockScans := #[], rules := #[] })
    blocks ret noSretRet rets hargs params core
  simp only [none8,Bool.false_eq_true,ite_false,range1,List.foldlM_cons,List.foldlM_nil,hd,bind,
    Except.bind,pure,Except.pure]
  exact ⟨_,rfl⟩
private def blockFixture : Clif.Function := {
  name := "scalar_complete_block"
  sig := { params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩], returns := [⟨.i64,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0, .i64), (1, .i64)], body := [⟨[2], .binary .iadd .i64 0 1⟩], term := .ret [2] }] }

private def blockFixtureChecks : Bool :=
  match Stock.buildCtx blockFixture with
  | .error _ => false
  | .ok (ctx,ranges,initial) =>
    blockFixture.blocks.all (fun b => b.params.all fun v => (ctx.valueReg? v.1).isSome) &&
    match blockFixture.blocks with
    | [b] =>
      match lowerBlockCore ctx singleOrder blockFixture b 0 ranges[0]!.1 ranges[0]!.2
          (instDataV "MultiAry" [opcodeV "Return", .values [2]]) #[] initial with
      | .ok _ => true
      | .error _ => false
    | _ => false

-- witness: native_decide (one fixed context build and block-core lowering only)
private theorem blockFixtureChecks_true : blockFixtureChecks = true := by native_decide

/-- Non-vacuity: a real scalar-class function inhabits every hypothesis of
`stock_lower_single_ret`, including a successful block core. -/
theorem stock_lower_single_ret_witness :
    ∃ (f : Clif.Function) (b : Clif.Block) (xs : List Nat) (ctx : Ctx)
      (ranges : Array (Nat × Nat)) (initial : State) (lowered : LoweredBlockCore),
      driverInB f = true ∧ f.sig.params.all Scalar.narrowAbiEligible = true ∧
      f.sig.returns.all Scalar.narrowAbiEligible = true ∧ f.blocks = [b] ∧ b.term = .ret xs ∧
      Stock.buildCtx f = .ok (ctx,ranges,initial) ∧ (∀ v ∈ b.params, (ctx.valueReg? v.1).isSome = true) ∧
      lowerBlockCore ctx singleOrder f b 0 ranges[0]!.1 ranges[0]!.2
        (instDataV "MultiAry" [opcodeV "Return", .values xs]) #[] initial = .ok lowered := by
  have h := blockFixtureChecks_true
  unfold blockFixtureChecks at h
  cases built : Stock.buildCtx blockFixture with
  | error message => simp [built] at h
  | ok triple =>
    obtain ⟨ctx,ranges,initial⟩ := triple
    simp only [built,Bool.and_eq_true] at h
    obtain ⟨hparams,hcore⟩ := h
    cases core : lowerBlockCore ctx singleOrder blockFixture blockFixture.blocks[0]! 0 ranges[0]!.1
        ranges[0]!.2 (instDataV "MultiAry" [opcodeV "Return", .values [2]]) #[] initial with
    | error message =>
      change (match lowerBlockCore ctx singleOrder blockFixture blockFixture.blocks[0]! 0 ranges[0]!.1
        ranges[0]!.2 (instDataV "MultiAry" [opcodeV "Return", .values [2]]) #[] initial with
        | .ok _ => true | .error _ => false) = true at hcore
      rw [core] at hcore
      cases hcore
    | ok lowered =>
      refine ⟨blockFixture,blockFixture.blocks[0]!,[2],ctx,ranges,initial,lowered,
        by decide +kernel,by decide +kernel,by decide +kernel,rfl,rfl,built,?_,core⟩
      intro v hv
      exact List.all_eq_true.mp (List.all_eq_true.mp hparams _ List.mem_cons_self) v hv
end Backend.Stock.Proof
