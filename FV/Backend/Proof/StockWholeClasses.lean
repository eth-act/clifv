import FV.Backend.Proof.StockWholeInstructionClasses
import FV.Backend.Proof.SpillClasses
import FV.Backend.Proof.StockEntryClassContracts
import FV.Backend.Proof.StockDriverAliasClasses
import FV.Backend.Proof.StockScanAliasClasses
import FV.Backend.Proof.StockWholeClassGrowth
import FV.Backend.Proof.StockCoverageDriver
import FV.Backend.Proof.StockEntryOrder
namespace Backend.Stock.Proof.WholeClassesDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Flow Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.BindingClassDraft Backend.Stock.Proof.HelperAliasClassDraft Backend.Stock.Proof.OperandClassDraft
open Backend.Stock.Proof.ScanAliasClassDraft Backend.Stock.Proof.Coverage
open Backend.Stock.Proof.ClassGrowthDraft Backend.Stock.Proof.InitialClassesDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm Stock.lower Stock.externCtor scanBlock emitBranch lowerBlockCore branchArgs collectOutgoing

private structure Inv (initial st : State) : Prop where
  growth : ClassGrowth initial st
  table : st.tryRegs = initial.tryRegs
  aliases : AliasClasses st
  empty : NoOpportunity st

private def fields (st : State) :=
  (st.base.classes,st.base.nextVreg,st.tryRegs,st.alias,st.opportunistic)

private theorem inv_fields {initial before after : State} (old : Inv initial before)
    (same : fields after = fields before) : Inv initial after := by
  have classes := congrArg Prod.fst same
  have frontier := congrArg (fun q => q.2.1) same
  have tables := congrArg (fun q => q.2.2.1) same
  have aliases := congrArg (fun q => q.2.2.2.1) same
  have remembered := congrArg (fun q => q.2.2.2.2) same
  change after.base.classes = before.base.classes at classes
  change after.base.nextVreg = before.base.nextVreg at frontier
  change after.tryRegs = before.tryRegs at tables
  change after.alias = before.alias at aliases
  change after.opportunistic = before.opportunistic at remembered
  refine ⟨clsStep_trans old.growth (clsStep_of_eq classes frontier),tables.trans old.table,?_,?_⟩
  · intro key target entry
    rw [aliases] at entry
    change after.base.classes[key]? = some RegClass.int ∧ after.base.classes[target]? = some RegClass.int
    rw [classes]
    exact old.aliases key target entry
  · intro v
    change after.opportunistic[v]! = none
    rw [remembered]
    exact old.empty v

private theorem fold_fields_eq {α β γ : Type} (field : α → γ)
    (step : α → β → Except String α)
    (hs : ∀ a b next, step a b = .ok next → field next = field a)
    (xs : List β) {a next : α} (h : xs.foldlM step a = .ok next) :
    field next = field a := by
  induction xs generalizing a with
  | nil => cases h; rfl
  | cons x xs ih =>
    rw [List.foldlM_cons] at h
    cases he : step a x with
    | error e => simp only [he, bind, Except.bind] at h; cases h
    | ok middle =>
      simp only [he, bind, Except.bind] at h
      exact (ih h).trans (hs a x middle he)

private theorem forIn_frame {α β γ : Type} (field : α → γ)
    (step : β → α → Except String (ForInStep α))
    (keeps : ∀ x a b, step x a = .ok (.yield b) → field b = field a)
    (no_break : ∀ x a b, step x a ≠ .ok (.done b))
    (xs : List β) {a next : α} (h : forIn xs a step = .ok next) :
    field next = field a := by
  induction xs generalizing a with
  | nil => simp only [List.forIn_nil, pure, Except.pure] at h; cases h; rfl
  | cons x xs ih =>
    rw [List.forIn_cons] at h
    cases call : step x a with
    | error e => simp only [call, bind, Except.bind] at h; cases h
    | ok result =>
      cases result with
      | done b => exact False.elim (no_break x a b call)
      | yield b =>
        simp only [call, bind, Except.bind] at h
        exact (ih h).trans (keeps x a b call)

private def argStep (ctx : Ctx) (rets pays : List Reg) (index nh : Nat)
    (arg : Clif.TryArg) (acc : State × Array Reg) :
    Except String (ForInStep (State × Array Reg)) := do
  match arg with
  | .val v =>
    let some r := ctx.valueReg? v | throw s!"unknown value v{v}"
    pure (.yield (acc.1.mark v, acc.2.push r))
  | .ret i =>
    if index < nh then throw "try_call return on exception edge"
    let some r := rets[i]? | throw "try_call return index"
    pure (.yield (acc.1, acc.2.push r))
  | .exn i =>
    if index == nh then throw "try_call payload on normal edge"
    let some r := pays[i]? | throw "try_call payload index"
    pure (.yield (acc.1, acc.2.push r))

private theorem arg_frame (ctx : Ctx) (rets pays : List Reg) (index nh : Nat)
    (arg : Clif.TryArg) (a b : State × Array Reg)
    (h : argStep ctx rets pays index nh arg a = .ok (.yield b)) :
    fields b.1 = fields a.1 := by
  cases arg <;> unfold argStep at h
  all_goals repeat' first | (solve | cases h <;> rfl) | split at h

private theorem arg_no_break (ctx : Ctx) (rets pays : List Reg) (index nh : Nat)
    (arg : Clif.TryArg) (a b : State × Array Reg) :
    argStep ctx rets pays index nh arg a ≠ .ok (.done b) := by
  intro h
  cases arg <;> unfold argStep at h
  all_goals repeat' first | (solve | cases h) | split at h

private theorem branch_frame {ctx : Ctx} {st next : State} {block index : Nat}
    {args : Array Reg} (h : branchArgs ctx st block index = .ok (args, next)) :
    fields next = fields st := by
  unfold branchArgs at h
  dsimp only at h
  split at h
  · rename_i id values lookup
    split at h
    · rename_i target found
      split at h
      · cases h
      · let ti := (st.instBlock.findIdx? (· == block)).getD 0 + ctx.func.blocks[block]!.body.length
        let reservations := st.tryRegs[ti]!
        let nh := match ctx.func.blocks[block]!.term with
          | .tryCall _ _ et | .tryCallIndirect _ _ et => et.handlers.length
          | _ => 0
        change (do
          let result ← forIn values (st, #[]) (argStep ctx reservations.1 reservations.2 index nh)
          pure (result.2, result.1)) = .ok (args, next) at h
        cases loop : forIn values (st, #[]) (argStep ctx reservations.1 reservations.2 index nh) with
        | error e => simp only [loop, bind, Except.bind] at h; cases h
        | ok result =>
          simp only [loop, bind, Except.bind, pure, Except.pure] at h
          cases h
          exact forIn_frame (fun a : State × Array Reg => fields a.1) _
            (arg_frame ctx reservations.1 reservations.2 index nh)
            (arg_no_break ctx reservations.1 reservations.2 index nh) values loop
    · cases h
  · cases h

private theorem outgoing_frame {ctx : Ctx} {order : Order} {bi : Nat} {targets : Array Nat}
    {st next : State} {outgoing : Array (Array Reg)}
    (h : collectOutgoing ctx order bi targets st = .ok (next, outgoing)) :
    fields next = fields st := by
  unfold collectOutgoing at h
  apply fold_fields_eq (fun a : State × Array (Array Reg) => fields a.1) _ ?_ _ h
  intro acc target result step
  unfold outgoingStep at step
  split at step
  · cases step; rfl
  · cases call : branchArgs ctx acc.1 bi target.2 with
    | error e => simp only [call, bind, Except.bind] at step; cases step
    | ok pair =>
      rcases pair with ⟨regs, state⟩
      simp only [call, bind, Except.bind, pure, Except.pure] at step
      cases step
      exact branch_frame call



private theorem named_alloc {ctx : Ctx} {term : String} {args : List V}
    {st next : State} {out : Option V} {trace : List RuleId}
    (h : Stock.runTerm ctx term args st = .ok (out, next, trace)) :
    AllocationLe st next := by
  unfold Stock.runTerm at h
  cases hr : Isle.Interp.run program (Stock.sem ctx) {} term args st with
  | error e => rw [hr] at h; cases h
  | ok result =>
    rw [hr] at h
    cases h
    unfold Isle.Interp.run at hr
    cases ht : program.termByName? term with
    | none => simp only [ht] at hr; cases hr
    | some t =>
      simp only [ht] at hr
      cases ha : (applyTerm program (Stock.sem ctx) {} (Config.fuel ({} : Config))
          t.ret t.id args).run (st, #[]) with
      | error e => simp only [ha, bind, Except.bind] at hr; cases hr
      | ok result =>
        rcases result with ⟨out, next, trace⟩
        simp only [ha, bind, Except.bind, pure, Except.pure] at hr
        cases hr
        exact stock_apply_allocationLe ha


private theorem branch_keeps {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {t : Clif.Terminator} {bi ti : Nat} {targets : Array Nat} {initial input : State}
    (old : Inv initial input) (reserved : ReservedClasses ctx input) {output : BranchEmission}
    (run : emitBranch ctx f t bi ti targets input = .ok output) : Inv initial output.state := by
  unfold emitBranch at run
  dsimp only at run
  let before : State := {input with current := some ti,color := none,base.emitted := #[]}
  cases call : Stock.runTerm ctx "lower_branch" [.inst ti,.labels targets.toList]
      {input with current := some ti,color := none,base.emitted := #[]} with
  | error e => simp only [call,bind,Except.bind] at run; cases run
  | ok q =>
    rcases q with ⟨out,next,trace⟩
    simp only [call,bind,Except.bind] at run
    split at run
    · cases run
    · cases code : branchCode f t targets next.base.emitted with
      | error e => simp only [code,bind,Except.bind] at run; cases run
      | ok ms =>
        simp only [code,bind,Except.bind,pure,Except.pure] at run
        cases run
        have beforeInv : Inv initial before := inv_fields old rfl
        have beforeReserved : ReservedClasses ctx before := reserved
        have nextAliases := (stock_named_alias_classes beforeReserved beforeInv.aliases call).1
        have nextGrowth := stock_named_classGrowth call
        have nextTables := (named_alloc call).2
        refine ⟨clsStep_trans beforeInv.growth nextGrowth,nextTables.trans beforeInv.table,nextAliases,?_⟩
        intro v
        rw [branch_noOpportunity mapped clean call]
        exact beforeInv.empty v

private theorem clean_stock {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) : Clean (sourceIdentityCtx ctx) := by
  obtain ⟨original,before,legacy,spec,view⟩ := buildCtx_source build
  intro i info lookup
  change ctx.insts[i]? = some info at lookup
  rw [view.insts] at lookup
  exact Cov.clean_of_build legacy i info lookup

private theorem clean_block {f : Clif.Function} {ctx : Ctx}
    (clean : Clean (sourceIdentityCtx ctx)) {t : Clif.Terminator} {data : V}
    (prepared : blockData f t = .ok data) (ti : Nat) (trs : List Reg × List Reg) :
    Clean (sourceIdentityCtx {Driver.termCtx ctx ti data with tryRegs := trs}) := by
  cases t <;> simp only [blockData] at prepared
  all_goals first | exact clean_tryCtx clean prepared ti trs | exact clean_termCtx clean prepared ti

private theorem core_alias {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) (scope : LowerScope f)
    {order : Order} {bi : Nat} {b : Clif.Block} (block : f.blocks[bi]? = some b)
    {range : Nat × Nat} (rangeRun : ranges[bi]? = some range) {data : V}
    (prepared : blockData f b.term = .ok data) {targets : Array Nat} {input : State}
    (old : Inv initial input) {output : LoweredBlockCore}
    (run : lowerBlockCore ctx order f b bi range.1 range.2 data targets input = .ok output) :
    Inv initial output.state := by
  let ti := range.2 - 1
  let selected : Ctx := {Driver.termCtx ctx ti data with tryRegs := input.tryRegs[ti]!}
  obtain ⟨original,before,legacy,spec,view⟩ := buildCtx_source build
  have rangeEq := spec.ranges bi b block
  rw [rangeRun] at rangeEq
  have endEq : ti = blockStart f bi + b.body.length := by cases rangeEq; dsimp [ti] <;> omega
  have ph : ctx.insts[ti]? = some ⟨.op .unit,[],[],none⟩ := by
    rw [view.insts,endEq]
    exact spec.facts.term bi b block
  have mapped : MappedCtxInv f selected := ((buildCtx_mappedInv scope build).termCtx ph data).withTryRegs _
  have clean : Clean (sourceIdentityCtx selected) := clean_block (clean_stock build) prepared ti _
  have initialClasses := InitialClassesDraft.stock_build_classes build
  have initialized := (stock_build_alias_class_inputs build).2.2 ti data
  have reserveAt (st : State) (growth : ClassGrowth initial st) : ReservedClasses selected st := by
    intro r member
    change r ∈ input.tryRegs[ti]!.1 ++ input.tryRegs[ti]!.2 at member
    rw [old.table] at member
    exact intCls_step growth (initialized r member)
  let branchCall : Except String (Option BranchEmission) :=
    if blockBranch b.term then some <$> emitBranch selected f b.term bi ti targets input else pure none
  have branchKeeps {br : Option BranchEmission} (call : branchCall = .ok br) :
      Inv initial (br.map (fun e => e.state) |>.getD input) := by
    unfold branchCall at call
    split at call
    · cases emitted : emitBranch selected f b.term bi ti targets input with
      | error e => simp only [emitted,Functor.map,Except.map] at call; cases call
      | ok e =>
        simp only [emitted,Functor.map,Except.map] at call
        cases call
        exact branch_keeps mapped clean old (reserveAt input old.growth) emitted
    · cases call; exact old
  have normal : lowerBlockCore ctx order f b bi range.1 range.2 data targets input = ((do
    let br ← branchCall
    let edge ← collectOutgoing ctx order bi targets (br.map (fun e => e.state) |>.getD input)
    let next := edge.1
    let outgoing := edge.2
    let beforeScan := {next with color := some next.endColor[bi]!}
    let indices := ((Array.range (range.2-range.1)).map (range.1+·)).reverse.toList
    let body ← scanBlock selected bi ti (blockBranch b.term) indices beforeScan
    pure ⟨body.state,body.code ++ (br.map (fun e => e.code) |>.getD #[]),outgoing,br,
      ⟨selected,bi,ti,blockBranch b.term,indices,beforeScan,body⟩⟩) : Except String LoweredBlockCore) := by
    unfold lowerBlockCore
    dsimp only [branchCall,blockBranch,selected,ti]
    split <;> simp_all only [branchCall,blockBranch,selected,ti] <;> rfl
  rw [normal] at run
  cases call : branchCall with
  | error e => simp only [call,bind,Except.bind] at run; cases run
  | ok br =>
    simp only [call,bind,Except.bind] at run
    cases edges : collectOutgoing ctx order bi targets (br.map (fun e => e.state) |>.getD input) with
    | error e => simp only [edges,bind,Except.bind] at run; cases run
    | ok pair =>
      rcases pair with ⟨next,outgoing⟩
      simp only [edges,bind,Except.bind] at run
      let beforeScan : State := {next with color := some next.endColor[bi]!}
      let indices := ((Array.range (range.2-range.1)).map (range.1+·)).reverse.toList
      have beforeInv : Inv initial beforeScan := inv_fields
        (inv_fields (branchKeeps call) (outgoing_frame edges)) rfl
      have invariant : ClsIs selected beforeScan.base beforeScan.base :=
        ⟨sz_step beforeInv.growth initialClasses.1,
          fun x r lookup => regCls_step beforeInv.growth (initialClasses.2.1 x r lookup),
          fun r member => (reserveAt beforeScan beforeInv.growth r (List.mem_append_left _ member)).1,
          fun r member => (reserveAt beforeScan beforeInv.growth r (List.mem_append_right _ member)).1,
          ⟨[],by simp,by simp⟩⟩
      cases bodyRun : scanBlock selected bi ti (blockBranch b.term)
          ((Array.range (range.2-range.1)).map (range.1+·)).reverse.toList
          {next with color := some next.endColor[bi]!} with
      | error e => simp only [bodyRun,bind,Except.bind] at run; cases run
      | ok body =>
        simp only [bodyRun,bind,Except.bind,pure,Except.pure] at run
        cases run
        have slots := built_scan_slots build scope block rangeRun prepared input.tryRegs[ti]!
        have aliases := stock_scanBlock_alias_classes mapped clean slots invariant
          (reserveAt beforeScan beforeInv.growth) beforeInv.aliases beforeInv.empty bodyRun
        exact ⟨clsStep_trans beforeInv.growth (stock_scanBlock_classGrowth bodyRun),
          (stock_scanBlock_allocationLe bodyRun).2.trans beforeInv.table,aliases.1,aliases.2.2.1⟩

private theorem original_bound {f : Clif.Function} (scope : LowerScope f)
    {order : Order} (ordered : blockOrder f = .ok order) {label bi : Nat}
    (inside : label < order.nodes.size) (node : order.nodes[label]! = .original bi) :
    bi < f.blocks.length := by
  have nonempty : f.blocks.length ≠ 0 := fun h => scope.nonempty (List.length_eq_zero_iff.mp h)
  have lookup : order.nodes[label]? = some (.original bi) := by
    rw [getElem!_pos order.nodes label inside] at node
    simp only [Array.getElem?_eq_getElem inside, node]
  apply (stock_blockOrder_originals_nodup ordered nonempty).2 bi
  unfold stockOriginals
  apply List.mem_filterMap.mpr
  exact ⟨.original bi, Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup), rfl⟩

private def GoodArray (classes : Array RegClass) (rs : Array Reg) : Prop :=
  ∀ r ∈ rs.toList,IntCls classes r
private def GoodRow (classes : Array RegClass) (row : Array (Array Reg)) : Prop :=
  ∀ rs ∈ row.toList,GoodArray classes rs
private def GoodEdges (classes : Array RegClass) (edges : Array (Array (Array Reg))) : Prop :=
  ∀ row ∈ edges.toList,GoodRow classes row
private def GoodBlocks (classes : Array RegClass) (blocks : Array VBlock) : Prop :=
  ∀ b ∈ blocks.toList,∀ r ∈ b.params.toList ++ b.branchArgs.toList,IntCls classes r

private theorem array_set {α : Type} {P : α → Prop} {xs : Array α} {i : Nat} {x : α}
    (old : ∀ y ∈ xs.toList,P y) (fresh : P x) : ∀ y ∈ (xs.set! i x).toList,P y := by
  intro y member
  obtain ⟨j,found⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
  rw [Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds] at found
  split at found
  · split at found
    · cases found; exact fresh
    · cases found
  · exact old y (Array.mem_toList_iff.mpr (Array.mem_of_getElem? found))

private theorem built_inputs {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial st : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial))
    (growth : ClassGrowth initial st) (tables : st.tryRegs = initial.tryRegs) :
    (∀ v r,ctx.valueReg? v = some r → IntCls st.base.classes r) ∧
    (∀ (ti : Nat),∀ r ∈ st.tryRegs[ti]!.1 ++ st.tryRegs[ti]!.2,IntCls st.base.classes r) := by
  have allocated := buildCtx_allocated build
  have initialClasses := InitialClassesDraft.stock_build_classes build
  refine ⟨?_,?_⟩
  · intro v r found
    obtain ⟨n,shape,_⟩ := allocated.2.2.1 v r found
    exact ⟨regCls_step growth (initialClasses.2.1 v r found),n,shape⟩
  · intro ti r member
    rw [tables] at member
    exact intCls_step growth ((stock_build_alias_class_inputs build).2.2 ti (.op .unit) r member)

private theorem arg_classes {ctx : Ctx} {rets pays : List Reg} {index nh : Nat}
    {classes : Array RegClass}
    (mapped : ∀ v r,ctx.valueReg? v = some r → IntCls classes r)
    (returned : ∀ r ∈ rets,IntCls classes r) (payload : ∀ r ∈ pays,IntCls classes r)
    {arg : Clif.TryArg} {a b : State × Array Reg} (old : GoodArray classes a.2)
    (run : argStep ctx rets pays index nh arg a = .ok (.yield b)) : GoodArray classes b.2 := by
  cases arg with
  | val v =>
    unfold argStep at run
    dsimp only at run
    split at run
    · rename_i r lookup
      cases run
      intro x member
      simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
      rcases member with member | rfl
      · exact old x member
      · exact mapped _ _ lookup
    · cases run
  | ret i =>
    unfold argStep at run
    dsimp only at run
    split at run
    · cases run
    · split at run
      · rename_i r lookup
        cases run
        intro x member
        simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
        rcases member with member | rfl
        · exact old x member
        · exact returned _ (List.mem_of_getElem? lookup)
      · cases run
  | exn i =>
    unfold argStep at run
    dsimp only at run
    split at run
    · cases run
    · split at run
      · rename_i r lookup
        cases run
        intro x member
        simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
        rcases member with member | rfl
        · exact old x member
        · exact payload _ (List.mem_of_getElem? lookup)
      · cases run

private theorem branch_classes {ctx : Ctx} {st next : State} {block index : Nat}
    {args : Array Reg} {classes : Array RegClass}
    (mapped : ∀ v r,ctx.valueReg? v = some r → IntCls classes r)
    (reserved : ∀ (ti : Nat),∀ r ∈ st.tryRegs[ti]!.1 ++ st.tryRegs[ti]!.2,IntCls classes r)
    (h : branchArgs ctx st block index = .ok (args,next)) : GoodArray classes args := by
  unfold branchArgs at h
  dsimp only at h
  split at h
  · rename_i id values lookup
    split at h
    · rename_i target found
      split at h
      · cases h
      · let ti := (st.instBlock.findIdx? (· == block)).getD 0 + ctx.func.blocks[block]!.body.length
        let reservations := st.tryRegs[ti]!
        let nh := match ctx.func.blocks[block]!.term with
          | .tryCall _ _ et | .tryCallIndirect _ _ et => et.handlers.length
          | _ => 0
        change (do
          let result ← forIn values (st,#[]) (argStep ctx reservations.1 reservations.2 index nh)
          pure (result.2,result.1)) = .ok (args,next) at h
        cases loop : forIn values (st,#[]) (argStep ctx reservations.1 reservations.2 index nh) with
        | error e => simp only [loop,bind,Except.bind] at h; cases h
        | ok result =>
          simp only [loop,bind,Except.bind,pure,Except.pure] at h
          cases h
          exact Prep.forIn_inv _ values (fun _ acc => GoodArray classes acc.2)
            (fun k x a b member held step => arg_classes mapped
              (fun r member => reserved ti r (List.mem_append_left _ member))
              (fun r member => reserved ti r (List.mem_append_right _ member)) held step)
            (fun x a b => arg_no_break ctx reservations.1 reservations.2 index nh x a b)
            (st,#[]) result (by simp [GoodArray]) loop
    · cases h
  · cases h

private theorem fold_inv {α β : Type} {P : α → Prop} (step : α → β → Except String α)
    (keeps : ∀ a x b,P a → step a x = .ok b → P b) (xs : List β)
    {a b : α} (held : P a) (run : xs.foldlM step a = .ok b) : P b := by
  induction xs generalizing a with
  | nil => cases run; exact held
  | cons x xs ih =>
    rw [List.foldlM_cons] at run
    cases call : step a x with
    | error e => simp only [call,bind,Except.bind] at run; cases run
    | ok next =>
      simp only [call,bind,Except.bind] at run
      exact ih (keeps a x next held call) run

private theorem outgoing_classes {ctx : Ctx} {order : Order} {bi : Nat} {targets : Array Nat}
    {st next : State} {outgoing : Array (Array Reg)} {classes : Array RegClass}
    (mapped : ∀ v r,ctx.valueReg? v = some r → IntCls classes r)
    (reserved : ∀ (ti : Nat),∀ r ∈ st.tryRegs[ti]!.1 ++ st.tryRegs[ti]!.2,IntCls classes r)
    (run : collectOutgoing ctx order bi targets st = .ok (next,outgoing)) : GoodRow classes outgoing := by
  let P (acc : State × Array (Array Reg)) : Prop :=
    (∀ (ti : Nat),∀ r ∈ acc.1.tryRegs[ti]!.1 ++ acc.1.tryRegs[ti]!.2,IntCls classes r) ∧ GoodRow classes acc.2
  have held : P (st,#[]) := ⟨reserved,by simp [GoodRow]⟩
  have kept : ∀ a x b,P a → outgoingStep ctx order bi a x = .ok b → P b := by
    intro acc target result old step
    unfold outgoingStep at step
    split at step
    · cases step
      refine ⟨old.1,?_⟩
      intro rs member
      simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
      rcases member with oldMember | rfl
      · exact old.2 rs oldMember
      · simp [GoodArray]
    · cases call : branchArgs ctx acc.1 bi target.2 with
      | error e => simp only [call,bind,Except.bind] at step; cases step
      | ok pair =>
        rcases pair with ⟨args,state⟩
        simp only [call,bind,Except.bind,pure,Except.pure] at step
        cases step
        have table := congrArg (fun q => q.2.2.1) (branch_frame call)
        change state.tryRegs = acc.1.tryRegs at table
        refine ⟨?_,?_⟩
        · intro ti r member
          rw [table] at member
          exact old.1 ti r member
        · intro rs member
          simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
          rcases member with oldMember | rfl
          · exact old.2 rs oldMember
          · exact branch_classes mapped old.1 call
  unfold collectOutgoing at run
  exact (fold_inv (outgoingStep ctx order bi) kept targets.zipIdx.toList held run).2

private theorem core_edges {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) (scope : LowerScope f)
    {order : Order} {bi : Nat} {b : Clif.Block} (block : f.blocks[bi]? = some b)
    {range : Nat × Nat} (rangeRun : ranges[bi]? = some range) {data : V}
    (prepared : blockData f b.term = .ok data) {targets : Array Nat} {input : State}
    (old : Inv initial input) {output : LoweredBlockCore}
    (run : lowerBlockCore ctx order f b bi range.1 range.2 data targets input = .ok output) :
    GoodRow output.state.base.classes output.outgoing := by
  let ti := range.2 - 1
  let selected : Ctx := {Driver.termCtx ctx ti data with tryRegs := input.tryRegs[ti]!}
  obtain ⟨original,before,legacy,spec,view⟩ := buildCtx_source build
  have rangeEq := spec.ranges bi b block
  rw [rangeRun] at rangeEq
  have endEq : ti = blockStart f bi + b.body.length := by cases rangeEq; dsimp [ti] <;> omega
  have ph : ctx.insts[ti]? = some ⟨.op .unit,[],[],none⟩ := by
    rw [view.insts,endEq]
    exact spec.facts.term bi b block
  have mapped : MappedCtxInv f selected := ((buildCtx_mappedInv scope build).termCtx ph data).withTryRegs _
  have clean : Clean (sourceIdentityCtx selected) := clean_block (clean_stock build) prepared ti _
  have initialClasses := InitialClassesDraft.stock_build_classes build
  have initialized := (stock_build_alias_class_inputs build).2.2 ti data
  have reserveAt (st : State) (growth : ClassGrowth initial st) : ReservedClasses selected st := by
    intro r member
    change r ∈ input.tryRegs[ti]!.1 ++ input.tryRegs[ti]!.2 at member
    rw [old.table] at member
    exact intCls_step growth (initialized r member)
  let branchCall : Except String (Option BranchEmission) :=
    if blockBranch b.term then some <$> emitBranch selected f b.term bi ti targets input else pure none
  have branchKeeps {br : Option BranchEmission} (call : branchCall = .ok br) :
      Inv initial (br.map (fun e => e.state) |>.getD input) := by
    unfold branchCall at call
    split at call
    · cases emitted : emitBranch selected f b.term bi ti targets input with
      | error e => simp only [emitted,Functor.map,Except.map] at call; cases call
      | ok e =>
        simp only [emitted,Functor.map,Except.map] at call
        cases call
        exact branch_keeps mapped clean old (reserveAt input old.growth) emitted
    · cases call; exact old
  have normal : lowerBlockCore ctx order f b bi range.1 range.2 data targets input = ((do
    let br ← branchCall
    let edge ← collectOutgoing ctx order bi targets (br.map (fun e => e.state) |>.getD input)
    let next := edge.1
    let outgoing := edge.2
    let beforeScan := {next with color := some next.endColor[bi]!}
    let indices := ((Array.range (range.2-range.1)).map (range.1+·)).reverse.toList
    let body ← scanBlock selected bi ti (blockBranch b.term) indices beforeScan
    pure ⟨body.state,body.code ++ (br.map (fun e => e.code) |>.getD #[]),outgoing,br,
      ⟨selected,bi,ti,blockBranch b.term,indices,beforeScan,body⟩⟩) : Except String LoweredBlockCore) := by
    unfold lowerBlockCore
    dsimp only [branchCall,blockBranch,selected,ti]
    split <;> simp_all only [branchCall,blockBranch,selected,ti] <;> rfl
  rw [normal] at run
  cases call : branchCall with
  | error e => simp only [call,bind,Except.bind] at run; cases run
  | ok br =>
    simp only [call,bind,Except.bind] at run
    cases edges : collectOutgoing ctx order bi targets (br.map (fun e => e.state) |>.getD input) with
    | error e => simp only [edges,bind,Except.bind] at run; cases run
    | ok pair =>
      rcases pair with ⟨next,outgoing⟩
      simp only [edges,bind,Except.bind] at run
      let beforeScan : State := {next with color := some next.endColor[bi]!}
      let indices := ((Array.range (range.2-range.1)).map (range.1+·)).reverse.toList
      have beforeInv : Inv initial beforeScan := inv_fields
        (inv_fields (branchKeeps call) (outgoing_frame edges)) rfl
      have invariant : ClsIs selected beforeScan.base beforeScan.base :=
        ⟨sz_step beforeInv.growth initialClasses.1,
          fun x r lookup => regCls_step beforeInv.growth (initialClasses.2.1 x r lookup),
          fun r member => (reserveAt beforeScan beforeInv.growth r (List.mem_append_left _ member)).1,
          fun r member => (reserveAt beforeScan beforeInv.growth r (List.mem_append_right _ member)).1,
          ⟨[],by simp,by simp⟩⟩
      cases bodyRun : scanBlock selected bi ti (blockBranch b.term)
          ((Array.range (range.2-range.1)).map (range.1+·)).reverse.toList
          {next with color := some next.endColor[bi]!} with
      | error e => simp only [bodyRun,bind,Except.bind] at run; cases run
      | ok body =>
        simp only [bodyRun,bind,Except.bind,pure,Except.pure] at run
        cases run
        have slots := built_scan_slots build scope block rangeRun prepared input.tryRegs[ti]!
        have aliases := stock_scanBlock_alias_classes mapped clean slots invariant
          (reserveAt beforeScan beforeInv.growth) beforeInv.aliases beforeInv.empty bodyRun
        have final : Inv initial body.state :=
          ⟨clsStep_trans beforeInv.growth (stock_scanBlock_classGrowth bodyRun),
            (stock_scanBlock_allocationLe bodyRun).2.trans beforeInv.table,aliases.1,aliases.2.2.1⟩
        have inputs := built_inputs build final.growth final.table
        have beforeReserved : ∀ (i : Nat),∀ r ∈
            (br.map (fun e => e.state) |>.getD input).tryRegs[i]!.1 ++
            (br.map (fun e => e.state) |>.getD input).tryRegs[i]!.2,IntCls body.state.base.classes r := by
          intro i r member
          rw [(branchKeeps call).table] at member
          apply inputs.2 i r
          rw [final.table]
          exact member
        exact outgoing_classes inputs.1 beforeReserved edges

private theorem assembled_entry {ctx : Ctx} {f : Clif.Function} {b : Clif.Block}
    {label : Nat} {targets : Array Nat} {outgoing : Array (Array Reg)}
    {params : List Nat} {uses : Array UseState} {code : Array MInst} {block : VBlock}
    (run : assembleOriginalBlock ctx f b 0 label targets outgoing params uses code = .ok block) :
    block.label = label ∧ block.params = #[] := by
  unfold assembleOriginalBlock at run
  simp only [beq_self_eq_true,ite_true,bind,Except.bind,pure,Except.pure] at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals cases run; exact ⟨rfl,rfl⟩

private def parameterReg (ctx : Ctx) (q : Nat × Clif.Ty) : Except String Reg :=
  match ctx.valueReg? q.1 with | some r => .ok r | none => .error s!"unknown value v{q.1}"

private theorem assembled_parameters {ctx : Ctx} {f : Clif.Function} {b : Clif.Block}
    {bi label : Nat} {targets : Array Nat} {outgoing : Array (Array Reg)}
    {params : List Nat} {uses : Array UseState} {code : Array MInst} {block : VBlock}
    (entry : bi ≠ 0)
    (run : assembleOriginalBlock ctx f b bi label targets outgoing params uses code = .ok block) :
    b.params.toArray.mapM (parameterReg ctx) = .ok block.params ∧ block.label = label := by
  have zero : (bi == 0) = false := by simp [entry]
  unfold assembleOriginalBlock at run
  simp only [zero,Bool.false_eq_true,ite_false] at run
  change (do
    let ps ← b.params.toArray.mapM (parameterReg ctx)
    pure ({label := label,insts := code,params := ps,branchArgs := if targets.size == 1 then outgoing[0]! else #[]} : VBlock)) = .ok block at run
  cases mapped : b.params.toArray.mapM (parameterReg ctx) with
  | error e => simp only [mapped,bind,Except.bind] at run; cases run
  | ok ps =>
    simp only [mapped,bind,Except.bind,pure,Except.pure] at run
    cases run
    exact ⟨rfl,rfl⟩
private theorem assembled_arguments {ctx : Ctx} {f : Clif.Function} {b : Clif.Block}
    {bi label : Nat} {targets : Array Nat} {outgoing : Array (Array Reg)}
    {params : List Nat} {uses : Array UseState} {code : Array MInst} {block : VBlock}
    (run : assembleOriginalBlock ctx f b bi label targets outgoing params uses code = .ok block) :
    block.branchArgs = (if targets.size == 1 then outgoing[0]! else #[]) ∧ block.label = label := by
  unfold assembleOriginalBlock at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals cases run; constructor <;> simp_all

private theorem mapM_classes {α : Type} {xs : Array α} {ys : Array Reg}
    {f : α → Except String Reg} {classes : Array RegClass}
    (typed : ∀ x r,f x = .ok r → IntCls classes r) (run : xs.mapM f = .ok ys) : GoodArray classes ys := by
  intro r member
  obtain ⟨i,found⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
  have facts := array_mapM_ok run
  have small := (Array.getElem?_eq_some_iff.mp found).1
  rw [facts.1] at small
  obtain ⟨out,called,placed⟩ := facts.2 i xs[i] (Array.getElem?_eq_getElem small)
  have same := Option.some.inj (placed.symm.trans found)
  subst out
  exact typed _ r called

private theorem assemble_regs {ctx : Ctx} {f : Clif.Function} {b : Clif.Block}
    {bi label : Nat} {targets : Array Nat} {outgoing : Array (Array Reg)}
    {params : List Nat} {uses : Array UseState} {code : Array MInst} {block : VBlock} {classes : Array RegClass}
    (mapped : ∀ v r,ctx.valueReg? v = some r → IntCls classes r)
    (edges : GoodRow classes outgoing)
    (run : assembleOriginalBlock ctx f b bi label targets outgoing params uses code = .ok block) :
    ∀ r ∈ block.params.toList ++ block.branchArgs.toList,IntCls classes r := by
  have parameters : GoodArray classes block.params := by
    by_cases entry : bi = 0
    · subst bi
      rw [(assembled_entry run).2]
      simp [GoodArray]
    · have actual := (assembled_parameters entry run).1
      apply mapM_classes ?_ actual
      intro q r call
      unfold parameterReg at call
      cases found : ctx.valueReg? q.1 with
      | none => simp only [found] at call; cases call
      | some reg =>
        simp only [found] at call
        cases call
        exact mapped _ _ found
  have arguments : GoodArray classes block.branchArgs := by
    rw [(assembled_arguments run).1]
    split
    · cases found : outgoing[0]? with
      | none =>
        simp only [getElem!_def,found,Option.getD_none]
        change GoodArray classes (#[] : Array Reg)
        simp [GoodArray]
      | some rs =>
        simp only [getElem!_def,found,Option.getD_some]
        exact edges rs (Array.mem_toList_iff.mpr (Array.mem_of_getElem? found))
    · simp [GoodArray]
  intro r member
  rcases List.mem_append.mp member with left | right
  · exact parameters r left
  · exact arguments r right

private theorem node_regs {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) (scope : LowerScope f)
    {order : Order} (ordered : blockOrder f = .ok order) {params : List Nat} {label : Nat}
    (inside : label < order.nodes.size) {input output : DriverState} (old : Inv initial input.state)
    (oldBlocks : GoodBlocks input.state.base.classes input.blocks)
    (oldEdges : GoodEdges input.state.base.classes input.edgeArgs)
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    Inv initial output.state ∧ GoodBlocks output.state.base.classes output.blocks ∧ GoodEdges output.state.base.classes output.edgeArgs := by
  cases node : order.nodes[label]! with
  | edge pred k target =>
    unfold lowerNode at run
    simp only [node] at run
    cases call : branchArgs ctx input.state pred k with
    | error e => simp only [call,bind,Except.bind] at run; cases run
    | ok pair =>
      rcases pair with ⟨args,next⟩
      simp only [call,bind,Except.bind,pure,Except.pure] at run
      cases run
      have inputs := built_inputs build old.growth old.table
      have typed := branch_classes inputs.1 inputs.2 call
      have table : next.base.classes = input.state.base.classes := congrArg Prod.fst (branch_frame call)
      refine ⟨inv_fields old (branch_frame call),?_,?_⟩
      · apply array_set (P := fun vb : VBlock => ∀ r ∈ vb.params.toList ++ vb.branchArgs.toList,IntCls next.base.classes r) (by rw [table]; exact oldBlocks)
        intro r member
        simp only [Array.toList_empty,List.nil_append] at member
        rw [table]
        exact typed r member
      · apply array_set (P := GoodRow next.base.classes) (by rw [table]; exact oldEdges)
        intro rs member
        simp only [Array.toList_push,Array.toList_empty,List.mem_singleton] at member
        subst rs
        rw [table]
        exact typed
  | original bi =>
    have valid := original_bound scope ordered inside node
    let b := f.blocks[bi]!
    have block : f.blocks[bi]? = some b := by
      simp only [b,getElem!_pos f.blocks bi valid,List.getElem?_eq_getElem valid]
    obtain ⟨original,before,legacy,spec,view⟩ := buildCtx_source build
    let start := blockStart f bi
    let stop := start + b.body.length + 1
    have rangeRun : ranges[bi]? = some (start,stop) := spec.ranges bi b block
    have range : ranges[bi]! = (start,stop) := by simp only [getElem!_def,rangeRun,Option.getD_some]
    let reject : Bool := (match b.term with | .ret .. => true | _ => false) &&
      (sretRet f).isEmpty && (sigRets f.sig != f.sig.returns)
    have normal : lowerNode ctx ranges order f params label input = (do
      let data ← blockData f b.term
      if reject then throw "sret parameter is not an entry-block parameter"
      let core ← lowerBlockCore ctx order f b bi start stop data order.successors[label]! input.state
      let block ← assembleOriginalBlock ctx f b bi label order.successors[label]!
        core.outgoing params core.state.uses core.code
      pure {recordCore input core bi stop with
        blocks := input.blocks.set! label block,edgeArgs := input.edgeArgs.set! label core.outgoing}) := by
      unfold lowerNode
      simp only [node]
      rw [range]
      dsimp only [blockData,reject,b]
      split <;> simp_all only [reject] <;> rfl
    rw [normal] at run
    cases dataRun : blockData f b.term with
    | error e => simp only [dataRun,bind,Except.bind] at run; cases run
    | ok data =>
      simp only [dataRun,bind,Except.bind] at run
      split at run
      · cases run
      · cases coreRun : lowerBlockCore ctx order f b bi start stop data order.successors[label]! input.state with
        | error e => simp only [coreRun,bind,Except.bind] at run; cases run
        | ok core =>
          simp only [coreRun,bind,Except.bind] at run
          cases assembled : assembleOriginalBlock ctx f b bi label order.successors[label]!
              core.outgoing params core.state.uses core.code with
          | error e => simp only [assembled,bind,Except.bind] at run; cases run
          | ok finished =>
            simp only [assembled,bind,Except.bind,pure,Except.pure] at run
            cases run
            have nextInv := core_alias build scope block rangeRun dataRun old coreRun
            have coreGrowth := (CoreClassDraft.stock_built_core_classes build scope block rangeRun dataRun old.growth old.table coreRun).1
            have edges := core_edges build scope block rangeRun dataRun old coreRun
            have inputs := built_inputs build nextInv.growth nextInv.table
            refine ⟨nextInv,?_,?_⟩
            · apply array_set (P := fun vb : VBlock => ∀ r ∈ vb.params.toList ++ vb.branchArgs.toList,IntCls core.state.base.classes r) (fun vb member r present => intCls_step coreGrowth (oldBlocks vb member r present))
              exact assemble_regs inputs.1 edges assembled
            · apply array_set (P := GoodRow core.state.base.classes) (fun row member rs present r inside => intCls_step coreGrowth (oldEdges row member rs present r inside))
              exact edges

private theorem traversal_regs {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) (scope : LowerScope f)
    {order : Order} (ordered : blockOrder f = .ok order) {params labels : List Nat}
    (inside : ∀ label ∈ labels,label < order.nodes.size) {input output : DriverState} (old : Inv initial input.state)
    (oldBlocks : GoodBlocks input.state.base.classes input.blocks)
    (oldEdges : GoodEdges input.state.base.classes input.edgeArgs)
    (run : labels.foldlM (fun d label => lowerNode ctx ranges order f params label d) input = .ok output) :
    Inv initial output.state ∧ GoodBlocks output.state.base.classes output.blocks ∧ GoodEdges output.state.base.classes output.edgeArgs := by
  induction labels generalizing input with
  | nil => cases run; exact ⟨old,oldBlocks,oldEdges⟩
  | cons label labels ih =>
    rw [List.foldlM_cons] at run
    cases call : lowerNode ctx ranges order f params label input with
    | error e => simp only [call,bind,Except.bind] at run; cases run
    | ok next =>
      simp only [call,bind,Except.bind] at run
      have head := node_regs build scope ordered (inside label (List.mem_cons_self ..)) old oldBlocks oldEdges call
      exact ih (fun k member => inside k (List.mem_cons_of_mem label member)) head.1 head.2.1 head.2.2 run

private theorem resolve_int {classes : Array RegClass} {aliases : Array (Option Nat)}
    (keeps : ∀ r,RegCls classes r → RegCls classes (Backend.lowerFunction.resolve aliases (aliases.size+1) r))
    {r : Reg} (typed : IntCls classes r) :
    IntCls classes (Backend.lowerFunction.resolve aliases (aliases.size+1) r) := by
  obtain ⟨classed,n,rfl⟩ := typed
  exact ⟨keeps _ classed,_,resolve_vreg aliases (aliases.size+1) n .int⟩

/-- Successful actual Stock lowering supplies the existing full ClassesOk
interface and classed virtual integer registers in every per-successor vector,
under the ORIGINAL source scope. Prefix, reservation and alias facts derive
internally through actual assembly and the complete driver traversal. -/
private theorem stock_lower_classes_all {f : Clif.Function} {result : Result}
    (scope : LowerScope f) (run : Stock.lower f = .ok result) :
    ClassesOkM result.code ∧ ClassesOk result.code ∧
      (∀ block ∈ result.code.blocks.toList,∀ r ∈ block.params.toList ++ block.branchArgs.toList,IntCls result.code.classes r) ∧
      ∀ row ∈ result.edgeArgs.toList,∀ args ∈ row.toList,∀ r ∈ args.toList,IntCls result.code.classes r := by
  have instructions := WholeInstructionClassDraft.stock_lower_instruction_classes scope run
  have resolver := (DriverAliasClassDraft.stock_lower_alias_classes scope run).2.2.2.2
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  cases run
  rename_i _ built hbuild _ order horder _ driver hdriver
  have initial : Inv built.2.2 built.2.2 :=
    ⟨clsStep_refl _,rfl,(stock_build_alias_class_inputs hbuild).1,buildCtx_noOpportunity hbuild⟩
  have initialBlocks : GoodBlocks built.2.2.base.classes (Array.replicate order.nodes.size default) := by
    intro block member r inside
    have same : block = default := (List.mem_replicate.mp
      (show block ∈ List.replicate order.nodes.size (default : VBlock) from
        by simpa only [Array.toList_replicate] using member)).2
    subst block
    cases inside
  have initialEdges : GoodEdges built.2.2.base.classes (Array.replicate order.nodes.size #[]) := by
    intro row member rs inside
    have same : row = #[] := (List.mem_replicate.mp
      (show row ∈ List.replicate order.nodes.size (#[] : Array (Array Reg)) from
        by simpa only [Array.toList_replicate] using member)).2
    subst row
    cases inside
  have final := traversal_regs (initial := built.2.2) hbuild scope horder
    (fun label member => by
      simpa only [Array.toList_reverse,List.mem_reverse,Array.toList_range,List.mem_range] using member)
    initial initialBlocks initialEdges hdriver
  have parameters : ∀ block ∈ (driver.blocks.map fun (b : VBlock) => {b with
      insts := b.insts.map (fun (i : MInst) => i.mapRegs (Backend.lowerFunction.resolve driver.state.alias (driver.state.alias.size+1)))
      params := b.params.map (Backend.lowerFunction.resolve driver.state.alias (driver.state.alias.size+1))
      branchArgs := b.branchArgs.map (Backend.lowerFunction.resolve driver.state.alias (driver.state.alias.size+1))}).toList,
      ∀ r ∈ block.params.toList ++ block.branchArgs.toList,IntCls driver.state.base.classes r := by
    intro block member r inside
    obtain ⟨raw,retained,rfl⟩ := List.mem_map.mp (by simpa only [Array.toList_map] using member)
    simp only [Array.toList_map,List.mem_append] at inside
    rcases inside with left | right
    · obtain ⟨reg,present,rfl⟩ := List.mem_map.mp left
      exact resolve_int resolver (final.2.1 raw retained reg (List.mem_append_left _ present))
    · obtain ⟨reg,present,rfl⟩ := List.mem_map.mp right
      exact resolve_int resolver (final.2.1 raw retained reg (List.mem_append_right _ present))
  have classed : ClassesOkM {
      name := f.name
      blocks := driver.blocks.map (fun (b : VBlock) => {b with
        insts := b.insts.map (fun (i : MInst) => i.mapRegs (Backend.lowerFunction.resolve driver.state.alias (driver.state.alias.size+1)))
        params := b.params.map (Backend.lowerFunction.resolve driver.state.alias (driver.state.alias.size+1))
        branchArgs := b.branchArgs.map (Backend.lowerFunction.resolve driver.state.alias (driver.state.alias.size+1))}),
      classes := driver.state.base.classes,slotBytes := (slotLayout f.slots).2,
      outgoing := driver.state.base.outgoing,rulesFired := driver.rules} := by
    refine ⟨instructions,?_⟩
    intro b member r inside
    obtain ⟨typed,n,shape⟩ := parameters b member r inside
    exact ⟨n,.int,shape,regCls_vreg.mp (by rw [← shape]; exact typed)⟩
  refine ⟨classed,classesOk_of classed,parameters,?_⟩
  intro row member args present r inside
  obtain ⟨rawRow,retained,rfl⟩ := List.mem_map.mp (by simpa only [Array.toList_map] using member)
  obtain ⟨rawArgs,atArgs,rfl⟩ := List.mem_map.mp (by simpa only [Array.toList_map] using present)
  obtain ⟨reg,atReg,rfl⟩ := List.mem_map.mp (by simpa only [Array.toList_map] using inside)
  exact resolve_int resolver (final.2.2 rawRow retained rawArgs atArgs reg atReg)

/-- The actual Stock producer supplies the existing full ClassesOk interfaces
and virtual integer classes for every executable per-successor vector under
original source scope, without a new class or alias certificate. -/
theorem stock_lower_classes {f : Clif.Function} {result : Result}
    (scope : LowerScope f) (run : Stock.lower f = .ok result) :
    ClassesOkM result.code ∧ ClassesOk result.code ∧
      ∀ row ∈ result.edgeArgs.toList,∀ args ∈ row.toList,∀ r ∈ args.toList,IntCls result.code.classes r := by
  have all := stock_lower_classes_all scope run
  exact ⟨all.1,all.2.1,all.2.2.2⟩

/-- Returned block parameters and branch arguments are actual virtual integers
of their recorded class; actual final resolution preserves this stronger shape. -/
theorem stock_lower_integer_block_classes {f : Clif.Function} {result : Result}
    (scope : LowerScope f) (run : Stock.lower f = .ok result) :
    ∀ block ∈ result.code.blocks.toList,∀ r ∈ block.params.toList ++ block.branchArgs.toList,IntCls result.code.classes r :=
  (stock_lower_classes_all scope run).2.2.1

end Backend.Stock.Proof.WholeClassesDraft
