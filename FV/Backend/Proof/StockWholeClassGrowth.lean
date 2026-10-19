import FV.Backend.Proof.StockClassGrowthContracts
import FV.Backend.Proof.StockInitialClasses
import FV.Backend.Proof.StockCoverageBlock
namespace Backend.Stock.Proof.WholeClassGrowthDraft
open Backend.Stock.Proof.Coverage
open Backend.Stock.Proof.ClassGrowthDraft Backend.Stock.Proof.InitialClassesDraft
open Backend.Proof Backend.Proof.Spill Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm scanBlock emitBranch lowerBlockCore
private def fields (st : State) := (st.base.classes, st.base.nextVreg)
private theorem fields_growth {st next : State} (h : fields next = fields st) :
    ClassGrowth st next := clsStep_of_eq (congrArg Prod.fst h) (congrArg Prod.snd h)
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



private theorem branch_growth {ctx : Ctx} {f : Clif.Function} {t : Clif.Terminator}
    {bi ti : Nat} {targets : Array Nat} {input : State} {output : BranchEmission}
    (run : emitBranch ctx f t bi ti targets input = .ok output) : ClassGrowth input output.state := by
  unfold emitBranch at run
  dsimp only at run
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
        have root := stock_named_classGrowth call
        have frameGrowth : ClassGrowth input {input with current := some ti,color := none,base.emitted := #[]} :=
          clsStep_of_eq rfl rfl
        exact clsStep_trans frameGrowth root

private theorem core_growth {ctx : Ctx} {order : Order} {f : Clif.Function}
    {b : Clif.Block} {bi start stop : Nat} {data : V} {targets : Array Nat}
    {input : State} {output : LoweredBlockCore}
    (run : lowerBlockCore ctx order f b bi start stop data targets input = .ok output) :
    ClassGrowth input output.state := by
  let ti := stop - 1
  let selected := {ctx with insts := ctx.insts.set! ti ⟨data,[],[],none⟩,tryRegs := input.tryRegs[ti]!}
  let branch := match b.term with | .ret .. | .trap .. | .returnCall .. => false | _ => true
  let branchCall : Except String (Option BranchEmission) := if branch then some <$> emitBranch selected f b.term bi ti targets input else pure none
  have branchKeeps {br : Option BranchEmission}
      (call : branchCall = .ok br) :
      ClassGrowth input (br.map (fun e : BranchEmission => e.state) |>.getD input) := by
    unfold branchCall at call
    cases flag : branch
    · simp only [flag,Bool.false_eq_true,↓reduceIte,pure,Except.pure] at call
      cases call; exact clsStep_refl _
    · simp only [flag,↓reduceIte] at call
      cases runBranch : emitBranch selected f b.term bi ti targets input with
      | error e => simp [runBranch] at call
      | ok emitted =>
        simp [runBranch] at call
        subst br
        exact branch_growth runBranch
  have normal : lowerBlockCore ctx order f b bi start stop data targets input = (do
    let br ← branchCall
    let (next,outgoing) ← collectOutgoing ctx order bi targets (br.map (fun e : BranchEmission => e.state) |>.getD input)
    let before := {next with color := some next.endColor[bi]!}
    let indices := ((Array.range (stop-start)).map (start+·)).reverse.toList
    let body ← scanBlock selected bi ti branch indices before
    pure (⟨body.state,body.code ++ (br.map (fun e : BranchEmission => e.code) |>.getD #[]),outgoing,br,
      ⟨selected,bi,ti,branch,indices,before,body⟩⟩ : LoweredBlockCore)) := by
    unfold lowerBlockCore
    dsimp only [selected,ti,branch,branchCall]
    split <;> simp_all only [selected,ti,branch,branchCall] <;> rfl
  rw [normal] at run
  cases call : branchCall with
  | error e => simp only [call,bind,Except.bind] at run; cases run
  | ok br =>
    simp only [call,bind,Except.bind] at run
    cases edges : collectOutgoing ctx order bi targets (br.map (fun e : BranchEmission => e.state) |>.getD input) with
    | error e => simp only [edges,bind,Except.bind] at run; cases run
    | ok q =>
      rcases q with ⟨next,outgoing⟩
      simp only [edges,bind,Except.bind] at run
      cases body : scanBlock selected bi ti branch
          ((Array.range (stop-start)).map (start+·)).reverse.toList
          {next with color := some next.endColor[bi]!} with
      | error e => simp only [body,bind,Except.bind] at run; cases run
      | ok scan =>
        simp only [body,bind,Except.bind,pure,Except.pure] at run
        cases run
        have scanned := stock_scanBlock_classGrowth body
        have beforeGrowth : ClassGrowth next {next with color := some next.endColor[bi]!} :=
          clsStep_of_eq rfl rfl
        exact clsStep_trans (branchKeeps call) (clsStep_trans (fields_growth (outgoing_frame edges))
          (clsStep_trans beforeGrowth scanned))
private theorem node_growth {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label : Nat} {input output : DriverState}
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    ClassGrowth input.state output.state := by
  cases node : order.nodes[label]! with
  | edge pred k target =>
    unfold lowerNode at run
    simp only [node] at run
    cases call : branchArgs ctx input.state pred k with
    | error e => simp only [call, bind, Except.bind] at run; cases run
    | ok pair =>
      rcases pair with ⟨args, next⟩
      simp only [call, bind, Except.bind, pure, Except.pure] at run
      cases run
      exact fields_growth (branch_frame call)
  | original bi =>
    let b := f.blocks[bi]!
    let start := (ranges[bi]!).1
    let stop := (ranges[bi]!).2
    let reject : Bool := (match b.term with | .ret .. => true | _ => false) &&
      (sretRet f).isEmpty && (sigRets f.sig != f.sig.returns)
    have normal : lowerNode ctx ranges order f params label input = (do
      let data ← blockData f b.term
      if reject then throw "sret parameter is not an entry-block parameter"
      let core ← lowerBlockCore ctx order f b bi start stop data order.successors[label]! input.state
      let block ← assembleOriginalBlock ctx f b bi label order.successors[label]!
        core.outgoing params core.state.uses core.code
      pure {recordCore input core bi stop with
        blocks := input.blocks.set! label block
        edgeArgs := input.edgeArgs.set! label core.outgoing}) := by
      unfold lowerNode
      simp only [node]
      dsimp only [blockData, reject, b, start, stop]
      split <;> simp_all only [reject] <;> rfl
    rw [normal] at run
    cases dataRun : blockData f b.term with
    | error e => simp only [dataRun, bind, Except.bind] at run; cases run
    | ok data =>
      simp only [dataRun, bind, Except.bind] at run
      split at run
      · cases run
      · cases coreRun : lowerBlockCore ctx order f b bi start stop data
            order.successors[label]! input.state with
        | error e => simp only [coreRun, bind, Except.bind] at run; cases run
        | ok core =>
          simp only [coreRun, bind, Except.bind] at run
          cases assembled : assembleOriginalBlock ctx f b bi label order.successors[label]!
              core.outgoing params core.state.uses core.code with
          | error e => simp only [assembled, bind, Except.bind] at run; cases run
          | ok block =>
            simp only [assembled, bind, Except.bind, pure, Except.pure] at run
            cases run
            exact core_growth coreRun

private theorem traversal_growth {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params labels : List Nat} {input output : DriverState}
    (run : labels.foldlM (fun d label => lowerNode ctx ranges order f params label d) input = .ok output) :
    ClassGrowth input.state output.state := by
  induction labels generalizing input with
  | nil => cases run; exact clsStep_refl _
  | cons label labels ih =>
    rw [List.foldlM_cons] at run
    cases call : lowerNode ctx ranges order f params label input with
    | error e => simp only [call,bind,Except.bind] at run; cases run
    | ok next =>
      simp only [call,bind,Except.bind] at run
      exact clsStep_trans (node_growth call) (ih run)

/-- Actual whole Stock lowering retains every initial class, records one class
per fresh register and supplies final class consistency for every source and
reserved register. No extra source scope or caller class certificate is needed. -/
theorem stock_lower_class_growth {f : Clif.Function} {result : Backend.Stock.Result}
    (run : Stock.lower f = .ok result) :
    ClassGrowth result.initial result.final ∧ Sz result.final.base ∧
    result.code.classes = result.final.base.classes ∧
    (∀ x r,result.ctx.valueReg? x = some r → RegCls result.code.classes r) ∧
    (∀ (i : Nat) (rs : List Reg × List Reg),result.initial.tryRegs[i]? = some rs → ∀ r ∈ rs.1 ++ rs.2,RegCls result.code.classes r) := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  cases run
  have growth := traversal_growth (by assumption)
  obtain ⟨size,values,reservations⟩ := stock_build_classes (by assumption)
  exact ⟨growth,sz_step growth size,rfl,
    fun x r lookup => regCls_step growth (values x r lookup),
    fun i rs slot r member => regCls_step growth (reservations i rs slot r member)⟩

end Backend.Stock.Proof.WholeClassGrowthDraft
