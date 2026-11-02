import FV.Backend.Proof.StockPureUnsunk
import FV.Backend.Proof.StockPureSourceColors

/-! Pure-slot invariants through actual original/critical-edge nodes and the
complete Stock traversal. No source admission condition or runtime certificate. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch lowerBlockCore lowerNode
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

private def frame (st : State) := (st.entryColor,st.sunk)

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
    frame b.1 = frame a.1 := by
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
    frame next = frame st := by
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
          exact forIn_frame (fun a : State × Array Reg => frame a.1) _
            (arg_frame ctx reservations.1 reservations.2 index nh)
            (arg_no_break ctx reservations.1 reservations.2 index nh) values loop
    · cases h
  · cases h

/-- Actual successor argument collection may mark source demands, but retains
both color and sunk tables, including exception-return and payload arguments. -/
private theorem branch_pair_frame {ctx : Ctx} {input next : State} {bi index : Nat}
    {args : Array Reg} (run : branchArgs ctx input bi index = .ok (args, next)) :
    frame next = frame input := branch_frame run

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


private theorem outgoing_frame {ctx : Ctx} {order : Order} {bi : Nat} {targets : Array Nat}
    {st next : State} {outgoing : Array (Array Reg)}
    (h : collectOutgoing ctx order bi targets st = .ok (next, outgoing)) :
    frame next = frame st := by
  unfold collectOutgoing at h
  apply fold_fields_eq (fun a : State × Array (Array Reg) => frame a.1) _ ?_ _ h
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



private theorem zero_refl (st : State) : ZeroColorLe st st := ⟨rfl,fun _ _ h => h⟩
private theorem zero_trans {a b c : State} (ab : ZeroColorLe a b) (bc : ZeroColorLe b c) :
    ZeroColorLe a c := by
  refine ⟨bc.1.trans ab.1,?_⟩
  intro i color safe
  exact bc.2 i (by rw [ab.1]; exact color) (ab.2 i color safe)
private theorem frame_rel {a b : State} (h : frame b = frame a) : ZeroColorLe a b := by
  refine ⟨congrArg Prod.fst h,?_⟩
  intro i _ safe
  have same := congrArg Prod.snd h
  change b.sunk = a.sunk at same
  rw [same]
  exact safe

private theorem branch_preserves {f : Clif.Function} {ctx : Ctx}
    {t : Clif.Terminator} {bi ti : Nat} {targets : Array Nat}
    {input : State} {output : BranchEmission}
    (run : emitBranch ctx f t bi ti targets input = .ok output) : ZeroColorLe input output.state := by
  unfold emitBranch at run
  dsimp only at run
  let before : State := {input with current := some ti,color := none,base.emitted := #[]}
  change ((do
    let (out,next,fired) ← Stock.runTerm ctx "lower_branch" [.inst ti,.labels targets.toList] before
    if out.isNone then throw s!"no lowering rule for terminator {repr t}"
    let code ← branchCode f t targets next.base.emitted
    pure ⟨next,code,⟨bi,ti,.emitted,before,next,[],fired,code⟩,fired⟩) : Except String BranchEmission) = .ok output at run
  cases root : Stock.runTerm ctx "lower_branch" [.inst ti,.labels targets.toList] before with
  | error e => simp only [root,bind,Except.bind] at run; cases run
  | ok result =>
    rcases result with ⟨out,next,fired⟩
    simp only [root,bind,Except.bind] at run
    split at run
    · cases run
    · cases code : branchCode f t targets next.base.emitted with
      | error e => simp only [code] at run; cases run
      | ok instructions =>
        simp only [code,pure,Except.pure] at run
        cases run
        exact zero_trans (frame_rel (a := input) (b := before) rfl) (stock_runTerm_zeroColorLe root)

private def isBranch (t : Clif.Terminator) : Bool :=
  match t with | .ret .. | .trap .. | .returnCall .. => false | _ => true

/-- Every actual original block carries the invariant through its branch,
outgoing demands, full scan and every retained record. -/
theorem stock_blockCore_zeroColorLe {ctx : Ctx} {order : Order} {f : Clif.Function}
    {b : Clif.Block} {bi start stop : Nat} {data : V} {targets : Array Nat}
    {input : State} {output : LoweredBlockCore}
    (run : lowerBlockCore ctx order f b bi start stop data targets input = .ok output) :
    ZeroColorLe input output.state ∧ ZeroColorLe input output.scan.input ∧
      ∀ r ∈ output.scan.output.records, ZeroColorLe input r.input ∧ ZeroColorLe input r.output.state := by
  let ti := stop-1
  let tc : Ctx := {ctx with insts := ctx.insts.set! ti ⟨data,[],[],none⟩,tryRegs := input.tryRegs[ti]!}
  let branchCall : Except String (Option BranchEmission) :=
    if isBranch b.term then some <$> emitBranch tc f b.term bi ti targets input else pure none
  have branch_keeps {br : Option BranchEmission} (call : branchCall = .ok br) :
      ZeroColorLe input (br.map (·.state) |>.getD input) := by
    unfold branchCall at call
    split at call
    · cases emitted : emitBranch tc f b.term bi ti targets input with
      | error e => simp only [emitted,Functor.map,Except.map] at call; cases call
      | ok e =>
        simp only [emitted,Functor.map,Except.map] at call
        cases call
        exact branch_preserves emitted
    · cases call; exact zero_refl _
  have normal : lowerBlockCore ctx order f b bi start stop data targets input = ((do
    let br ← branchCall
    let edge ← collectOutgoing ctx order bi targets (br.map (·.state) |>.getD input)
    let beforeScan := {edge.1 with color := some edge.1.endColor[bi]!}
    let indices := ((Array.range (stop-start)).map (start+·)).reverse.toList
    let scanned ← scanBlock tc bi ti (isBranch b.term) indices beforeScan
    pure ⟨scanned.state,scanned.code ++ (br.map (·.code) |>.getD #[]),edge.2,br,
      ⟨tc,bi,ti,isBranch b.term,indices,beforeScan,scanned⟩⟩) : Except String LoweredBlockCore) := by
    unfold lowerBlockCore
    dsimp only [branchCall,isBranch,tc,ti]
    split <;> simp_all only [isBranch,tc,ti] <;> rfl
  rw [normal] at run
  cases branch : branchCall with
  | error e => simp only [branch,bind,Except.bind] at run; cases run
  | ok br =>
    simp only [branch,bind,Except.bind] at run
    cases edges : collectOutgoing ctx order bi targets (br.map (·.state) |>.getD input) with
    | error e => simp only [edges,bind,Except.bind] at run; cases run
    | ok edge =>
      rcases edge with ⟨next,outgoing⟩
      simp only [edges,bind,Except.bind] at run
      let before : State := {next with color := some next.endColor[bi]!}
      let indices := ((Array.range (stop-start)).map (start+·)).reverse.toList
      cases scans : scanBlock tc bi ti (isBranch b.term) indices before with
      | error e =>
        dsimp only [indices,before] at scans
        simp only [scans] at run
        cases run
      | ok scanned =>
        dsimp only [indices,before] at scans
        simp only [scans,pure,Except.pure] at run
        cases run
        have pre : ZeroColorLe input before :=
          zero_trans (branch_keeps branch) (zero_trans (frame_rel (a := br.map (·.state) |>.getD input) (b := next) (outgoing_frame edges)) (frame_rel (a := next) (b := before) rfl))
        have frames := stock_scans_zeroColorLe (runScans_spec scans)
        refine ⟨zero_trans pre frames.1,pre,?_⟩
        intro r member
        obtain ⟨a,b⟩ := frames.2 r member
        exact ⟨zero_trans pre a,zero_trans pre b⟩

private def blockData (f : Clif.Function) (t : Clif.Terminator) : Except String V :=
  match t with
  | .tryCall .. | .tryCallIndirect .. => tryCallData f t
  | _ => termData (abiTerm f t)

def RecordsZeroColorLe (initial : State) (events : Array BlockScanEvent) : Prop :=
  ∀ event ∈ events.toList, ZeroColorLe initial event.input ∧
    ∀ record ∈ event.output.records,
      ZeroColorLe initial record.input ∧ ZeroColorLe initial record.output.state

/-- Both original and critical-edge nodes preserve the invariant and all
previous records; newly retained records inherit the real node input. -/
theorem stock_node_zeroColorLe {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label : Nat} {input output : DriverState}
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    ZeroColorLe input.state output.state ∧
      ∀ initial, ZeroColorLe initial input.state → RecordsZeroColorLe initial input.blockScans →
        RecordsZeroColorLe initial output.blockScans := by
  cases node : order.nodes[label]! with
  | edge pred k target =>
    unfold lowerNode at run
    simp only [node] at run
    cases edge : branchArgs ctx input.state pred k with
    | error e => simp only [edge,bind,Except.bind] at run; cases run
    | ok pair =>
      rcases pair with ⟨args,next⟩
      simp only [edge,bind,Except.bind,pure,Except.pure] at run
      cases run
      exact ⟨frame_rel (a := input.state) (b := next) (branch_frame edge),fun _ _ old => old⟩
  | original bi =>
    let b := f.blocks[bi]!
    let start := ranges[bi]!.1
    let stop := ranges[bi]!.2
    let reject : Bool := (match b.term with | .ret .. => true | _ => false) &&
      (sretRet f).isEmpty && (sigRets f.sig != f.sig.returns)
    have normal : lowerNode ctx ranges order f params label input = (do
        let data ← blockData f b.term
        if reject then throw "sret parameter is not an entry-block parameter"
        let lowered ← lowerBlockCore ctx order f b bi start stop data order.successors[label]! input.state
        let assembled ← assembleOriginalBlock ctx f b bi label order.successors[label]!
          lowered.outgoing params lowered.state.uses lowered.code
        pure {recordCore input lowered bi stop with
          blocks := input.blocks.set! label assembled,
          edgeArgs := input.edgeArgs.set! label lowered.outgoing}) := by
      unfold lowerNode
      simp only [node]
      dsimp only [blockData,reject,b,start,stop]
      split <;> simp_all only [reject] <;> rfl
    rw [normal] at run
    cases dataRun : blockData f b.term with
    | error e => simp only [dataRun,bind,Except.bind] at run; cases run
    | ok data =>
      simp only [dataRun,bind,Except.bind] at run
      split at run
      · cases run
      · cases core : lowerBlockCore ctx order f b bi start stop data order.successors[label]! input.state with
        | error e => simp only [core] at run; cases run
        | ok lowered =>
          simp only [core] at run
          cases assembled : assembleOriginalBlock ctx f b bi label order.successors[label]!
              lowered.outgoing params lowered.state.uses lowered.code with
          | error e => simp only [assembled] at run; cases run
          | ok finished =>
            simp only [assembled,pure,Except.pure] at run
            cases run
            have facts := stock_blockCore_zeroColorLe core
            refine ⟨facts.1,?_⟩
            intro initial prior old event member
            change event ∈ (input.blockScans.push lowered.scan).toList at member
            simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
            rcases member with member | rfl
            · exact old event member
            · refine ⟨zero_trans prior facts.2.1,?_⟩
              intro record retained
              obtain ⟨pre,post⟩ := facts.2.2 record retained
              exact ⟨zero_trans prior pre,zero_trans prior post⟩

/-- The complete reverse node traversal retains every actual prior fact. -/
theorem stock_traversal_zeroColorLe {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params labels : List Nat} {input output : DriverState}
    (run : labels.foldlM (fun d label => lowerNode ctx ranges order f params label d) input = .ok output) :
    ZeroColorLe input.state output.state ∧
      ∀ initial, ZeroColorLe initial input.state → RecordsZeroColorLe initial input.blockScans →
        RecordsZeroColorLe initial output.blockScans := by
  induction labels generalizing input with
  | nil => cases run; exact ⟨zero_refl _,fun _ _ old => old⟩
  | cons label labels ih =>
    rw [List.foldlM_cons] at run
    cases call : lowerNode ctx ranges order f params label input with
    | error e => simp only [call,bind,Except.bind] at run; cases run
    | ok next =>
      simp only [call,bind,Except.bind] at run
      have head := stock_node_zeroColorLe call
      have tail := ih run
      refine ⟨zero_trans head.1 tail.1,?_⟩
      intro initial prior old
      exact tail.2 initial (zero_trans prior head.1) (head.2 initial prior old)

private theorem lower_color_facts {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) :
    (∃ ctx ranges, Stock.buildCtx f = .ok (ctx,ranges,result.initial)) ∧
    ZeroColorLe result.initial result.final ∧ RecordsZeroColorLe result.initial result.blockScans := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  cases run
  rename_i _ built hbuild _ order horder _ driver hdriver
  change (∃ ctx ranges, Stock.buildCtx f = .ok (ctx,ranges,built.2.2)) ∧
    ZeroColorLe built.2.2 driver.state ∧ RecordsZeroColorLe built.2.2 driver.blockScans
  have traversal := stock_traversal_zeroColorLe hdriver
  exact ⟨⟨built.1,built.2.1,hbuild⟩,traversal.1,
    traversal.2 built.2.2 (zero_refl _) (by simp [RecordsZeroColorLe])⟩

/-- Successful actual Stock lowering preserves colors and every zero-color
unsunk fact through final assembly and all recorded source boundaries. -/
theorem stock_lower_zeroColorLe {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) :
    ZeroColorLe result.initial result.final ∧ RecordsZeroColorLe result.initial result.blockScans :=
  (lower_color_facts run).2

/-- Actual pure source syntax and context construction discharge the metadata
premises for the complete driver, without native facts or an extra input check. -/
theorem stock_lower_pure_single_block_unsunk {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {b : Clif.Block} (blocks : f.blocks = [b])
    (quiet : ∀ stm ∈ b.body, colored stm.inst = false) {q : Nat} (inside : q < b.body.length) :
    result.initial.entryColor[q]! = 0 ∧ result.final.sunk[q]! = false ∧
      ∀ event ∈ result.blockScans.toList, event.input.sunk[q]! = false ∧
        ∀ record ∈ event.output.records,
          record.input.sunk[q]! = false ∧ record.output.state.sunk[q]! = false := by
  obtain ⟨⟨ctx,ranges,build⟩,final,events⟩ := lower_color_facts run
  obtain ⟨zero,safe⟩ := buildCtx_pure_single_block build blocks quiet inside
  refine ⟨zero,final.2 q zero safe,?_⟩
  intro event member
  obtain ⟨pre,records⟩ := events event member
  refine ⟨pre.2 q zero safe,?_⟩
  intro record retained
  obtain ⟨a,b⟩ := records record retained
  exact ⟨a.2 q zero safe,b.2 q zero safe⟩

end Backend.Stock.Proof
