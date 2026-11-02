import FV.Backend.Proof.StockNoLoadSource
import FV.Backend.Proof.StockNoLoadScan

/-! Sunk-array invariants through actual original/critical-edge nodes and the
complete Stock traversal. No source admission condition or runtime certificate. -/
namespace Backend.Stock.Proof.SinkRules
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch lowerBlockCore lowerNode scanBlock scanInstruction emitInstruction
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

private def frame (st : State) := st.sunk

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
the complete sunk table, including exception-return and payload arguments. -/
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



private theorem zero_refl (st : State) : SunkEq st st := ⟨rfl⟩
private theorem zero_trans {a b c : State} (ab : SunkEq a b) (bc : SunkEq b c) :
    SunkEq a c := ⟨Eq.trans bc.sunk ab.sunk⟩
private theorem frame_rel {a b : State} (h : frame b = frame a) : SunkEq a b := ⟨h⟩

private def branchDecoded (f : Clif.Function) (t : Clif.Terminator) (bi ti : Nat)
    (targets : Array Nat) (before : State)
    (root : Except String (Option V × State × List RuleId)) : Except String BranchEmission := do
  let (out,next,fired) ← root
  if out.isNone then throw s!"no lowering rule for terminator {repr t}"
  let code ← branchCode f t targets next.base.emitted
  pure ⟨next,code,⟨bi,ti,.emitted,before,next,[],fired,code⟩,fired⟩

private theorem branch_decoded_preserves {f : Clif.Function} {t : Clif.Terminator}
    {bi ti : Nat} {targets : Array Nat} {before : State} {output : BranchEmission}
    {root : Except String (Option V × State × List RuleId)}
    (keeps : ∀ {out next trace}, root = .ok (out,next,trace) → SunkEq before next)
    (run : branchDecoded f t bi ti targets before root = .ok output) :
    SunkEq before output.state := by
  unfold branchDecoded at run
  cases executed : root with
  | error e => simp only [executed,bind,Except.bind] at run; cases run
  | ok result =>
    rcases result with ⟨out,next,fired⟩
    simp only [executed,bind,Except.bind] at run
    split at run
    · cases run
    · cases code : branchCode f t targets next.base.emitted with
      | error e => simp only [code] at run; cases run
      | ok instructions =>
        simp only [code,pure,Except.pure] at run
        cases run
        exact keeps executed

private theorem branch_preserves {f : Clif.Function} {ctx : Ctx} (noLoads : NoLoadData ctx)
    {t : Clif.Terminator} {bi ti : Nat} {targets : Array Nat}
    {input : State} {output : BranchEmission}
    (run : emitBranch ctx f t bi ti targets input = .ok output) : SunkEq input output.state := by
  let before : State := {input with current := some ti,color := none,base.emitted := #[]}
  unfold emitBranch at run
  have frame : SunkEq before output.state :=
    branch_decoded_preserves (f := f) (t := t) (bi := bi) (ti := ti)
      (targets := targets) (before := before)
      (root := Stock.runTerm ctx "lower_branch" [.inst ti,.labels targets.toList] before)
      (fun call => ⟨no_load_branch noLoads call⟩) run
  exact zero_trans (a := input) (b := before) ⟨rfl⟩ frame

private def isBranch (t : Clif.Terminator) : Bool :=
  match t with | .ret .. | .trap .. | .returnCall .. => false | _ => true

private theorem optional_branch_preserves {flag : Bool} {input : State}
    {result : Except String BranchEmission} {br : Option BranchEmission}
    (keeps : ∀ e, result = .ok e → SunkEq input e.state)
    (run : (if flag then some <$> result else pure none) = .ok br) :
    SunkEq input (br.map (·.state) |>.getD input) := by
  split at run
  · cases executed : result with
    | error message => simp only [executed,Functor.map,Except.map] at run; cases run
    | ok e =>
      simp only [executed,Functor.map,Except.map] at run
      cases run
      exact keeps e executed
  · cases run; exact zero_refl _

/-- Every actual original block carries the invariant through its branch,
outgoing demands, full scan and every retained record. -/
theorem stock_blockCore_no_load_sunk_eq {ctx : Ctx} (noLoads : NoLoadData ctx) {order : Order} {f : Clif.Function}
    {b : Clif.Block} {bi start stop : Nat} {data : V} {targets : Array Nat}
    {input : State} {output : LoweredBlockCore}
    (dataSafe : ∀ fmt fields, fmt = 16 ∨ fmt = 17 →
      (Backend.sem ctx).unData 152 data ≠ some (fmt,fields))
    (run : lowerBlockCore ctx order f b bi start stop data targets input = .ok output) :
    SunkEq input output.state ∧ SunkEq input output.scan.input ∧
      ∀ r ∈ output.scan.output.records, SunkEq input r.input ∧ SunkEq input r.output.state := by
  let ti := stop-1
  let tc : Ctx := {ctx with insts := ctx.insts.set! ti ⟨data,[],[],none⟩,tryRegs := input.tryRegs[ti]!}
  have tcSafe : NoLoadData tc := term_ctx_no_load noLoads ti data dataSafe
  let branchCall : Except String (Option BranchEmission) :=
    if isBranch b.term then some <$> emitBranch tc f b.term bi ti targets input else pure none
  have branch_keeps {br : Option BranchEmission} (call : branchCall = .ok br) :
      SunkEq input (br.map (·.state) |>.getD input) :=
    optional_branch_preserves (flag := isBranch b.term)
      (result := emitBranch tc f b.term bi ti targets input)
      (fun e run => branch_preserves tcSafe run) call
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
        have pre : SunkEq input before :=
          zero_trans (branch_keeps branch) (zero_trans (frame_rel (a := br.map (·.state) |>.getD input) (b := next) (outgoing_frame edges)) (frame_rel (a := next) (b := before) rfl))
        unfold scanBlock at scans
        have frames := scans_no_load_unsunk tcSafe (runScans_spec scans)
        refine ⟨zero_trans pre frames.1,pre,?_⟩
        intro r member
        obtain ⟨a,b⟩ := frames.2 r member
        exact ⟨zero_trans pre a,zero_trans pre b⟩

private def blockData (f : Clif.Function) (t : Clif.Terminator) : Except String V :=
  match t with
  | .tryCall .. | .tryCallIndirect .. => tryCallData f t
  | _ => termData (abiTerm f t)

private theorem block_data_safe {ctx : Ctx} {f : Clif.Function}
    {term : Clif.Terminator} {data : V} (run : blockData f term = .ok data) :
    ∀ fmt fields, fmt = 16 ∨ fmt = 17 →
      (Backend.sem ctx).unData 152 data ≠ some (fmt,fields) := by
  unfold blockData at run
  split at run
  · exact try_call_data_no_load run
  · exact try_call_data_no_load run
  · exact term_data_no_load run

def RecordsSunkEq (initial : State) (events : Array BlockScanEvent) : Prop :=
  ∀ event ∈ events.toList, SunkEq initial event.input ∧
    ∀ record ∈ event.output.records,
      SunkEq initial record.input ∧ SunkEq initial record.output.state

/-- Both original and critical-edge nodes preserve the invariant and all
previous records; newly retained records inherit the real node input. -/
theorem stock_node_no_load_sunk_eq {ctx : Ctx} (noLoads : NoLoadData ctx) {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label : Nat} {input output : DriverState}
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    SunkEq input.state output.state ∧
      ∀ initial, SunkEq initial input.state → RecordsSunkEq initial input.blockScans →
        RecordsSunkEq initial output.blockScans := by
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
            have facts := stock_blockCore_no_load_sunk_eq noLoads (block_data_safe dataRun) core
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
theorem stock_traversal_no_load_sunk_eq {ctx : Ctx} (noLoads : NoLoadData ctx) {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params labels : List Nat} {input output : DriverState}
    (run : labels.foldlM (fun d label => lowerNode ctx ranges order f params label d) input = .ok output) :
    SunkEq input.state output.state ∧
      ∀ initial, SunkEq initial input.state → RecordsSunkEq initial input.blockScans →
        RecordsSunkEq initial output.blockScans := by
  induction labels generalizing input with
  | nil => cases run; exact ⟨zero_refl _,fun _ _ old => old⟩
  | cons label labels ih =>
    rw [List.foldlM_cons] at run
    cases call : lowerNode ctx ranges order f params label input with
    | error e => simp only [call,bind,Except.bind] at run; cases run
    | ok next =>
      simp only [call,bind,Except.bind] at run
      have head := stock_node_no_load_sunk_eq noLoads call
      have tail := ih run
      refine ⟨zero_trans head.1 tail.1,?_⟩
      intro initial prior old
      exact tail.2 initial (zero_trans prior head.1) (head.2 initial prior old)

private theorem lower_color_facts {f : Clif.Function} {result : Result}
    (scope : LowerScope f)
    (formats : ∀ b ∈ f.blocks, ∀ stm ∈ b.body, CastComplete.MemoryFormat stm.inst)
    (run : Stock.lower f = .ok result) :
    (∃ ctx ranges, Stock.buildCtx f = .ok (ctx,ranges,result.initial)) ∧
    SunkEq result.initial result.final ∧ RecordsSunkEq result.initial result.blockScans := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  cases run
  rename_i _ built hbuild _ order horder _ driver hdriver
  change (∃ ctx ranges, Stock.buildCtx f = .ok (ctx,ranges,built.2.2)) ∧
    SunkEq built.2.2 driver.state ∧ RecordsSunkEq built.2.2 driver.blockScans
  have traversal := stock_traversal_no_load_sunk_eq (scoped_build_ctx_no_load hbuild scope formats) hdriver
  exact ⟨⟨built.1,built.2.1,hbuild⟩,traversal.1,
    traversal.2 built.2.2 (zero_refl _) (by simp [RecordsSunkEq])⟩

/-- Successful actual Stock lowering preserves the complete sunk array through final assembly and all recorded source boundaries. -/
theorem stock_lower_no_load_sunk_eq {f : Clif.Function} {result : Result}
    (scope : LowerScope f)
    (formats : ∀ b ∈ f.blocks, ∀ stm ∈ b.body, CastComplete.MemoryFormat stm.inst)
    (run : Stock.lower f = .ok result) :
    SunkEq result.initial result.final ∧ RecordsSunkEq result.initial result.blockScans :=
  (lower_color_facts scope formats run).2

/-- The original scope and source formats derive unsunkness at every actual
retained boundary, including colored, unused and consumed divisions. -/
theorem stock_lower_no_load_unsunk {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    (formats : ∀ b ∈ f.blocks, ∀ stm ∈ b.body, CastComplete.MemoryFormat stm.inst)
    (q : Nat) : result.final.sunk[q]! = false ∧
      ∀ event ∈ result.blockScans.toList, event.input.sunk[q]! = false ∧
        ∀ record ∈ event.output.records,
          record.input.sunk[q]! = false ∧ record.output.state.sunk[q]! = false := by
  obtain ⟨⟨ctx,ranges,built⟩,final,events⟩ := lower_color_facts scope formats run
  have initial := build_ctx_sunk_false built q
  refine ⟨?_,?_⟩
  · rw [final.sunk]; exact initial
  · intro event member
    obtain ⟨pre,records⟩ := events event member
    refine ⟨?_,?_⟩
    · rw [pre.sunk]; exact initial
    · intro record retained
      obtain ⟨before,after⟩ := records record retained
      constructor
      · rw [before.sunk]; exact initial
      · rw [after.sunk]; exact initial

/-- Any number and ordering of proved scalar operations and divisions inherits
the actual whole-driver invariant, without a demand or return-result restriction. -/
theorem stock_lower_scalar_div_unsunk {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    (family : ∀ b ∈ f.blocks, ∀ stm ∈ b.body,
      HighMulBody.Family stm.inst ∨ ∃ op ty x y, stm.inst = .div op ty x y)
    (q : Nat) : result.final.sunk[q]! = false ∧
      ∀ event ∈ result.blockScans.toList, event.input.sunk[q]! = false ∧
        ∀ record ∈ event.output.records,
          record.input.sunk[q]! = false ∧ record.output.state.sunk[q]! = false :=
  stock_lower_no_load_unsunk run scope
    (fun b hb stm hs => scalar_div_formats (family b hb stm hs)) q

/-- Equality of one installed sink flag across an actual driver boundary. -/
structure SlotEq (slot : Nat) (st next : State) : Prop where
  sunk : next.sunk[slot]! = st.sunk[slot]!

private theorem slot_refl (slot : Nat) (st : State) : SlotEq slot st st := ⟨rfl⟩
private theorem slot_trans {slot : Nat} {a b c : State}
    (ab : SlotEq slot a b) (bc : SlotEq slot b c) : SlotEq slot a c :=
  ⟨bc.sunk.trans ab.sunk⟩

private theorem branch_decoded_slot {slot : Nat} {f : Clif.Function} {t : Clif.Terminator}
    {bi ti : Nat} {targets : Array Nat} {before : State} {output : BranchEmission}
    {root : Except String (Option V × State × List RuleId)}
    (keeps : ∀ {out next trace},root = .ok (out,next,trace) → SlotEq slot before next)
    (run : branchDecoded f t bi ti targets before root = .ok output) :
    SlotEq slot before output.state := by
  unfold branchDecoded at run
  cases executed : root with
  | error e => simp only [executed,bind,Except.bind] at run; cases run
  | ok result =>
    rcases result with ⟨out,next,fired⟩
    simp only [executed,bind,Except.bind] at run
    split at run
    · cases run
    · cases code : branchCode f t targets next.base.emitted with
      | error e => simp only [code] at run; cases run
      | ok instructions =>
        simp only [code,pure,Except.pure] at run
        cases run
        exact keeps executed

private theorem branch_slot_of_helper {slot : Nat} {f : Clif.Function} {ctx : Ctx}
    (keeps : ∀ {vs st next out trace},Stock.runTerm ctx "lower_branch" vs st = .ok (out,next,trace) →
      next.sunk[slot]! = st.sunk[slot]!)
    {t : Clif.Terminator} {bi ti : Nat} {targets : Array Nat}
    {input : State} {output : BranchEmission}
    (run : emitBranch ctx f t bi ti targets input = .ok output) : SlotEq slot input output.state := by
  let before : State := {input with current := some ti,color := none,base.emitted := #[]}
  unfold emitBranch at run
  have framed : SlotEq slot before output.state :=
    branch_decoded_slot (f := f) (t := t) (bi := bi) (ti := ti)
      (targets := targets) (before := before)
      (root := Stock.runTerm ctx "lower_branch" [.inst ti,.labels targets.toList] before)
      (fun call => ⟨keeps call⟩) run
  exact slot_trans (a := input) (b := before) ⟨rfl⟩ framed

private theorem optional_branch_slot {slot : Nat} {flag : Bool} {input : State}
    {result : Except String BranchEmission} {br : Option BranchEmission}
    (keeps : ∀ e,result = .ok e → SlotEq slot input e.state)
    (run : (if flag then some <$> result else pure none) = .ok br) :
    SlotEq slot input (br.map (·.state) |>.getD input) := by
  split at run
  · cases executed : result with
    | error message => simp only [executed,Functor.map,Except.map] at run; cases run
    | ok e =>
      simp only [executed,Functor.map,Except.map] at run
      cases run
      exact keeps e executed
  · cases run; exact slot_refl _ _

/-- Actual branch and statement helper frames lift through a complete original block. -/
theorem slot_blockCore_of_helpers {slot : Nat} {ctx : Ctx} {order : Order} {f : Clif.Function}
    {b : Clif.Block} {bi start stop : Nat} {data : V} {targets : Array Nat}
    {input : State} {output : LoweredBlockCore}
    (helperKeeps : ∀ (reservations : List Reg × List Reg) (branch : Bool) {vs st next out trace},
      Stock.runTerm {ctx with insts := ctx.insts.set! (stop-1) ⟨data,[],[],none⟩,tryRegs := reservations}
        (if branch then "lower_branch" else "lower") vs st = .ok (out,next,trace) →
          next.sunk[slot]! = st.sunk[slot]!)
    (run : lowerBlockCore ctx order f b bi start stop data targets input = .ok output) :
    SlotEq slot input output.state ∧ SlotEq slot input output.scan.input ∧
      ∀ r ∈ output.scan.output.records,SlotEq slot input r.input ∧ SlotEq slot input r.output.state := by
  let ti := stop-1
  let tc : Ctx := {ctx with insts := ctx.insts.set! ti ⟨data,[],[],none⟩,tryRegs := input.tryRegs[ti]!}
  let branchCall : Except String (Option BranchEmission) :=
    if isBranch b.term then some <$> emitBranch tc f b.term bi ti targets input else pure none
  have branch_keeps {br : Option BranchEmission} (call : branchCall = .ok br) :
      SlotEq slot input (br.map (·.state) |>.getD input) :=
    optional_branch_slot (flag := isBranch b.term)
      (result := emitBranch tc f b.term bi ti targets input)
      (fun e run => branch_slot_of_helper (fun call => helperKeeps input.tryRegs[ti]! true call) run) call
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
        have outgoingKeeps : SlotEq slot (br.map (·.state) |>.getD input) next :=
          ⟨congrArg (fun bits => bits[slot]!) (outgoing_frame edges)⟩
        have pre : SlotEq slot input before :=
          slot_trans (branch_keeps branch) (slot_trans outgoingKeeps ⟨rfl⟩)
        unfold scanBlock at scans
        have frames := scans_sunk_at_of_lower
          (fun call => helperKeeps input.tryRegs[ti]! false call) (runScans_spec scans)
        refine ⟨slot_trans pre ⟨frames.1⟩,pre,?_⟩
        intro r member
        obtain ⟨a,b⟩ := frames.2 r member
        exact ⟨slot_trans pre ⟨a⟩,slot_trans pre ⟨b⟩⟩

/-- Every retained event has the same protected flag at all record boundaries. -/
def SlotRecords (slot : Nat) (initial : State) (events : Array BlockScanEvent) : Prop :=
  ∀ event ∈ events.toList,SlotEq slot initial event.input ∧
    ∀ record ∈ event.output.records,SlotEq slot initial record.input ∧
      SlotEq slot initial record.output.state

/-- Actual original and critical-edge nodes inherit a derived block contract. -/
theorem slot_node_of_core {slot : Nat} {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label : Nat} {input output : DriverState}
    (coreKeeps : ∀ bi,order.nodes[label]! = .original bi → ∀ (data : V)
      {before : State} {core : LoweredBlockCore},
      lowerBlockCore ctx order f f.blocks[bi]! bi ranges[bi]!.1 ranges[bi]!.2
        data order.successors[label]! before = .ok core →
      SlotEq slot before core.state ∧ SlotEq slot before core.scan.input ∧
        ∀ record ∈ core.scan.output.records,SlotEq slot before record.input ∧
          SlotEq slot before record.output.state)
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    SlotEq slot input.state output.state ∧
      ∀ initial,SlotEq slot initial input.state → SlotRecords slot initial input.blockScans →
        SlotRecords slot initial output.blockScans := by
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
      exact ⟨⟨congrArg (fun bits => bits[slot]!) (branch_frame edge)⟩,fun _ _ old => old⟩
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
            have facts := coreKeeps bi node data core
            refine ⟨facts.1,?_⟩
            intro initial prior old event member
            change event ∈ (input.blockScans.push lowered.scan).toList at member
            simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
            rcases member with member | rfl
            · exact old event member
            · refine ⟨slot_trans prior facts.2.1,?_⟩
              intro record retained
              obtain ⟨pre,post⟩ := facts.2.2 record retained
              exact ⟨slot_trans prior pre,slot_trans prior post⟩

/-- Complete traversal transports the protected flag and every retained event. -/
theorem slot_traversal_of_cores {slot : Nat} {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params labels : List Nat} {input output : DriverState}
    (coreKeeps : ∀ label ∈ labels,∀ bi,order.nodes[label]! = .original bi → ∀ (data : V)
      {before : State} {core : LoweredBlockCore},
      lowerBlockCore ctx order f f.blocks[bi]! bi ranges[bi]!.1 ranges[bi]!.2
        data order.successors[label]! before = .ok core →
      SlotEq slot before core.state ∧ SlotEq slot before core.scan.input ∧
        ∀ record ∈ core.scan.output.records,SlotEq slot before record.input ∧
          SlotEq slot before record.output.state)
    (run : labels.foldlM (fun d label => lowerNode ctx ranges order f params label d) input = .ok output) :
    SlotEq slot input.state output.state ∧
      ∀ initial,SlotEq slot initial input.state → SlotRecords slot initial input.blockScans →
        SlotRecords slot initial output.blockScans := by
  induction labels generalizing input with
  | nil => cases run; exact ⟨slot_refl _ _,fun _ _ old => old⟩
  | cons label labels ih =>
    rw [List.foldlM_cons] at run
    cases call : lowerNode ctx ranges order f params label input with
    | error e => simp only [call,bind,Except.bind] at run; cases run
    | ok next =>
      simp only [call,bind,Except.bind] at run
      have head := slot_node_of_core (coreKeeps label (List.mem_cons_self ..)) call
      have tail := ih (fun k member => coreKeeps k (List.mem_cons_of_mem _ member)) run
      refine ⟨slot_trans head.1 tail.1,?_⟩
      intro initial prior old
      exact tail.2 initial (slot_trans prior head.1) (head.2 initial prior old)

end Backend.Stock.Proof.SinkRules
