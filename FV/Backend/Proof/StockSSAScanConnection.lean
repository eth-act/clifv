import FV.Backend.Proof.StockSourceSSA
import FV.Backend.Proof.StockAliasScanEntries

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private def ssaFunction : Clif.Function := {
  name := "source_ssa"
  sig := { params := [], returns := [⟨.i64, .none, .normal⟩] }
  blocks := [{
    id := 0
    params := []
    body := [⟨[0], .iconst .i64 7⟩, ⟨[1], .iconst .i64 9⟩]
    term := .ret [1] }] }
private def ssaBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx ssaFunction).toOption.getD (sinkCtx, #[], sinkState)
private def firstInfo : IInfo := infoOf ssaFunction ⟨[0], .iconst .i64 7⟩
private def secondInfo : IInfo := infoOf ssaFunction ⟨[1], .iconst .i64 9⟩
private theorem ssaBuild : Stock.buildCtx ssaFunction = .ok ssaBuilt := rfl
private theorem ssaInput : (valueDefs ssaFunction).Nodup := by decide
private theorem firstLookup : ssaBuilt.1.insts[0]? = some firstInfo := rfl
private theorem firstResult : (0 : Nat) ∈ firstInfo.results := by decide


/-- The actual block scan preserves a previously bound source result once its
remaining indices exclude the defining instruction. Existing source SSA supplies
all result exclusions; actual allocation supplies reservation separation. -/
theorem stock_scanBlock_ssa_aliasEntry {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    (ssa : (valueDefs f).Nodup) {x key owner ti : Nat} {info : IInfo}
    (definition : ctx.insts[owner]? = some info) (result : x ∈ info.results)
    (mapped : ctx.valueReg? x = some (.vreg key .int))
    (data : V) {block : Nat} {branch : Bool} {indices : List Nat}
    {st : State} {output : BlockScan}
    (reservations : st.tryRegs = initial.tryRegs)
    (noRevisit : owner ∉ indices)
    (run : scanBlock { Driver.termCtx ctx ti data with tryRegs := st.tryRegs[ti]! }
      block ti branch indices st = .ok output) :
    (output.state.alias[key]?).join = (st.alias[key]?).join := by
  apply stock_scanBlock_sourceAliasEntry
    (ctx := { Driver.termCtx ctx ti data with tryRegs := st.tryRegs[ti]! })
    (slot := ti) build mapped (fun _ => rfl) ?_ ?_ run
  · simp only [reservations]
  · intro i member
    exact stock_buildCtx_term_other_results build ssa data definition result
      (fun eq => noRevisit (eq ▸ member))

private def jointCtx : Ctx :=
  { Driver.termCtx ssaBuilt.1 2 (.int 17) with tryRegs := ssaBuilt.2.2.tryRegs[2]! }
private def jointBase : LState :=
  let a := (ssaBuilt.2.2.base.fresh .int).2
  let b := (a.fresh .int).2
  let c := (b.fresh .int).2
  (c.fresh .int).2
private def jointInput : State :=
  { ssaBuilt.2.2 with
    base := jointBase
    demand := #[1, 1]
    alias := aliasStep #[] (193, 196)
    opportunistic := #[some ⟨0, [.vreg 197 .int], 1⟩, none] }
private def jointNext : State :=
  { scanState jointInput 0 with
    alias := aliasStep jointInput.alias (192, 197)
    opportunistic := #[none, none] }
private def jointScan : Scan :=
  ⟨jointNext, some ⟨0, 0, .opportunistic, scanState jointInput 0,
    jointNext, [], [], #[]⟩, #[]⟩
private def jointBlock : BlockScan :=
  ⟨jointNext, [⟨0, jointInput, jointScan⟩], #[]⟩
private theorem joint_scan : scanInstruction jointCtx 0 0 2 false jointInput =
    .ok jointScan := rfl
private theorem joint_block : scanBlock jointCtx 0 2 false [0] jointInput =
    .ok jointBlock := by
  unfold scanBlock
  rw [runScans_ref]
  simp only [runScansRef, joint_scan, bind, Except.bind, pure, Except.pure, Array.empty_append]
  rfl

/-- A real two-definition source context, its actual terminator override and a
nonempty opportunistic scan inhabit all SSA/frame premises. Source value1's
stored 193→196 survives the distinct value0 binding192→197. No whole-function
execution or reachability of this chosen incoming state is claimed. -/
theorem stock_scanBlock_ssa_aliasEntry_witness :
    Stock.buildCtx ssaFunction = .ok ssaBuilt ∧
    (valueDefs ssaFunction).Nodup ∧
    ssaBuilt.1.insts[1]? = some secondInfo ∧ (1 : Nat) ∈ secondInfo.results ∧
    ssaBuilt.1.valueReg? 1 = some (.vreg 193 .int) ∧
    jointInput.tryRegs = ssaBuilt.2.2.tryRegs ∧ (1 : Nat) ∉ [0] ∧
    scanBlock jointCtx 0 2 false [0] jointInput = .ok jointBlock ∧
    (jointInput.alias[193]?).join = some 196 ∧
    (jointBlock.state.alias[192]?).join = some 197 ∧
    (jointBlock.state.alias[193]?).join = (jointInput.alias[193]?).join := by
  have definition : ssaBuilt.1.insts[1]? = some secondInfo := rfl
  have result : (1 : Nat) ∈ secondInfo.results := by decide
  have mapping : ssaBuilt.1.valueReg? 1 = some (.vreg 193 .int) := rfl
  refine ⟨ssaBuild, ssaInput, definition, result, mapping, rfl, by decide,
    joint_block, by decide, by decide, ?_⟩
  exact stock_scanBlock_ssa_aliasEntry ssaBuild ssaInput definition result mapping (.int 17)
    (by rfl) (by decide) joint_block

end Backend.Stock.Proof
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem scans_entry_frame {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan} {key : Nat}
    (cert : ScansSpec exec indices input output)
    (keeps : ∀ i ∈ indices, ∀ st scan, exec i st = .ok scan →
      (scan.state.alias[key]?).join = (st.alias[key]?).join) :
    (output.state.alias[key]?).join = (input.alias[key]?).join := by
  induction cert with
  | nil input => rfl
  | cons head tail ih =>
    exact (ih (fun i member => keeps i (List.mem_cons_of_mem _ member))).trans
      (keeps _ (List.mem_cons_self ..) _ _ head)

private theorem scans_record_entry {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan} {key owner : Nat}
    (cert : ScansSpec exec indices input output) (unique : indices.Nodup)
    (keeps : ∀ i ∈ indices, i ≠ owner → ∀ st scan, exec i st = .ok scan →
      (scan.state.alias[key]?).join = (st.alias[key]?).join)
    {record : ScanRecord} (member : record ∈ output.records) (which : record.inst = owner) :
    (output.state.alias[key]?).join = (record.output.state.alias[key]?).join := by
  induction cert with
  | nil input => cases member
  | @cons i rest input scan tail head remaining ih =>
    have nd := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with same | tailMember
    · subst record
      change i = owner at which
      subst owner
      apply scans_entry_frame remaining
      intro j jm st out run
      exact keeps j (List.mem_cons_of_mem _ jm) (fun eq => nd.1 (eq ▸ jm)) st out run
    · exact ih nd.2 (fun j jm => keeps j (List.mem_cons_of_mem _ jm)) tailMember

/-- In the actual nonrepeating block scan, later records cannot rebind an
previously bound source definition. The conclusion transports its post-scan
alias entry to the complete block output, without a caller-supplied alias fact. -/
theorem stock_scanBlock_record_aliasEntry {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    (ssa : (valueDefs f).Nodup) {x key owner ti : Nat} {info : IInfo}
    (definition : ctx.insts[owner]? = some info) (result : x ∈ info.results)
    (mapped : ctx.valueReg? x = some (.vreg key .int))
    (data : V) {block : Nat} {branch : Bool} {indices : List Nat}
    {st : State} {output : BlockScan}
    (unique : indices.Nodup)
    (run : scanBlock { Driver.termCtx ctx ti data with tryRegs := initial.tryRegs[ti]! }
      block ti branch indices st = .ok output)
    {record : ScanRecord} (member : record ∈ output.records) (which : record.inst = owner) :
    (output.state.alias[key]?).join = (record.output.state.alias[key]?).join := by
  apply scans_record_entry (runScans_spec run) unique ?_ member which
  intro i _ different a scan step
  exact stock_scan_sourceAliasEntry
    (ctx := { Driver.termCtx ctx ti data with tryRegs := initial.tryRegs[ti]! })
    (slot := ti) build mapped (fun _ => rfl) rfl
    (stock_buildCtx_term_other_results build ssa data definition result different) step

/-- The exact backward range used by lowerBlockCore has no repeated instruction
index, regardless of empty/reversed bounds. -/
theorem stock_scan_indices_nodup (start stop : Nat) :
    (((Array.range (stop - start)).map (start + ·)).reverse.toList).Nodup := by
  simp only [Array.toList_reverse, Array.toList_map, Array.toList_range]
  apply List.pairwise_reverse.mpr
  exact List.Pairwise.map (fun n => start + n)
    (fun a b different eq => different (Nat.add_left_cancel eq.symm)) List.nodup_range

private def recordInput : State :=
  { jointInput with
    alias := #[]
    opportunistic := #[some ⟨0, [.vreg 197 .int], 1⟩, some ⟨0, [.vreg 196 .int], 1⟩] }
private def recordMiddle : State :=
  { scanState recordInput 1 with
    alias := aliasStep #[] (193, 196)
    opportunistic := #[some ⟨0, [.vreg 197 .int], 1⟩, none] }
private def recordFirst : Scan :=
  ⟨recordMiddle, some ⟨0, 1, .opportunistic, scanState recordInput 1,
    recordMiddle, [], [], #[]⟩, #[]⟩
private def protectedRecord : ScanRecord := ⟨1, recordInput, recordFirst⟩
private def recordBlock : BlockScan :=
  ⟨jointNext, [protectedRecord, ⟨0, recordMiddle, jointScan⟩], #[]⟩
private theorem record_head : scanInstruction jointCtx 0 1 2 false recordInput =
    .ok recordFirst := by
  have sunk : recordInput.sunk[1]! = false := rfl
  have original : jointCtx.insts[1]!.clif = some (.iconst .i64 9) := rfl
  have results : jointCtx.insts[1]!.results = [1] := rfl
  have demand : (scanState recordInput 1).demand[1]! = 1 := rfl
  have color : (scanState recordInput 1).entryColor[1]! = 0 := rfl
  have opp : (scanState recordInput 1).opportunistic[1]! =
      some ⟨0, [Reg.vreg 196 .int], 1⟩ := rfl
  have mapping : jointCtx.valueReg? 1 = some (.vreg 193 .int) := rfl
  have committed : commitOpportunistic jointCtx 0 1 (scanState recordInput 1) =
      .ok (some recordMiddle) := by
    unfold commitOpportunistic
    simp only [results, List.all_cons, List.all_nil, demand, opp, Option.any_some,
      show (1 == 0) = false from rfl, show (0 == 0) = true from rfl,
      show (1 == 1) = true from rfl, Bool.false_or, Bool.true_and,
      Bool.not_true, Bool.false_eq_true, ite_false]
    unfold commitOpportunisticValues
    simp only [List.foldlM_cons, List.foldlM_nil, opp, mapping, bind, Except.bind,
      pure, Except.pure]
    rfl
  unfold scanInstruction
  simp only [sunk, Bool.false_eq_true, ite_false, show (1 == 2) = false from rfl,
    Bool.false_and, original, Option.any_some, mustLower, results,
    List.any_cons, List.any_nil, demand, color]
  rw [committed]
  rfl
private theorem record_tail : scanInstruction jointCtx 0 0 2 false recordMiddle =
    .ok jointScan := rfl
private theorem record_block : scanBlock jointCtx 0 2 false [1, 0] recordInput =
    .ok recordBlock := by
  unfold scanBlock
  rw [runScans_ref]
  simp only [runScansRef, record_head, recordFirst, record_tail, bind, Except.bind,
    pure, Except.pure, Array.empty_append]
  rfl

/-- Two actual opportunistic records bind193→196 and then192→197. The protected
source1 entry starts absent, is installed by its record and reaches the final
block output. This inhabits record membership and all context/SSA premises;
it does not claim a whole-function run or reachable chosen incoming state. -/
theorem stock_scanBlock_record_aliasEntry_witness :
    Stock.buildCtx ssaFunction = .ok ssaBuilt ∧
    (valueDefs ssaFunction).Nodup ∧
    ssaBuilt.1.insts[1]? = some secondInfo ∧ (1 : Nat) ∈ secondInfo.results ∧
    ssaBuilt.1.valueReg? 1 = some (.vreg 193 .int) ∧
    ([1, 0] : List Nat).Nodup ∧
    scanBlock jointCtx 0 2 false [1, 0] recordInput = .ok recordBlock ∧
    protectedRecord ∈ recordBlock.records ∧ protectedRecord.inst = 1 ∧
    (recordInput.alias[193]?).join = none ∧
    (protectedRecord.output.state.alias[193]?).join = some 196 ∧
    (recordBlock.state.alias[192]?).join = some 197 ∧
    (recordBlock.state.alias[193]?).join =
      (protectedRecord.output.state.alias[193]?).join := by
  have definition : ssaBuilt.1.insts[1]? = some secondInfo := rfl
  have result : (1 : Nat) ∈ secondInfo.results := by decide
  have mapping : ssaBuilt.1.valueReg? 1 = some (.vreg 193 .int) := rfl
  have member : protectedRecord ∈ recordBlock.records := List.mem_cons_self ..
  refine ⟨ssaBuild, ssaInput, definition, result, mapping, by decide, record_block,
    member, rfl, rfl, by decide, by decide, ?_⟩
  exact stock_scanBlock_record_aliasEntry ssaBuild ssaInput definition result mapping (.int 17)
    (by decide) record_block member rfl

/-- A nonempty backward range and an empty/reversed range both satisfy the
unconditional index-uniqueness result. -/
theorem stock_scan_indices_nodup_witness :
    (((Array.range (5 - 2)).map (2 + ·)).reverse.toList) = [4, 3, 2] ∧
    (((Array.range (5 - 2)).map (2 + ·)).reverse.toList).Nodup ∧
    (((Array.range (2 - 5)).map (5 + ·)).reverse.toList).Nodup := by
  refine ⟨?_, stock_scan_indices_nodup 2 5, stock_scan_indices_nodup 5 2⟩
  simp only [Array.toList_reverse, Array.toList_map, Array.toList_range]
  decide

end Backend.Stock.Proof
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- At the exact backward range used by lowerBlockCore, the driver itself
supplies index uniqueness. A recorded definition's alias reaches block exit
without a no-revisit or alias-preservation premise supplied by the caller. -/
theorem stock_scanBlock_backward_record_aliasEntry {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    (ssa : (valueDefs f).Nodup) {x key owner ti : Nat} {info : IInfo}
    (definition : ctx.insts[owner]? = some info) (result : x ∈ info.results)
    (mapped : ctx.valueReg? x = some (.vreg key .int))
    (data : V) {block start stop : Nat} {branch : Bool}
    {st : State} {output : BlockScan}
    (run : scanBlock { Driver.termCtx ctx ti data with tryRegs := initial.tryRegs[ti]! }
      block ti branch (((Array.range (stop - start)).map (start + ·)).reverse.toList)
      st = .ok output)
    {record : ScanRecord} (member : record ∈ output.records) (which : record.inst = owner) :
    (output.state.alias[key]?).join = (record.output.state.alias[key]?).join := by
  exact stock_scanBlock_record_aliasEntry build ssa definition result mapped data
    (stock_scan_indices_nodup start stop) run member which

/-- The two real opportunistic scans use the concrete backward range0–2.
The first recorded source alias survives to the actual block output. This is
an inhabited scan witness, without a claim of whole-function reachability. -/
theorem stock_scanBlock_backward_record_aliasEntry_witness :
    Stock.buildCtx ssaFunction = .ok ssaBuilt ∧
    (valueDefs ssaFunction).Nodup ∧
    ssaBuilt.1.insts[1]? = some secondInfo ∧ (1 : Nat) ∈ secondInfo.results ∧
    ssaBuilt.1.valueReg? 1 = some (.vreg 193 .int) ∧
    scanBlock jointCtx 0 2 false
      (((Array.range (2 - 0)).map (0 + ·)).reverse.toList) recordInput = .ok recordBlock ∧
    protectedRecord ∈ recordBlock.records ∧ protectedRecord.inst = 1 ∧
    (protectedRecord.output.state.alias[193]?).join = some 196 ∧
    (recordBlock.state.alias[193]?).join =
      (protectedRecord.output.state.alias[193]?).join := by
  have definition : ssaBuilt.1.insts[1]? = some secondInfo := rfl
  have result : (1 : Nat) ∈ secondInfo.results := by decide
  have mapping : ssaBuilt.1.valueReg? 1 = some (.vreg 193 .int) := rfl
  have indices : (((Array.range (2 - 0)).map (0 + ·)).reverse.toList) = [1, 0] := by
    simp only [Array.toList_reverse, Array.toList_map, Array.toList_range]
    decide
  have run : scanBlock jointCtx 0 2 false
      (((Array.range (2 - 0)).map (0 + ·)).reverse.toList) recordInput = .ok recordBlock := by
    rw [indices]
    exact record_block
  have member : protectedRecord ∈ recordBlock.records := List.mem_cons_self ..
  refine ⟨ssaBuild, ssaInput, definition, result, mapping, run, member, rfl, by decide, ?_⟩
  exact stock_scanBlock_backward_record_aliasEntry ssaBuild ssaInput definition result mapping
    (.int 17) run member rfl

end Backend.Stock.Proof
