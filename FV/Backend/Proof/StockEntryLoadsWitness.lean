module

public import FV.E2E.RegLevelDriverSem
public import FV.Backend.Proof.StockEntryLoads
public import FV.Backend.Proof.StockEntryAssembly
public import FV.Backend.Proof.StockEntryPrelude
public import FV.Backend.Lowering.StockD0
public import FV.Backend.Proof.LowerDecide
public import FV.Backend.Proof.MemRefines

@[expose] public section

namespace Backend.Stock.Proof.EntryLoadsWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private def function : Clif.Function :=
  let base := D0.source "entry_stack" .systemVI64 []
  {base with
    sig := {base.sig with params := (List.range 9).map fun _ => ⟨.i64,.none,.normal⟩}
    blocks := [{id := 0,params := (List.range 9).map fun i => (i,.i64),body := [],term := .ret [8]}]}

private theorem finite :
    ((Backend.buildCtx function).toOption.map
      (fun s => decide (s.1.valDef = Array.replicate 9 none))).getD false = true ∧
    lowerScopeB function = true := by decide +kernel
private theorem domain : Dominated function ∧ LowerScope function := by
  have stored : ∀ {ctx ranges st0}, Backend.buildCtx function = .ok (ctx,ranges,st0) →
      ctx.valDef = Array.replicate 9 none := by
    intro ctx ranges st0 build
    have h := finite.1
    rw [build] at h
    exact of_decide_eq_true h
  refine ⟨?_,lowerScope_of finite.2⟩
  constructor
  · decide +kernel
  · intro ctx ranges st0 build bi b block
    cases bi with
    | zero =>
      have same : b = function.blocks[0]! := by simpa [function,D0.source] using block.symm
      subst b
      constructor
      · intro j stm statement
        simp [function] at statement
      · intro y member
        change y ∈ [8] at member
        have same : y = 8 := List.mem_singleton.mp member
        subst y
        simp [availOf,function,D0.source,defsBefore,defsFrom,List.range_succ]
    | succ bi => simp [function] at block
  · intro ctx ranges st0 build tl x available notLocal y member
    cases tl with
    | zero =>
      have absent : Ctx.defInst? ctx x = none := by
        by_cases bound : x < 9 <;>
          simp [Ctx.defInst?,stored build,Array.getElem?_replicate,bound]
      simp [defArgs,absent] at member
    | succ tl => simp [parsOf,function,D0.source]

theorem success : (Stock.lower function).isOk = true := by native_decide
private theorem some_result : (Stock.lower function).toOption.isSome := by
  have h := success
  cases actual : Stock.lower function with
  | error e => rw [actual] at h; cases h
  | ok r => rfl
private def result : Result := (Stock.lower function).toOption.get some_result
private theorem run : Stock.lower function = .ok result := by
  cases actual : Stock.lower function with
  | error e => have h := success; rw [actual] at h; cases h
  | ok r => unfold result; simp only [actual,Except.toOption,Option.get_some]
theorem event_bound : 0 < result.blockScans.size := by native_decide
private def event : BlockScanEvent := result.blockScans[0]'event_bound
private theorem events : event ∈ result.blockScans.toList := Array.getElem_mem_toList event_bound

/-- A real ninth parameter is stack-passed and loaded; all eight earlier
parameters have no entry copies. Native facts describe this fixed trace only. -/
theorem stack_parameter_trace :
    result.initial.uses.toList.take 8 = List.replicate 8 .unused ∧
    event.ctx.valueReg? 8 = some (.vreg 200 .int) ∧
    result.code.blocks[0]!.insts =
      #[.load (loadOpOfBytes 8) (.vreg 200 .int) (.fpOffset 16) trustedFlags,
        .rets [(.vreg 200 .int,.x 0)]] := by native_decide

private def address (w : Arm.ArmState) : BitVec 64 :=
  Arm.r (.GPR 29#5) w + BitVec.ofInt 64 16
private def word (w : Arm.ArmState) : BitVec 64 := (Arm.read_mem_bytes 8 (address w) w).setWidth 64
private def stackValue (w : Arm.ArmState) : Clif.Val := ⟨.i64,word w⟩
private def arguments (w : Arm.ArmState) : List Clif.Val :=
  (List.range 8).map (fun i => ⟨.i64,Arm.r (.GPR (rnum i)) w⟩) ++ [stackValue w]
private def frame (w : Arm.ArmState) : Clif.Frame := {
  func := function,regs := (Clif.Regs.empty.setMany (List.range 9) (arguments w)).getD Clif.Regs.empty,
  slots := [],body := [],term := .ret [8] }

/-- The witness values satisfy the original ABI entry relation, including the
ninth parameter in memory, for every machine world. -/
theorem stack_arguments_at_entry (w : Arm.ArmState) :
    ArgsAtEntry (fun _ => False) function.sig (arguments w) w := by
  intro loc val member
  change (loc,val) ∈ [(.reg (.x 0),⟨.i64,Arm.r (.GPR (rnum 0)) w⟩),(.reg (.x 1),⟨.i64,Arm.r (.GPR (rnum 1)) w⟩),(.reg (.x 2),⟨.i64,Arm.r (.GPR (rnum 2)) w⟩),(.reg (.x 3),⟨.i64,Arm.r (.GPR (rnum 3)) w⟩),(.reg (.x 4),⟨.i64,Arm.r (.GPR (rnum 4)) w⟩),(.reg (.x 5),⟨.i64,Arm.r (.GPR (rnum 5)) w⟩),(.reg (.x 6),⟨.i64,Arm.r (.GPR (rnum 6)) w⟩),(.reg (.x 7),⟨.i64,Arm.r (.GPR (rnum 7)) w⟩),(.stack 0,stackValue w)] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h <;> cases h
  all_goals simp only [VHolds,regVal,Clif.Ty.width,stackValue,word,address]
  all_goals try (rw [BitVec.setWidth_setWidth_of_le _ (by decide),BitVec.setWidth_eq])
  refine ⟨?_,rfl⟩
  intro i bound h
  exact h

/-- Actual Stock stack-argument code executes on arbitrary machine memory and
preserves every initialized source value, including omitted entry parameters. -/
theorem stack_parameter_load_witness (X : ExtSem) (w : Arm.ArmState) :
    Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
    ArgsAtEntry (fun _ => False) function.sig (arguments w) w ∧
    Clif.enterFunc function (arguments w) Clif.Mem.empty = .ok (frame w,Clif.Mem.empty) ∧
    ∃ ρ' w', seqRun (csem (fun _ => False) ⟨0,0⟩ X)
      [.load (loadOpOfBytes 8) (.vreg 200 .int) (.fpOffset 16) trustedFlags]
      (entrySeed event.ctx (frame w)) w = some (.fall ρ' w') ∧
      ValuesHeld (fun _ => True) event.ctx (frame w) ρ' ∧
      VHolds (stackValue w) (ρ' 200) ∧ SameWorld (fun _ => False) w' w := by
  have entered : Clif.enterFunc function (arguments w) Clif.Mem.empty =
      .ok (frame w,Clif.Mem.empty) := rfl
  have held := entrySeed_entered_values run domain.2 domain.1 events entered
  have inv := (stock_lower_record_context run domain.2 events).1
  let entries : List (((Nat × Clif.Ty) × ArgLoc) × Nat) := [(((200,.i64),.stack 0),8)]
  have memSem : MemRefines (fun _ => False) 0 (fun _ => none) (csem (fun _ => False) ⟨0,0⟩ X) :=
    memRefines_csem (fun _ => False) ⟨0,0⟩ X rfl (fun _ _ h => by cases h)
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by
    intro _ _ _ _ _ _
    trivial
  have safe : ∀ q ∈ entries, ∀ off, q.1.2 = .stack off →
      (q.2 = 1 ∨ q.2 = 2 ∨ q.2 = 4 ∨ q.2 = 8) ∧
      Avoids (fun _ => False) q.2 (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int))) := by
    intro q member off location
    have equal := List.mem_singleton.mp member
    subst q
    refine ⟨by decide,?_⟩
    intro i bound h
    exact h
  have physical : ∀ x v key q off, (frame w).regs x = some v →
      event.ctx.valueReg? x = some (.vreg key .int) → q ∈ entries → q.1.1.1 = key →
      q.1.2 = .stack off → VHolds v (ofX (loadVal (loadOpOfBytes q.2)
        (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int))) w)) := by
    intro x v key q off found mapped member keyEq location
    have equal := List.mem_singleton.mp member
    subst q
    change 200 = key at keyEq
    subst key
    have source : x = 8 := inv.injective x 8 200 mapped stack_parameter_trace.2.1
    subst x
    change some (stackValue w) = some v at found
    cases found
    have zero : off = 0 := (ArgLoc.stack.inj location).symm
    subst off
    simp only [VHolds,stackValue,word,address,ofX,loadVal,loadOpOfBytes,loadSigned,LoadOp.bytes,Clif.Ty.width,Bool.false_eq_true,ite_false,Int.ofNat_zero,Int.add_zero]
    rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
    simp only [BitVec.setWidth_eq]
    change (Arm.read_mem_bytes 8 (address w) w).setWidth 64 = Arm.read_mem_bytes 8 (address w) w
    rw [BitVec.setWidth_eq]
  obtain ⟨ρ',w',execution,memory,values,same⟩ := entry_loads_preserve_values memSem stable entries
    (by decide) held (cm := Clif.Mem.empty) trivial safe physical
  have loaded := values.read (x := 8) trivial (show (frame w).regs 8 = some (stackValue w) from rfl)
    stack_parameter_trace.2.1
  refine ⟨run,domain.2,domain.1,stack_arguments_at_entry w,entered,ρ',w',?_,values,loaded,same⟩
  simpa only [entries,List.filterMap_cons,List.filterMap_nil,entryLoadOf,Option.some.injEq,
    Int.ofNat_zero,Int.add_zero,id_eq] using execution
private def assembled := assembleOriginalBlock event.ctx function function.blocks[0]! 0 0 #[] #[]
  (List.replicate 9 8) result.initial.uses event.output.code

/-- Actual entry assembly agrees with the real compiled block and has a
nonempty stack-load prelude. This is fixed trace data, not an input certificate. -/
theorem stack_assembly_trace :
    (assembled.toOption.map (fun block => decide
      (block.insts = result.code.blocks[0]!.insts ∧ block.insts.size = 2 ∧ event.output.code.size = 1))).getD false = true := by
  native_decide

/-- Source-preserving entry rows and exact code are derived from a real
successful Stock entry constructor, including its actual omitted parameters. -/
theorem stack_assembly_rows_witness :
    ∃ (block : VBlock) (locs : List ArgLoc) (stack : Nat) (rows : List MappedEntryRow),
      assembled = .ok block ∧ sigParamBytes function.sig = .ok (List.replicate 9 8) ∧
      sigArgLocs function.sig = .ok (locs,stack) ∧
      mappedEntryRows event.ctx result.initial.uses
        ((function.blocks[0]!.params.zip locs).zip (List.replicate 9 8)) = .ok rows ∧
      rows ≠ [] ∧
      (rows.map (·.input)).Sublist
        ((function.blocks[0]!.params.zip locs).zip (List.replicate 9 8)) ∧
      (∀ row ∈ rows, result.initial.uses[row.input.1.1.1]! ≠ .unused ∧
        event.ctx.valueReg? row.input.1.1.1 = some row.reg) ∧
      block.insts = result.code.blocks[0]!.insts ∧
      block = { label := 0, insts := entryPrelude (mappedEntryPairs rows) (mappedEntryLoads rows) ++ event.output.code, params := #[], branchArgs := #[] } := by
  have facts := stack_assembly_trace
  cases actual : assembled with
  | error message => rw [actual] at facts; cases facts
  | ok block =>
    rw [actual] at facts
    have properties : block.insts = result.code.blocks[0]!.insts ∧
        block.insts.size = 2 ∧ event.output.code.size = 1 := of_decide_eq_true facts
    obtain ⟨locs,stack,rows,signature,mapped,order,lookups,code⟩ := assemble_entry_source_rows actual
    have nonempty : rows ≠ [] := by
      intro empty
      have sizes : block.insts.size = event.output.code.size := by
        rw [code]
        simp [empty,mappedEntryPairs,mappedEntryLoads,entryPrelude]
      omega
    exact ⟨block,locs,stack,rows,rfl,rfl,signature,mapped,nonempty,order,lookups,properties.1,code⟩

/-- The whole-driver entry theorem executes its actual emitted stack prelude
on arbitrary machine memory and derives all row/width/mapping obligations. -/
theorem stack_whole_entry_prelude_witness (X : ExtSem) (w : Arm.ArmState) :
    Stock.lower function = .ok result ∧
    ∃ (actual : BlockScanEvent) (block : VBlock) (prelude body : Array MInst)
      (ρ' : Nat → CV) (w' : Arm.ArmState),
      actual ∈ result.blockScans.toList ∧ actual.block = 0 ∧
      result.code.blocks[0]? = some block ∧ block.insts = prelude ++ body ∧
      seqRun (csem (fun _ => False) ⟨0,0⟩ X) prelude.toList
        (entrySeed actual.ctx (frame w)) w = some (.fall ρ' w') ∧
      ValuesHeld (fun _ => True) actual.ctx (frame w) ρ' ∧ SameWorld (fun _ => False) w' w := by
  have entered : Clif.enterFunc function (arguments w) Clif.Mem.empty =
      .ok (frame w,Clif.Mem.empty) := rfl
  have memSem : MemRefines (fun _ => False) 0 (fun _ => none) (csem (fun _ => False) ⟨0,0⟩ X) :=
    memRefines_csem (fun _ => False) ⟨0,0⟩ X rfl (fun _ _ h => by cases h)
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by
    intro _ _ _ _ _ _
    trivial
  obtain ⟨actual,block,prelude,body,ρ',w',events,zero,placed,code,execution,_,values,same,_⟩ :=
    stock_lower_entry_prelude_refines run domain.2 domain.1 entered
      (driverSem_csem (fun _ => False) ⟨0,0⟩ X) memSem stable trivial (stack_arguments_at_entry w)
  exact ⟨run,actual,block,prelude,body,ρ',w',events,zero,placed,code,execution,values,same⟩

end Backend.Stock.Proof.EntryLoadsWitness
