import FV.Backend.Proof.StockShiftRecordValues
import FV.Backend.Proof.LowerValueRelations
namespace Backend.Stock.Proof.ScalarShift.Witness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
def wide (ty : Clif.Ty) : Bool := ty == .i64
def rootIndex (literal : Bool) : Nat := if literal then 1 else 0
def instruction (kind : Kind) (ty : Clif.Ty) : Clif.Inst := .binary kind.cop ty 7 31
def function (kind : Kind) (ty : Clif.Ty) (literal : Bool) : Clif.Function := {
  name := "stock_shift_values"
  sig := {
    params := (if literal then [⟨ty,.none,.normal⟩] else [⟨ty,.none,.normal⟩,⟨.i64,.none,.normal⟩])
    returns := [⟨ty,.none,.normal⟩]
    callConv := some .systemV }
  blocks := [{id := 0,params := (if literal then [(7,ty)] else [(7,ty),(31,.i64)]),body :=
    (if literal then [⟨[31],.iconst .i64 (BitVec.ofNat 64 273)⟩] else []) ++ [⟨[100],instruction kind ty⟩],term := .ret [100]}] }
def built (kind : Kind) (ty : Clif.Ty) (literal : Bool) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (function kind ty literal)).toOption.getD (sinkCtx,#[],sinkState)
def frame (kind : Kind) (ty : Clif.Ty) (literal : Bool) : Clif.Frame := {
  func := function kind ty literal,regs := fun x => if x = 7 then some (.ofInt ty (-91)) else
    if x = 31 then some (.ofInt .i64 273) else none,
  slots := [],body := [⟨[100],instruction kind ty⟩],term := .ret [100] }
def regs (ty : Clif.Ty) (literal : Bool) (n : Nat) : CV :=
  if n = 192 then BitVec.ofNat 128 (2^100+(Clif.Val.ofInt ty (-91)).bits.toNat)
  else if n = 193 then (if literal then 0 else BitVec.ofNat 128 (2^112+273)) else 0
def demand (literal : Bool) : Array Nat :=
  let ds := (Array.replicate 101 0).modify 7 (·+1) |>.modify 100 (·+1)
  if literal then ds else ds.modify 31 (·+1)
def sourceKey (info : IInfo) := (info.clif,info.results)
def ctxKey (ctx : Ctx) := (ctx.insts.map sourceKey,ctx.valTy,ctx.valDef,ctx.valReg)
theorem scope (kind : Kind) (ty : Clif.Ty) (literal : Bool)
    (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) : LowerScope (function kind ty literal) :=
  lowerScope_of (by cases kind <;> cases literal <;> rcases supported with rfl | rfl | rfl | rfl <;> decide +kernel)
section Runs
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
def observedReport (kind : Kind) (ty : Clif.Ty) (literal : Bool) : Option Bool :=
(Stock.lower (function kind ty literal)).toOption.map (fun result =>
      decide (aliasNum result.final.alias 192 = 192) && decide (aliasNum result.final.alias 193 = 193) && result.blockScans.toList.any (fun event =>
        decide (ctxKey event.ctx = ctxKey (built kind ty literal).1) && event.output.records.any (fun record =>
          record.inst == rootIndex literal && decide (record.output.state.demand = demand literal) &&
          record.output.step.any (fun step => step.decision == .emitted && decide (step.rules.getLast? = some (kind.rule (wide ty)).id)))))

private theorem observed_lsl_i8_false : observedReport .lsl .i8 false = some true := by decide +kernel
private theorem observed_lsl_i8_true : observedReport .lsl .i8 true = some true := by decide +kernel
private theorem observed_lsl_i16_false : observedReport .lsl .i16 false = some true := by decide +kernel
private theorem observed_lsl_i16_true : observedReport .lsl .i16 true = some true := by decide +kernel
private theorem observed_lsl_i32_false : observedReport .lsl .i32 false = some true := by decide +kernel
private theorem observed_lsl_i32_true : observedReport .lsl .i32 true = some true := by decide +kernel
private theorem observed_lsl_i64_false : observedReport .lsl .i64 false = some true := by decide +kernel
private theorem observed_lsl_i64_true : observedReport .lsl .i64 true = some true := by decide +kernel
private theorem observed_lsr_i8_false : observedReport .lsr .i8 false = some true := by decide +kernel
private theorem observed_lsr_i8_true : observedReport .lsr .i8 true = some true := by decide +kernel
private theorem observed_lsr_i16_false : observedReport .lsr .i16 false = some true := by decide +kernel
private theorem observed_lsr_i16_true : observedReport .lsr .i16 true = some true := by decide +kernel
private theorem observed_lsr_i32_false : observedReport .lsr .i32 false = some true := by decide +kernel
private theorem observed_lsr_i32_true : observedReport .lsr .i32 true = some true := by decide +kernel
private theorem observed_lsr_i64_false : observedReport .lsr .i64 false = some true := by decide +kernel
private theorem observed_lsr_i64_true : observedReport .lsr .i64 true = some true := by decide +kernel
private theorem observed_asr_i8_false : observedReport .asr .i8 false = some true := by decide +kernel
private theorem observed_asr_i8_true : observedReport .asr .i8 true = some true := by decide +kernel
private theorem observed_asr_i16_false : observedReport .asr .i16 false = some true := by decide +kernel
private theorem observed_asr_i16_true : observedReport .asr .i16 true = some true := by decide +kernel
private theorem observed_asr_i32_false : observedReport .asr .i32 false = some true := by decide +kernel
private theorem observed_asr_i32_true : observedReport .asr .i32 true = some true := by decide +kernel
private theorem observed_asr_i64_false : observedReport .asr .i64 false = some true := by decide +kernel
private theorem observed_asr_i64_true : observedReport .asr .i64 true = some true := by decide +kernel

private theorem observed (kind : Kind) (ty : Clif.Ty) (literal : Bool)
    (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) :
    observedReport kind ty literal = some true := by
  cases kind <;> cases literal <;> rcases supported with rfl | rfl | rfl | rfl
  · exact observed_lsl_i8_false
  · exact observed_lsl_i16_false
  · exact observed_lsl_i32_false
  · exact observed_lsl_i64_false
  · exact observed_lsl_i8_true
  · exact observed_lsl_i16_true
  · exact observed_lsl_i32_true
  · exact observed_lsl_i64_true
  · exact observed_lsr_i8_false
  · exact observed_lsr_i16_false
  · exact observed_lsr_i32_false
  · exact observed_lsr_i64_false
  · exact observed_lsr_i8_true
  · exact observed_lsr_i16_true
  · exact observed_lsr_i32_true
  · exact observed_lsr_i64_true
  · exact observed_asr_i8_false
  · exact observed_asr_i16_false
  · exact observed_asr_i32_false
  · exact observed_asr_i64_false
  · exact observed_asr_i8_true
  · exact observed_asr_i16_true
  · exact observed_asr_i32_true
  · exact observed_asr_i64_true
end Runs

structure Inputs (kind : Kind) (ty : Clif.Ty) (literal : Bool) where
  result : Result
  event : BlockScanEvent
  record : ScanRecord
  info : IInfo
  step : Step
  run : Stock.lower (function kind ty literal) = .ok result
  events : event ∈ result.blockScans.toList
  records : record ∈ event.output.records
  current : record.inst = rootIndex literal
  source : event.ctx.insts[record.inst]? = some info
  clif : info.clif = some (instruction kind ty)
  results : info.results = [100]
  mapped : event.ctx.valueReg? 100 = some (.vreg 194 .int)
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  selectedId : step.rules.getLast? = some (kind.rule (wide ty)).id
  insts : event.ctx.insts.map sourceKey = (built kind ty literal).1.insts.map sourceKey
  types : event.ctx.valTy = (built kind ty literal).1.valTy
  defs : event.ctx.valDef = (built kind ty literal).1.valDef
  held : ValuesHeld (Demanded record.output.state) event.ctx (frame kind ty literal)
    (fun k => regs ty literal (aliasNum result.final.alias k))
theorem inputs (kind : Kind) (ty : Clif.Ty) (literal : Bool)
    (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) : Nonempty (Inputs kind ty literal) := by
  have actual := observed kind ty literal supported
  unfold observedReport at actual
  cases run : Stock.lower (function kind ty literal) with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,Bool.and_eq_true,
      decide_eq_true_eq,List.any_eq_true,beq_iff_eq,and_assoc] at actual
    obtain ⟨alias192,alias193,event,events,ctxEq,record,records,current,demandEq,stepData⟩ := actual
    simp only [ctxKey,Prod.mk.injEq] at ctxEq
    obtain ⟨insts,types,defs,maps⟩ := ctxEq
    obtain ⟨step,recorded,emitted,selectedId⟩ := (by
      simpa only [Option.any_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] using stepData :
        ∃ step,record.output.step = some step ∧ step.decision = .emitted ∧
          step.rules.getLast? = some (kind.rule (wide ty)).id)
    have keyAt : (event.ctx.insts[record.inst]?).map sourceKey = some (some (instruction kind ty),[100]) := by
      rw [← Array.getElem?_map,insts,current]
      cases kind <;> cases literal <;> rcases supported with rfl | rfl | rfl | rfl <;> decide +kernel
    obtain ⟨info,source,keyEq⟩ := Option.map_eq_some_iff.mp keyAt
    have clif := congrArg Prod.fst keyEq
    have results := congrArg Prod.snd keyEq
    change info.clif = some (instruction kind ty) at clif
    change info.results = [100] at results
    have mapped : event.ctx.valueReg? 100 = some (.vreg 194 .int) := by
      simp only [Ctx.valueReg?,maps]
      cases kind <;> cases literal <;> rcases supported with rfl | rfl | rfl | rfl <;> rfl
    have held : ValuesHeld (Demanded record.output.state) event.ctx (frame kind ty literal)
        (fun n => regs ty literal (aliasNum result.final.alias n)) := by
      intro x needed val lookup
      by_cases seven : x = 7
      · subst x
        change some (.ofInt ty (-91)) = some val at lookup
        cases lookup
        refine ⟨192,?_,?_⟩
        · simp only [Ctx.valueReg?,maps]
          cases kind <;> cases literal <;> rcases supported with rfl | rfl | rfl | rfl <;> rfl
        · dsimp only
          rw [alias192]
          cases literal <;> rcases supported with rfl | rfl | rfl | rfl <;> unfold VHolds <;> decide +kernel
      · by_cases thirtyone : x = 31
        · subst x
          cases literal
          · change some (.ofInt .i64 273) = some val at lookup
            cases lookup
            refine ⟨193,?_,?_⟩
            · simp only [Ctx.valueReg?,maps]
              cases kind <;> rcases supported with rfl | rfl | rfl | rfl <;> rfl
            · dsimp only; rw [alias193]; rcases supported with rfl | rfl | rfl | rfl <;> unfold VHolds <;> decide +kernel
          · have unused : record.output.state.demand[31]! = 0 := by rw [demandEq]; rfl
            exact False.elim (needed unused)
        · simp [frame,seven,thirtyone] at lookup
    exact ⟨⟨result,event,record,info,step,run,events,records,current,source,clif,results,mapped,
      recorded,emitted,selectedId,insts,types,defs,held⟩⟩

end Backend.Stock.Proof.ScalarShift.Witness
