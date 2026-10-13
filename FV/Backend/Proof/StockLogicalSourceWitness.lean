import FV.Backend.Proof.StockLogicalRecordWitness
import FV.Backend.Proof.LowerSim

namespace Backend.Stock.Proof.LogicalSelected
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.LogicalSemantics
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
private theorem rrDominated : Dominated (formFunction .registers) := by
  constructor
  · decide +kernel
  · intro ctx ranges st build bi b block
    cases bi with
    | zero =>
      simp [formFunction,formX,formY] at block
      subst b
      constructor
      · intro j stm statement y member
        cases j <;> simp at statement
        subst stm
        change y ∈ [7, 31] at member
        change y ∈ (([7, 31] ++ (availIn (formFunction .registers) ctx).getD 0 [] ++ []).filter (fun x => decide (x ∉ [100])))
        simp only [List.mem_filter, decide_eq_true_eq, List.append_nil]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> simp
      · intro y member
        change y ∈ [100] at member
        have equal := List.mem_singleton.mp member
        subst y
        change 100 ∈ (([7, 31] ++ (availIn (formFunction .registers) ctx).getD 0 [] ++ [100]).filter
          (fun x => decide (x ∉ ([] : List Nat))))
        simp
    | succ bi => simp [formFunction,formX,formY] at block
  · intro ctx ranges st build tl x available notLocal y member
    have bounds := (inFix_fixOk (f := (formFunction .registers)) (ctx := ctx) (gn := id)).cand tl x available
    have length : (formFunction .registers).blocks.length = 1 := rfl
    omega
private theorem rrAvailable (ctx : Ctx) (y : Nat) :
    y ∈ availOf (formFunction .registers) (availIn (formFunction .registers) ctx) 0 0 ↔ y = 7 ∨ y = 31 := by
  have noEntry : y ∉ (availIn (formFunction .registers) ctx).getD 0 [] := by
    intro member
    have bound := (inFix_fixOk (f := (formFunction .registers)) (ctx := ctx) (gn := id)).cand 0 y member
    omega
  rw [mem_av (show (formFunction .registers).blocks[0]? = some
    ({id := 0, params := [(7, .i64), (31, .i64)], body := [⟨[100], .binary .bor .i64 7 31⟩], term := .ret [100]} : Clif.Block) from rfl)]
  constructor
  · intro available
    rcases available.1 with param | entry | ⟨k, stm, earlier, _, _⟩
    · simpa using param
    · exact False.elim (noEntry entry)
    · omega
  · intro equal
    rcases equal with rfl | rfl
    all_goals
      refine ⟨Or.inl (by simp), ?_⟩
      intro ⟨k, stm, _, statement, member⟩
      cases k <;> simp at statement
      subst stm
      simp at member

private def rrFrame : Clif.Frame := { formFrame .registers with
  body := [⟨[100],.binary .bor .i64 7 31⟩] }

private theorem rrRestricted (ctx : Ctx) :
    (restrict rrFrame (availOf (formFunction .registers)
      (availIn (formFunction .registers) ctx) 0 0)).regs = rrFrame.regs := by
  funext x
  by_cases seven : x = 7
  · subst x
    exact restrict_regs_of_mem ((rrAvailable ctx 7).mpr (Or.inl rfl))
  · by_cases thirtyone : x = 31
    · subst x
      exact restrict_regs_of_mem ((rrAvailable ctx 31).mpr (Or.inr rfl))
    · simp [restrict,rrFrame,formFrame,seven,thirtyone]

/-- A complete logical source step inhabits availability-restricted DFG and
actual record value transfer, preserving both parameter registers. -/
theorem stock_lower_logical_source_values_witness :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (ρ' : Nat → CV) (fr' : Clif.Frame),
      Stock.lower (formFunction .registers) = .ok result ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      PRun (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) (formRegs .registers) ρ' ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst
        (rrFrame,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf (formFunction .registers) (availIn (formFunction .registers) result.ctx) 0 1)
        event.ctx fr' (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨input⟩ := stock_lower_logical_record_inputs_witness .registers
  have sourceX : rrFrame.getAs 7 .i64 = .ok (BitVec.ofNat 64 7) := rfl
  have sourceY : rrFrame.getAs 31 .i64 = .ok (BitVec.ofNat 64 5) := rfl
  have restrictedX := getAs_congr (fr := rrFrame) (x := 7) (ty := .i64)
    (congrFun (rrRestricted input.result.ctx) 7)
  have restrictedY := getAs_congr (fr := rrFrame) (x := 31) (ty := .i64)
    (congrFun (rrRestricted input.result.ctx) 31)
  have restrictedDFG := dfgCons_congr (ctx := input.event.ctx) (fr := formFrame .registers)
    (fr' := restrict rrFrame (availOf (formFunction .registers)
      (availIn (formFunction .registers) input.result.ctx) 0 0)) rfl rfl (rrRestricted input.result.ctx) input.dfg
  have guarded := input.held.mono (fun y (h : Demanded input.record.output.state y ∧ y ∈
    availOf (formFunction .registers) (availIn (formFunction .registers) input.result.ctx) 0 0) => h.1)
  have block : (formFunction .registers).blocks[0]? = some ((formFunction .registers).blocks[0]!) := rfl
  have statement : ((formFunction .registers).blocks[0]!).body[0]? =
      some (⟨[100],.binary .bor .i64 7 31⟩ : Clif.Stmt) := rfl
  have current : input.record.inst = blockStart (formFunction .registers) 0 + 0 := by
    have zero := input.current
    change input.record.inst = 0 at zero
    simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using zero
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  obtain ⟨ρ',execution,value,kept,installed⟩ := stock_lower_logical_available_values input.run
    (formScope .registers) rrDominated input.events input.records block statement current .bor
    input.source input.clif input.results rfl input.mapped input.recorded input.emitted input.selectedId self
    restrictedDFG guarded (restrictedX.trans sourceX) (restrictedY.trans sourceY)
  let val : Clif.Val := ⟨Clif.Ty.i64,Clif.Sem.binary .bor (BitVec.ofNat 64 7) (BitVec.ofNat 64 5)⟩
  let fr' : Clif.Frame := { rrFrame with regs := rrFrame.regs.set 100 val, body := [] }
  have evaluated : instOutcome Clif.Env.empty {funcs := []} rrFrame Clif.Mem.empty
      (.binary .bor .i64 7 31) = .ok ([val],Clif.Mem.empty) := rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (rrFrame,Clif.Mem.empty) (fr',Clif.Mem.empty) :=
    ⟨input.info,.binary .bor .i64 7 31,[val],rrFrame.regs.set 100 val,[],
      input.source,input.clif,by rw [input.results]; rfl,evaluated,by rw [input.results]; rfl,rfl⟩
  have sourceHeld := source_single_result_values input.source input.clif input.results sourceStep evaluated installed
  exact ⟨input.result,input.event,input.record,ρ',fr',input.run,input.events,input.records,execution,sourceStep,sourceHeld⟩

end Backend.Stock.Proof.LogicalSelected
