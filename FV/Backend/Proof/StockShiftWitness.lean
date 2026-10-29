module

public import FV.Backend.Proof.StockShiftWitnessInputs

@[expose] public section

namespace Backend.Stock.Proof.ScalarShift.Witness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private theorem dfg_base (kind : Kind) (ty : Clif.Ty) (literal : Bool)
    (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) :
    DFGCons (built kind ty literal).1 (frame kind ty literal) := by
  constructor
  · intro x j info cl v defined found original pure lookup
    by_cases seven : x = 7
    · subst x
      have absent : (built kind ty literal).1.defInst? 7 = none := by
        cases kind <;> cases literal <;> rcases supported with rfl | rfl | rfl | rfl <;> rfl
      rw [absent] at defined; cases defined
    · by_cases thirtyone : x = 31
      · subst x
        cases literal
        · have absent : (built kind ty false).1.defInst? 31 = none := by
            cases kind <;> rcases supported with rfl | rfl | rfl | rfl <;> rfl
          rw [absent] at defined; cases defined
        · cases kind <;> rcases supported with rfl | rfl | rfl | rfl
          all_goals
            change some 0 = some j at defined
            cases defined
            obtain ⟨bound,equal⟩ := Array.getElem?_eq_some_iff.mp found
            subst info
            cases original
            cases lookup
            exact ⟨[_],fun cm => rfl,rfl⟩
      · simp [frame,seven,thirtyone] at lookup
  · intro x t v typed lookup
    by_cases seven : x = 7
    · subst x
      cases kind <;> cases literal <;> rcases supported with rfl | rfl | rfl | rfl
      all_goals
        change some (.int _) = some t at typed
        cases typed
        cases lookup
        rfl
    · by_cases thirtyone : x = 31
      · subst x
        cases kind <;> cases literal <;> rcases supported with rfl | rfl | rfl | rfl
        all_goals
          change some (.int 64) = some t at typed
          cases typed
          cases lookup
          rfl
      · simp [frame,seven,thirtyone] at lookup
private theorem dfg_transport {a b : Ctx} {fr : Clif.Frame}
    (insts : a.insts.map sourceKey = b.insts.map sourceKey)
    (types : a.valTy = b.valTy) (defs : a.valDef = b.valDef) (dfg : DFGCons b fr) : DFGCons a fr := by
  constructor
  · intro x j info cl v defined found original pure lookup
    have view : (b.insts[j]?).map sourceKey = some (sourceKey info) := by
      rw [← Array.getElem?_map,← insts,Array.getElem?_map,found]; rfl
    obtain ⟨info',found',same⟩ := Option.map_eq_some_iff.mp view
    have clifEq := congrArg Prod.fst same
    have resultsEq := congrArg Prod.snd same
    change info'.clif = info.clif at clifEq
    change info'.results = info.results at resultsEq
    obtain ⟨vals,evaluated,written⟩ := dfg.1 x j info' cl v
      (by simpa only [Ctx.defInst?,defs] using defined) found' (clifEq.trans original) pure lookup
    exact ⟨vals,evaluated,by rw [← resultsEq]; exact written⟩
  · simpa only [FrameTyped,Ctx.valueType?,types] using dfg.2
private theorem dominated (kind : Kind) (ty : Clif.Ty) (literal : Bool)
    (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) : Dominated (function kind ty literal) := by
  constructor
  · cases literal
    · change ([7,31,100] : List Nat).Nodup; decide +kernel
    · change ([7,31,100] : List Nat).Nodup; decide +kernel
  · intro ctx ranges st build bi b block
    cases bi with
    | zero =>
      simp [function] at block
      subst b
      constructor
      · intro j stm statement v member
        cases literal
        · cases j <;> simp [function] at statement
          subst stm
          change v ∈ [7,31] at member
          simp only [List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl <;> simp [availOf,function,defsBefore,defsFrom]
        · cases j
          · simp [function] at statement
            subst stm
            cases member
          · rename_i j
            cases j <;> simp [function] at statement
            subst stm
            change v ∈ [7,31] at member
            simp only [List.mem_cons,List.not_mem_nil,or_false] at member
            rcases member with rfl | rfl <;> simp [availOf,function,defsBefore,defsFrom]
      · intro v member
        have narrowed : v ∈ [100] := by cases kind <;> cases literal <;> rcases supported with rfl | rfl | rfl | rfl <;> exact member
        have equal := List.mem_singleton.mp narrowed
        subst v
        cases literal <;> simp [availOf,function,defsBefore,defsFrom]
    | succ bi => simp [function] at block
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := function kind ty literal) (ctx := ctx) (gn := id)).cand tl x available
    have length : (function kind ty literal).blocks.length = 1 := rfl
    omega
private theorem frame_available (kind : Kind) (ty : Clif.Ty) (literal : Bool) (ctx : Ctx) :
    (restrict (frame kind ty literal) (availOf (function kind ty literal) (availIn (function kind ty literal) ctx) 0
      (rootIndex literal))).regs = (frame kind ty literal).regs := by
  funext x
  by_cases present : x = 7 ∨ x = 31
  · rcases present with rfl | rfl
    all_goals apply restrict_regs_of_mem
    all_goals cases literal <;> simp [availOf,function,rootIndex,defsBefore,defsFrom]
  · simp only [not_or] at present
    simp [restrict,frame,present.1,present.2]

/-- Complete actual source/record witnesses cover all scalar widths,
operations and count selections. Literal counts are deliberately unmaterialized;
source and count registers otherwise contain dirty upper bits. -/
theorem stock_lower_shift_source_values_witness (kind : Kind) (ty : Clif.Ty) (literal : Bool)
    (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (d : Nat) (ρ' : Nat → CV) (fr' : Clif.Frame),
      Stock.lower (function kind ty literal) = .ok result ∧ LowerScope (function kind ty literal) ∧ Dominated (function kind ty literal) ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      PRun (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) (regs ty literal) ρ' ∧
      VHolds ⟨ty,kind.value (BitVec.ofInt ty.width (-91)) (.ofInt .i64 273)⟩ (ρ' d) ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst
        (frame kind ty literal,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      ValuesHeld (fun v => Demanded record.input v ∧
        v ∈ availOf (function kind ty literal) (availIn (function kind ty literal) result.ctx) 0 (rootIndex literal+1))
        event.ctx fr' (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (literal = true → regs ty literal 193 = 0) := by
  obtain ⟨input⟩ := inputs kind ty literal supported
  have getX : (frame kind ty literal).getAs 7 ty = .ok (BitVec.ofInt ty.width (-91)) := by
    rcases supported with rfl | rfl | rfl | rfl <;> rfl
  have getY : (frame kind ty literal).regs 31 = some (.ofInt .i64 273) := rfl
  have rawDFG := dfg_transport input.insts input.types input.defs (dfg_base kind ty literal supported)
  have sameFrame := frame_available kind ty literal input.result.ctx
  have restrictedDFG := dfgCons_congr (ctx := input.event.ctx) (fr := frame kind ty literal)
    (fr' := restrict (frame kind ty literal) (availOf (function kind ty literal) (availIn (function kind ty literal) input.result.ctx) 0 (rootIndex literal)))
    rfl rfl sameFrame rawDFG
  have restrictedX := getAs_congr (fr := frame kind ty literal) (x := 7) (ty := ty) (congrFun sameFrame 7)
  have restrictedY := congrFun sameFrame 31
  have guarded := input.held.mono (fun v (h : Demanded input.record.output.state v ∧
    v ∈ availOf (function kind ty literal) (availIn (function kind ty literal) input.result.ctx) 0 (rootIndex literal)) => h.1)
  have block : (function kind ty literal).blocks[0]? = some ((function kind ty literal).blocks[0]!) := rfl
  have statement : ((function kind ty literal).blocks[0]!).body[rootIndex literal]? =
      some (⟨[100],instruction kind ty⟩ : Clif.Stmt) := by cases literal <;> rfl
  have current : input.record.inst = blockStart (function kind ty literal) 0 + rootIndex literal := by
    simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using input.current
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  obtain ⟨d,ρ',output,resultBounds,defs,execution,value,kept,installed⟩ := stock_lower_shift_available_values input.run
    (scope kind ty literal supported) (dominated kind ty literal supported) input.events input.records
    block statement current kind (wide ty) input.source input.clif input.results rfl input.mapped input.recorded input.emitted
    input.selectedId self restrictedDFG guarded (restrictedX.trans getX) (restrictedY.trans getY)
  let val : Clif.Val := ⟨ty,kind.value (BitVec.ofInt ty.width (-91)) (.ofInt .i64 273)⟩
  let fr' : Clif.Frame := {frame kind ty literal with regs := (frame kind ty literal).regs.set 100 val,body := []}
  have evaluated : instOutcome Clif.Env.empty {funcs := []} (frame kind ty literal) Clif.Mem.empty (instruction kind ty) =
      .ok ([val],Clif.Mem.empty) := by cases kind <;> rcases supported with rfl | rfl | rfl | rfl <;> rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (frame kind ty literal,Clif.Mem.empty) (fr',Clif.Mem.empty) :=
    ⟨input.info,instruction kind ty,[val],(frame kind ty literal).regs.set 100 val,[],input.source,input.clif,
      by rw [input.results]; rfl,evaluated,by rw [input.results]; rfl,rfl⟩
  have sourceHeld := source_single_result_values input.source input.clif input.results sourceStep evaluated installed
  exact ⟨input.result,input.event,input.record,d,ρ',fr',input.run,scope kind ty literal supported,
    dominated kind ty literal supported,input.events,input.records,resultBounds,execution,value,sourceStep,sourceHeld,
    fun yes => by subst literal; rfl⟩

end Backend.Stock.Proof.ScalarShift.Witness
