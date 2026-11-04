import FV.Backend.Proof.StockTableSelection
import FV.Backend.Proof.StockConditionalResolved
import FV.Backend.Proof.StockDemandMono
import FV.Backend.Proof.StockDemandExtent

/-! The Stock `br_table` terminator: branch values (#140, CB-14a).

The actual code of a `br_table` on an `i32` index with fewer than 4096 targets is `tableCode`
(`table_named_code`). Through the final aliases, it reads the resolved register of the index;
its two temporaries are fresh, so the resolver keeps them. If that register holds the source
index, the resolved code stops at the `jt_sequence` (its last instruction) on the edge of
`branchIdx`: the table entry `x + 1` when `x` is less than the table size, else the default `0`
(`table_code_runs`). The stop is before the `jt_sequence` writes its temporaries, so the register
file at the stop is the initial one, and the world differs only in the flags
(`TableCalls.values`, `table_named_values`). This is the table analog of
`comparison_branch_values_last`, stated on the actual named branch call. -/

namespace Backend.Stock.Proof.TableBranch
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000

/-- The branch index of a table of `n` targets on index `v`: the entry `v + 1` in range, else the
default `0` (`branchIdx`). -/
def tableTarget (v n : Nat) : Nat := if v < n then v+1 else 0

/-- A run of `code` that stops at its last instruction, a terminator with targets `labels`, on the
edge `target`, with the initial register file and the same world but for the flags. -/
def LastTableExecution (F : BitVec 64 → Prop) (isem : Backend.Proof.Sem) (labels : List Label)
    (code : List MInst) (target : Nat) (ρ : Nat → CV) (world : Arm.ArmState) : Prop :=
  ∃ index inst ops prefixWorld outs endWorld,
    seqRun isem code ρ world = some (.stop index inst ops ρ prefixWorld outs endWorld (.goto target)) ∧
    index+1 = code.length ∧ SameWorldNF F endWorld world ∧
    inst.targets = labels ∧ inst.isTerminator = true

/-- The resolved `tableCode`: the index register is resolved through the aliases, and the two
temporaries, at or above the alias extent, are kept. -/
theorem tableCode_resolved {aliases : Array (Option Nat)} {n : Nat} (bounded : aliases.size ≤ n)
    (d : Label) (ts : List Label) (key : Nat) :
    (tableCode d ts (.vreg key .int) n).map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))) =
      tableCode d ts (.vreg (aliasNum aliases key) .int) n := by
  have first : aliasNum aliases n = n := by
    apply chaseF_none
    rw [Array.getElem?_eq_none bounded]
    rfl
  have second : aliasNum aliases (n+1) = n+1 := by
    apply chaseF_none
    rw [Array.getElem?_eq_none (by omega)]
    rfl
  simp only [tableCode,List.map_cons,List.map_nil,MInst.mapRegs,resolve_vreg]
  change [MInst.emitIsland (4*(8+ts.length)),
    MInst.aluRRImm12 .subS .size32 (Backend.lowerFunction.resolve aliases (aliases.size+1) .xzr)
      (.vreg (aliasNum aliases key) .int) ⟨ts.length,false⟩,
    MInst.jtSequence d ts (.vreg (aliasNum aliases key) .int) (.vreg (aliasNum aliases n) .int)
      (.vreg (aliasNum aliases (n+1)) .int)] = _
  rw [first,second]
  rfl

/-- **`tableCode` takes the edge of the index.** If the low 32 bits of the index register are `v`
and the table has fewer than 4096 targets, the code stops at its `jt_sequence` on the edge
`tableTarget v ts.length`, with the initial register file. -/
theorem table_code_runs {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (d : Label) {ts : List Label} (small : ts.length < 4096) (key n : Nat) {ρ : Nat → CV} {v : Nat}
    (index : ((lo64 (ρ key)).setWidth 32).toNat = v) (world : Arm.ArmState) :
    LastTableExecution F isem (d :: ts) (tableCode d ts (.vreg key .int) n) (tableTarget v ts.length) ρ world := by
  have island : Runs F isem [MInst.emitIsland (4*(8+ts.length))] ρ world (fun ρ1 _ => ρ1 = ρ) :=
    Runs.one refines (operands_emitIsland _) (by rfl) rfl (SameWorldNF.refl F world)
      fun _ _ => vdefUpd_nil _ _
  have compare : ∀ ρ1 w1,ρ1 = ρ → Runs F isem [MInst.aluRRImm12 .subS .size32 .xzr (.vreg key .int) ⟨ts.length,false⟩]
      ρ1 w1 (fun ρ2 w2 => ρ2 = ρ ∧
        Arm.ConditionHolds Cond.hs.bits w2 = decide (ts.length ≤ v)) := by
    rintro ρ1 w1 rfl
    have bits : (⟨ts.length,false⟩ : Imm12).bits < 4096 := small
    refine (Runs.flags refines ⟨_,rfl,rfl,fun w => ispec_cmpImm32 key bits (ρ1 key) w⟩ w1).imp ?_
    rintro ρ2 w2 - ⟨rfl,condition⟩
    refine ⟨rfl,?_⟩
    rw [condition]
    refine (hs_cmp32 (opnd .size32 (ρ2 key)) (BitVec.ofNat 32 (⟨ts.length,false⟩ : Imm12).value)).trans ?_
    have size : (BitVec.ofNat 32 (⟨ts.length,false⟩ : Imm12).value).toNat = ts.length := by
      simp only [Imm12.value,Bool.false_eq_true,ite_false,BitVec.toNat_ofNat]
      omega
    rw [size]
    change decide (ts.length ≤ ((lo64 (ρ2 key)).setWidth 32).toNat) = _
    rw [index]
  obtain ⟨ρ2,w2,prefixRun,prefixWorld,rfl,condition⟩ := island.append compare
  have dispatch : ispec (MInst.jtSequence d ts (.vreg key .int) (.vreg n .int) (.vreg (n+1) .int)) [ρ2 key] w2 =
      some ([ofX 0,ofX 0],w2,.goto (tableTarget v ts.length)) := by
    simp only [ispec,condition,index,tableTarget]
    by_cases inside : v < ts.length
    · have outside : ¬ ts.length ≤ v := by omega
      simp [inside,outside]
    · have above : ts.length ≤ v := by omega
      simp [inside,above]
  obtain ⟨endWorld,stopRun,same⟩ := seqRun_one_stop refines (operands_jtSeq d ts key n (n+1))
    (by unfold tableTarget; split <;> simp) dispatch rfl
  have joined := seqRun_append_fall_stop isem prefixRun stopRun
  simp only [List.cons_append,List.nil_append,List.length_cons,List.length_nil] at joined
  exact ⟨_,_,_,_,_,endWorld,joined,rfl,(SameWorld.nf same).trans prefixWorld,rfl,rfl⟩

/-- The selected table code defines only its two temporaries, the next two fresh registers. -/
theorem tableCode_defs (d : Label) (ts : List Label) (key n : Nat) :
    ∀ m ∈ tableCode d ts (.vreg key .int) n,∀ k ∈ vdefs m,n ≤ k ∧ k < n+2 := by
  intro m member k defined
  simp only [tableCode,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · simp [vdefs,operands_emitIsland] at defined
  · have none : vdefs (MInst.aluRRImm12 .subS .size32 .xzr (.vreg key .int) ⟨ts.length,false⟩) = [] := rfl
    rw [none] at defined
    simp at defined
  · have actual : vdefs (MInst.jtSequence d ts (.vreg key .int) (.vreg n .int) (.vreg (n+1) .int)) = [n,n+1] := by
      simp [vdefs,operands_jtSeq,Operand.isDef]
    rw [actual] at defined
    simp only [List.mem_cons,List.not_mem_nil,or_false] at defined
    omega

/-- **The selected calls of a `br_table` on an `i32` index take the edge of the source index.**
From values held for the values demanded at the output state, the resolved actual code stops at
its `jt_sequence` on the edge `tableTarget bits.toNat n` of the source index `bits`, with the
initial register file and the same world but for the flags. -/
theorem TableCalls.values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i : Nat} {labels : List Label} {before next : State} {out : V}
    (calls : TableCalls ctx i labels before out next) {x : Nat} (source : calls.source = .value x)
    (typeX : ctx.valueType? x = some (.int 32)) (small : calls.table.length < 4096)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {bits : BitVec 32} (getX : fr.getAs x .i32 = .ok bits)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ before.base.nextVreg)
    (extent : ∀ value r,ctx.valueReg? value = some r → value < before.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ code : List MInst,next.base.emitted = before.base.emitted ++ code.toArray ∧
      (∀ m ∈ code,∀ k ∈ vdefs m,before.base.nextVreg ≤ k ∧ k < next.base.nextVreg) ∧
      ∀ world,LastTableExecution F isem labels (code.map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))))
        (tableTarget bits.toNat calls.table.length) ρ world := by
  obtain ⟨r,mapped,_,extended,code⟩ := calls.code source typeX small
  obtain ⟨key,rfl⟩ := inv.valueReg x r mapped
  have marked : Demanded next x := by
    have implRun := calls.implRun
    unfold ApplyInternal at implRun
    have mono := stock_apply_demand_mono implRun x
    rw [extended] at mono
    change (before.mark x).demand[x]! ≤ next.demand[x]! at mono
    rw [(mark_demand before x (extent x _ mapped)).1] at mono
    unfold Demanded
    omega
  have holds := held.read marked (getAs_ok getX) mapped
  have index : ((lo64 (ρ (aliasNum aliases key))).setWidth 32).toNat = bits.toNat := by
    change (ρ (aliasNum aliases key)).setWidth 32 = bits at holds
    rw [lo64,BitVec.setWidth_setWidth_of_le _ (by decide),holds]
  refine ⟨tableCode calls.default calls.table (.vreg key .int) before.base.nextVreg,?_,?_,fun world => ?_⟩
  · rw [code]; exact tableState_emitted _ _ _ _
  · rw [code,tableState_nextVreg]
    exact tableCode_defs _ _ _ _
  · rw [tableCode_resolved bounded]
    have execution := table_code_runs refines calls.default small (aliasNum aliases key) before.base.nextVreg index world
    rw [← calls.labels_eq] at execution
    exact execution

/-- **A real named `br_table` on an `i32` index with fewer than 4096 targets takes the edge of the
source index.** The rule, its calls and its exact code are derived from the actual named call; the
resolved code stops at its last instruction, the `jt_sequence` with targets `labels`, on the edge
`tableTarget bits.toNat ts.length` (`branchIdx`), with the initial register file and the same world
but for the flags. -/
theorem table_named_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {labels : List Label} (slot : ctx.insts[i]? = some ⟨tableData x,[],[],none⟩)
    (typeX : ctx.valueType? x = some (.int 32)) (small : labels.length ≤ 4096)
    {before next : State} {out : V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower_branch" [.inst i,.labels labels] before = .ok (some out,next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {bits : BitVec 32} (getX : fr.getAs x .i32 = .ok bits)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ before.base.nextVreg)
    (extent : ∀ value r,ctx.valueReg? value = some r → value < before.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ (d : Label) (ts : List Label) (code : List MInst),labels = d :: ts ∧ next.base.emitted = before.base.emitted ++ code.toArray ∧
      next.base.nextVreg = before.base.nextVreg+2 ∧
      (∀ m ∈ code,∀ k ∈ vdefs m,before.base.nextVreg ≤ k ∧ k < next.base.nextVreg) ∧
      ∀ world,LastTableExecution F isem labels (code.map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))))
        (tableTarget bits.toNat ts.length) ρ world := by
  obtain ⟨calls,source⟩ := table_named_calls slot run
  have short : calls.table.length < 4096 := by
    have equal := congrArg List.length calls.labels_eq
    simp only [List.length_cons] at equal
    omega
  obtain ⟨_,_,_,_,code⟩ := calls.code source typeX short
  obtain ⟨actual,emitted,defs,execution⟩ := calls.values inv source typeX short refines getX bounded extent held
  refine ⟨calls.default,calls.table,actual,calls.labels_eq,emitted,?_,defs,execution⟩
  rw [code]
  exact tableState_nextVreg _ _ _ _

/-- **The bounds of a real named `br_table` on an `i32` index with fewer than 4096 targets.** The
frontier grows by the two temporaries, the demand array keeps its extent, and the index is
demanded at the output state. -/
theorem table_named_bounds {ctx : Ctx} {i x : Nat} {labels : List Label}
    (slot : ctx.insts[i]? = some ⟨tableData x,[],[],none⟩)
    (typeX : ctx.valueType? x = some (.int 32)) (small : labels.length ≤ 4096)
    {before next : State} {out : V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower_branch" [.inst i,.labels labels] before = .ok (some out,next,trace))
    (extent : x < before.demand.size) :
    next.base.nextVreg = before.base.nextVreg+2 ∧ next.demand.size = before.demand.size ∧
      Demanded next x := by
  obtain ⟨calls,source⟩ := table_named_calls slot run
  have short : calls.table.length < 4096 := by
    have equal := congrArg List.length calls.labels_eq
    simp only [List.length_cons] at equal
    omega
  obtain ⟨_,_,_,extended,code⟩ := calls.code source typeX short
  refine ⟨by rw [code]; exact tableState_nextVreg _ _ _ _,Extent.named_demand_size run,?_⟩
  have implRun := calls.implRun
  unfold ApplyInternal at implRun
  have mono := stock_apply_demand_mono implRun x
  rw [extended] at mono
  change (before.mark x).demand[x]! ≤ next.demand[x]! at mono
  rw [(mark_demand before x extent).1] at mono
  unfold Demanded
  omega

/-- **A `br_table` on an `i32` index with fewer than 4096 targets has a fixed allocation**: any two
real named runs at the same slot, from any inputs and with any such labels, allocate the same
number of registers (the form of `ConditionalBodySpec.FixedAllocation`). -/
theorem table_fixed_allocation {ctx : Ctx} {i x : Nat}
    (slot : ctx.insts[i]? = some ⟨tableData x,[],[],none⟩)
    (typeX : ctx.valueType? x = some (.int 32)) {labels labels' : List Label}
    (small : labels.length ≤ 4096) (small' : labels'.length ≤ 4096)
    {before before' next next' : State} {out out' : V} {trace trace' : List RuleId}
    (run : Stock.runTerm ctx "lower_branch" [.inst i,.labels labels] before = .ok (some out,next,trace))
    (run' : Stock.runTerm ctx "lower_branch" [.inst i,.labels labels'] before' = .ok (some out',next',trace')) :
    next'.base.nextVreg + before.base.nextVreg = before'.base.nextVreg + next.base.nextVreg := by
  obtain ⟨_,_,_,_,_,_,_,frontier⟩ := table_named_code slot typeX small run
  obtain ⟨_,_,_,_,_,_,_,frontier'⟩ := table_named_code slot typeX small' run'
  omega

end Backend.Stock.Proof.TableBranch
