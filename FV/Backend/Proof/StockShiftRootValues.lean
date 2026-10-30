import FV.Backend.Proof.StockShiftValues
import FV.Backend.Proof.StockShiftPrepValues
namespace Backend.Stock.Proof.ScalarShift
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

def Kind.value (kind : Kind) {ty : Clif.Ty} (u : BitVec ty.width) (amount : Clif.Val) : BitVec ty.width :=
  match kind with
  | .lsl => Clif.Sem.ishl u amount.bits
  | .lsr => Clif.Sem.ushr u amount.bits
  | .asr => Clif.Sem.sshr u amount.bits
private theorem operation (kind : Kind) : Backend.Proof.ShiftOp kind.tag kind.op := by
  cases kind <;> simp [Backend.Proof.ShiftOp,Kind.tag,Kind.op]
private theorem finish_value (kind : Kind) (wide : Bool) {ty : Clif.Ty} {u : BitVec ty.width}
    {amount : Clif.Val} {X D : CV} (gate : if wide then ty.width = 64 else ty.width ≤ 32)
    (prep : PrepHolds kind wide ty u X)
    (width : IW ty.width)
    (shift : opnd (szOf ty.width) D = shiftF kind.op (opnd (szOf ty.width) X) (amount.bits.toNat % ty.width)) :
    VHolds ⟨ty,kind.value u amount⟩ D := by
  cases kind
  · change D.setWidth ty.width = u <<< (amount.bits.toNat % ty.width)
    exact fin_lsl (szOf ty.width) (szOf_bits width.le) prep shift
  · cases wide
    · change ty.width ≤ 32 at gate
      have sizeEq : szOf ty.width = .size32 := by simp [szOf,gate]
      rw [sizeEq] at shift
      have prepared := prep.2 gate
      exact fin_lsr .size32 (by change ty.width ≤ 32; exact gate) prepared shift
    · change ty.width = 64 at gate
      cases ty <;> simp [Clif.Ty.width] at gate <;>
      exact fin_lsr .size64 (Nat.le_refl _) (hA64 prep.1) shift
  · cases wide
    · change ty.width ≤ 32 at gate
      have sizeEq : szOf ty.width = .size32 := by simp [szOf,gate]
      rw [sizeEq] at shift
      have prepared := prep.2 gate
      exact fin_asr .size32 (by change ty.width ≤ 32; exact gate) prepared shift
    · change ty.width = 64 at gate
      cases ty <;> simp [Clif.Ty.width] at gate <;>
      exact fin_asr .size64 (Nat.le_refl _) (hA64s prep.1) shift
private theorem output_run {p : Program} (hp : Data p) (ctx : Ctx) (st : State) (tr : Array RuleId)
    (n : Nat) (r : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n+10) 25 172 [.reg r]).run (st,tr) =
      .ok (some (.regsVec [[r]]),st,tr.push rule_prelude_lower_105.id) := by
  have ctor : ∀ t vs q,(Stock.sem ctx).ctor t vs q = Stock.externCtor ctx t vs q := fun _ _ _ => rfl
  have value : ∀ q,Stock.externCtor ctx T.value_reg [.reg r] q = .ok (.regs [r],q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.value_reg _ q (by decide)]; rfl
  have output : ∀ q,Stock.externCtor ctx T.output [.regs [r]] q = .ok (.regsVec [[r]],q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.output _ q (by decide)]; rfl
  cases hp
  isel_eval [*,rule_prelude_lower_105]

def ShiftRootValueOut (F : BitVec 64 → Prop) (isem : Backend.Proof.Sem) (kind : Kind)
    (ty : Clif.Ty) (u : BitVec ty.width) (amount : Clif.Val) (st next : State) (out : V)
    (aliases : Array (Option Nat)) (ρ : Nat → CV) : Prop :=
  ∃ (ms : List MInst) (d : Nat) (ρ' : Nat → CV),out = .regsVec [[.vreg d .int]] ∧
    next.base.emitted = st.base.emitted ++ ms.toArray ∧ st.base.nextVreg ≤ next.base.nextVreg ∧
    (st.base.nextVreg ≤ d ∧ d < next.base.nextVreg) ∧
    (∀ m ∈ ms,∀ r ∈ vdefs m,st.base.nextVreg ≤ r ∧ r < next.base.nextVreg) ∧
    PRun F isem (ms.map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
    VHolds ⟨ty,kind.value u amount⟩ (ρ' (aliasNum aliases d)) ∧
    ∀ n,n < st.base.nextVreg ∨ next.base.nextVreg ≤ n → ρ' n = ρ n

/-- Preparation and the selected shift compose under source endpoint
separation derived from original record availability. These local guards are
not new checker or accepted-input conditions. -/
theorem stock_shift_root_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem) (kind : Kind) (wide : Bool)
    {ty : Clif.Ty} (width : IW ty.width) (gate : if wide then ty.width = 64 else ty.width ≤ 32)
    {x y : Nat} {fr : Clif.Frame} (dfg : DFGCons ctx fr) {u : BitVec ty.width} {amount : Clif.Val}
    (sourceX : fr.getAs x ty = .ok u) (sourceY : fr.regs y = some amount)
    {st next : State} {out : V} {tr trace : Array RuleId} {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun z => ρ (aliasNum aliases z)))
    (outsideX : ∀ a,ctx.valueReg? x = some (.vreg a .int) → aliasNum aliases a < st.base.nextVreg ∨ next.base.nextVreg ≤ aliasNum aliases a)
    (outsideY : ∀ a,ctx.valueReg? y = some (.vreg a .int) → aliasNum aliases a < st.base.nextVreg ∨ next.base.nextVreg ≤ aliasNum aliases a)
    (rhs : (evalExpr program (Stock.sem ctx) {} 999999 (kind.rule wide).rhs (rootEnv wide ty.width x y)).run
      (st,tr) = .ok (some out,next,trace)) :
    ShiftRootValueOut F isem kind ty u amount st next out aliases ρ := by
  obtain ⟨prepared,result,middle,after,prepTrace,shiftTrace,prepRun,helper,output⟩ := stock_shift_rhs_receipts kind wide rhs
  have actualWidth : (if wide then 64 else ty.width) = ty.width := by cases wide <;> simp_all
  rw [actualWidth] at helper
  have outputMono := stock_apply_demand_mono output
  have helperMono := stock_apply_demand_mono helper
  have outputFront := (stock_apply_allocationLe output).1
  have prepHeld : ValuesHeld (Demanded middle) ctx fr (fun z => ρ (aliasNum aliases z)) := by
    apply held.mono
    intro z needed
    unfold Demanded at needed ⊢
    have m := helperMono z
    have o := outputMono z
    omega
  obtain ⟨ms1,a,ρ1,preparedEq,prepCode,prepMono,prepDefs,prepExec,prepValue,prepKept,location,demandSize⟩ :=
    stock_shift_prep_values inv refines kind wide dfg sourceX bounded extent prepHeld prepRun
  rw [preparedEq] at helper
  have allocates := stock_do_shift_allocates data_program inv (operation kind) width (by decide) dfg sourceY helper
  have middleBound : aliases.size ≤ middle.base.nextVreg := by omega
  have separation : aliasNum aliases a ≠ middle.base.nextVreg := by
    rcases location with mapped | ⟨fresh,before⟩
    · have outside := outsideX a mapped
      omega
    · have resolved : aliasNum aliases a = a := by
        apply chaseF_none
        rw [Array.getElem?_eq_none (by omega : aliases.size ≤ a)]
        rfl
      rw [resolved]; omega
  have countHeld : ValuesHeld (fun z => z = y ∧ Demanded after z) ctx fr (fun z => ρ1 (aliasNum aliases z)) := by
    intro z needed val lookup
    obtain ⟨same,needed⟩ := needed
    subst z
    obtain ⟨r,mapped,value⟩ := held y (by unfold Demanded at *; have grows := outputMono y; omega) val lookup
    refine ⟨r,mapped,?_⟩
    change VHolds val (ρ1 (aliasNum aliases r))
    rw [prepKept _ (by have outside := outsideY r mapped; omega)]
    exact value
  have middleExtent : ∀ x r,ctx.valueReg? x = some r → x < middle.demand.size := by
    intro z r mapped; rw [demandSize]; exact extent z r mapped
  obtain ⟨ms2,d,ρ',resultEq,shiftCode,shiftMono,resultBounds,shiftDefs,shiftExec,shiftValue,shiftKept⟩ :=
    stock_do_shift_values_of_count data_program inv refines (operation kind) width (by decide) dfg sourceY
      middleBound separation middleExtent countHeld helper
  rw [resultEq,output_run data_program ctx after shiftTrace 999988 (.vreg d .int)] at output
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at output
  obtain ⟨outputEq,afterEq,traceEq⟩ := output
  have value := finish_value kind wide gate prepValue width shiftValue
  refine ⟨ms1++ms2,d,ρ',outputEq.symm,?_,?_,?_,?_,?_,value,?_⟩
  · rw [← afterEq,shiftCode,prepCode]
    simp [Array.append_assoc]
  · rw [← afterEq]; omega
  · rw [← afterEq]; omega
  · intro m member r defined
    rcases List.mem_append.mp member with pre | shift
    · have bounds := prepDefs m pre r defined
      rw [← afterEq]; omega
    · have bounds := shiftDefs m shift r defined
      rw [← afterEq]; omega
  · rw [List.map_append]
    exact prun_append prepExec shiftExec
  · intro n outside
    have keepShift : n < middle.base.nextVreg ∨ after.base.nextVreg ≤ n := by
      rw [← afterEq] at outside
      omega
    rw [shiftKept n keepShift]
    apply prepKept
    rw [← afterEq] at outside
    omega
end Backend.Stock.Proof.ScalarShift
