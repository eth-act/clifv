module

public import FV.Backend.Proof.StockShiftRootReceipts
public import FV.Backend.Proof.StockDemandExtent
public import FV.Backend.Proof.IselFamAluBShift

@[expose] public section

namespace Backend.Stock.Proof.ScalarShift
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

def PrepHolds (kind : Kind) (wide : Bool) (ty : Clif.Ty) (u : BitVec ty.width) (value : CV) : Prop :=
  match kind with
  | .lsl => VHolds ⟨ty,u⟩ value
  | .lsr => ExtHolds false (extTarget wide) ⟨ty,u⟩ value
  | .asr => ExtHolds true (extTarget wide) ⟨ty,u⟩ value

def PrepValueOut (F : BitVec 64 → Prop) (isem : Backend.Proof.Sem) (ctx : Ctx) (x : Nat)
    (kind : Kind) (wide : Bool) (ty : Clif.Ty) (u : BitVec ty.width) (st middle : State) (out : V)
    (aliases : Array (Option Nat)) (ρ : Nat → CV) : Prop :=
  ∃ (ms : List MInst) (a : Nat) (ρ' : Nat → CV),out = .reg (.vreg a .int) ∧
    middle.base.emitted = st.base.emitted ++ ms.toArray ∧ st.base.nextVreg ≤ middle.base.nextVreg ∧
    (∀ m ∈ ms,∀ d ∈ vdefs m,st.base.nextVreg ≤ d ∧ d < middle.base.nextVreg) ∧
    PRun F isem (ms.map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
    PrepHolds kind wide ty u (ρ' (aliasNum aliases a)) ∧
    (∀ n,n < st.base.nextVreg ∨ middle.base.nextVreg ≤ n → ρ' n = ρ n) ∧
    (ctx.valueReg? x = some (.vreg a .int) ∨ st.base.nextVreg ≤ a ∧ a < middle.base.nextVreg) ∧
    middle.demand.size = st.demand.size

private theorem ext_location {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {sg : Bool} {to : Nat} {pass : List CTy} {x : Nat} {st middle : State} {out : V} {a : Nat}
    (shape : MappedExtOut ctx x sg to pass st middle out) (output : out = .reg (.vreg a .int)) :
    (ctx.valueReg? x = some (.vreg a .int) ∨ st.base.nextVreg ≤ a ∧ a < middle.base.nextVreg) := by
  obtain ⟨t,typed,safe,rx,mapped,form⟩ := shape
  obtain ⟨nx,rfl⟩ := inv.valueReg x rx mapped
  rcases form with ⟨passes,equal,rfl⟩ | ⟨passes,width,equal,rfl⟩
  · rw [equal] at output
    cases output
    exact Or.inl mapped
  · change out = .reg (.vreg st.base.nextVreg .int) at equal
    rw [equal] at output
    cases output
    right
    simp only [State.mark,LState.fresh,LState.emit]
    omega

private theorem ext_prep_values {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (sg wide : Bool) {x : Nat} {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {ty : Clif.Ty} {u : BitVec ty.width} (source : fr.getAs x ty = .ok u)
    {st middle : State} {out : V} {tr prepTrace : Array RuleId} {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded middle) ctx fr (fun k => ρ (aliasNum aliases k)))
    (run : ApplyInternal p (Stock.sem ctx) {} 999991 27 (extTerm sg wide) [.value x] (st,tr) out (middle,prepTrace)) :
    ∃ (ms : List MInst) (a : Nat) (ρ' : Nat → CV),out = .reg (.vreg a .int) ∧
      middle.base.emitted = st.base.emitted ++ ms.toArray ∧ st.base.nextVreg ≤ middle.base.nextVreg ∧
      (∀ m ∈ ms,∀ d ∈ vdefs m,st.base.nextVreg ≤ d ∧ d < middle.base.nextVreg) ∧
      PRun F isem (ms.map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
      ExtHolds sg (extTarget wide) ⟨ty,u⟩ (ρ' (aliasNum aliases a)) ∧
      (∀ n,n < st.base.nextVreg ∨ middle.base.nextVreg ≤ n → ρ' n = ρ n) ∧
      (ctx.valueReg? x = some (.vreg a .int) ∨ st.base.nextVreg ≤ a ∧ a < middle.base.nextVreg) ∧
      middle.demand.size = st.demand.size := by
  have shape : MappedExtOut ctx x sg (extTarget wide) (extPass wide) st middle out := by
    cases wide <;> cases sg
    · exact stock_zext32_out hp rfl (by decide) run
    · exact stock_sext32_out hp rfl (by decide) run
    · exact stock_zext64_out hp rfl (by decide) run
    · exact stock_sext64_out hp rfl (by decide) run
  obtain ⟨ms,a,ρ',output,code,mono,defs,execution,value,kept⟩ :=
    stock_ext_helper_values hp inv refines sg wide (by decide) dfg source bounded extent held run
  exact ⟨ms,a,ρ',output,code,mono,defs,execution,value,kept,ext_location inv shape output,
    Extent.apply_demand_size run⟩

/-- Actual operand preparation establishes the original scalar value or
required extension, complete fragment, demand extent and result location. -/
theorem stock_shift_prep_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem) (kind : Kind) (wide : Bool)
    {x : Nat} {fr : Clif.Frame} (dfg : DFGCons ctx fr) {ty : Clif.Ty} {u : BitVec ty.width}
    (source : fr.getAs x ty = .ok u) {st middle : State} {out : V} {tr prepTrace : Array RuleId}
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded middle) ctx fr (fun k => ρ (aliasNum aliases k)))
    (run : PrepRun ctx kind wide x st middle tr prepTrace out) :
    PrepValueOut F isem ctx x kind wide ty u st middle out aliases ρ := by
  cases kind
  · obtain ⟨request,trace⟩ := run
    obtain ⟨safe,rx,mapped,rfl,rfl⟩ := (stock_put_in_reg_iff ctx st x out middle).mp request
    obtain ⟨a,rfl⟩ := inv.valueReg x rx mapped
    have needed : Demanded (st.mark x) x := by
      rw [Demanded,(mark_demand st x (extent x _ mapped)).1]; omega
    have value := held.read needed (getAs_ok source) mapped
    refine ⟨[],a,ρ,rfl,by simp [State.mark],Nat.le_refl _,by simp,prun_nil _,value,fun _ _ => rfl,Or.inl mapped,?_⟩
    simp [State.mark]
  · exact ext_prep_values data_program inv refines false wide dfg source bounded extent held run
  · exact ext_prep_values data_program inv refines true wide dfg source bounded extent held run
end Backend.Stock.Proof.ScalarShift
