import FV.Backend.Proof.StockDivRequests
import FV.Backend.Proof.StockDivImmOperandValues
import FV.Backend.Proof.StockDivResolvedGuards
import FV.Backend.Proof.StockExtendValues
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private theorem alias_fresh {aliases : Array (Option Nat)} {lo n : Nat}
    (bound : aliases.size ≤ lo) (fresh : lo ≤ n) : aliasNum aliases n = n := by
  apply chaseF_none
  rw [Array.getElem?_eq_none (by omega)]
  rfl
private theorem ext_location {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {x : Nat} {sg : Bool} {st middle : State} {r : Reg} {d : Nat}
    (shape : ScalarShift.MappedExtOut ctx x sg 32 [.int 32,.int 64] st middle (.reg r))
    (output : V.reg r = .reg (.vreg d .int)) :
    ctx.valueReg? x = some (.vreg d .int) ∨ st.base.nextVreg ≤ d ∧ d < middle.base.nextVreg := by
  obtain ⟨t,typed,safe,rx,mapped,form⟩ := shape
  obtain ⟨nx,rfl⟩ := inv.valueReg x rx mapped
  rcases form with ⟨_,equal,rfl⟩ | ⟨_,_,equal,rfl⟩
  · rw [equal] at output; cases output; exact Or.inl mapped
  · change V.reg r = .reg (.vreg st.base.nextVreg .int) at equal
    rw [equal] at output; cases output
    right
    simp only [State.mark,LState.fresh,LState.emit]
    omega
def DivisorValueOut (F : BitVec 64 → Prop) (isem : Backend.Proof.Sem) (ctx : Ctx) (y e : Nat)
    (ty : Clif.Ty) (u : BitVec ty.width) (st next : State) (out : V)
    (aliases : Array (Option Nat)) (ρ : Nat → CV) : Prop :=
  ∃ ms d,out = .reg (.vreg d .int) ∧ Frag st.base next.base ms ∧
    (ctx.valueReg? y = some (.vreg d .int) ∨ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg) ∧
    ∀ world,(u = 0#ty.width → TrapRun isem (ms.map (·.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world .intDivz) ∧
      (u ≠ 0#ty.width → Runs F isem (ms.map (·.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
        DivOpnd (e == 0) u (ρ' (aliasNum aliases d)) ∧
        ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k))
/-- Real divisor execution composes original constants or guarded source
register/widening paths with alias-resolved zero checks. Both source trap and
normal outcomes remain, under the original restricted DFG and held-value guards. -/
theorem stock_div_divisor_values {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {y e n : Nat} {ty : Clif.Ty} {u : BitVec ty.width}
    (get : fr.getAs y ty = .ok u) (enough : 120 ≤ n)
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64) (extension : e = 0 ∨ e = 1)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) {} n 27 698 [.value y,.data 125 e [],.ty (.int ty.width)]
      (st,tr) out (next,trace)) {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (idem : ∀ k,aliasNum aliases (aliasNum aliases k) = aliasNum aliases k)
    (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k))) :
    DivisorValueOut F isem ctx y e ty u st next out aliases ρ := by
  have observed := stock_div_divisor_observed_with_fuel hp ctx (cfg := {}) rfl enough width extension run
  rcases observed with ⟨j,info,i,defined,found,data,nonzero,fuel,materialTrace,fuelBound,materialized⟩ |
    ⟨wide,safe,ry,mapped,output,finish⟩ | ⟨narrow,r,middle,shape,output,finish⟩
  · obtain ⟨original,constant⟩ := stock_div_constant_source_value inv dfg get defined found data
    have sourceNonzero : u ≠ 0#ty.width := by
      apply imm64OfIconst_ne_zero
      rw [← constant]; exact nonzero
    obtain ⟨k,fuelEq⟩ : ∃ k,fuel+1=k+40 := ⟨fuel-39,by omega⟩
    unfold ApplyInternal at materialized
    rw [fuelEq] at materialized
    obtain ⟨ms,d,frame,reg,code,bound,values⟩ := stock_div_original_imm_operand_resolved hp inv dfg get
      defined found data false (cfg := {}) rfl refines width extension materialized bounded idem
    unfold DivisorValueOut
    refine ⟨ms,d,reg,⟨code.emitted,code.mono,code.defs⟩,Or.inr ⟨code.res,bound⟩,?_⟩
    intro world
    refine ⟨fun zero => False.elim (sourceNonzero zero),fun _ => ?_⟩
    obtain ⟨ρ',execution,value,kept⟩ := values ρ
    rw [← alias_fresh bounded code.res] at value
    exact prun_runs execution world (fun _ => ⟨value,kept⟩)
  · dsimp only [Prod.fst] at finish output
    obtain ⟨d,rfl⟩ := inv.valueReg y ry mapped
    have needed : Demanded next y := by
      rw [finish]
      change Demanded (st.mark y) y
      rw [Demanded,(mark_demand st y (extent y _ mapped)).1]
      omega
    have operand : DivOpnd (e == 0) u (ρ (aliasNum aliases d)) :=
      divOpnd_of_vholds64 wide (held.read needed (getAs_ok get) mapped)
    have code : Frag st.base next.base [.trapIf (.zero (.vreg d .int) .size64) .intDivz] := by
      rw [finish]
      exact Frag.emit_nodef st.base (vdefs_trapIf_zero _ _ _)
    unfold DivisorValueOut
    refine ⟨_,d,output,code,Or.inl mapped,?_⟩
    intro world
    have outcomes := stock_div_zero_guard_resolved refines (show ty.width ≤ 64 by omega) operand world
    have size : szOf ty.width = .size64 := by rw [wide]; rfl
    rw [size] at outcomes
    refine ⟨outcomes.1,fun nonzero => ?_⟩
    exact (outcomes.2 nonzero).imp (fun ρ' _ _ equal => by subst ρ'; exact ⟨operand,fun _ _ => rfl⟩)
  · dsimp only [Prod.fst] at finish output
    have heldMiddle : ValuesHeld (Demanded middle) ctx fr (fun k => ρ (aliasNum aliases k)) := by
      intro x needed value lookup
      apply held x ?_ value lookup
      simpa only [finish,Demanded] using needed
    obtain ⟨ms,d,ρ1,reg,emitted,mono,defs,execution,value,kept⟩ := ScalarShift.stock_ext_values inv refines
      (toB := 32) (Or.inl rfl) (pass := [.int 32,.int 64])
      (by intro t member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member; rcases member with rfl | rfl; exact Or.inr ⟨rfl,rfl⟩; exact Or.inl rfl)
      (by intro _; simp) dfg get bounded extent heldMiddle shape
    have location := ext_location inv shape reg
    have operand : DivOpnd (e == 0) u (ρ1 (aliasNum aliases d)) := by
      unfold DivOpnd
      simp only [narrow,ite_true]
      exact value.2 (by simp; omega)
    have resultReg : r = .vreg d .int := V.reg.inj reg
    subst r
    have code : Frag st.base next.base (ms ++ [.trapIf (.zero (.vreg d .int) .size32) .intDivz]) := by
      rw [finish]
      exact (show Frag st.base middle.base ms from ⟨emitted,mono,defs⟩).append
        (Frag.emit_nodef middle.base (vdefs_trapIf_zero _ _ _))
    have nextCount : next.base.nextVreg = middle.base.nextVreg := by rw [finish]; rfl
    unfold DivisorValueOut
    refine ⟨_,d,output,code,?_,?_⟩
    · rcases location with mapped | fresh
      · exact Or.inl mapped
      · exact Or.inr ⟨fresh.1,by rw [nextCount]; exact fresh.2⟩
    · intro world
      simp only [List.map_append,List.map_cons,List.map_nil]
      have preparation :=  prun_runs execution world (P := fun ρ' _ => ρ' = ρ1) (fun _ => rfl)
      have size : szOf ty.width = .size32 := by simp [szOf,narrow]
      refine ⟨fun zero => ?_,fun nonzero => ?_⟩
      · refine TrapRun.prefix preparation (fun ρ' nextWorld equal => ?_)
        subst ρ'
        have outcomes := stock_div_zero_guard_resolved refines (show ty.width ≤ 64 by omega) operand nextWorld
        rw [size] at outcomes
        exact outcomes.1 zero
      · refine Runs.append preparation (fun ρ' nextWorld equal => ?_)
        subst ρ'
        have outcomes := stock_div_zero_guard_resolved refines (show ty.width ≤ 64 by omega) operand nextWorld
        rw [size] at outcomes
        exact (outcomes.2 nonzero).imp (fun ρ' _ _ same => by
          subst ρ'
          refine ⟨operand,fun k outside => ?_⟩
          apply kept k
          simpa only [nextCount] using outside)
end Backend.Stock.Proof.ScalarDiv
