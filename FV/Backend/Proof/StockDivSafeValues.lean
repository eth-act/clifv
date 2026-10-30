import FV.Backend.Proof.StockDivDividendValues
import FV.Backend.Proof.StockDivUdivWideValues
import FV.Backend.Proof.StockDivSafeObservations
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
theorem stock_div_safe_sdiv_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) (wide : Bool)
    {id x y : Nat} {ty : Clif.Ty} (relation : if wide then ty.width = 64 else ty.width ≤ 32) {info : IInfo} (source : ctx.insts[id]? = some info)
    (clif : info.clif = some (.div .sdiv ty x y))
    {st next : State} {out : V} {j : Nat} {constant : IInfo} {i : Int}
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some constant)
    (data : constant.data = .data 152 35 [.data 151 57 [],.int i])
    (guard : u64 i % 2^((CTy.int ty.width).bytes*8) ≠ 0 ∧
      u64 i % 2^((CTy.int ty.width).bytes*8) ≠ 2^((CTy.int ty.width).bytes*8)-1)
    (safe : SafeSdivReceipt program ctx wide 999949 x ty.width i
      (u64 i % 2^((CTy.int ty.width).bytes*8)) st next #[] out)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {u v : BitVec ty.width}
    (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (idem : ∀ k,aliasNum aliases (aliasNum aliases k) = aliasNum aliases k)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k)))
    (outside : ∀ z key,ctx.valueReg? z = some (.vreg key .int) → (fr.regs z).isSome = true →
      aliasNum aliases key < st.base.nextVreg ∨ next.base.nextVreg ≤ aliasNum aliases key) :
    SourceDivisionOut F isem .sdiv ty u v st next out aliases ρ := by
  obtain ⟨rx,ry,s1,s2,t1,t2,shape,dividend,immediate,output,finish⟩ := safe
  have widths := (stock_div_source_data inv .sdiv source clif).1
  have bits : ty.width ≤ 64 := by omega
  have bytes : (CTy.int ty.width).bytes*8 = ty.width := by
    rcases widths with h | h | h | h <;> simp [CTy.bytes,CTy.bits,h]
  have original := (stock_div_constant_source_value inv dfg getY defined found data).2
  have encoded : u64 i = v.toNat := by rw [original,u64_imm64OfIconst bits]
  have guarded : v.toNat ≠ 0 ∧ v.toNat ≠ 2^ty.width-1 := by
    simpa only [bytes,encoded,Nat.mod_eq_of_lt v.isLt] using guard
  have nonzero : v ≠ 0#ty.width := by
    intro zero
    apply guarded.1
    rw [zero]; rfl
  have notMinusOne : v ≠ BitVec.allOnes ty.width := by
    intro minusOne
    apply guarded.2
    rw [minusOne,BitVec.toNat_allOnes]
  have frontier1 := (stock_apply_allocationLe dividend).1
  have bound1 : aliases.size ≤ s1.base.nextVreg := by omega
  obtain ⟨msY,ny,frameY,regY,shapeY,upperY,valuesY⟩ := stock_div_original_imm_operand_resolved data_program inv dfg getY
    defined found data true (cfg := {}) rfl refines (e := 0) widths (by decide)
    (n := 999952) (by simpa only [divisorLiteral,ite_true,Int.natCast_emod,Int.natCast_pow,show ((2:Nat):Int) = 2 from rfl] using immediate) bound1 idem
  have fragmentY : Frag s1.base s2.base msY := ⟨shapeY.emitted,shapeY.mono,shapeY.defs⟩
  have sameY : ry = .vreg ny .int := V.reg.inj regY
  subst ry
  have demandY := congrArg (fun q : State => q.demand) frameY
  change s2.demand = s1.demand at demandY
  have heldS1 : ValuesHeld (Demanded s1) ctx fr (fun k => ρ (aliasNum aliases k)) := by
    intro z needed value lookup
    apply held z ?_ value lookup
    simpa only [finish,quotientState,Demanded,demandY] using needed
  obtain ⟨msX,nx,ρ0,regX,fragmentX,locationX,executionX,inputX,keptX⟩ :=
    stock_div_extended_dividend_values data_program inv refines true wide (n := 999992) (by decide)
      dfg getX relation bounded extent heldS1 (by simpa only [ApplyInternal,ScalarShift.extTerm,ite_true] using dividend)
  have sameX : rx = .vreg nx .int := V.reg.inj regX
  subst rx
  obtain ⟨ρ1,executionY,inputY,keptY⟩ := valuesY ρ0
  have freshY : aliasNum aliases ny = ny := by
    apply chaseF_none
    rw [Array.getElem?_eq_none (by have lower := shapeY.res; omega)]
    rfl
  have divisor : DivOpnd true v (ρ1 (aliasNum aliases ny)) := by rw [freshY]; exact inputY
  let d := s2.base.nextVreg
  let quotient : MInst := .aluRRR .sDiv (szOf ty.width) (.vreg d .int) (.vreg nx .int) (.vreg ny .int)
  have frontier2 := fragmentY.mono
  have frontier3 : s2.base.nextVreg ≤ next.base.nextVreg := by rw [finish]; simp [quotientState,LState.fresh,LState.emit]
  have fragmentQ : Frag s2.base next.base [quotient] := by
    refine ⟨?_,frontier3,?_⟩
    · rw [finish]; simp [quotientState,LState.fresh,LState.emit,quotient,d]
    · intro m member key defined
      have same := List.mem_singleton.mp member
      subst m
      change key ∈ [d] at defined
      have same := List.mem_singleton.mp defined
      subst key
      rw [finish]; simp [quotientState,LState.fresh,LState.emit,d]
  have fragment := fragmentX.append (fragmentY.append fragmentQ)
  have fresh : st.base.nextVreg ≤ d := by omega
  have upper : d < next.base.nextVreg := by rw [finish]; simp [quotientState,LState.fresh,LState.emit,d]
  have outsideX : aliasNum aliases nx < s1.base.nextVreg ∨ s2.base.nextVreg ≤ aliasNum aliases nx := by
    rcases locationX with mapped | allocated
    · have range := outside x nx mapped (by rw [getAs_ok getX]; rfl)
      omega
    · have fixed : aliasNum aliases nx = nx := by
        apply chaseF_none
        rw [Array.getElem?_eq_none (by omega)]
        rfl
      rw [fixed]
      exact Or.inl allocated.2
  have dividend2 : DivOpnd true u (ρ1 (aliasNum aliases nx)) := by rw [keptY _ outsideX]; exact inputX
  unfold SourceDivisionOut
  refine ⟨_,d,output,fragment,⟨fresh,upper⟩,?_⟩
  intro world
  simp only [List.map_append,List.map_cons,List.map_nil]
  refine ⟨?_,?_⟩
  · intro c failed
    rcases sdiv_trap failed with ⟨zero,_⟩ | ⟨_,_,minusOne,_⟩
    · exact False.elim (nonzero zero)
    · exact False.elim (notMinusOne minusOne)
  · intro q success
    refine Runs.append (prun_runs executionX world (P := fun ρ' _ => ρ' = ρ0) (fun _ => rfl)) (fun ρ' wd equal => ?_)
    subst ρ'
    refine Runs.append (prun_runs executionY wd (P := fun ρ' _ => ρ' = ρ1) (fun _ => rfl)) (fun ρ' wd1 equal => ?_)
    subst ρ'
    obtain ⟨ρ2,execution,value,keptQ⟩ := stock_div_quotient_source_values refines true (ty := ty) widths success
      (aliases := aliases) (ρ := ρ1) (a := nx) (b := ny) (d := d) (by omega) dividend2 divisor
    apply prun_runs execution wd1
    intro _
    refine ⟨value,fun k range => ?_⟩
    rw [keptQ k (by omega),keptY k (by omega)]
    exact keptX k (by omega)
end Backend.Stock.Proof.ScalarDiv
