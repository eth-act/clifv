module

public import FV.Backend.Proof.StockLogicalExtrMatchReceipt
public import FV.Backend.Proof.StockLogicalExtrValues

@[expose] public section

namespace Backend.Stock.Proof.LogicalExtr
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private theorem original_word_value {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {value : Nat} {left : Bool} (word : SourceWord ctx value left)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {ty : Clif.Ty} {v : BitVec ty.width}
    (getter : fr.getAs value ty = .ok v) (count : word.amount.toNat < ty.width) :
    ∃ u,fr.getAs word.word ty = .ok u ∧
      v = if left then u <<< word.amount.toNat else u >>> word.amount.toNat := by
  have accepted := inv.instE word.literalInst word.literal _ word.countFound word.countOriginal
  have literalSupported : eTy word.literalTy = true := by
    simpa [Compile.instE,Compile.tyE,eTy] using accepted
  have amount : word.amount.toNat = word.bits.toNat := by
    unfold SourceWord.amount
    rw [Int.toNat_natCast,u64_imm64OfIconst (eTy_width literalSupported)]
  have shift : (if left then Clif.BinaryOp.ishl else .ushr).isShift = true := by cases left <;> rfl
  obtain ⟨u,source,shifted⟩ := shift_const_value dfg shift word.defined word.found word.original
    word.countDefined word.countFound word.countOriginal getter
  have bounded : word.bits.toNat < ty.width := by rwa [amount] at count
  cases left
  · simp only [Bool.false_eq_true,ite_false,ite_true,Clif.Sem.shift,Clif.Sem.ishl,Clif.Sem.ushr,Clif.Sem.shiftAmt,Nat.mod_eq_of_lt bounded,Option.some.injEq] at shifted
    exact ⟨u,source,by simpa only [amount,Bool.false_eq_true,ite_false,ite_true] using shifted.symm⟩
  · simp only [Bool.false_eq_true,ite_false,ite_true,Clif.Sem.shift,Clif.Sem.ishl,Clif.Sem.ushr,Clif.Sem.shiftAmt,Nat.mod_eq_of_lt bounded,Option.some.injEq] at shifted
    exact ⟨u,source,by simpa only [amount,Bool.false_eq_true,ite_false,ite_true] using shifted.symm⟩

/-- Actual matching and RHS execution derive all EXTR width/count/source-word
facts internally. The emitted instruction computes the original source OR,
including its mirrored operand order, through final aliases and a fresh write. -/
theorem matched_values {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (mirrored : Bool) {i a b m n : Nat} {ty : Clif.Ty} {info : IInfo}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.binary .bor ty a b))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {u v : BitVec ty.width}
    (sourceX : fr.getAs a ty = .ok u) (sourceY : fr.getAs b ty = .ok v)
    {st next : State} {out : V} {tr trace : Array RuleId}
    {env : Isle.Interp.Env V} {middle : State × Array RuleId}
    {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun z => ρ (aliasNum aliases z)))
    (matched : (matchRule p (Stock.sem ctx) {} (m+20) (extrRule mirrored) [.inst i]).run (st,tr) =
      .ok (some env,middle))
    (rhs : (evalExpr p (Stock.sem ctx) {} (n+60) (extrRule mirrored).rhs env).run middle =
      .ok (some out,next,trace)) :
    ∃ (mi : MInst) (ρ' : Nat → CV),out = .regsVec [[.vreg st.base.nextVreg .int]] ∧
      next.base = (st.base.fresh .int).2.emit mi ∧
      PRun F isem [mi.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary .bor u v⟩ (ρ' st.base.nextVreg) ∧
      ∀ z,z ≠ st.base.nextVreg → ρ' z = ρ z := by
  obtain ⟨first,second,width,guard,envEq,middleEq⟩ := match_receipt hp inv mirrored source clif matched
  rw [envEq,middleEq] at rhs
  have narrow : ty.width ≤ 64 := by rcases width with h | h <;> omega
  cases mirrored with
  | false =>
    simp only [Bool.false_eq_true,ite_false,ite_true] at *
    obtain ⟨sum,positiveX,positiveY,_,_,_⟩ := extrOk_nat narrow guard
    have countX : first.amount.toNat < ty.width := by omega
    have countY : second.amount.toNat < ty.width := by omega
    obtain ⟨x,getX,valueX⟩ := original_word_value inv first dfg sourceX countX
    obtain ⟨y,getY,valueY⟩ := original_word_value inv second dfg sourceY countY
    obtain ⟨mi,ρ',output,state,execution,value,kept⟩ :=
      rhs_values hp false refines width sum countY getX getY bounded extent held rhs
    exact ⟨mi,ρ',output,state,execution,by simpa only [Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_false,ite_true,Clif.Sem.binary,Clif.Sem.bor,valueX,valueY] using value,kept⟩
  | true =>
    simp only [Bool.false_eq_true,ite_false,ite_true] at *
    obtain ⟨sum,positiveX,positiveY,_,_,_⟩ := extrOk_nat narrow guard
    have countX : second.amount.toNat < ty.width := by omega
    have countY : first.amount.toNat < ty.width := by omega
    obtain ⟨x,getX,valueX⟩ := original_word_value inv second dfg sourceY countX
    obtain ⟨y,getY,valueY⟩ := original_word_value inv first dfg sourceX countY
    obtain ⟨mi,ρ',output,state,execution,value,kept⟩ :=
      rhs_values hp true refines width sum countY getX getY bounded extent held rhs
    exact ⟨mi,ρ',output,state,execution,
      by simpa only [Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_false,ite_true,Clif.Sem.binary,Clif.Sem.bor,valueX,valueY,BitVec.or_comm] using value,kept⟩
end Backend.Stock.Proof.LogicalExtr
