import FV.Backend.Proof.StockDivImmResolved
import FV.Backend.Proof.StockDivConstantSource
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- A correctly encoded source constant is a real signed/unsigned division
operand after actual alias-resolved materialization, with no semantic-invariance
premise and preservation of every register outside its allocation interval. -/
theorem stock_div_imm_operand_resolved {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {w e : Nat}
    (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (extension : e = 0 ∨ e = 1)
    {i : Int} {u : BitVec w} (encoded : u64 i = u.toNat)
    {st next : State} {tr trace : Array RuleId} {n : Nat} {out : V}
    (run : (applyTerm p (Stock.sem ctx) cfg (n+40) 27 553 (immArgs w e i)).run (st,tr) = .ok (some out,next,trace))
    {aliases : Array (Option Nat)} (bounded : aliases.size ≤ st.base.nextVreg)
    (idem : ∀ k,aliasNum aliases (aliasNum aliases k) = aliasNum aliases k) :
    ∃ ms d,next = {st with base := next.base} ∧ out = .reg (.vreg d .int) ∧
      CodeShape st.base next.base ms d st.base.nextVreg ∧ d < next.base.nextVreg ∧
      ∀ ρ,∃ ρ',PRun F isem (ms.map (·.mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
        DivOpnd (e == 0) u (ρ' d) ∧
        ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k := by
  obtain ⟨ms,d,frame,output,shape,bound,values⟩ := stock_div_imm_resolved hp ctx hc refines width extension run bounded idem
  refine ⟨ms,d,frame,output,shape,bound,?_⟩
  intro ρ
  obtain ⟨ρ',X,execution,value,modulo,extended,kept⟩ := values ρ
  rw [encoded] at modulo extended
  exact ⟨ρ',execution,imm_divOpnd width extension u modulo extended value,kept⟩
def divisorLiteral (masked : Bool) (w : Nat) (i : Int) : Int :=
  if masked then ((u64 i % 2^((CTy.int w).bytes*8) : Nat) : Int) else (u64 i : Int)
/-- Original look-through data and original restricted DFG/getter derive the
constant encoding internally for both general nonzero and safe signed paths. -/
theorem stock_div_original_imm_operand_resolved {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {fr : Clif.Frame} (dfg : DFGCons ctx fr) {y j : Nat} {info : IInfo}
    {ty : Clif.Ty} {u : BitVec ty.width} (get : fr.getAs y ty = .ok u)
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some info)
    {i : Int} (data : info.data = .data 152 35 [.data 151 57 [],.int i])
    (masked : Bool) {cfg : Config} (hc : cfg.checkOverlap = false)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem) {e : Nat}
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64) (extension : e = 0 ∨ e = 1)
    {st next : State} {tr trace : Array RuleId} {n : Nat} {out : V}
    (run : (applyTerm p (Stock.sem ctx) cfg (n+40) 27 553
      (immArgs ty.width e (divisorLiteral masked ty.width i))).run (st,tr) = .ok (some out,next,trace))
    {aliases : Array (Option Nat)} (bounded : aliases.size ≤ st.base.nextVreg)
    (idem : ∀ k,aliasNum aliases (aliasNum aliases k) = aliasNum aliases k) :
    ∃ ms d,next = {st with base := next.base} ∧ out = .reg (.vreg d .int) ∧
      CodeShape st.base next.base ms d st.base.nextVreg ∧ d < next.base.nextVreg ∧
      ∀ ρ,∃ ρ',PRun F isem (ms.map (·.mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
        DivOpnd (e == 0) u (ρ' d) ∧
        ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k := by
  obtain ⟨_,equal⟩ := stock_div_constant_source_value inv dfg get defined found data
  subst i
  have bits : ty.width ≤ 64 := by omega
  have bytes : (CTy.int ty.width).bytes*8 = ty.width := by
    rcases width with h | h | h | h <;> simp [CTy.bytes,CTy.bits,h]
  have encoded : u64 (divisorLiteral masked ty.width (imm64OfIconst ty u)) = u.toNat := by
    cases masked
    · simp only [divisorLiteral,Bool.false_eq_true,ite_false]
      rw [u64_ofNat (u64_lt' _),u64_imm64OfIconst bits]
    · simp only [divisorLiteral,ite_true]
      rw [bytes,u64_imm64OfIconst bits,Nat.mod_eq_of_lt u.isLt]
      exact u64_ofNat (Nat.lt_of_lt_of_le u.isLt (Nat.pow_le_pow_right (by decide) bits))
  exact stock_div_imm_operand_resolved hp ctx hc refines width extension encoded run bounded idem
end Backend.Stock.Proof.ScalarDiv
