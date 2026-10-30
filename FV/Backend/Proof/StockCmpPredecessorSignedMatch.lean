import FV.Backend.Proof.IselCmpEmit
import FV.Backend.Proof.IselTermsImm
import FV.Backend.Proof.StockProjection
import FV.Backend.Proof.IselCtlTry
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (ty : Nat) (v : V) :
    (Stock.sem ctx).unData ty v = (Backend.sem ctx).unData ty v := rfl
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
section Integers
attribute [local semireducible] Isle.Aarch64.program
private theorem one (ctx : Ctx) : (Stock.sem ctx).int 4 1 = .int 1 := rfl
private theorem yes (ctx : Ctx) : (Stock.sem ctx).bool true = .bool true := rfl
end Integers
private theorem normalized_sub_one (i : Int) : u64 ((u64 i : Int)-1) = u64 (i-1) := by
  unfold u64
  have positive : 0 ≤ i % (2^64 : Int) := Int.emod_nonneg _ (by decide)
  rw [Int.toNat_of_nonneg positive,Int.sub_emod,Int.emod_emod]
  rw [← Int.sub_emod]
/-- The actual adjusted-immediate rule matches its original typed operand and
odd defining constant, retaining the exact four-field environment and full state. -/
theorem stock_cmp_predecessor_signed_match {p : Program} (hp : Data p) (ctx : Ctx) (sz : OperandSize)
    {x y j : Nat} {info : IInfo} {i : Int} {imm : Imm12}
    (typed : ctx.valueType? x = some (.int sz.bits))
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int i])
    (odd : u64 i % 2 = 1) (encoded : Imm12.ofNat? (u64 (i-1)) = some imm)
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+20) rule_inst_5160
      [.data 145 (ccIdx .sge) [],.value x,.value y]).run (st,tr) =
      .ok (some #[some (.ty (.int sz.bits)),some (.value x),some (.int (u64 i)),some (.op (.imm12 imm))],st,tr) := by
  have lookup := ext_value_type ctx st.base typed
  have definition := ext_def_inst_some ctx st.base defined
  have instruction := ext_inst_data_value ctx st.base found
  rw [data] at instruction
  have normalized := ext_u64_from_imm64 ctx st.base i
  have oddInt : (u64 i : Int) % 2 = 1 := by omega
  have oddCall : Stock.externCtor ctx T.u64_is_odd [.int (u64 i)] st = .ok (.bool true,st) := by
    rw [stock_ctor_baseOnly ctx T.u64_is_odd _ st (by decide)]
    have call := (ctor_u64_is_odd_iff (ctx := ctx) (st := st.base) (u64 i) (.bool true) st.base).mpr
      ⟨by simp [oddInt],rfl⟩
    exact congrArg (fun r => match r with
      | .ok (v,base) => ExtResult.ok (v,{st with base})
      | .fail => .fail | .unmodeled e => .unmodeled e) call
  have subtractCall : Stock.externCtor ctx T.u64_wrapping_sub [.int (u64 i),.int 1] st = .ok (.int (u64 (i-1)),st) := by
    rw [stock_ctor_baseOnly ctx T.u64_wrapping_sub _ st (by decide)]
    change (ExtResult.ok (V.int (u64 ((u64 i : Int)-1)),st) : ExtResult (V × State)) = _
    rw [normalized_sub_one]
  have normalizedEncoded : Imm12.ofNat? (u64 (u64 (i-1))) = some imm := by
    rw [u64_ofNat (u64_lt' (i-1))]; exact encoded
  have literal := (ext_imm12_from_u64_iff (ctx := ctx) (st := st.base) (u64 (i-1)) [.op (.imm12 imm)]).mpr
    ⟨imm,normalizedEncoded,rfl⟩
  cases hp
  cases sz
  all_goals isel_eval [*,rule_inst_5160,sem_extract,sem_unData,sem_ctor,sem_eq,one,yes,
    ext_ty_32_or_64_32,ext_ty_32_or_64_64,OperandSize.bits,ccIdx,stock_matchArgs]
  all_goals apply congrArg (fun env : Isle.Interp.Env V => Except.ok (some env,st,tr))
  all_goals apply Array.toList_inj.mp
  all_goals simp [Array.toList_setIfInBounds,List.set,List.replicate]
end Backend.Stock.Proof.ScalarCmp
