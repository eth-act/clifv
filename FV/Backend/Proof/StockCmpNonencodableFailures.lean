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
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
private theorem base_eq (ctx : Ctx) (a b : V) : (Backend.sem ctx).eq a b = (a == b) := rfl
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_bool (ctx : Ctx) (b : Bool) : (Stock.sem ctx).bool b = .bool b := rfl
section Integers
attribute [local semireducible] Isle.Aarch64.program
private theorem one (ctx : Ctx) : (Stock.sem ctx).int 4 1 = .int 1 := rfl
private theorem zero (ctx : Ctx) : (Stock.sem ctx).int 4 0 = .int 0 := rfl
end Integers
private theorem normalized_sub_one (i : Int) : u64 ((u64 i : Int)-1) = u64 (i-1) := by
  unfold u64
  have positive : 0 ≤ i % (2^64 : Int) := Int.emod_nonneg _ (by decide)
  rw [Int.toNat_of_nonneg positive,Int.sub_emod,Int.emod_emod]
  rw [← Int.sub_emod]
theorem stock_cmp_nonencodable_ordinary_failure {p : Program} (hp : Data p) (ctx : Ctx) (cc : Clif.IntCC) (sz : OperandSize)
    {x y j : Nat} {info : IInfo} {i : Int}
    (typed : ctx.valueType? x = some (.int sz.bits))
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int i])
    (nonencodable : Imm12.ofNat? (u64 i) = none) (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+20) rule_inst_5165
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (none,st,tr) := by
  have lookup := ext_value_type ctx st.base typed
  have definition := ext_def_inst_some ctx st.base defined
  have instruction := ext_inst_data_value ctx st.base found
  rw [data] at instruction
  have normalized := ext_u64_from_imm64 ctx st.base i
  have normalizedNonencodable : Imm12.ofNat? (u64 (u64 i)) = none := by
    rw [u64_ofNat (u64_lt' i)]; exact nonencodable
  have absent : externExtract ctx T.imm12_from_u64 (.int (u64 i)) st.base = .fail := by
    rw [ext_imm12_from_u64,normalizedNonencodable]
  cases hp
  cases sz
  all_goals isel_eval [*,rule_inst_5165,sem_extract,sem_unData,sem_eq,stock_matchArgs,
    ext_ty_32_or_64_32,ext_ty_32_or_64_64,OperandSize.bits]
/-- When the predecessor also cannot be encoded, the actual adjusted-immediate
rule fails without changing the full scheduling state or trace. -/
theorem stock_cmp_nonencodable_predecessor_failure {p : Program} (hp : Data p) (ctx : Ctx)
    (signed : Bool) (cc : Clif.IntCC) (sz : OperandSize)
    {x y j : Nat} {info : IInfo} {i : Int}
    (typed : ctx.valueType? x = some (.int sz.bits))
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int i])
    (nonencodable : Imm12.ofNat? (u64 (i-1)) = none) (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+20) (if signed then rule_inst_5160 else rule_inst_5155)
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (none,st,tr) := by
  have lookup := ext_value_type ctx st.base typed
  have definition := ext_def_inst_some ctx st.base defined
  have instruction := ext_inst_data_value ctx st.base found
  rw [data] at instruction
  have normalized := ext_u64_from_imm64 ctx st.base i
  have oddCall : Stock.externCtor ctx T.u64_is_odd [.int (u64 i)] st =
      .ok (.bool ((u64 i : Int) % 2 == 1),st) := by
    rw [stock_ctor_baseOnly ctx T.u64_is_odd _ st (by decide)]
    rfl
  have subtractCall : Stock.externCtor ctx T.u64_wrapping_sub [.int (u64 i),.int 1] st = .ok (.int (u64 (i-1)),st) := by
    rw [stock_ctor_baseOnly ctx T.u64_wrapping_sub _ st (by decide)]
    change (ExtResult.ok (V.int (u64 ((u64 i : Int)-1)),st) : ExtResult (V × State)) = _
    rw [normalized_sub_one]
  have normalizedNonencodable : Imm12.ofNat? (u64 (u64 (i-1))) = none := by
    rw [u64_ofNat (u64_lt' (i-1))]; exact nonencodable
  have absent : externExtract ctx T.imm12_from_u64 (.int (u64 (i-1))) st.base = .fail := by
    rw [ext_imm12_from_u64,normalizedNonencodable]
  cases parity : ((u64 i : Int) % 2 == 1)
  all_goals rw [parity] at oddCall
  all_goals cases hp
  all_goals cases signed <;> cases cc <;> cases sz
  all_goals isel_eval [*,rule_inst_5155,rule_inst_5160,sem_extract,sem_unData,sem_ctor,sem_eq,base_eq,sem_bool,one,
    stock_matchArgs,ext_ty_32_or_64_32,ext_ty_32_or_64_64,OperandSize.bits,ccIdx]
  all_goals rfl
/-- A nonzero original constant cannot match either right-zero comparison rule. -/
theorem stock_cmp_nonencodable_zero_failure {p : Program} (hp : Data p) (ctx : Ctx)
    (nonzeroRule : Bool) (cc : Clif.IntCC) {x y j : Nat} {info : IInfo} {i : Int}
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int i]) (nonzero : u64 i ≠ 0)
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+20) (if nonzeroRule then rule_inst_5172 else rule_inst_5170)
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (none,st,tr) := by
  have definition := ext_def_inst_some ctx st.base defined
  have instruction := ext_inst_data_value ctx st.base found
  rw [data] at instruction
  have normalized := ext_u64_from_imm64 ctx st.base i
  have distinct : (V.int (u64 i) == V.int 0) = false := by
    apply Bool.eq_false_iff.mpr
    intro same
    have equal := V.int.inj (beq_iff_eq.mp same)
    omega
  cases hp
  cases nonzeroRule <;> cases cc
  all_goals isel_eval [*,rule_inst_5170,rule_inst_5172,sem_extract,sem_unData,sem_eq,base_eq,zero,stock_matchArgs,ccIdx]
end Backend.Stock.Proof.ScalarCmp
