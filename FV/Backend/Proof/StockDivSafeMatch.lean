module

public import FV.Backend.Proof.StockDivRhs
public import FV.Backend.Proof.IselCmpDivRem

@[expose] public section

namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_extract (ctx : Ctx) (t : Term) (vs : V) (st : State) :
    (Stock.sem ctx).extract t vs st = Backend.externExtract ctx t vs st.base := rfl
private theorem sem_unData (ctx : Ctx) (t : Nat) (v : V) :
    (Stock.sem ctx).unData t v = (Backend.sem ctx).unData t v := rfl
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
private theorem sem_prim (ctx : Ctx) : (Stock.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
/-- The higher-priority safe signed root matches the real looked-through
constant and tests its original zero/minus-one exclusions. -/
theorem stock_div_safe_wide_match {p : Program} (hp : Data p) (ctx : Ctx)
    {id x y j : Nat} {info constant : IInfo} {i : Int}
    (source : ctx.insts[id]? = some info) (type : info.resTys.head? = some (.int 64))
    (data : info.data = .data 152 2 [.data 151 83 [],.values [x,y]])
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some constant)
    (literal : constant.data = .data 152 35 [.data 151 57 [],.int i])
    (safe : u64 i % 2^64 ≠ 0 ∧ u64 i % 2^64 ≠ 2^64-1)
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+10) rule_lower_1163 [.inst id]).run (st,tr) =
      .ok (some (safeWideEnv x i (u64 i % 2^64)),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  have definition := ext_def_inst_some ctx st.base defined
  have constantData := ext_inst_data_value ctx st.base found
  rw [literal] at constantData
  have safeCall : ∀ q,Stock.externCtor ctx T.safe_divisor_from_imm64 [.ty (.int 64),.int i] q =
      .ok (.int (u64 i % 2^64),q) := by
    intro q
    rw [stock_ctor_baseOnly ctx T.safe_divisor_from_imm64 _ q (by decide)]
    have h := (ctor_safe_divisor_iff ctx q.base q.base (.int 64) i (.int (u64 i % 2^64))).mpr
      ⟨by simpa [CTy.bytes,CTy.bits] using safe,rfl,rfl⟩
    rw [h]
  cases hp
  isel_eval [*,rule_lower_1163,safeWideEnv,sem_extract,sem_unData,sem_eq,sem_prim,sem_ctor,ext_value_array_2]
theorem stock_div_safe_narrow_match {p : Program} (hp : Data p) (ctx : Ctx)
    {id x y j w : Nat} (width : w ≤ 32) {info constant : IInfo} {i : Int}
    (source : ctx.insts[id]? = some info) (type : info.resTys.head? = some (.int w))
    (data : info.data = .data 152 2 [.data 151 83 [],.values [x,y]])
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some constant)
    (literal : constant.data = .data 152 35 [.data 151 57 [],.int i])
    (safe : u64 i % 2^((CTy.int w).bytes*8) ≠ 0 ∧ u64 i % 2^((CTy.int w).bytes*8) ≠ 2^((CTy.int w).bytes*8)-1)
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+10) rule_lower_1167 [.inst id]).run (st,tr) =
      .ok (some (safeNarrowEnv w x i (u64 i % 2^((CTy.int w).bytes*8))),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  have definition := ext_def_inst_some ctx st.base defined
  have constantData := ext_inst_data_value ctx st.base found
  rw [literal] at constantData
  have safeCall : ∀ q,Stock.externCtor ctx T.safe_divisor_from_imm64 [.ty (.int w),.int i] q =
      .ok (.int (u64 i % 2^((CTy.int w).bytes*8)),q) := by
    intro q
    rw [stock_ctor_baseOnly ctx T.safe_divisor_from_imm64 _ q (by decide)]
    have h := (ctor_safe_divisor_iff ctx q.base q.base (.int w) i (.int (u64 i % 2^((CTy.int w).bytes*8)))).mpr
      ⟨safe,rfl,rfl⟩
    rw [h]
  have fits := ext_fits_in_32_ty_fa ctx st.base (.int w)
  simp only [CTy.bits,width,ite_true] at fits
  cases hp
  isel_eval [*,rule_lower_1167,safeNarrowEnv,sem_extract,sem_unData,sem_eq,sem_prim,sem_ctor,ext_value_array_2]
end Backend.Stock.Proof.ScalarDiv
