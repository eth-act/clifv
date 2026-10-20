import FV.Backend.Proof.StockLogicalExtrMatch

namespace Backend.Stock.Proof.LogicalExtr
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem forward_sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem forward_sem_unData (ctx : Ctx) (t : Nat) (v : V) :
    (Stock.sem ctx).unData t v = (Backend.sem ctx).unData t v := rfl
private theorem forward_sem_bool (ctx : Ctx) (b : Bool) : (Stock.sem ctx).bool b = .bool b := rfl
private theorem forward_sem_int (ctx : Ctx) (ty : TypeId) (i : Int) :
    (Stock.sem ctx).int ty i = .int (normInt ty i) := rfl
private theorem forward_sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
private theorem forward_sem_prim (ctx : Ctx) (name : String) :
    (Stock.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
private theorem forward_sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem pure_ctor (ctx : Ctx) (t : Term) (args : List V) (st : State) (v : V)
    (unrevised : t.id ∉ revisedCtors)
    (base : Backend.externCtor ctx t args st.base = .ok (v,st.base)) :
    Stock.externCtor ctx t args st = .ok (v,st) := by
  rw [stock_ctor_baseOnly ctx t args st unrevised,base]
private theorem stock_u8_into_u64 (ctx : Ctx) (st : State) (a : Int) :
    Stock.externCtor ctx T.u8_into_u64 [.int a] st = .ok (.int a,st) :=
  pure_ctor ctx _ _ st _ (by decide) (ctor_u8_into_u64 ctx st.base a)
private theorem stock_wrapping_add (ctx : Ctx) (st : State) (a b : Int) :
    Stock.externCtor ctx T.u64_wrapping_add [.int a,.int b] st = .ok (.int (u64 (a+b)),st) :=
  pure_ctor ctx _ _ st _ (by decide) (ctor_u64_wrapping_add ctx st.base a b)
private theorem stock_eq (ctx : Ctx) (st : State) (a b : Int) :
    Stock.externCtor ctx T.u64_eq [.int a,.int b] st = .ok (.bool (a == b),st) :=
  pure_ctor ctx _ _ st _ (by decide) (ctor_u64_eq ctx st.base a b)
private theorem stock_gt (ctx : Ctx) (st : State) (a b : Int) :
    Stock.externCtor ctx T.u64_gt [.int a,.int b] st = .ok (.bool (decide (a>b)),st) :=
  pure_ctor ctx _ _ st _ (by decide) (ctor_u64_gt ctx st.base a b)
private theorem stock_bits (ctx : Ctx) (st : State) (w : Nat) :
    Stock.externCtor ctx T.ty_bits [.ty (.int w)] st = .ok (.int w,st) :=
  pure_ctor ctx _ _ st _ (by decide) (ctor_ty_bits ctx st.base w)
variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
variable (st : State) (tr : Array RuleId) (n : Nat)
include hp in
private theorem stock_match_1501 {i a b x c1 y c2 w j1 j2 j3 j4 : Nat} {kx ky : Int}
    {info info1 info2 info3 info4 : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w = 32 ∨ w = 64)
    (hd : info.data = .data 152 2 [.data 151 98 [], .values [a, b]])
    (hj1 : ctx.defInst? a = some j1) (hij1 : ctx.insts[j1]? = some info1)
    (hd1 : info1.data = .data 152 2 [.data 151 103 [], .values [x, c1]])
    (hj2 : ctx.defInst? c1 = some j2) (hij2 : ctx.insts[j2]? = some info2)
    (hd2 : info2.data = .data 152 35 [.data 151 57 [], .int kx])
    (hj3 : ctx.defInst? b = some j3) (hij3 : ctx.insts[j3]? = some info3)
    (hd3 : info3.data = .data 152 2 [.data 151 104 [], .values [y, c2]])
    (hj4 : ctx.defInst? c2 = some j4) (hij4 : ctx.insts[j4]? = some info4)
    (hd4 : info4.data = .data 152 35 [.data 151 57 [], .int ky])
    (hok : ExtrOk w (u64 kx) (u64 ky)) :
    (matchRule p (Stock.sem ctx) cfg (n+20) rule_lower_1501 [.inst i]).run (st, tr) =
      .ok (some (env5 (.ty (.int w)) (.value x) (.int (u64 kx)) (.value y) (.int (u64 ky))), (st, tr)) := by
  obtain ⟨hx8, hy8, hsum, hx0, hy0⟩ := hok
  have hx0' : decide ((u64 kx : Int) > 0) = true := by simpa using hx0
  have hy0' : decide ((u64 ky : Int) > 0) = true := by simpa using hy0
  have h0 := ext_inst_data_value ctx st.base hi
  rw [hd, hty, Option.getD_some] at h0
  have h1 := ext_inst_data_value ctx st.base hij1
  rw [hd1] at h1
  have h2 := ext_inst_data_value ctx st.base hij2
  rw [hd2] at h2
  have h3 := ext_inst_data_value ctx st.base hij3
  rw [hd3] at h3
  have h4 := ext_inst_data_value ctx st.base hij4
  rw [hd4] at h4
  have g1 := ext_def_inst_some ctx st.base hj1
  have g2 := ext_def_inst_some ctx st.base hj2
  have g3 := ext_def_inst_some ctx st.base hj3
  have g4 := ext_def_inst_some ctx st.base hj4
  have h5 := ext_ty_32_or_64 ctx st.base w
  simp only [hw, ↓reduceIte] at h5
  cases hp
  isel_eval [*,forward_sem_bool,forward_sem_int,forward_sem_extract,forward_sem_unData,forward_sem_eq,forward_sem_prim,forward_sem_ctor, rule_lower_1501, ext_value_array_2, ext_u64_from_imm64, ext_u8_from_u64,
    stock_u8_into_u64, stock_wrapping_add, stock_eq, stock_gt, stock_bits,
    beq_bool_true_true, and_self]

set_option maxRecDepth 20000 in

include hp in
private theorem stock_match_1501_none {i a b x c1 y c2 w j1 j2 j3 j4 : Nat} {kx ky : Int}
    {info info1 info2 info3 info4 : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w = 32 ∨ w = 64)
    (hd : info.data = .data 152 2 [.data 151 98 [], .values [a, b]])
    (hj1 : ctx.defInst? a = some j1) (hij1 : ctx.insts[j1]? = some info1)
    (hd1 : info1.data = .data 152 2 [.data 151 103 [], .values [x, c1]])
    (hj2 : ctx.defInst? c1 = some j2) (hij2 : ctx.insts[j2]? = some info2)
    (hd2 : info2.data = .data 152 35 [.data 151 57 [], .int kx])
    (hj3 : ctx.defInst? b = some j3) (hij3 : ctx.insts[j3]? = some info3)
    (hd3 : info3.data = .data 152 2 [.data 151 104 [], .values [y, c2]])
    (hj4 : ctx.defInst? c2 = some j4) (hij4 : ctx.insts[j4]? = some info4)
    (hd4 : info4.data = .data 152 35 [.data 151 57 [], .int ky])
    (hno : ¬ ExtrOk w (u64 kx) (u64 ky)) :
    (matchRule p (Stock.sem ctx) cfg (n+20) rule_lower_1501 [.inst i]).run (st, tr) = .ok (none, (st, tr)) := by
  unfold ExtrOk at hno
  have h0 := ext_inst_data_value ctx st.base hi
  rw [hd, hty, Option.getD_some] at h0
  have h1 := ext_inst_data_value ctx st.base hij1
  rw [hd1] at h1
  have h2 := ext_inst_data_value ctx st.base hij2
  rw [hd2] at h2
  have h3 := ext_inst_data_value ctx st.base hij3
  rw [hd3] at h3
  have h4 := ext_inst_data_value ctx st.base hij4
  rw [hd4] at h4
  have g1 := ext_def_inst_some ctx st.base hj1
  have g2 := ext_def_inst_some ctx st.base hj2
  have g3 := ext_def_inst_some ctx st.base hj3
  have g4 := ext_def_inst_some ctx st.base hj4
  have h5 := ext_ty_32_or_64 ctx st.base w
  simp only [hw, ↓reduceIte] at h5
  cases hp
  by_cases c1 : 0 ≤ (u64 kx : Int) ∧ (u64 kx : Int) < 256
  · by_cases c2 : 0 ≤ (u64 ky : Int) ∧ (u64 ky : Int) < 256
    · by_cases c3 : ((w : Int) == ((u64 ((u64 kx : Int) + (u64 ky : Int)) : Nat) : Int)) = true
      · by_cases c4 : 0 < (u64 kx : Int)
        · have c5 : decide ((u64 ky : Int) > 0) = false := by
            simp only [decide_eq_false_iff_not]
            exact fun h => hno (by first | exact ⟨c1, c2, c3, c4, h⟩ | exact ⟨c2, c1, c3, c4, h⟩)
          have c4' : decide ((u64 kx : Int) > 0) = true := by simpa using c4
          isel_eval [*,forward_sem_bool,forward_sem_int,forward_sem_extract,forward_sem_unData,forward_sem_eq,forward_sem_prim,forward_sem_ctor, rule_lower_1501, ext_value_array_2, ext_u64_from_imm64, ext_u8_from_u64,
    stock_u8_into_u64, stock_wrapping_add, stock_eq, stock_gt, stock_bits,
    beq_bool_true_true, beq_bool_false_true, and_self]
        · have c4' : decide ((u64 kx : Int) > 0) = false := by simpa using c4
          isel_eval [*,forward_sem_bool,forward_sem_int,forward_sem_extract,forward_sem_unData,forward_sem_eq,forward_sem_prim,forward_sem_ctor, rule_lower_1501, ext_value_array_2, ext_u64_from_imm64, ext_u8_from_u64,
    stock_u8_into_u64, stock_wrapping_add, stock_eq, stock_gt, stock_bits,
    beq_bool_true_true, beq_bool_false_true, and_self]
      · have c3' : ((w : Int) == ((u64 ((u64 kx : Int) + (u64 ky : Int)) : Nat) : Int)) = false := by
          simpa using c3
        isel_eval [*,forward_sem_bool,forward_sem_int,forward_sem_extract,forward_sem_unData,forward_sem_eq,forward_sem_prim,forward_sem_ctor, rule_lower_1501, ext_value_array_2, ext_u64_from_imm64, ext_u8_from_u64,
    stock_u8_into_u64, stock_wrapping_add, stock_eq, stock_gt, stock_bits,
    beq_bool_true_true, beq_bool_false_true, and_self]
    · isel_eval [*,forward_sem_bool,forward_sem_int,forward_sem_extract,forward_sem_unData,forward_sem_eq,forward_sem_prim,forward_sem_ctor, rule_lower_1501, ext_value_array_2, ext_u64_from_imm64, ext_u8_from_u64,
    stock_u8_into_u64, stock_wrapping_add, stock_eq, stock_gt, stock_bits,
    beq_bool_true_true, beq_bool_false_true, and_self]
  · isel_eval [*,forward_sem_bool,forward_sem_int,forward_sem_extract,forward_sem_unData,forward_sem_eq,forward_sem_prim,forward_sem_ctor, rule_lower_1501, ext_value_array_2, ext_u64_from_imm64, ext_u8_from_u64,
    stock_u8_into_u64, stock_wrapping_add, stock_eq, stock_gt, stock_bits,
    beq_bool_true_true, beq_bool_false_true, and_self]

set_option maxRecDepth 20000 in

include hp in
private theorem stock_match_1507 {i a b x c1 y c2 w j1 j2 j3 j4 : Nat} {kx ky : Int}
    {info info1 info2 info3 info4 : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w = 32 ∨ w = 64)
    (hd : info.data = .data 152 2 [.data 151 98 [], .values [a, b]])
    (hj1 : ctx.defInst? a = some j1) (hij1 : ctx.insts[j1]? = some info1)
    (hd1 : info1.data = .data 152 2 [.data 151 104 [], .values [y, c1]])
    (hj2 : ctx.defInst? c1 = some j2) (hij2 : ctx.insts[j2]? = some info2)
    (hd2 : info2.data = .data 152 35 [.data 151 57 [], .int ky])
    (hj3 : ctx.defInst? b = some j3) (hij3 : ctx.insts[j3]? = some info3)
    (hd3 : info3.data = .data 152 2 [.data 151 103 [], .values [x, c2]])
    (hj4 : ctx.defInst? c2 = some j4) (hij4 : ctx.insts[j4]? = some info4)
    (hd4 : info4.data = .data 152 35 [.data 151 57 [], .int kx])
    (hok : ExtrOk w (u64 kx) (u64 ky)) :
    (matchRule p (Stock.sem ctx) cfg (n+20) rule_lower_1507 [.inst i]).run (st, tr) =
      .ok (some (env5 (.ty (.int w)) (.value y) (.int (u64 ky)) (.value x) (.int (u64 kx))), (st, tr)) := by
  obtain ⟨hx8, hy8, hsum, hx0, hy0⟩ := hok
  have hx0' : decide ((u64 kx : Int) > 0) = true := by simpa using hx0
  have hy0' : decide ((u64 ky : Int) > 0) = true := by simpa using hy0
  have h0 := ext_inst_data_value ctx st.base hi
  rw [hd, hty, Option.getD_some] at h0
  have h1 := ext_inst_data_value ctx st.base hij1
  rw [hd1] at h1
  have h2 := ext_inst_data_value ctx st.base hij2
  rw [hd2] at h2
  have h3 := ext_inst_data_value ctx st.base hij3
  rw [hd3] at h3
  have h4 := ext_inst_data_value ctx st.base hij4
  rw [hd4] at h4
  have g1 := ext_def_inst_some ctx st.base hj1
  have g2 := ext_def_inst_some ctx st.base hj2
  have g3 := ext_def_inst_some ctx st.base hj3
  have g4 := ext_def_inst_some ctx st.base hj4
  have h5 := ext_ty_32_or_64 ctx st.base w
  simp only [hw, ↓reduceIte] at h5
  cases hp
  isel_eval [*,forward_sem_bool,forward_sem_int,forward_sem_extract,forward_sem_unData,forward_sem_eq,forward_sem_prim,forward_sem_ctor, rule_lower_1507, ext_value_array_2, ext_u64_from_imm64, ext_u8_from_u64,
    stock_u8_into_u64, stock_wrapping_add, stock_eq, stock_gt, stock_bits,
    beq_bool_true_true, beq_bool_false_true, and_self]

set_option maxRecDepth 20000 in

include hp in
private theorem stock_match_1507_none {i a b x c1 y c2 w j1 j2 j3 j4 : Nat} {kx ky : Int}
    {info info1 info2 info3 info4 : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w = 32 ∨ w = 64)
    (hd : info.data = .data 152 2 [.data 151 98 [], .values [a, b]])
    (hj1 : ctx.defInst? a = some j1) (hij1 : ctx.insts[j1]? = some info1)
    (hd1 : info1.data = .data 152 2 [.data 151 104 [], .values [y, c1]])
    (hj2 : ctx.defInst? c1 = some j2) (hij2 : ctx.insts[j2]? = some info2)
    (hd2 : info2.data = .data 152 35 [.data 151 57 [], .int ky])
    (hj3 : ctx.defInst? b = some j3) (hij3 : ctx.insts[j3]? = some info3)
    (hd3 : info3.data = .data 152 2 [.data 151 103 [], .values [x, c2]])
    (hj4 : ctx.defInst? c2 = some j4) (hij4 : ctx.insts[j4]? = some info4)
    (hd4 : info4.data = .data 152 35 [.data 151 57 [], .int kx])
    (hno : ¬ ExtrOk w (u64 kx) (u64 ky)) :
    (matchRule p (Stock.sem ctx) cfg (n+20) rule_lower_1507 [.inst i]).run (st, tr) = .ok (none, (st, tr)) := by
  unfold ExtrOk at hno
  have h0 := ext_inst_data_value ctx st.base hi
  rw [hd, hty, Option.getD_some] at h0
  have h1 := ext_inst_data_value ctx st.base hij1
  rw [hd1] at h1
  have h2 := ext_inst_data_value ctx st.base hij2
  rw [hd2] at h2
  have h3 := ext_inst_data_value ctx st.base hij3
  rw [hd3] at h3
  have h4 := ext_inst_data_value ctx st.base hij4
  rw [hd4] at h4
  have g1 := ext_def_inst_some ctx st.base hj1
  have g2 := ext_def_inst_some ctx st.base hj2
  have g3 := ext_def_inst_some ctx st.base hj3
  have g4 := ext_def_inst_some ctx st.base hj4
  have h5 := ext_ty_32_or_64 ctx st.base w
  simp only [hw, ↓reduceIte] at h5
  cases hp
  by_cases c1 : 0 ≤ (u64 ky : Int) ∧ (u64 ky : Int) < 256
  · by_cases c2 : 0 ≤ (u64 kx : Int) ∧ (u64 kx : Int) < 256
    · by_cases c3 : ((w : Int) == ((u64 ((u64 kx : Int) + (u64 ky : Int)) : Nat) : Int)) = true
      · by_cases c4 : 0 < (u64 kx : Int)
        · have c5 : decide ((u64 ky : Int) > 0) = false := by
            simp only [decide_eq_false_iff_not]
            exact fun h => hno (by first | exact ⟨c1, c2, c3, c4, h⟩ | exact ⟨c2, c1, c3, c4, h⟩)
          have c4' : decide ((u64 kx : Int) > 0) = true := by simpa using c4
          isel_eval [*,forward_sem_bool,forward_sem_int,forward_sem_extract,forward_sem_unData,forward_sem_eq,forward_sem_prim,forward_sem_ctor, rule_lower_1507, ext_value_array_2, ext_u64_from_imm64, ext_u8_from_u64,
    stock_u8_into_u64, stock_wrapping_add, stock_eq, stock_gt, stock_bits,
    beq_bool_true_true, beq_bool_false_true, and_self]
        · have c4' : decide ((u64 kx : Int) > 0) = false := by simpa using c4
          isel_eval [*,forward_sem_bool,forward_sem_int,forward_sem_extract,forward_sem_unData,forward_sem_eq,forward_sem_prim,forward_sem_ctor, rule_lower_1507, ext_value_array_2, ext_u64_from_imm64, ext_u8_from_u64,
    stock_u8_into_u64, stock_wrapping_add, stock_eq, stock_gt, stock_bits,
    beq_bool_true_true, beq_bool_false_true, and_self]
      · have c3' : ((w : Int) == ((u64 ((u64 kx : Int) + (u64 ky : Int)) : Nat) : Int)) = false := by
          simpa using c3
        isel_eval [*,forward_sem_bool,forward_sem_int,forward_sem_extract,forward_sem_unData,forward_sem_eq,forward_sem_prim,forward_sem_ctor, rule_lower_1507, ext_value_array_2, ext_u64_from_imm64, ext_u8_from_u64,
    stock_u8_into_u64, stock_wrapping_add, stock_eq, stock_gt, stock_bits,
    beq_bool_true_true, beq_bool_false_true, and_self]
    · isel_eval [*,forward_sem_bool,forward_sem_int,forward_sem_extract,forward_sem_unData,forward_sem_eq,forward_sem_prim,forward_sem_ctor, rule_lower_1507, ext_value_array_2, ext_u64_from_imm64, ext_u8_from_u64,
    stock_u8_into_u64, stock_wrapping_add, stock_eq, stock_gt, stock_bits,
    beq_bool_true_true, beq_bool_false_true, and_self]
  · isel_eval [*,forward_sem_bool,forward_sem_int,forward_sem_extract,forward_sem_unData,forward_sem_eq,forward_sem_prim,forward_sem_ctor, rule_lower_1507, ext_value_array_2, ext_u64_from_imm64, ext_u8_from_u64,
    stock_u8_into_u64, stock_wrapping_add, stock_eq, stock_gt, stock_bits,
    beq_bool_true_true, beq_bool_false_true, and_self]

include hp in
private theorem match_observed_1501 {i a b x c1 y c2 w j1 j2 j3 j4 : Nat} {kx ky : Int}
    {info info1 info2 info3 info4 : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w = 32 ∨ w = 64)
    (hd : info.data = .data 152 2 [.data 151 98 [], .values [a, b]])
    (hj1 : ctx.defInst? a = some j1) (hij1 : ctx.insts[j1]? = some info1)
    (hd1 : info1.data = .data 152 2 [.data 151 103 [], .values [x, c1]])
    (hj2 : ctx.defInst? c1 = some j2) (hij2 : ctx.insts[j2]? = some info2)
    (hd2 : info2.data = .data 152 35 [.data 151 57 [], .int kx])
    (hj3 : ctx.defInst? b = some j3) (hij3 : ctx.insts[j3]? = some info3)
    (hd3 : info3.data = .data 152 2 [.data 151 104 [], .values [y, c2]])
    (hj4 : ctx.defInst? c2 = some j4) (hij4 : ctx.insts[j4]? = some info4)
    (hd4 : info4.data = .data 152 35 [.data 151 57 [], .int ky])
    {env : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) cfg (n+20) rule_lower_1501 [.inst i]).run (st,tr) =
      .ok (some env,middle)) :
    ExtrOk w (u64 kx) (u64 ky) ∧ env = env5 (.ty (.int w)) (.value x) (.int (u64 kx)) (.value y) (.int (u64 ky)) ∧ middle = (st,tr) := by
  classical
  by_cases guard : ExtrOk w (u64 kx) (u64 ky)
  · have forward := stock_match_1501 (cfg := cfg) hp ctx st tr n hi hty hw hd hj1 hij1 hd1 hj2 hij2 hd2 hj3 hij3 hd3 hj4 hij4 hd4 guard
    rw [forward] at matched
    have same := Except.ok.inj matched
    exact ⟨guard,(Option.some.inj (congrArg Prod.fst same)).symm,(congrArg Prod.snd same).symm⟩
  · have failed := stock_match_1501_none (cfg := cfg) hp ctx st tr n hi hty hw hd hj1 hij1 hd1 hj2 hij2 hd2 hj3 hij3 hd3 hj4 hij4 hd4 guard
    rw [failed] at matched
    cases matched

include hp in
private theorem match_observed_1507 {i a b x c1 y c2 w j1 j2 j3 j4 : Nat} {kx ky : Int}
    {info info1 info2 info3 info4 : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w = 32 ∨ w = 64)
    (hd : info.data = .data 152 2 [.data 151 98 [], .values [a, b]])
    (hj1 : ctx.defInst? a = some j1) (hij1 : ctx.insts[j1]? = some info1)
    (hd1 : info1.data = .data 152 2 [.data 151 104 [], .values [y, c1]])
    (hj2 : ctx.defInst? c1 = some j2) (hij2 : ctx.insts[j2]? = some info2)
    (hd2 : info2.data = .data 152 35 [.data 151 57 [], .int ky])
    (hj3 : ctx.defInst? b = some j3) (hij3 : ctx.insts[j3]? = some info3)
    (hd3 : info3.data = .data 152 2 [.data 151 103 [], .values [x, c2]])
    (hj4 : ctx.defInst? c2 = some j4) (hij4 : ctx.insts[j4]? = some info4)
    (hd4 : info4.data = .data 152 35 [.data 151 57 [], .int kx])
    {env : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) cfg (n+20) rule_lower_1507 [.inst i]).run (st,tr) =
      .ok (some env,middle)) :
    ExtrOk w (u64 kx) (u64 ky) ∧ env = env5 (.ty (.int w)) (.value y) (.int (u64 ky)) (.value x) (.int (u64 kx)) ∧ middle = (st,tr) := by
  classical
  by_cases guard : ExtrOk w (u64 kx) (u64 ky)
  · have forward := stock_match_1507 (cfg := cfg) hp ctx st tr n hi hty hw hd hj1 hij1 hd1 hj2 hij2 hd2 hj3 hij3 hd3 hj4 hij4 hd4 guard
    rw [forward] at matched
    have same := Except.ok.inj matched
    exact ⟨guard,(Option.some.inj (congrArg Prod.fst same)).symm,(congrArg Prod.snd same).symm⟩
  · have failed := stock_match_1507_none (cfg := cfg) hp ctx st tr n hi hty hw hd hj1 hij1 hd1 hj2 hij2 hd2 hj3 hij3 hd3 hj4 hij4 hd4 guard
    rw [failed] at matched
    cases matched

end Backend.Stock.Proof.LogicalExtr

namespace Backend.Stock.Proof.LogicalExtr
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

private theorem matched_width {p : Program} (hp : Data p) {ctx : Ctx} (mirrored : Bool)
    {i w n : Nat} {info : IInfo} (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int w))
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (n+20) (extrRule mirrored) [.inst i]).run (st,tr) =
      .ok (some env,middle)) : w = 32 ∨ w = 64 := by
  obtain ⟨q,shape⟩ : ∃ q,(extrRule mirrored).args = [.term 18 209
      [.term 14 120 [.bind 14 0 (.wildcard 14)],q]] := by
    cases mirrored <;> exact ⟨_,rfl⟩
  obtain ⟨initial,args,_⟩ := matchRule_some_inv matched
  rw [stock_matchArgs,shape] at args
  obtain ⟨e1,root,_⟩ := matchArgs_cons_inv args
  obtain ⟨fields,extracted,patterns⟩ := matchPat_extract_inv hp.t209 term_209_kind rfl root
  have expected := ext_inst_data_value ctx st.base source
  rw [type,Option.getD_some] at expected
  rw [Backend.Proof.sem_extract,expected] at extracted
  cases extracted
  obtain ⟨e2,typeMatch,_⟩ := matchArgs_cons_inv patterns
  obtain ⟨typeFields,typeExtract,_⟩ := matchPat_extract_inv hp.t120 term_120_kind rfl typeMatch
  rw [Backend.Proof.sem_extract,ext_ty_32_or_64] at typeExtract
  split at typeExtract
  · assumption
  · cases typeExtract

/-- Original source facts recovered from a lookthrough match, retained with
all four actual instruction/definition links. -/
structure SourceWord (ctx : Ctx) (value : Nat) (left : Bool) where
  inst : Nat
  word : Nat
  count : Nat
  literalInst : Nat
  info : IInfo
  literal : IInfo
  ty : Clif.Ty
  literalTy : Clif.Ty
  bits : BitVec literalTy.width
  defined : ctx.defInst? value = some inst
  found : ctx.insts[inst]? = some info
  original : info.clif = some (.binary (if left then .ishl else .ushr) ty word count)
  countDefined : ctx.defInst? count = some literalInst
  countFound : ctx.insts[literalInst]? = some literal
  countOriginal : literal.clif = some (.iconst literalTy bits)

def SourceWord.amount {ctx : Ctx} {value : Nat} {left : Bool} (word : SourceWord ctx value left) : Int :=
  u64 (imm64OfIconst word.literalTy word.bits)

private theorem original_word {ctx : Ctx} {value : Nat} {left : Bool}
    (source : WordSource ctx value left) : Nonempty (SourceWord ctx value left) := by
  obtain ⟨j,x,c,k,info,literal,ty,literalTy,bits,defined,found,original,cdef,cfound,coriginal⟩ := source
  exact ⟨⟨j,x,c,k,info,literal,ty,literalTy,bits,defined,found,original,cdef,cfound,coriginal⟩⟩

section Data
attribute [local semireducible] Isle.Aarch64.program
private theorem source_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i a b : Nat} {ty : Clif.Ty} {info : IInfo} (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary .bor ty a b)) :
    info.data = .data 152 2 [.data 151 98 [],.values [a,b]] ∧
      info.resTys.head? = some (.int ty.width) := by
  have accepted := inv.instE i info _ source clif
  have supported : eTy ty = true := by
    simpa [Compile.instE,Compile.binaryE,Compile.tyE,eTy] using accepted
  have raw := inv.data i info _ source clif
  obtain ⟨types,result,typed,_⟩ := inv.resTys i info _ source clif
  simp only [Clif.Inst.resultTypes] at result
  cases result
  refine ⟨?_,by rw [typed]; simp [ofClif_int_width (isInt_of_eTy supported)]⟩
  have expected : instData f (.binary .bor ty a b) = .ok (.data 152 2 [.data 151 98 [],.values [a,b]]) := by
    simp only [instData,binaryOpcode,supported,ite_true]
    rfl
  exact Except.ok.inj (raw.symm.trans expected)

private theorem source_word_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {value : Nat} {left : Bool} (word : SourceWord ctx value left) :
    word.info.data = .data 152 2 [.data 151 (if left then 103 else 104) [],.values [word.word,word.count]] ∧
      word.literal.data = .data 152 35 [.data 151 57 [],.int (imm64OfIconst word.literalTy word.bits)] := by
  have accepted := inv.instE word.inst word.info _ word.found word.original
  have supported : eTy word.ty = true := by
    cases left <;> simpa [Compile.instE,Compile.binaryE,Compile.tyE,eTy] using accepted
  have raw := inv.data word.inst word.info _ word.found word.original
  have expected : instData f (.binary (if left then .ishl else .ushr) word.ty word.word word.count) =
      .ok (.data 152 2 [.data 151 (if left then 103 else 104) [],.values [word.word,word.count]]) := by
    cases left <;> simp only [instData,binaryOpcode,supported,ite_true] <;> rfl
  have literalAccepted := inv.instE word.literalInst word.literal _ word.countFound word.countOriginal
  have literalSupported : eTy word.literalTy = true := by
    simpa [Compile.instE,Compile.tyE,eTy] using literalAccepted
  have literalRaw := inv.data word.literalInst word.literal _ word.countFound word.countOriginal
  have literalExpected : instData f (.iconst word.literalTy word.bits) =
      .ok (.data 152 35 [.data 151 57 [],.int (imm64OfIconst word.literalTy word.bits)]) := by
    simp only [instData,literalSupported,ite_true]
    rfl
  exact ⟨Except.ok.inj (raw.symm.trans expected),Except.ok.inj (literalRaw.symm.trans literalExpected)⟩
end Data
end Backend.Stock.Proof.LogicalExtr


namespace Backend.Stock.Proof.LogicalExtr
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
/-- A real successful source match derives its canonical environment, unchanged
complete state/trace and the original positive shift/sum guards internally.
Both original word/literal definition chains remain available to source DFG. -/
theorem match_receipt {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (mirrored : Bool) {i a b n : Nat} {ty : Clif.Ty} {info : IInfo}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.binary .bor ty a b))
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {middle : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (n+20) (extrRule mirrored) [.inst i]).run (st,tr) =
      .ok (some env,middle)) :
    ∃ (first : SourceWord ctx a (!mirrored)) (second : SourceWord ctx b mirrored),
      (ty.width = 32 ∨ ty.width = 64) ∧
      ExtrOk ty.width (if mirrored then second.amount else first.amount)
        (if mirrored then first.amount else second.amount) ∧
      env = extrEnv mirrored ty.width
        (if mirrored then second.word else first.word) (if mirrored then second.amount else first.amount)
        (if mirrored then first.word else second.word) (if mirrored then first.amount else second.amount) ∧
      middle = (st,tr) := by
  obtain ⟨data,type⟩ := source_data inv source clif
  have width := matched_width hp mirrored source type matched
  obtain ⟨leftSource,rightSource⟩ := matched_sources hp inv mirrored source data matched
  obtain ⟨first⟩ := original_word leftSource
  obtain ⟨second⟩ := original_word rightSource
  obtain ⟨shiftFirst,literalFirst⟩ := source_word_data inv first
  obtain ⟨shiftSecond,literalSecond⟩ := source_word_data inv second
  refine ⟨first,second,width,?_⟩
  cases mirrored with
  | false =>
    exact match_observed_1501 hp ctx st tr n source type width data
      first.defined first.found shiftFirst first.countDefined first.countFound literalFirst
      second.defined second.found shiftSecond second.countDefined second.countFound literalSecond matched
  | true =>
    exact match_observed_1507 hp ctx st tr n source type width data
      first.defined first.found shiftFirst first.countDefined first.countFound literalFirst
      second.defined second.found shiftSecond second.countDefined second.countFound literalSecond matched
end Backend.Stock.Proof.LogicalExtr
