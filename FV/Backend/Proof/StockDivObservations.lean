import FV.Backend.Proof.StockDivRhs
import FV.Backend.Proof.StockDivSourceRequests
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem ext_reg {ctx : Ctx} {x to : Nat} {sg : Bool} {pass : List CTy}
    {s next : State} {out : V} (shape : ScalarShift.MappedExtOut ctx x sg to pass s next out) :
    ∃ r,out = .reg r := by
  obtain ⟨t,typed,safe,r,mapped,form⟩ := shape
  rcases form with ⟨_,equal,_⟩ | ⟨_,_,equal,_⟩
  · exact ⟨r,equal⟩
  · exact ⟨_,equal⟩
/-- A real successful divisor call returns a register on every immediate,
wide guard or narrow extension path, derived internally from execution. -/
theorem stock_div_divisor_reg {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {n y e w : Nat} (enough : 120 ≤ n)
    (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (extension : e = 0 ∨ e = 1)
    {s next : State × Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) cfg n 27 698 [.value y,.data 125 e [],.ty (.int w)] s out next) :
    ∃ r,out = .reg r := by
  have observed := stock_div_divisor_observed_with_fuel hp ctx hc enough width extension run
  rcases observed with ⟨j,info,i,defined,found,data,nonzero,fuel,trace,bound,materialized⟩ | guarded | widened
  · obtain ⟨k,equal⟩ : ∃ k,fuel+1 = k+40 := ⟨fuel-39,by omega⟩
    unfold ApplyInternal at materialized
    rw [equal] at materialized
    have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
    obtain ⟨frame,ms,d,output,shape,value⟩ := stock_div_imm_values hp ctx hc self width extension materialized
    exact ⟨.vreg d .int,output⟩
  · obtain ⟨_,_,r,_,output,_⟩ := guarded
    exact ⟨r,output⟩
  · obtain ⟨_,r,_,_,output,_⟩ := widened
    exact ⟨r,output⟩
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_prim (ctx : Ctx) : (Stock.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl
private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl
def WideUdivReceipt (p : Program) (ctx : Ctx) (n x y : Nat) (st next : State)
    (tr : Array RuleId) (out : V) : Prop :=
  DemandAllowed ctx st x ∧ ∃ rx ry middle middleTrace,
      ctx.valueReg? x = some rx ∧
      (applyTerm p (Stock.sem ctx) {} (n+43) 27 698 [.value y,.data 125 1 [],.ty (.int 64)]).run
        (st.mark x,tr) = .ok (some (.reg ry),middle,middleTrace) ∧
      out = .regsVec [[(middle.base.fresh .int).1]] ∧ next = quotientState false 64 middle rx ry
/-- The actual wide unsigned RHS supplies its guarded mapping, divisor call,
result and complete state without caller helper certificates. -/
theorem stock_div_udiv_wide_observed {p : Program} (hp : Data p) (ctx : Ctx)
    {n x y : Nat} (enough : 120 ≤ n) {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+50) rule_lower_1116.rhs (baseWideEnv .udiv x y)).run
      (st,tr) = .ok (some out,next,trace)) :
    WideUdivReceipt p ctx n x y st next tr out := by
  have hp' := hp
  have original := run
  cases hp
  isel_inv [*,baseWideEnv,baseWideRule,rule_lower_1116,sem_ctor,sem_prim,sem_mkData] at run
  all_goals simp only [stock_put_in_reg_iff] at *
  all_goals isel_destruct <;> subst_vars
  obtain ⟨called⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) {} _ 27 698
    [.value y,.data 125 1 [],.ty (.int 64)] (st.mark x,tr) _ _) := ⟨by assumption⟩
  obtain ⟨ry,output⟩ := stock_div_divisor_reg hp' ctx (cfg := {}) rfl (run := called) (by omega) (by decide) (by decide)
  rw [output] at called
  unfold ApplyInternal at called
  obtain ⟨mapped⟩ : Nonempty (ctx.valueReg? x = some _) := ⟨by assumption⟩
  have safe : DemandAllowed ctx st x := by assumption
  obtain ⟨expectedTrace,expected⟩ := stock_div_udiv_wide_from_parts hp' ctx mapped st safe tr n called
  rw [original] at expected
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at expected
  unfold WideUdivReceipt
  exact ⟨safe,_,ry,_,_,mapped,called,expected.1,expected.2.1⟩
private theorem sem_prim32 (ctx : Ctx) : (Stock.sem ctx).prim 14 "I32" = some (.ty (.int 32)) := rfl
def NarrowUdivReceipt (p : Program) (ctx : Ctx) (n x y w : Nat) (st next : State)
    (tr : Array RuleId) (out : V) : Prop :=
  ∃ rx ry prepared preparedTrace middle middleTrace,
    ScalarShift.MappedExtOut ctx x false 32 [.int 32,.int 64] st prepared (.reg rx) ∧
    (applyTerm p (Stock.sem ctx) {} (n+44) 27 556 [.value x]).run (st,tr) =
      .ok (some (.reg rx),prepared,preparedTrace) ∧
    (applyTerm p (Stock.sem ctx) {} (n+43) 27 698 [.value y,.data 125 1 [],.ty (.int w)]).run
      (prepared,preparedTrace) = .ok (some (.reg ry),middle,middleTrace) ∧
    out = .regsVec [[(middle.base.fresh .int).1]] ∧ next = quotientState false 32 middle rx ry
/-- Actual narrow unsigned selection's RHS internally derives its original
widening guard and complete divisor/output states. -/
theorem stock_div_udiv_narrow_observed {p : Program} (hp : Data p) (ctx : Ctx)
    {n x y w : Nat} (enough : 120 ≤ n) (width : w = 8 ∨ w = 16 ∨ w = 32)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+50) rule_lower_1119.rhs (baseNarrowEnv .udiv w x y)).run
      (st,tr) = .ok (some out,next,trace)) :
    NarrowUdivReceipt p ctx n x y w st next tr out := by
  have hp' := hp
  have original := run
  cases hp
  isel_inv [*,baseNarrowEnv,baseNarrowRule,rule_lower_1119,sem_ctor,sem_prim32,sem_mkData] at run
  all_goals isel_destruct <;> subst_vars
  obtain ⟨first⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) {} _ 27 556 [.value x] (st,tr) _ _) := ⟨by assumption⟩
  have extended := ScalarShift.stock_zext32_out hp' (ctx := ctx) (cfg := {}) rfl (h := first) (by omega)
  obtain ⟨rx,firstOutput⟩ := ext_reg extended
  rw [firstOutput] at first extended
  obtain ⟨called⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) {} _ 27 698
    [.value y,.data 125 1 [],.ty (.int w)] _ _ _) := ⟨by assumption⟩
  obtain ⟨ry,output⟩ := stock_div_divisor_reg hp' ctx (cfg := {}) rfl (run := called) (by omega)
    (by omega) (by decide)
  rw [output] at called
  unfold ApplyInternal at first called
  obtain ⟨expectedTrace,expected⟩ := stock_div_udiv_narrow_from_parts hp' ctx st tr n first called
  rw [original] at expected
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at expected
  unfold NarrowUdivReceipt
  exact ⟨rx,ry,_,_,_,_,extended,first,called,expected.1,expected.2.1⟩
def WideRemReceipt (p : Program) (ctx : Ctx) (signed : Bool) (n x y : Nat) (st next : State)
    (tr : Array RuleId) (out : V) : Prop :=
  ∃ rx ry prepared preparedTrace middle middleTrace,
    ScalarShift.MappedExtOut ctx x signed 64 [.int 64] st prepared (.reg rx) ∧
    (applyTerm p (Stock.sem ctx) {} (n+97) 27 (if signed then 557 else 558) [.value x]).run (st,tr) =
      .ok (some (.reg rx),prepared,preparedTrace) ∧
    (applyTerm p (Stock.sem ctx) {} (n+96) 27 698
      [.value y,.data 125 (if signed then 0 else 1) [],.ty (.int 64)]).run
      (prepared,preparedTrace) = .ok (some (.reg ry),middle,middleTrace) ∧
    out = .regsVec [[((quotientState signed 64 middle rx ry).base.fresh .int).1]] ∧
    next = remainderState signed 64 middle rx ry
/-- Both actual wide remainder RHSs derive original guarded source preparation,
divisor execution and divide/multiply-subtract output internally. -/
theorem stock_div_rem_wide_observed {p : Program} (hp : Data p) (ctx : Ctx) (signed : Bool)
    {n x y : Nat} (enough : 120 ≤ n) {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+100) (baseWideRule (if signed then .srem else .urem)).rhs
      (baseWideEnv (if signed then .srem else .urem) x y)).run (st,tr) = .ok (some out,next,trace)) :
    WideRemReceipt p ctx signed n x y st next tr out := by
  have hp' := hp
  have original := run
  cases hp
  cases signed
  · isel_inv [*,baseWideEnv,baseWideRule,rule_lower_1190,sem_ctor,sem_prim,sem_mkData] at run
    all_goals isel_destruct <;> subst_vars
    obtain ⟨first⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) {} _ 27 558 [.value x] (st,tr) _ _) := ⟨by assumption⟩
    have extended := ScalarShift.stock_zext64_out hp' (ctx := ctx) (cfg := {}) rfl (h := first) (by omega)
    obtain ⟨rx,firstOutput⟩ := ext_reg extended
    rw [firstOutput] at first extended
    obtain ⟨called⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) {} _ 27 698
      [.value y,.data 125 1 [],.ty (.int 64)] _ _ _) := ⟨by assumption⟩
    obtain ⟨ry,output⟩ := stock_div_divisor_reg hp' ctx (cfg := {}) rfl (run := called)
      (by omega) (by decide) (by decide)
    rw [output] at called
    unfold ApplyInternal at first called
    obtain ⟨expectedTrace,expected⟩ := stock_div_rem_wide_from_parts hp' ctx false st tr n first called
    simp only [Bool.false_eq_true,ite_false,ite_true] at expected
    rw [original] at expected
    simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at expected
    unfold WideRemReceipt
    exact ⟨rx,ry,_,_,_,_,extended,first,called,expected.1,expected.2.1⟩
  · isel_inv [*,baseWideEnv,baseWideRule,rule_lower_1204,sem_ctor,sem_prim,sem_mkData] at run
    all_goals isel_destruct <;> subst_vars
    obtain ⟨first⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) {} _ 27 557 [.value x] (st,tr) _ _) := ⟨by assumption⟩
    have extended := ScalarShift.stock_sext64_out hp' (ctx := ctx) (cfg := {}) rfl (h := first) (by omega)
    obtain ⟨rx,firstOutput⟩ := ext_reg extended
    rw [firstOutput] at first extended
    obtain ⟨called⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) {} _ 27 698
      [.value y,.data 125 0 [],.ty (.int 64)] _ _ _) := ⟨by assumption⟩
    obtain ⟨ry,output⟩ := stock_div_divisor_reg hp' ctx (cfg := {}) rfl (run := called)
      (by omega) (by decide) (by decide)
    rw [output] at called
    unfold ApplyInternal at first called
    obtain ⟨expectedTrace,expected⟩ := stock_div_rem_wide_from_parts hp' ctx true st tr n first called
    simp only [Bool.false_eq_true,ite_false,ite_true] at expected
    rw [original] at expected
    simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at expected
    unfold WideRemReceipt
    exact ⟨rx,ry,_,_,_,_,extended,first,called,expected.1,expected.2.1⟩
def NarrowRemReceipt (p : Program) (ctx : Ctx) (signed : Bool) (n x y w : Nat) (st next : State)
    (tr : Array RuleId) (out : V) : Prop :=
  ∃ rx ry prepared preparedTrace middle middleTrace,
    ScalarShift.MappedExtOut ctx x signed 32 [.int 32,.int 64] st prepared (.reg rx) ∧
    (applyTerm p (Stock.sem ctx) {} (n+97) 27 (if signed then 555 else 556) [.value x]).run (st,tr) =
      .ok (some (.reg rx),prepared,preparedTrace) ∧
    (applyTerm p (Stock.sem ctx) {} (n+96) 27 698
      [.value y,.data 125 (if signed then 0 else 1) [],.ty (.int w)]).run
      (prepared,preparedTrace) = .ok (some (.reg ry),middle,middleTrace) ∧
    out = .regsVec [[((quotientState signed w middle rx ry).base.fresh .int).1]] ∧
    next = remainderState signed w middle rx ry
/-- Both actual wide remainder RHSs derive original guarded source preparation,
divisor execution and divide/multiply-subtract output internally. -/
theorem stock_div_rem_narrow_observed {p : Program} (hp : Data p) (ctx : Ctx) (signed : Bool)
    {n x y w : Nat} (enough : 120 ≤ n) (width : w = 8 ∨ w = 16 ∨ w = 32) {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+100) (baseNarrowRule (if signed then .srem else .urem)).rhs
      (baseNarrowEnv (if signed then .srem else .urem) w x y)).run (st,tr) = .ok (some out,next,trace)) :
    NarrowRemReceipt p ctx signed n x y w st next tr out := by
  have hp' := hp
  have original := run
  cases hp
  cases signed
  · isel_inv [*,baseNarrowEnv,baseNarrowRule,rule_lower_1197,sem_ctor,sem_prim,sem_mkData] at run
    all_goals isel_destruct <;> subst_vars
    obtain ⟨first⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) {} _ 27 556 [.value x] (st,tr) _ _) := ⟨by assumption⟩
    have extended := ScalarShift.stock_zext32_out hp' (ctx := ctx) (cfg := {}) rfl (h := first) (by omega)
    obtain ⟨rx,firstOutput⟩ := ext_reg extended
    rw [firstOutput] at first extended
    obtain ⟨called⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) {} _ 27 698
      [.value y,.data 125 1 [],.ty (.int w)] _ _ _) := ⟨by assumption⟩
    obtain ⟨ry,output⟩ := stock_div_divisor_reg hp' ctx (cfg := {}) rfl (run := called)
      (by omega) (by omega) (by decide)
    rw [output] at called
    unfold ApplyInternal at first called
    obtain ⟨expectedTrace,expected⟩ := stock_div_rem_narrow_from_parts hp' ctx false (by omega) st tr n first called
    simp only [Bool.false_eq_true,ite_false,ite_true] at expected
    rw [original] at expected
    simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at expected
    unfold NarrowRemReceipt
    exact ⟨rx,ry,_,_,_,_,extended,first,called,expected.1,expected.2.1⟩
  · isel_inv [*,baseNarrowEnv,baseNarrowRule,rule_lower_1211,sem_ctor,sem_prim,sem_mkData] at run
    all_goals isel_destruct <;> subst_vars
    obtain ⟨first⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) {} _ 27 555 [.value x] (st,tr) _ _) := ⟨by assumption⟩
    have extended := ScalarShift.stock_sext32_out hp' (ctx := ctx) (cfg := {}) rfl (h := first) (by omega)
    obtain ⟨rx,firstOutput⟩ := ext_reg extended
    rw [firstOutput] at first extended
    obtain ⟨called⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) {} _ 27 698
      [.value y,.data 125 0 [],.ty (.int w)] _ _ _) := ⟨by assumption⟩
    obtain ⟨ry,output⟩ := stock_div_divisor_reg hp' ctx (cfg := {}) rfl (run := called)
      (by omega) (by omega) (by decide)
    rw [output] at called
    unfold ApplyInternal at first called
    obtain ⟨expectedTrace,expected⟩ := stock_div_rem_narrow_from_parts hp' ctx true (by omega) st tr n first called
    simp only [Bool.false_eq_true,ite_false,ite_true] at expected
    rw [original] at expected
    simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at expected
    unfold NarrowRemReceipt
    exact ⟨rx,ry,_,_,_,_,extended,first,called,expected.1,expected.2.1⟩
end Backend.Stock.Proof.ScalarDiv
