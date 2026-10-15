import FV.Backend.Proof.StockDivObservations
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
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_prim (ctx : Ctx) : (Stock.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl
private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl
/-- Successful minimum checks derive their actual check register and full state. -/
theorem stock_div_intmin_observed {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {n w : Nat} (enough : 59 ≤ n)
    (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) {st next : State} {tr trace : Array RuleId} {out : V} {r : Reg}
    (run : ApplyInternal p (Stock.sem ctx) cfg n 27 562 [.ty (.int w),.reg r] (st,tr) out (next,trace)) :
    out = .reg (if w ≤ 16 then (st.base.fresh .int).1 else r) ∧
      next = (if w ≤ 16 then {st with base := ((st.base.fresh .int).2.emit
        (.aluRRImmShift .lsl .size32 (st.base.fresh .int).1 r (32-w)))} else st) := by
  obtain ⟨k,fuelEq⟩ : ∃ k,n+1=k+60 := ⟨n-59,by omega⟩
  obtain ⟨actualTrace,forward⟩ := stock_div_intmin_helper hp ctx hc width st tr k r
  unfold ApplyInternal at run
  rw [fuelEq,forward] at run
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at run
  exact ⟨run.1.symm,run.2.1.symm⟩
/-- Successful overflow guard emission returns its original dividend and
preserves every scheduling field, deriving exact flag/trap code from execution. -/
theorem stock_div_overflow_observed {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {n w : Nat} (enough : 59 ≤ n)
    (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) {st next : State} {tr trace : Array RuleId} {out : V}
    {check rx ry : Reg}
    (run : ApplyInternal p (Stock.sem ctx) cfg n 27 561 [.ty (.int w),.reg check,.reg rx,.reg ry]
      (st,tr) out (next,trace)) : out = .reg rx ∧ next = {st with base := overflowBase st.base w check ry} := by
  obtain ⟨k,fuelEq⟩ : ∃ k,n+1=k+60 := ⟨n-59,by omega⟩
  obtain ⟨actualTrace,forward⟩ := stock_div_overflow_guard_helper hp ctx hc width st tr k check rx ry
  unfold ApplyInternal at run
  rw [fuelEq,forward] at run
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at run
  exact ⟨run.1.symm,run.2.1.symm⟩
def GeneralSdivReceipt (p : Program) (ctx : Ctx) (wide : Bool) (n x y w : Nat)
    (st next : State) (tr : Array RuleId) (out : V) : Prop :=
  ∃ rx ry check s1 s2 s3 s4 t1 t2 t3 t4,
    ScalarShift.MappedExtOut ctx x true (if wide then 64 else 32)
      (if wide then [.int 64] else [.int 32,.int 64]) st s1 (.reg rx) ∧
    (applyTerm p (Stock.sem ctx) {} (n+97) 27 (if wide then 557 else 555) [.value x]).run (st,tr) =
      .ok (some (.reg rx),s1,t1) ∧
    (applyTerm p (Stock.sem ctx) {} (n+96) 27 698 [.value y,.data 125 0 [],.ty (.int w)]).run (s1,t1) =
      .ok (some (.reg ry),s2,t2) ∧
    (applyTerm p (Stock.sem ctx) {} (n+95) 27 562 [.ty (.int w),.reg rx]).run (s2,t2) =
      .ok (some (.reg check),s3,t3) ∧
    (applyTerm p (Stock.sem ctx) {} (n+94) 27 561 [.ty (.int w),.reg check,.reg rx,.reg ry]).run (s3,t3) =
      .ok (some (.reg rx),s4,t4) ∧
    out = .regsVec [[(s4.base.fresh .int).1]] ∧ next = quotientState true w s4 rx ry
/-- The actual general signed RHS internally derives every guarded source,
minimum/overflow check, output and full-state receipt. -/
theorem stock_div_sdiv_wide_observed {p : Program} (hp : Data p) (ctx : Ctx)
    {n x y  : Nat} (enough : 120 ≤ n) 
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+100) rule_lower_1145.rhs (baseWideEnv .sdiv x y)).run
      (st,tr) = .ok (some out,next,trace)) : GeneralSdivReceipt p ctx true n x y 64 st next tr out := by
  have hp' := hp
  have original := run
  cases hp
  isel_inv [*,baseWideEnv,baseWideRule,baseNarrowEnv,baseNarrowRule,rule_lower_1145,sem_ctor,sem_prim,sem_mkData] at run
  all_goals isel_destruct <;> subst_vars
  obtain ⟨first⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) {} _ 27 557 [.value x] (st,tr) _ _) := ⟨by assumption⟩
  have extended := ScalarShift.stock_sext64_out hp' (ctx := ctx) (cfg := {}) rfl (h := first) (by omega)
  obtain ⟨rx,firstOutput⟩ := ext_reg extended
  subst_vars
  obtain ⟨called⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) {} _ 27 698
    [.value y,.data 125 0 [],.ty (.int 64)] _ _ _) := ⟨by assumption⟩
  obtain ⟨ry,output⟩ := stock_div_divisor_reg hp' ctx (cfg := {}) rfl (run := called)
    (by omega) (by decide) (by decide)
  subst_vars
  obtain ⟨minimum⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) {} _ 27 562
    [.ty (.int 64),.reg rx] _ _ _) := ⟨by assumption⟩
  have checked := stock_div_intmin_observed hp' ctx (cfg := {}) rfl (run := minimum) (by omega) (by decide)
  have checkedOut := checked.1
  subst_vars
  obtain ⟨overflow⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) {} _ 27 561
    [.ty (.int 64),.reg _,.reg rx,.reg ry] _ _ _) := ⟨by assumption⟩
  have guarded := stock_div_overflow_observed hp' ctx (cfg := {}) rfl (run := overflow) (by omega) (by decide)
  have guardedOut := guarded.1
  subst_vars
  unfold ApplyInternal at first called minimum overflow
  obtain ⟨expectedTrace,expected⟩ := stock_div_sdiv_wide_from_parts hp' ctx  st tr n first called minimum overflow
  rw [original] at expected
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at expected
  unfold GeneralSdivReceipt
  exact ⟨rx,ry,_,_,_,_,_,_,_,_,_,extended,first,called,minimum,overflow,expected.1,expected.2.1⟩
/-- The actual general signed RHS internally derives every guarded source,
minimum/overflow check, output and full-state receipt. -/
theorem stock_div_sdiv_narrow_observed {p : Program} (hp : Data p) (ctx : Ctx)
    {n x y w : Nat} (enough : 120 ≤ n) (width : w = 8 ∨ w = 16 ∨ w = 32)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+100) rule_lower_1153.rhs (baseNarrowEnv .sdiv w x y)).run
      (st,tr) = .ok (some out,next,trace)) : GeneralSdivReceipt p ctx false n x y w st next tr out := by
  have hp' := hp
  have original := run
  cases hp
  isel_inv [*,baseWideEnv,baseWideRule,baseNarrowEnv,baseNarrowRule,rule_lower_1153,sem_ctor,sem_prim,sem_mkData] at run
  all_goals isel_destruct <;> subst_vars
  obtain ⟨first⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) {} _ 27 555 [.value x] (st,tr) _ _) := ⟨by assumption⟩
  have extended := ScalarShift.stock_sext32_out hp' (ctx := ctx) (cfg := {}) rfl (h := first) (by omega)
  obtain ⟨rx,firstOutput⟩ := ext_reg extended
  subst_vars
  obtain ⟨called⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) {} _ 27 698
    [.value y,.data 125 0 [],.ty (.int w)] _ _ _) := ⟨by assumption⟩
  obtain ⟨ry,output⟩ := stock_div_divisor_reg hp' ctx (cfg := {}) rfl (run := called)
    (by omega) (by omega) (by decide)
  subst_vars
  obtain ⟨minimum⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) {} _ 27 562
    [.ty (.int w),.reg rx] _ _ _) := ⟨by assumption⟩
  have checked := stock_div_intmin_observed hp' ctx (cfg := {}) rfl (run := minimum) (by omega) (by omega)
  have checkedOut := checked.1
  subst_vars
  obtain ⟨overflow⟩ : Nonempty (ApplyInternal p (Stock.sem ctx) {} _ 27 561
    [.ty (.int w),.reg _,.reg rx,.reg ry] _ _ _) := ⟨by assumption⟩
  have guarded := stock_div_overflow_observed hp' ctx (cfg := {}) rfl (run := overflow) (by omega) (by omega)
  have guardedOut := guarded.1
  subst_vars
  unfold ApplyInternal at first called minimum overflow
  obtain ⟨expectedTrace,expected⟩ := stock_div_sdiv_narrow_from_parts hp' ctx (by omega) st tr n first called minimum overflow
  rw [original] at expected
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at expected
  unfold GeneralSdivReceipt
  exact ⟨rx,ry,_,_,_,_,_,_,_,_,_,extended,first,called,minimum,overflow,expected.1,expected.2.1⟩
end Backend.Stock.Proof.ScalarDiv
