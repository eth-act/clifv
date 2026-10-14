import FV.Backend.Proof.StockDivRootMatch
import FV.Backend.Proof.StockDivHelpers
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_mkData (ctx : Ctx) (t k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData t k vs = .data t k vs := rfl
private theorem output_run {p : Program} (hp : Data p) (ctx : Ctx) (st : State)
    (tr : Array RuleId) (n : Nat) (r : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n+10) 25 172 [.reg r]).run (st,tr) =
      .ok (some (.regsVec [[r]]),st,tr.push rule_prelude_lower_105.id) := by
  have value : ∀ q,Stock.externCtor ctx T.value_reg [.reg r] q = .ok (.regs [r],q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.value_reg _ q (by decide)]; rfl
  have output : ∀ q,Stock.externCtor ctx T.output [.regs [r]] q = .ok (.regsVec [[r]],q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.output _ q (by decide)]; rfl
  cases hp
  isel_eval [*,rule_prelude_lower_105,sem_ctor]
/-- The actual wide unsigned division RHS composes its guarded dividend
request and real divisor call with quotient emission and output binding. -/
theorem stock_div_udiv_wide_from_parts {p : Program} (hp : Data p) (ctx : Ctx)
    {x y : Nat} {rx ry : Reg} (mapX : ctx.valueReg? x = some rx)
    (st : State) (safeX : DemandAllowed ctx st x) (tr : Array RuleId) (n : Nat)
    {middle : State} {middleTrace : Array RuleId}
    (divisor : (applyTerm p (Stock.sem ctx) {} (n+43) 27 698
      [.value y,.data 125 1 [],.ty (.int 64)]).run (st.mark x,tr) =
        .ok (some (.reg ry),middle,middleTrace)) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+50) rule_lower_1116.rhs
      (baseWideEnv .udiv x y)).run (st,tr) =
      .ok (some (.regsVec [[(middle.base.fresh .int).1]]),
        {middle with base := ((middle.base.fresh .int).2.emit
          (.aluRRR .uDiv .size64 (middle.base.fresh .int).1 rx ry))},trace) := by
  have request := stock_put_in_reg ctx st x rx mapX safeX
  obtain ⟨quotientTrace,quotient⟩ := stock_div_quotient_helper hp ctx (cfg := {}) rfl (w := 64)
    (by decide) false middle middleTrace (n+17) rx ry
  simp only [Nat.add_assoc, Nat.reduceAdd, Bool.false_eq_true, ite_false] at quotient
  have output := fun q trace fuel r => output_run hp ctx q trace fuel r
  have primitive : (Stock.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl
  cases hp
  refine Exists.intro ?trace ?proof
  case proof =>
    simp only [baseWideEnv,baseWideRule] at *
    isel_eval [*,rule_lower_1116,sem_ctor,sem_mkData]
    all_goals rfl
theorem stock_div_udiv_narrow_from_parts {p : Program} (hp : Data p) (ctx : Ctx)
    {x y w : Nat} {rx ry : Reg}
    (st : State) (tr : Array RuleId) (n : Nat)
    {prepared : State} {preparedTrace : Array RuleId}
    (first : (applyTerm p (Stock.sem ctx) {} (n+44) 27 556 [.value x]).run (st,tr) =
      .ok (some (.reg rx),prepared,preparedTrace))
    {middle : State} {middleTrace : Array RuleId}
    (divisor : (applyTerm p (Stock.sem ctx) {} (n+43) 27 698
      [.value y,.data 125 1 [],.ty (.int w)]).run (prepared,preparedTrace) =
        .ok (some (.reg ry),middle,middleTrace)) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+50) rule_lower_1119.rhs
      (baseNarrowEnv .udiv w x y)).run (st,tr) =
      .ok (some (.regsVec [[(middle.base.fresh .int).1]]),
        {middle with base := ((middle.base.fresh .int).2.emit
          (.aluRRR .uDiv .size32 (middle.base.fresh .int).1 rx ry))},trace) := by
  obtain ⟨quotientTrace,quotient⟩ := stock_div_quotient_helper hp ctx (cfg := {}) rfl (w := 32)
    (by decide) false middle middleTrace (n+17) rx ry
  simp only [Nat.add_assoc, Nat.reduceAdd, Bool.false_eq_true, ite_false] at quotient
  have output := fun q trace fuel r => output_run hp ctx q trace fuel r
  have primitive : (Stock.sem ctx).prim 14 "I32" = some (.ty (.int 32)) := rfl
  cases hp
  refine Exists.intro ?trace ?proof
  case proof =>
    simp only [baseNarrowEnv,baseNarrowRule] at *
    isel_eval [*,rule_lower_1119,sem_ctor,sem_mkData]
    all_goals rfl
def quotientState (signed : Bool) (w : Nat) (s : State) (rx ry : Reg) : State :=
  {s with base := ((s.base.fresh .int).2.emit
    (.aluRRR (if signed then .sDiv else .uDiv) (szOf w) (s.base.fresh .int).1 rx ry))}
def remainderState (signed : Bool) (w : Nat) (s : State) (rx ry : Reg) : State :=
  let q := quotientState signed w s rx ry
  {q with base := ((q.base.fresh .int).2.emit
    (.aluRRRR .mSub (szOf w) (q.base.fresh .int).1 (s.base.fresh .int).1 ry rx))}
/-- Actual wide remainder RHSs preserve both source preparations and reconstruct
remainder using the real divide and multiply-subtract helpers. -/
theorem stock_div_rem_wide_from_parts {p : Program} (hp : Data p) (ctx : Ctx) (signed : Bool)
    {x y : Nat} {rx ry : Reg} (st : State) (tr : Array RuleId) (n : Nat)
    {prepared middle : State} {preparedTrace middleTrace : Array RuleId}
    (first : (applyTerm p (Stock.sem ctx) {} (n+97) 27 (if signed then 557 else 558)
      [.value x]).run (st,tr) = .ok (some (.reg rx),prepared,preparedTrace))
    (divisor : (applyTerm p (Stock.sem ctx) {} (n+96) 27 698
      [.value y,.data 125 (if signed then 0 else 1) [],.ty (.int 64)]).run (prepared,preparedTrace) =
        .ok (some (.reg ry),middle,middleTrace)) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+100)
      (baseWideRule (if signed then .srem else .urem)).rhs
      (baseWideEnv (if signed then .srem else .urem) x y)).run (st,tr) =
      .ok (some (.regsVec [[((quotientState signed 64 middle rx ry).base.fresh .int).1]]),
        remainderState signed 64 middle rx ry,trace) := by
  obtain ⟨quotientTrace,quotient⟩ := stock_div_quotient_helper hp ctx (cfg := {}) rfl (w := 64)
    (by decide) signed middle middleTrace (n+65) rx ry
  obtain ⟨remainderTrace,remainder⟩ := stock_div_msub_helper hp ctx (cfg := {}) rfl (w := 64)
    (by decide) (quotientState signed 64 middle rx ry) quotientTrace (n+64)
    (middle.base.fresh .int).1 ry rx
  simp only [Nat.add_assoc,Nat.reduceAdd] at quotient remainder
  have output := fun q trace fuel r => output_run hp ctx q trace fuel r
  have primitive : (Stock.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl
  cases hp
  cases signed
  · refine Exists.intro ?traceU ?proofU
    case proofU =>
      simp only [baseWideRule,baseWideEnv,quotientState,remainderState,Bool.false_eq_true,ite_false] at *
      isel_eval [*,rule_lower_1190,sem_ctor,sem_mkData]
      all_goals rfl
  · refine Exists.intro ?traceS ?proofS
    case proofS =>
      simp only [baseWideRule,baseWideEnv,quotientState,remainderState,ite_true] at *
      isel_eval [*,rule_lower_1204,sem_ctor,sem_mkData]
      all_goals rfl
theorem stock_div_rem_narrow_from_parts {p : Program} (hp : Data p) (ctx : Ctx) (signed : Bool)
    {x y w : Nat} (width : w ≤ 32) {rx ry : Reg} (st : State) (tr : Array RuleId) (n : Nat)
    {prepared middle : State} {preparedTrace middleTrace : Array RuleId}
    (first : (applyTerm p (Stock.sem ctx) {} (n+97) 27 (if signed then 555 else 556)
      [.value x]).run (st,tr) = .ok (some (.reg rx),prepared,preparedTrace))
    (divisor : (applyTerm p (Stock.sem ctx) {} (n+96) 27 698
      [.value y,.data 125 (if signed then 0 else 1) [],.ty (.int w)]).run (prepared,preparedTrace) =
        .ok (some (.reg ry),middle,middleTrace)) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+100)
      (baseNarrowRule (if signed then .srem else .urem)).rhs
      (baseNarrowEnv (if signed then .srem else .urem) w x y)).run (st,tr) =
      .ok (some (.regsVec [[((quotientState signed w middle rx ry).base.fresh .int).1]]),
        remainderState signed w middle rx ry,trace) := by
  obtain ⟨quotientTrace,quotient⟩ := stock_div_quotient_helper hp ctx (cfg := {}) rfl (w := w)
    (by omega) signed middle middleTrace (n+65) rx ry
  obtain ⟨remainderTrace,remainder⟩ := stock_div_msub_helper hp ctx (cfg := {}) rfl (w := w)
    (by omega) (quotientState signed w middle rx ry) quotientTrace (n+64)
    (middle.base.fresh .int).1 ry rx
  simp only [Nat.add_assoc,Nat.reduceAdd] at quotient remainder
  have output := fun q trace fuel r => output_run hp ctx q trace fuel r
  cases hp
  cases signed
  · refine Exists.intro ?traceU ?proofU
    case proofU =>
      simp only [baseNarrowRule,baseNarrowEnv,quotientState,remainderState,Bool.false_eq_true,ite_false] at *
      isel_eval [*,rule_lower_1197,sem_ctor,sem_mkData]
      all_goals rfl
  · refine Exists.intro ?traceS ?proofS
    case proofS =>
      simp only [baseNarrowRule,baseNarrowEnv,quotientState,remainderState,ite_true] at *
      isel_eval [*,rule_lower_1211,sem_ctor,sem_mkData]
      all_goals rfl
/-- General signed division retains its zero and signed-overflow checks in
the actual RHS composition; no nonzero or no-overflow source restriction is
introduced. -/
theorem stock_div_sdiv_wide_from_parts {p : Program} (hp : Data p) (ctx : Ctx)
    {x y : Nat} {rx ry check : Reg} (st : State) (tr : Array RuleId) (n : Nat)
    {s1 s2 s3 s4 : State} {t1 t2 t3 t4 : Array RuleId}
    (first : (applyTerm p (Stock.sem ctx) {} (n+97) 27 557 [.value x]).run (st,tr) = .ok (some (.reg rx),s1,t1))
    (divisor : (applyTerm p (Stock.sem ctx) {} (n+96) 27 698
      [.value y,.data 125 0 [],.ty (.int 64)]).run (s1,t1) = .ok (some (.reg ry),s2,t2))
    (minimum : (applyTerm p (Stock.sem ctx) {} (n+95) 27 562 [.ty (.int 64),.reg rx]).run (s2,t2) =
      .ok (some (.reg check),s3,t3))
    (overflow : (applyTerm p (Stock.sem ctx) {} (n+94) 27 561 [.ty (.int 64),.reg check,.reg rx,.reg ry]).run (s3,t3) =
      .ok (some (.reg rx),s4,t4)) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+100) rule_lower_1145.rhs (baseWideEnv .sdiv x y)).run (st,tr) =
      .ok (some (.regsVec [[(s4.base.fresh .int).1]]),quotientState true 64 s4 rx ry,trace) := by
  obtain ⟨quotientTrace,quotient⟩ := stock_div_quotient_helper hp ctx (cfg := {}) rfl (w := 64)
    (by decide) true s4 t4 (n+63) rx ry
  simp only [Nat.add_assoc,Nat.reduceAdd,ite_true] at quotient
  have output := fun q trace fuel r => output_run hp ctx q trace fuel r
  have primitive : (Stock.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl
  cases hp
  refine Exists.intro ?trace ?proof
  case proof =>
    simp only [baseWideEnv,baseWideRule,quotientState,ite_true] at *
    isel_eval [*,rule_lower_1145,sem_ctor,sem_mkData]
    all_goals rfl
/-- General signed division retains its zero and signed-overflow checks in
the actual RHS composition; no nonzero or no-overflow source restriction is
introduced. -/
theorem stock_div_sdiv_narrow_from_parts {p : Program} (hp : Data p) (ctx : Ctx)
    {x y w : Nat} (width : w ≤ 32) {rx ry check : Reg} (st : State) (tr : Array RuleId) (n : Nat)
    {s1 s2 s3 s4 : State} {t1 t2 t3 t4 : Array RuleId}
    (first : (applyTerm p (Stock.sem ctx) {} (n+97) 27 555 [.value x]).run (st,tr) = .ok (some (.reg rx),s1,t1))
    (divisor : (applyTerm p (Stock.sem ctx) {} (n+96) 27 698
      [.value y,.data 125 0 [],.ty (.int w)]).run (s1,t1) = .ok (some (.reg ry),s2,t2))
    (minimum : (applyTerm p (Stock.sem ctx) {} (n+95) 27 562 [.ty (.int w),.reg rx]).run (s2,t2) =
      .ok (some (.reg check),s3,t3))
    (overflow : (applyTerm p (Stock.sem ctx) {} (n+94) 27 561 [.ty (.int w),.reg check,.reg rx,.reg ry]).run (s3,t3) =
      .ok (some (.reg rx),s4,t4)) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+100) rule_lower_1153.rhs (baseNarrowEnv .sdiv w x y)).run (st,tr) =
      .ok (some (.regsVec [[(s4.base.fresh .int).1]]),quotientState true w s4 rx ry,trace) := by
  obtain ⟨quotientTrace,quotient⟩ := stock_div_quotient_helper hp ctx (cfg := {}) rfl (w := w)
    (by omega) true s4 t4 (n+63) rx ry
  simp only [Nat.add_assoc,Nat.reduceAdd,ite_true] at quotient
  have output := fun q trace fuel r => output_run hp ctx q trace fuel r
  cases hp
  refine Exists.intro ?trace ?proof
  case proof =>
    simp only [baseNarrowEnv,baseNarrowRule,quotientState,ite_true] at *
    isel_eval [*,rule_lower_1153,sem_ctor,sem_mkData]
    all_goals rfl
def safeWideEnv (x : Nat) (i v : Int) : Isle.Interp.Env V :=
  (((Array.replicate 3 none).setIfInBounds 0 (some (.value x))).setIfInBounds 1 (some (.int i))).setIfInBounds 2 (some (.int v))
def safeNarrowEnv (w x : Nat) (i v : Int) : Isle.Interp.Env V :=
  ((((Array.replicate 4 none).setIfInBounds 0 (some (.ty (.int w)))).setIfInBounds 1 (some (.value x))).setIfInBounds 2 (some (.int i))).setIfInBounds 3 (some (.int v))
theorem stock_div_sdiv_safe_wide_from_parts {p : Program} (hp : Data p) (ctx : Ctx)
    {x : Nat} {i v : Int} {rx ry : Reg} (st : State) (tr : Array RuleId) (n : Nat)
    {prepared middle : State} {preparedTrace middleTrace : Array RuleId}
    (first : (applyTerm p (Stock.sem ctx) {} (n+44) 27 557 [.value x]).run (st,tr) =
      .ok (some (.reg rx),prepared,preparedTrace))
    (literal : (applyTerm p (Stock.sem ctx) {} (n+43) 27 553
      [.ty (.int 64),.data 122 0 [],.int v]).run (prepared,preparedTrace) =
        .ok (some (.reg ry),middle,middleTrace)) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+50) rule_lower_1163.rhs
      (safeWideEnv x i v)).run (st,tr) =
      .ok (some (.regsVec [[(middle.base.fresh .int).1]]),quotientState true 64 middle rx ry,trace) := by
  obtain ⟨quotientTrace,quotient⟩ := stock_div_quotient_helper hp ctx (cfg := {}) rfl (w := 64)
    (by decide) true middle middleTrace (n+17) rx ry
  simp only [Nat.add_assoc,Nat.reduceAdd,ite_true] at quotient
  have output := fun q trace fuel r => output_run hp ctx q trace fuel r
  have primitive : (Stock.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl
  cases hp
  refine Exists.intro ?trace ?proof
  case proof =>
    simp only [safeWideEnv,quotientState,ite_true] at *
    isel_eval [*,rule_lower_1163,sem_ctor,sem_mkData]
    all_goals rfl
theorem stock_div_sdiv_safe_narrow_from_parts {p : Program} (hp : Data p) (ctx : Ctx)
    {x w : Nat} (width : w ≤ 32) {i v : Int} {rx ry : Reg} (st : State) (tr : Array RuleId) (n : Nat)
    {prepared middle : State} {preparedTrace middleTrace : Array RuleId}
    (first : (applyTerm p (Stock.sem ctx) {} (n+44) 27 555 [.value x]).run (st,tr) =
      .ok (some (.reg rx),prepared,preparedTrace))
    (literal : (applyTerm p (Stock.sem ctx) {} (n+43) 27 553
      [.ty (.int w),.data 122 0 [],.int v]).run (prepared,preparedTrace) =
        .ok (some (.reg ry),middle,middleTrace)) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+50) rule_lower_1167.rhs
      (safeNarrowEnv w x i v)).run (st,tr) =
      .ok (some (.regsVec [[(middle.base.fresh .int).1]]),quotientState true w middle rx ry,trace) := by
  obtain ⟨quotientTrace,quotient⟩ := stock_div_quotient_helper hp ctx (cfg := {}) rfl (w := w)
    (by omega) true middle middleTrace (n+17) rx ry
  simp only [Nat.add_assoc,Nat.reduceAdd,ite_true] at quotient
  have output := fun q trace fuel r => output_run hp ctx q trace fuel r
  cases hp
  refine Exists.intro ?trace ?proof
  case proof =>
    simp only [safeNarrowEnv,quotientState,ite_true] at *
    isel_eval [*,rule_lower_1167,sem_ctor,sem_mkData]
    all_goals rfl
end Backend.Stock.Proof.ScalarDiv
