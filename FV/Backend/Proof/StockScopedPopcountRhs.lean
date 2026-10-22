import FV.Backend.Proof.StockPopcountHelpers
import FV.Backend.Proof.StockPopcountDispatch
import FV.Backend.Proof.StockRequestSuccess
import FV.Backend.Proof.StockCmpOutput
namespace Backend.Stock.Proof.Popcount
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
attribute [local irreducible] Isle.Aarch64.program

private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl

section Numbers
attribute [local semireducible] Isle.Aarch64.program
private theorem sem_int0 (ctx : Ctx) : (Stock.sem ctx).int 1 0 = .int 0 := rfl
end Numbers

def popcountBase (w : Nat) (st : LState) (rx : Reg) : LState :=
  let (a,s) := st.fresh .float
  let s := s.emit (.movToFpu a rx (if w = 64 then .size64 else .size32))
  let (b,s) := s.fresh .float
  let s := s.emit (.vecMisc .cnt b a .size8x8)
  if w = 8 then
    let (d,s) := s.fresh .int
    s.emit (.movFromVec d b 0 .size8)
  else
    let (c,s) := s.fresh .float
    let s := if w = 16 then s.emit (.vecRRR .addp c b b .size8x8)
      else s.emit (.vecLanes .addv c b .size8x8)
    let (d,s) := s.fresh .int
    s.emit (.movFromVec d c 0 .size8)

def popcountAlloc (w : Nat) : Nat := if w = 8 then 3 else 4

def popcountEnv (w x : Nat) : Isle.Interp.Env V :=
  (Array.replicate (popcountAlloc w) none).setIfInBounds 0 (some (.value x))

def popcountResult (w d : Nat) : Nat := d + popcountAlloc w - 1

/-- Actual successful wide RHS emits the real four-instruction vector template
and preserves the complete scheduling state apart from its guarded source use. -/
theorem rhs_wide_observed {p : Program} (hp : Data p) (ctx : Ctx) {w : Nat} (width : w = 32 ∨ w = 64) {x n : Nat}
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+200) (popcountRule w).rhs (popcountEnv w x)).run (st,tr) =
      .ok (some out,next,trace)) :
    ∃ rx,DemandAllowed ctx st x ∧ ctx.valueReg? x = some rx ∧
      out = .regsVec [[.vreg (st.base.nextVreg+3) .int]] ∧
      next = {st.mark x with base := popcountBase w st.base rx} := by
  let sz : ScalarSize := if w = 64 then .size64 else .size32
  rcases width with rfl | rfl
  all_goals
    have hp' := hp
    cases hp
    isel_inv [*,popcountRule,rule_lower_2086,rule_lower_2092,sem_ctor,sem_int0,popcountEnv,popcountAlloc] at run
    obtain ⟨safe,rx,mapped,rfl,rfl⟩ :=
      (stock_put_in_reg_iff ctx st x _ _).mp ‹Stock.externCtor ctx T.put_in_reg [.value x] st = .ok _›
    have h1 := ‹ApplyInternal p (Stock.sem ctx) _ _ 27 409 _ _ _ _›
    obtain ⟨rfl,m1,hm1,hs1⟩ := mov_to_fpu_observed hp' ctx rfl (by omega) (by first | exact .inl rfl | exact .inr rfl) h1
    have h2 := ‹ApplyInternal p (Stock.sem ctx) _ _ 27 524 _ _ _ _›
    obtain ⟨rfl,m2,hm2,hs2⟩ := cnt_observed hp' ctx rfl (by omega) h2
    have h3 := ‹ApplyInternal p (Stock.sem ctx) _ _ 27 473 _ _ _ _›
    obtain ⟨rfl,m3,hm3,hs3⟩ := addv_observed hp' ctx rfl (by omega) h3
    have h4 := ‹ApplyInternal p (Stock.sem ctx) _ _ 27 414 _ _ _ _›
    obtain ⟨rfl,m4,hm4,hs4⟩ := mov_from_vec_observed hp' ctx rfl (by omega) h4
    have hO := ‹ApplyInternal p (Stock.sem ctx) _ _ 25 172 _ _ _ _›
    obtain ⟨rfl,last⟩ := ScalarCmp.stock_cmp_output_observed hp' ctx (by omega) hO
    rw [hs3] at hm4 hs4
    rw [hs2] at hm3 hs3 hm4 hs4
    rw [hs1] at hm2 hs2 hm3 hs3 hm4 hs4
    have e1 : m1 = .movToFpu (.vreg st.base.nextVreg .float) rx sz :=
      Option.some.inj (hm1.symm.trans rfl)
    subst m1
    have e2 : m2 = .vecMisc .cnt (.vreg (st.base.nextVreg+1) .float) (.vreg st.base.nextVreg .float) .size8x8 :=
      Option.some.inj (hm2.symm.trans rfl)
    subst m2
    have e3 : m3 = .vecLanes .addv (.vreg (st.base.nextVreg+2) .float) (.vreg (st.base.nextVreg+1) .float) .size8x8 :=
      Option.some.inj (hm3.symm.trans rfl)
    subst m3
    have e4 : m4 = .movFromVec (.vreg (st.base.nextVreg+3) .int) (.vreg (st.base.nextVreg+2) .float) 0 .size8 :=
      Option.some.inj (hm4.symm.trans rfl)
    subst m4
    refine ⟨safe,rx,mapped,?_,?_⟩
    · rw [hs3]
      rfl
    · rw [last,hs4]
      rfl

theorem rhs64_observed {p : Program} (hp : Data p) (ctx : Ctx) {x n : Nat}
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+200) rule_lower_2092.rhs (popcountEnv 64 x)).run (st,tr) =
      .ok (some out,next,trace)) :
    ∃ rx,DemandAllowed ctx st x ∧ ctx.valueReg? x = some rx ∧
      out = .regsVec [[.vreg (st.base.nextVreg+3) .int]] ∧
      next = {st.mark x with base := popcountBase 64 st.base rx} := by
  exact rhs_wide_observed hp ctx (Or.inr rfl) run

theorem rhs32_observed {p : Program} (hp : Data p) (ctx : Ctx) {x n : Nat}
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+200) rule_lower_2086.rhs (popcountEnv 32 x)).run (st,tr) =
      .ok (some out,next,trace)) :
    ∃ rx,DemandAllowed ctx st x ∧ ctx.valueReg? x = some rx ∧
      out = .regsVec [[.vreg (st.base.nextVreg+3) .int]] ∧
      next = {st.mark x with base := popcountBase 32 st.base rx} := by
  exact rhs_wide_observed hp ctx (Or.inl rfl) run

theorem rhs8_observed {p : Program} (hp : Data p) (ctx : Ctx) {x n : Nat}
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+200) rule_lower_2074.rhs (popcountEnv 8 x)).run (st,tr) =
      .ok (some out,next,trace)) :
    ∃ rx,DemandAllowed ctx st x ∧ ctx.valueReg? x = some rx ∧
      out = .regsVec [[.vreg (st.base.nextVreg+2) .int]] ∧
      next = {st.mark x with base := popcountBase 8 st.base rx} := by
  have hp' := hp
  cases hp
  isel_inv [*,rule_lower_2074,sem_ctor,sem_int0,popcountEnv,popcountAlloc] at run
  obtain ⟨safe,rx,mapped,rfl,rfl⟩ :=
    (stock_put_in_reg_iff ctx st x _ _).mp ‹Stock.externCtor ctx T.put_in_reg [.value x] st = .ok _›
  have h1 := ‹ApplyInternal p (Stock.sem ctx) _ _ 27 409 _ _ _ _›
  obtain ⟨rfl,m1,hm1,hs1⟩ := mov_to_fpu_observed hp' ctx rfl (by omega) (by first | exact .inl rfl | exact .inr rfl) h1
  have h2 := ‹ApplyInternal p (Stock.sem ctx) _ _ 27 524 _ _ _ _›
  obtain ⟨rfl,m2,hm2,hs2⟩ := cnt_observed hp' ctx rfl (by omega) h2
  have h4 := ‹ApplyInternal p (Stock.sem ctx) _ _ 27 414 _ _ _ _›
  obtain ⟨rfl,m4,hm4,hs4⟩ := mov_from_vec_observed hp' ctx rfl (by omega) h4
  have hO := ‹ApplyInternal p (Stock.sem ctx) _ _ 25 172 _ _ _ _›
  obtain ⟨rfl,last⟩ := ScalarCmp.stock_cmp_output_observed hp' ctx (by omega) hO
  rw [hs2] at hm4 hs4
  rw [hs1] at hm2 hs2 hm4 hs4
  have e1 : m1 = .movToFpu (.vreg st.base.nextVreg .float) rx .size32 :=
    Option.some.inj (hm1.symm.trans rfl)
  subst m1
  have e2 : m2 = .vecMisc .cnt (.vreg (st.base.nextVreg+1) .float) (.vreg st.base.nextVreg .float) .size8x8 :=
    Option.some.inj (hm2.symm.trans rfl)
  subst m2
  have e4 : m4 = .movFromVec (.vreg (st.base.nextVreg+2) .int) (.vreg (st.base.nextVreg+1) .float) 0 .size8 :=
    Option.some.inj (hm4.symm.trans rfl)
  subst m4
  refine ⟨safe,rx,mapped,?_,?_⟩
  · rw [hs2]
    rfl
  · rw [last,hs4]
    rfl

theorem rhs16_observed {p : Program} (hp : Data p) (ctx : Ctx) {x n : Nat}
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+200) rule_lower_2080.rhs (popcountEnv 16 x)).run (st,tr) =
      .ok (some out,next,trace)) :
    ∃ rx,DemandAllowed ctx st x ∧ ctx.valueReg? x = some rx ∧
      out = .regsVec [[.vreg (st.base.nextVreg+3) .int]] ∧
      next = {st.mark x with base := popcountBase 16 st.base rx} := by
  have hp' := hp
  cases hp
  isel_inv [*,rule_lower_2080,sem_ctor,sem_int0,popcountEnv,popcountAlloc] at run
  obtain ⟨safe,rx,mapped,rfl,rfl⟩ :=
    (stock_put_in_reg_iff ctx st x _ _).mp ‹Stock.externCtor ctx T.put_in_reg [.value x] st = .ok _›
  have h1 := ‹ApplyInternal p (Stock.sem ctx) _ _ 27 409 _ _ _ _›
  obtain ⟨rfl,m1,hm1,hs1⟩ := mov_to_fpu_observed hp' ctx rfl (by omega) (by first | exact .inl rfl | exact .inr rfl) h1
  have h2 := ‹ApplyInternal p (Stock.sem ctx) _ _ 27 524 _ _ _ _›
  obtain ⟨rfl,m2,hm2,hs2⟩ := cnt_observed hp' ctx rfl (by omega) h2
  have h3 := ‹ApplyInternal p (Stock.sem ctx) _ _ 27 469 _ _ _ _›
  obtain ⟨rfl,m3,hm3,hs3⟩ := addp_observed hp' ctx rfl (by omega) h3
  have h4 := ‹ApplyInternal p (Stock.sem ctx) _ _ 27 414 _ _ _ _›
  obtain ⟨rfl,m4,hm4,hs4⟩ := mov_from_vec_observed hp' ctx rfl (by omega) h4
  have hO := ‹ApplyInternal p (Stock.sem ctx) _ _ 25 172 _ _ _ _›
  obtain ⟨rfl,last⟩ := ScalarCmp.stock_cmp_output_observed hp' ctx (by omega) hO
  rw [hs3] at hm4 hs4
  rw [hs2] at hm3 hs3 hm4 hs4
  rw [hs1] at hm2 hs2 hm3 hs3 hm4 hs4
  have e1 : m1 = .movToFpu (.vreg st.base.nextVreg .float) rx .size32 :=
    Option.some.inj (hm1.symm.trans rfl)
  subst m1
  have e2 : m2 = .vecMisc .cnt (.vreg (st.base.nextVreg+1) .float) (.vreg st.base.nextVreg .float) .size8x8 :=
    Option.some.inj (hm2.symm.trans rfl)
  subst m2
  have e3 : m3 = .vecRRR .addp (.vreg (st.base.nextVreg+2) .float) (.vreg (st.base.nextVreg+1) .float) (.vreg (st.base.nextVreg+1) .float) .size8x8 :=
    Option.some.inj (hm3.symm.trans rfl)
  subst m3
  have e4 : m4 = .movFromVec (.vreg (st.base.nextVreg+3) .int) (.vreg (st.base.nextVreg+2) .float) 0 .size8 :=
    Option.some.inj (hm4.symm.trans rfl)
  subst m4
  refine ⟨safe,rx,mapped,?_,?_⟩
  · rw [hs3]
    rfl
  · rw [last,hs4]
    rfl

/-- All original scalar widths share actual request, output and scheduling-state observation. -/
theorem rhs_observed {p : Program} (hp : Data p) (ctx : Ctx) {w x n : Nat} (width : IW w)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+200) (popcountRule w).rhs (popcountEnv w x)).run (st,tr) =
      .ok (some out,next,trace)) :
    ∃ rx,DemandAllowed ctx st x ∧ ctx.valueReg? x = some rx ∧
      out = .regsVec [[.vreg (popcountResult w st.base.nextVreg) .int]] ∧
      next = {st.mark x with base := popcountBase w st.base rx} := by
  rcases width with rfl | rfl | rfl | rfl
  · simpa [popcountRule,popcountResult,popcountAlloc] using rhs8_observed hp ctx run
  · simpa [popcountRule,popcountResult,popcountAlloc] using rhs16_observed hp ctx run
  · simpa [popcountRule,popcountResult,popcountAlloc] using rhs32_observed hp ctx run
  · simpa [popcountRule,popcountResult,popcountAlloc] using rhs64_observed hp ctx run

end Backend.Stock.Proof.Popcount
