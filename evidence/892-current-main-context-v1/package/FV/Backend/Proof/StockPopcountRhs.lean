import FV.Backend.Proof.IselFamAluBShiftTerms
import FV.Backend.Proof.StockValues
import FV.Backend.Proof.IselCtlTry
import FV.Backend.Proof.StockPopcountPure
namespace Backend.Stock.Proof.ScalarPopcount
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : LState) :
    (Backend.sem ctx).ctor t vs st = Backend.externCtor ctx t vs st := rfl
private theorem sem_prim (ctx : Ctx) (name : String) :
    (Backend.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
private theorem sem_mkData (ctx : Ctx) (t k : Nat) (vs : List V) :
    (Backend.sem ctx).mkData t k vs = .data t k vs := rfl
private theorem temp (ctx : Ctx) (st : LState) :
    Backend.externCtor ctx T.temp_writable_reg [.ty (.vec 8 16 false)] st =
      .ok (.reg (st.fresh .float).1,(st.fresh .float).2) := rfl
private theorem temp_int (ctx : Ctx) (st : LState) :
    Backend.externCtor ctx T.temp_writable_reg [.ty (.int 64)] st =
      .ok (.reg (st.fresh .int).1,(st.fresh .int).2) := rfl
private theorem legacy_to_vec {p : Program} (hp : Data p) (ctx : Ctx) (wide : Bool)
    (st : LState) (tr : Array RuleId) (n : Nat) (rx : Reg) :
    (applyTerm p (Backend.sem ctx) {} (n+50) 27 409
      [.reg rx,.data 95 (if wide then 3 else 2) []]).run (st,tr) =
      .ok (some (.reg (st.fresh .float).1),
        (st.fresh .float).2.emit (.movToFpu (st.fresh .float).1 rx (if wide then .size64 else .size32)),
        (tr.push rule_inst_2938.id).push rule_inst_2930.id) := by
  have tmp := fun q => temp ctx q
  have reg := fun q r => ctor_writable_reg_to_reg ctx q r
  have emit : ∀ q rd,Backend.externCtor ctx T.emit [.data 58 75 [.reg rd,.reg rx,.data 95 (if wide then 3 else 2) []]] q =
      .ok (.op .unit,q.emit (.movToFpu rd rx (if wide then .size64 else .size32))) := by
    intro q rd; apply ctor_emit; cases wide <;> rfl
  cases hp
  cases wide
  all_goals simp only [Bool.false_eq_true,ite_false,ite_true] at *
  all_goals isel_eval [*,rule_inst_2930,rule_inst_2938,rule_inst_2941,sem_ctor,sem_prim,sem_mkData]
  all_goals rfl
private theorem legacy_count {p : Program} (hp : Data p) (ctx : Ctx)
    (st : LState) (tr : Array RuleId) (n : Nat) (rx : Reg) :
    (applyTerm p (Backend.sem ctx) {} (n+50) 27 524 [.reg rx,.data 97 0 []]).run (st,tr) =
      .ok (some (.reg (st.fresh .float).1),
        (st.fresh .float).2.emit (.vecMisc .cnt (st.fresh .float).1 rx .size8x8),
        (tr.push rule_inst_2802.id).push rule_inst_3545.id) := by
  have tmp := fun q => temp ctx q
  have reg := fun q r => ctor_writable_reg_to_reg ctx q r
  have emit : ∀ q rd,Backend.externCtor ctx T.emit [.data 58 96 [.data 107 17 [],.reg rd,.reg rx,.data 97 0 []]] q =
      .ok (.op .unit,q.emit (.vecMisc .cnt rd rx .size8x8)) := fun q rd => ctor_emit ctx q rfl
  cases hp
  isel_eval [*,rule_inst_3545,rule_inst_2802,sem_ctor,sem_prim,sem_mkData]
  all_goals rfl
private theorem legacy_pair {p : Program} (hp : Data p) (ctx : Ctx)
    (st : LState) (tr : Array RuleId) (n : Nat) (rx : Reg) :
    (applyTerm p (Backend.sem ctx) {} (n+50) 27 469 [.reg rx,.reg rx,.data 97 0 []]).run (st,tr) =
      .ok (some (.reg (st.fresh .float).1),
        (st.fresh .float).2.emit (.vecRRR .addp (st.fresh .float).1 rx rx .size8x8),
        (tr.push rule_inst_2552.id).push rule_inst_3290.id) := by
  have tmp := fun q => temp ctx q
  have reg := fun q r => ctor_writable_reg_to_reg ctx q r
  have emit : ∀ q rd,Backend.externCtor ctx T.emit [.data 58 93 [.data 105 34 [],.reg rd,.reg rx,.reg rx,.data 97 0 []]] q =
      .ok (.op .unit,q.emit (.vecRRR .addp rd rx rx .size8x8)) := fun q rd => ctor_emit ctx q rfl
  cases hp
  isel_eval [*,rule_inst_3290,rule_inst_2552,sem_ctor,sem_prim,sem_mkData]
  all_goals rfl
private theorem legacy_sum {p : Program} (hp : Data p) (ctx : Ctx)
    (st : LState) (tr : Array RuleId) (n : Nat) (rx : Reg) :
    (applyTerm p (Backend.sem ctx) {} (n+50) 27 473 [.reg rx,.data 97 0 []]).run (st,tr) =
      .ok (some (.reg (st.fresh .float).1),
        (st.fresh .float).2.emit (.vecLanes .addv (st.fresh .float).1 rx .size8x8),
        (tr.push rule_inst_2612.id).push rule_inst_3311.id) := by
  have tmp := fun q => temp ctx q
  have reg := fun q r => ctor_writable_reg_to_reg ctx q r
  have emit : ∀ q rd,Backend.externCtor ctx T.emit [.data 58 97 [.data 114 0 [],.reg rd,.reg rx,.data 97 0 []]] q =
      .ok (.op .unit,q.emit (.vecLanes .addv rd rx .size8x8)) := fun q rd => ctor_emit ctx q rfl
  cases hp
  isel_eval [*,rule_inst_3311,rule_inst_2612,sem_ctor,sem_prim,sem_mkData]
  all_goals rfl
private theorem legacy_from_vec {p : Program} (hp : Data p) (ctx : Ctx)
    (st : LState) (tr : Array RuleId) (n : Nat) (rx : Reg) :
    (applyTerm p (Backend.sem ctx) {} (n+50) 27 414 [.reg rx,.int 0,.data 95 0 []]).run (st,tr) =
      .ok (some (.reg (st.fresh .int).1),
        (st.fresh .int).2.emit (.movFromVec (st.fresh .int).1 rx 0 .size8),tr.push rule_inst_2970.id) := by
  have tmp := fun q => temp_int ctx q
  have reg := fun q r => ctor_writable_reg_to_reg ctx q r
  have emit : ∀ q rd,Backend.externCtor ctx T.emit [.data 58 78 [.reg rd,.reg rx,.int 0,.data 95 0 []]] q =
      .ok (.op .unit,q.emit (.movFromVec rd rx 0 .size8)) := fun q rd => ctor_emit ctx q rfl
  cases hp
  isel_eval [*,rule_inst_2970,sem_ctor,sem_prim,sem_mkData]
  all_goals rfl
theorem stock_popcount_to_vec {p : Program} (hp : Data p) (ctx : Ctx) (wide : Bool)
    (st : State) (tr : Array RuleId) (n : Nat) (rx : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n+50) 27 409
      [.reg rx,.data 95 (if wide then 3 else 2) []]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .float).1),
        {st with base := (st.base.fresh .float).2.emit (.movToFpu (st.base.fresh .float).1 rx (if wide then .size64 else .size32))},
        (tr.push rule_inst_2938.id).push rule_inst_2930.id) := by
  exact stock_popcount_pure_helper hp ctx (cfg := {}) rfl (by decide) (legacy_to_vec hp ctx wide st.base tr n rx)
theorem stock_popcount_count {p : Program} (hp : Data p) (ctx : Ctx)
    (st : State) (tr : Array RuleId) (n : Nat) (rx : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n+50) 27 524 [.reg rx,.data 97 0 []]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .float).1),
        {st with base := (st.base.fresh .float).2.emit (.vecMisc .cnt (st.base.fresh .float).1 rx .size8x8)},
        (tr.push rule_inst_2802.id).push rule_inst_3545.id) := by
  exact stock_popcount_pure_helper hp ctx (cfg := {}) rfl (by decide) (legacy_count hp ctx st.base tr n rx)
theorem stock_popcount_pair {p : Program} (hp : Data p) (ctx : Ctx)
    (st : State) (tr : Array RuleId) (n : Nat) (rx : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n+50) 27 469 [.reg rx,.reg rx,.data 97 0 []]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .float).1),
        {st with base := (st.base.fresh .float).2.emit (.vecRRR .addp (st.base.fresh .float).1 rx rx .size8x8)},
        (tr.push rule_inst_2552.id).push rule_inst_3290.id) := by
  exact stock_popcount_pure_helper hp ctx (cfg := {}) rfl (by decide) (legacy_pair hp ctx st.base tr n rx)
theorem stock_popcount_sum_vec {p : Program} (hp : Data p) (ctx : Ctx)
    (st : State) (tr : Array RuleId) (n : Nat) (rx : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n+50) 27 473 [.reg rx,.data 97 0 []]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .float).1),
        {st with base := (st.base.fresh .float).2.emit (.vecLanes .addv (st.base.fresh .float).1 rx .size8x8)},
        (tr.push rule_inst_2612.id).push rule_inst_3311.id) := by
  exact stock_popcount_pure_helper hp ctx (cfg := {}) rfl (by decide) (legacy_sum hp ctx st.base tr n rx)
theorem stock_popcount_from_vec {p : Program} (hp : Data p) (ctx : Ctx)
    (st : State) (tr : Array RuleId) (n : Nat) (rx : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n+50) 27 414 [.reg rx,.int 0,.data 95 0 []]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.movFromVec (st.base.fresh .int).1 rx 0 .size8)},tr.push rule_inst_2970.id) := by
  exact stock_popcount_pure_helper hp ctx (cfg := {}) rfl (by decide) (legacy_from_vec hp ctx st.base tr n rx)
private theorem stock_mkData (ctx : Ctx) (t k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData t k vs = .data t k vs := rfl
private theorem stock_sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
section Zero
attribute [local semireducible] Isle.Aarch64.program
private theorem zero (ctx : Ctx) : (Stock.sem ctx).int 1 0 = .int 0 := rfl
end Zero
private theorem output_run {p : Program} (hp : Data p) (ctx : Ctx) (st : State) (tr : Array RuleId)
    (n : Nat) (r : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n+10) 25 172 [.reg r]).run (st,tr) =
      .ok (some (.regsVec [[r]]),st,tr.push rule_prelude_lower_105.id) := by
  have value : ∀ q,Stock.externCtor ctx T.value_reg [.reg r] q = .ok (.regs [r],q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.value_reg _ q (by decide)]; rfl
  have output : ∀ q,Stock.externCtor ctx T.output [.regs [r]] q = .ok (.regsVec [[r]],q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.output _ q (by decide)]; rfl
  cases hp
  isel_eval [*,rule_prelude_lower_105,stock_sem_ctor]
def popcountRule (w : Nat) : Rule :=
  if w = 8 then rule_lower_2074 else if w = 16 then rule_lower_2080
  else if w = 32 then rule_lower_2086 else rule_lower_2092
def popcountEnv (w x : Nat) : Isle.Interp.Env V :=
  (Array.replicate (if w = 8 then 3 else 4) none).setIfInBounds 0 (some (.value x))
def popcountResult (w d : Nat) : Nat := if w = 8 then d+2 else d+3
def popcountAlloc (w : Nat) : Nat := if w = 8 then 3 else 4
def popcountBase (w : Nat) (st : LState) (rx : Reg) : LState :=
  let first := (st.fresh .float).2.emit (.movToFpu (st.fresh .float).1 rx (if w = 64 then .size64 else .size32))
  let counted := (first.fresh .float).2.emit (.vecMisc .cnt (first.fresh .float).1 (st.fresh .float).1 .size8x8)
  if w = 8 then (counted.fresh .int).2.emit (.movFromVec (counted.fresh .int).1 (first.fresh .float).1 0 .size8)
  else
    let summed := (counted.fresh .float).2.emit (if w = 16 then
      .vecRRR .addp (counted.fresh .float).1 (first.fresh .float).1 (first.fresh .float).1 .size8x8
      else .vecLanes .addv (counted.fresh .float).1 (first.fresh .float).1 .size8x8)
    (summed.fresh .int).2.emit (.movFromVec (summed.fresh .int).1 (counted.fresh .float).1 0 .size8)
/-- All four actual scalar popcount roots derive the marked Stock state and
complete mixed-class SIMD fragment from one guarded mapped source request. -/
theorem stock_popcount_rhs {p : Program} (hp : Data p) (ctx : Ctx) {w x : Nat} (width : IW w)
    {rx : Reg} (mapped : ctx.valueReg? x = some rx) (st : State) (safe : DemandAllowed ctx st x)
    (tr : Array RuleId) (n : Nat) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+120) (popcountRule w).rhs (popcountEnv w x)).run (st,tr) =
      .ok (some (.regsVec [[.vreg (popcountResult w st.base.nextVreg) .int]]),
        {st.mark x with base := popcountBase w st.base rx},trace) := by
  have request := stock_put_in_reg ctx st x rx mapped safe
  have move := fun q trace fuel => stock_popcount_to_vec hp ctx (w = 64) q trace fuel rx
  have count := fun q trace fuel r => stock_popcount_count hp ctx q trace fuel r
  have pair := fun q trace fuel r => stock_popcount_pair hp ctx q trace fuel r
  have sum := fun q trace fuel r => stock_popcount_sum_vec hp ctx q trace fuel r
  have extract :=  fun q trace fuel r => stock_popcount_from_vec hp ctx q trace fuel r
  have output := fun q trace fuel r => output_run hp ctx q trace fuel r
  cases hp
  rcases width with rfl | rfl | rfl | rfl
  · refine Exists.intro ?trace8 ?proof8
    case proof8 =>
      simp only [popcountRule,popcountEnv,popcountResult,popcountBase,Nat.reduceEqDiff,ite_true,ite_false,decide_true,decide_false,Bool.false_eq_true] at *
      isel_eval [*,rule_lower_2074,rule_lower_2080,rule_lower_2086,rule_lower_2092,stock_sem_ctor,stock_mkData,zero]
      all_goals rfl
  · refine Exists.intro ?trace16 ?proof16
    case proof16 =>
      simp only [popcountRule,popcountEnv,popcountResult,popcountBase,Nat.reduceEqDiff,ite_true,ite_false,decide_true,decide_false,Bool.false_eq_true] at *
      isel_eval [*,rule_lower_2074,rule_lower_2080,rule_lower_2086,rule_lower_2092,stock_sem_ctor,stock_mkData,zero]
      all_goals rfl
  · refine Exists.intro ?trace32 ?proof32
    case proof32 =>
      simp only [popcountRule,popcountEnv,popcountResult,popcountBase,Nat.reduceEqDiff,ite_true,ite_false,decide_true,decide_false,Bool.false_eq_true] at *
      isel_eval [*,rule_lower_2074,rule_lower_2080,rule_lower_2086,rule_lower_2092,stock_sem_ctor,stock_mkData,zero]
      all_goals rfl
  · refine Exists.intro ?trace64 ?proof64
    case proof64 =>
      simp only [popcountRule,popcountEnv,popcountResult,popcountBase,Nat.reduceEqDiff,ite_true,ite_false,decide_true,decide_false,Bool.false_eq_true] at *
      isel_eval [*,rule_lower_2074,rule_lower_2080,rule_lower_2086,rule_lower_2092,stock_sem_ctor,stock_mkData,zero]
      all_goals rfl
/-- Guarded mapped inputs inhabit all four actual RHS contracts. This local
execution witness supplements, rather than replaces, complete original
source/retained-driver witnesses required by the family batch. -/
theorem stock_popcount_rhs_witness : ∀ w ∈ ([8,16,32,64] : List Nat),
    ∃ trace,(evalExpr program (Stock.sem sinkCtx) {} 120 (popcountRule w).rhs
      (popcountEnv w 1)).run (sinkState,#[]) =
      .ok (some (.regsVec [[.vreg (popcountResult w sinkState.base.nextVreg) .int]]),
        {sinkState.mark 1 with base := popcountBase w sinkState.base (.vreg 193 .int)},trace) := by
  intro w member
  have width : IW w := by simpa only [List.mem_cons,List.not_mem_nil,or_false,IW] using member
  have guard : DemandAllowed sinkCtx sinkState 1 := by
    intro i defined
    change none = some i at defined
    cases defined
  exact stock_popcount_rhs data_program sinkCtx width rfl sinkState guard #[] 0
end Backend.Stock.Proof.ScalarPopcount
