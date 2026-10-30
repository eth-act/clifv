import FV.Backend.Proof.StockRequestSuccess
import FV.Backend.Proof.StockSelectionReceipts
import FV.Backend.Proof.StockShiftHelper
import FV.Backend.Proof.IselFamALUAExt
import FV.Backend.Proof.IselFamAluBExtend
namespace Backend.Stock.Proof.ScalarCast
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
def extendRule (sg : Bool) : Rule := if sg then rule_lower_1315 else rule_lower_1261
def extendOpcode (sg : Bool) : Nat := if sg then 142 else 141
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (t : Nat) (v : V) :
    (Stock.sem ctx).unData t v = (Backend.sem ctx).unData t v := rfl
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_bool (ctx : Ctx) (b : Bool) : (Stock.sem ctx).bool b = .bool b := rfl
private theorem ctor_ty_bits (ctx : Ctx) (st : State) (t : CTy) :
    Stock.externCtor ctx T.ty_bits [.ty t] st = .ok (.int t.bits,st) := rfl

private theorem output_run {p : Program} (hp : Data p) (ctx : Ctx) (st : State) (tr : Array RuleId)
    (n : Nat) (r : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n+10) 25 172 [.reg r]).run (st,tr) =
      .ok (some (.regsVec [[r]]),st,tr.push rule_prelude_lower_105.id) := by
  have ctor : ∀ t vs q,(Stock.sem ctx).ctor t vs q = Stock.externCtor ctx t vs q := fun _ _ _ => rfl
  have value : ∀ q,Stock.externCtor ctx T.value_reg [.reg r] q = .ok (.regs [r],q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.value_reg _ q (by decide)]; rfl
  have output : ∀ q,Stock.externCtor ctx T.output [.regs [r]] q = .ok (.regsVec [[r]],q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.output _ q (by decide)]; rfl
  cases hp
  isel_eval [*,rule_prelude_lower_105]

/-- Actual base zero/sign-extension matches preserve complete scheduling state;
widths exceeding64 are rejected. -/
theorem stock_extend_match {p : Program} (hp : Data p) (ctx : Ctx) (sg : Bool)
    {i x w : Nat} {info : IInfo} (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int w))
    (data : info.data = .data 152 29 [.data 151 (extendOpcode sg) [],.value x])
    {t : CTy} (typed : ctx.valueType? x = some t)
    (st : State) (tr : Array RuleId) (m : Nat) :
    (matchRule p (Stock.sem ctx) {} (m+10) (extendRule sg) [.inst i]).run (st,tr) =
      .ok ((if w ≤ 64 then some (envExt w x t) else none),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  have fits := ext_fits_in_64 ctx st.base w
  by_cases small : w ≤ 64
  · simp only [small,ite_true] at fits ⊢
    have types := ext_value_type ctx st.base typed
    cases hp
    cases sg <;> isel_eval [*,extendRule,extendOpcode,rule_lower_1261,rule_lower_1315,sem_extract,sem_unData]
  · simp only [small,ite_false] at fits ⊢
    cases hp
    cases sg <;> isel_eval [*,extendRule,extendOpcode,rule_lower_1261,rule_lower_1315,sem_extract,sem_unData]

/-- The real base extension RHS marks its operand and emits exactly one fresh
extension, retaining every other scheduling field. -/
theorem stock_extend_rhs {p : Program} (hp : Data p) (ctx : Ctx) (sg : Bool)
    {x w : Nat} {t : CTy} {rx : Reg} (mapped : ctx.valueReg? x = some rx)
    (st : State) (safe : DemandAllowed ctx st x) (tr : Array RuleId) (n : Nat) :
    ∃ trace, (evalExpr p (Stock.sem ctx) {} (n+40) (extendRule sg).rhs (envExt w x t)).run (st,tr) =
      .ok (some (.regsVec [[(st.base.fresh .int).1]]),
        {st.mark x with base := (st.base.fresh .int).2.emit (.extend (st.base.fresh .int).1 rx sg t.bits w)},trace) := by
  have requested := stock_put_in_reg ctx st x rx mapped safe
  have bits := fun (st : State) t => ctor_ty_bits ctx st t
  have extended := fun (st : State) tr n rx sg a b => ScalarShift.stock_extend_helper hp ctx (cfg := {}) (by rfl) st tr n rx sg a b
  have output := fun (st : State) tr n r => output_run hp ctx st tr n r
  cases hp
  cases sg
  all_goals
    refine ⟨(tr.push rule_inst_2991.id).push rule_prelude_lower_105.id,?_⟩
    isel_eval [*,extendRule,rule_lower_1261,rule_lower_1315,sem_ctor,sem_bool]
    rfl
end Backend.Stock.Proof.ScalarCast

namespace Backend.Stock.Proof.ScalarCast
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private def castMachine (sg : Bool) (fromB to : Nat) (x : CV) : CV :=
  ofX (if to = 16 then (if sg then ((lo64 x).setWidth fromB).signExtend 32 |>.setWidth 64 else ((lo64 x).setWidth fromB).setWidth 64)
    else if sg then (((lo64 x).setWidth fromB).signExtend to).setWidth 64
    else (((lo64 x).setWidth fromB).setWidth to).setWidth 64)
def extendBits (sg : Bool) (to : Nat) {fromB : Nat} (x : BitVec fromB) : BitVec to :=
  if sg then x.signExtend to else x.setWidth to
/-- All six scalar widening pairs establish original extension bits, including
the special i8→i16 instruction whose physical sign extension goes to32 bits. -/
theorem stock_cast_extend_holds (sg : Bool) {ty target : Clif.Ty} {bits : BitVec ty.width}
    (sourceWidth : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32)
    (targetWidth : target.width = 16 ∨ target.width = 32 ∨ target.width = 64)
    (grows : ty.width < target.width) {x : CV} (held : VHolds ⟨ty,bits⟩ x) :
    VHolds ⟨target,extendBits sg target.width bits⟩ (castMachine sg ty.width target.width x) := by
  have original : (lo64 x).setWidth ty.width = bits := by
    change (x.setWidth 64).setWidth ty.width = bits
    rw [BitVec.setWidth_setWidth_of_le _ (by rcases sourceWidth with h | h | h <;> omega)]
    exact held
  unfold castMachine
  rw [original]
  unfold VHolds extendBits
  dsimp only
  rcases targetWidth with h | h | h <;> rw [h]
  all_goals cases sg
  all_goals simp only [Bool.false_eq_true,ite_false,ite_true,Nat.reduceEqDiff,ofX]
  all_goals simp [BitVec.setWidth_setWidth_of_le,setWidth_signExtend_of_le]

private theorem cast_spec {d : Nat} {rn : Reg} {sg : Bool} {a b : Nat} {x : CV} {w : Arm.ArmState}
    (sourceWidth : a = 8 ∨ a = 16 ∨ a = 32) (targetWidth : b = 16 ∨ b = 32 ∨ b = 64) (grows : a < b) :
    ispec (.extend (.vreg d .int) rn sg a b) [x] w = some ([castMachine sg a b x],w,.next) := by
  rcases sourceWidth with rfl | rfl | rfl <;> rcases targetWidth with rfl | rfl | rfl <;>
    simp at grows <;> rfl
end Backend.Stock.Proof.ScalarCast

namespace Backend.Stock.Proof.ScalarCast
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Successful base extension RHS supplies its actual mapped and unsunk request. -/
theorem stock_extend_rhs_requests {p : Program} (hp : Data p) (ctx : Ctx) (sg : Bool)
    {x w n : Nat} {t : CTy} {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+40) (extendRule sg).rhs (envExt w x t)).run
      (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ ∃ rx, ctx.valueReg? x = some rx := by
  cases requested : Stock.externCtor ctx T.put_in_reg [.value x] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+40) (extendRule sg).rhs (envExt w x t)).run
        (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      cases sg <;> isel_eval [*,extendRule,rule_lower_1261,rule_lower_1315,sem_ctor]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | unmodeled err =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+40) (extendRule sg).rhs (envExt w x t)).run
        (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      cases sg <;> isel_eval [*,extendRule,rule_lower_1261,rule_lower_1315,sem_ctor]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | ok result =>
    obtain ⟨v,st'⟩ := result
    obtain ⟨safe,rx,mapped,_,_⟩ := (stock_put_in_reg_iff ctx st x v st').mp requested
    exact ⟨safe,rx,mapped⟩
end Backend.Stock.Proof.ScalarCast

namespace Backend.Stock.Proof.ScalarCast
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
theorem stock_cast_extend_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (sg : Bool) {ty : Clif.Ty} (sourceWidth : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32)
    {target : Clif.Ty} (targetWidth : target.width = 16 ∨ target.width = 32 ∨ target.width = 64) (grows : ty.width < target.width)
    {ctx : Ctx} {fr : Clif.Frame} {aliases : Array (Option Nat)} {ρ : Nat → CV} {x nx d : Nat}
    (bounded : aliases.size ≤ d) (mapped : ctx.valueReg? x = some (.vreg nx .int))
    (held : ValuesHeld (fun z => z = x) ctx fr (fun k => ρ (aliasNum aliases k)))
    {bits : BitVec ty.width} (source : fr.getAs x ty = .ok bits) :
    ∃ ρ', PRun F isem
      [(MInst.extend (.vreg d .int) (.vreg nx .int) sg ty.width target.width).mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      VHolds ⟨target,extendBits sg target.width bits⟩ (ρ' d) ∧ ∀ n,n ≠ d → ρ' n = ρ n := by
  have input := held.read rfl (getAs_ok source) mapped
  let value := castMachine sg ty.width target.width (ρ (aliasNum aliases nx))
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none
    rw [Array.getElem?_eq_none bounded]
    rfl
  have code : (MInst.extend (.vreg d .int) (.vreg nx .int) sg ty.width target.width).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) =
      .extend (.vreg d .int) (.vreg (aliasNum aliases nx) .int) sg ty.width target.width := by
    change MInst.extend (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int))
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg nx .int)) sg ty.width target.width = _
    rw [resolve_vreg,resolve_vreg]
    change MInst.extend (.vreg (aliasNum aliases d) .int) (.vreg (aliasNum aliases nx) .int) sg ty.width target.width = _
    rw [fresh]
  refine ⟨upd ρ d value,?_,?_,?_⟩
  · intro w
    obtain ⟨w',executed,world⟩ := refines _ _ _ _ _
      (cast_spec (d := d) (rn := .vreg (aliasNum aliases nx) .int) (sg := sg) (x := ρ (aliasNum aliases nx))
        (w := w) sourceWidth targetWidth grows)
    refine ⟨w',?_,world⟩
    rw [code]
    simp only [seqRun,operands_extend']
    have uses : vuses #[⟨d,.int,.def,.late,.reg⟩,⟨aliasNum aliases nx,.int,.use,.early,.reg⟩] ρ =
      [ρ (aliasNum aliases nx)] := rfl
    rw [uses,executed]
    rfl
  · rw [upd_same]
    exact stock_cast_extend_holds sg sourceWidth targetWidth grows input
  · intro n different; simp only [upd,different,ite_false]
end Backend.Stock.Proof.ScalarCast

namespace Backend.Stock.Proof.ScalarCast
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
def extendOp (sg : Bool) : Clif.ExtendOp := if sg then .sextend else .uextend
section Data
attribute [local semireducible] Isle.Aarch64.program
private theorem source_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (sg : Bool) {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.extend (extendOp sg) ty x)) :
    IW ty.width ∧ info.data = .data 152 29 [.data 151 (extendOpcode sg) [],.value x] ∧
      info.resTys.head? = some (.int ty.width) := by
  have accepted := inv.instE i info _ source clif
  have supported : eTy ty = true := by
    simpa [extendOp,Compile.instE,Compile.tyE,eTy] using accepted
  have raw := inv.data i info _ source clif
  obtain ⟨types,result,typed,len⟩ := inv.resTys i info _ source clif
  simp only [Clif.Inst.resultTypes] at result
  cases result
  refine ⟨?_,?_,by rw [typed]; simp [ofClif_int_width (isInt_of_eTy supported)]⟩
  · cases ty <;> simp [eTy,Clif.Ty.width,IW] at supported ⊢
  · have expected : instData f (.extend (extendOp sg) ty x) = .ok
        (.data 152 29 [.data 151 (extendOpcode sg) [],.value x]) := by
      cases sg <;> simp only [extendOp,extendOpcode,instData,supported,ite_true] <;> rfl
    exact Except.ok.inj (raw.symm.trans expected)
end Data
/-- Missing original operand types cannot produce a successful base extension match. -/
theorem stock_extend_match_no_type {p : Program} (hp : Data p) (ctx : Ctx) (sg : Bool)
    {i x w : Nat} {info : IInfo} (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int w))
    (data : info.data = .data 152 29 [.data 151 (extendOpcode sg) [],.value x])
    (typed : ctx.valueType? x = none) (st next : State) (tr trace : Array RuleId) (m : Nat) (env : Isle.Interp.Env V) :
    (matchRule p (Stock.sem ctx) {} (m+10) (extendRule sg) [.inst i]).run (st,tr) ≠ .ok (some env,next,trace) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  have fits := ext_fits_in_64 ctx st.base w
  have types := ext_value_type_none ctx st.base typed
  by_cases small : w ≤ 64
  all_goals simp only [small,ite_true,ite_false] at fits
  all_goals cases hp
  all_goals cases sg <;> isel_eval [*,extendRule,extendOpcode,rule_lower_1261,rule_lower_1315,sem_extract,sem_unData]
  all_goals intro impossible; cases impossible
end Backend.Stock.Proof.ScalarCast

namespace Backend.Stock.Proof.ScalarCast
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
/-- Actual selected base extension roots derive the canonical match, source
width, guarded request and complete fresh fragment internally. -/
theorem stock_extend_selected_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (sg : Bool) {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.extend (extendOp sg) ty x))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {val : Clif.Val} (lookup : fr.regs x = some val)
    (grows : val.ty.width < ty.width)
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules)
    (chosen : selected.rule = extendRule sg) {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k))) :
    ∃ ρ', out = .regsVec [[.vreg st.base.nextVreg .int]] ∧
      next = {st.mark x with base := (st.base.fresh .int).2.emit (.extend (.vreg st.base.nextVreg .int) ((ctx.valueReg? x).getD .xzr) sg val.ty.width ty.width)} ∧
      PRun F isem [(MInst.extend (.vreg st.base.nextVreg .int) ((ctx.valueReg? x).getD .xzr) sg val.ty.width ty.width).mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      VHolds ⟨ty,extendBits sg ty.width val.bits⟩ (ρ' st.base.nextVreg) ∧
      ∀ n,n ≠ st.base.nextVreg → ρ' n = ρ n := by
  obtain ⟨width,data,type⟩ := source_data inv sg source clif
  have small : ty.width ≤ 64 := by rcases width with h | h | h | h <;> omega
  have enough := selected.fuelBound
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+10 := ⟨selected.matchFuel-10,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq] at matched
  cases typed : ctx.valueType? x with
  | none => exact False.elim (stock_extend_match_no_type data_program ctx sg source type data typed st
      selected.matched #[] selected.matchTrace m selected.env matched)
  | some t =>
    rw [stock_extend_match data_program ctx sg source type data typed st #[] m,if_pos small] at matched
    simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
    obtain ⟨envEq,stateEq,traceEq⟩ := matched
    have rhs := selected.rhsRun
    rw [chosen,← envEq,← stateEq,← traceEq] at rhs
    change (evalExpr program (Stock.sem ctx) {} (999959+40) (extendRule sg).rhs
      (envExt ty.width x t)).run (st,#[]) = .ok (some out,next,selected.rhsTrace) at rhs
    obtain ⟨safe,rx,mapped⟩ := stock_extend_rhs_requests data_program ctx sg rhs
    obtain ⟨nx,rfl⟩ := inv.valueReg x rx mapped
    have typeEq := (dfg.2 x t val typed lookup).symm
    have supported := inv.valTyE x t typed
    rw [typeEq] at supported
    have fromWidths : t.bits = 8 ∨ t.bits = 16 ∨ t.bits = 32 ∨ t.bits = 64 := by
      have accepted := inv.valTyE x t typed
      simp only [eCTys,List.mem_cons,List.not_mem_nil,or_false] at accepted
      rcases accepted with rfl | rfl | rfl | rfl <;> decide +kernel
    have fromEq : val.ty.width = t.bits := by rw [typeEq,ofClif_bits]
    have sourceWidth : val.ty.width = 8 ∨ val.ty.width = 16 ∨ val.ty.width = 32 := by
      rw [fromEq]
      rcases fromWidths with h | h | h | h <;> omega
    have targetWidth : ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64 := by
      rcases sourceWidth with h | h | h <;> rcases width with h' | h' | h' | h' <;> omega
    obtain ⟨trace,forward⟩ := stock_extend_rhs data_program ctx sg mapped st safe #[] 999959 (w := ty.width) (t := t)
    rw [forward] at rhs
    simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at rhs
    obtain ⟨outEq,stateEq,traceEq⟩ := rhs
    have inputHeld : ValuesHeld (fun z => z = x) ctx fr (fun k => ρ (aliasNum aliases k)) := by
      apply held.mono
      intro z same; subst z
      rw [← stateEq,Demanded]
      change (st.mark x).demand[x]! ≠ 0
      rw [(mark_demand st x (extent x _ mapped)).1]
      omega
    obtain ⟨ρ',execution,value,kept⟩ := stock_cast_extend_resolved refines sg sourceWidth targetWidth grows
      bounded mapped inputHeld (bits := val.bits) (by cases val; simp [Clif.Frame.getAs,Clif.Frame.get,lookup,Clif.Val.as?])
    refine ⟨ρ',outEq.symm,?_,?_,value,kept⟩
    · rw [← stateEq,mapped,Option.getD_some,typeEq,ofClif_bits]; rfl
    · simpa only [mapped,Option.getD_some] using execution
end Backend.Stock.Proof.ScalarCast
