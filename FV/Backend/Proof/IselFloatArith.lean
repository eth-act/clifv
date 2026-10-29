module

import FV.Backend.Proof.IselFloatBitcast
public import FV.Backend.Proof.IselFamAluBPopcnt
import FV.Backend.Proof.IselFamAluBShiftTerms
import FV.Backend.Proof.IselCmpTerms
import FV.Backend.Proof.IselCmpBase
import FV.Backend.Proof.IselExtern
import FV.Backend.Proof.IselInterp
import FV.Backend.Proof.FastSubst
import FV.Backend.Proof.IselAttr
import FV.Arm.MinTheory

public section

/-!
# S11f: scalar float arithmetic roots over float-capable contexts

The `lower` roots of the scalar float arithmetic (`lower.isle:485-559`), proven over `CtxInvT`
(`LowerRuleOkT`) against the shared IEEE core: CLIF's `Inst.float` (`Clif.evalFloat`,
`FV/Clif/FSem.lean`) and the Arm instruction the rule emits (`ispecFP`'s `fpu2Val`/`fpu1Val`,
the Arm model's `exec_fp_data_processing_{one,two}_source`) are the same `IEEE` functions with
`FPCR = 0` and rounding to nearest even, so each rule is a statement about one function:

* `fpu_rrr` (`FpuRRR`, `fadd/fsub/fmul/fdiv/fmin/fmax sd, sn, sm` / `… dd, dn, dm`): `fadd` 662
  (`rule_lower_485`), `fsub` 664 (493), `fmul` 666 (501), `fdiv` 668 (509), `fmin` 670 (517),
  `fmax` 672 (525);
* `fpu_rr` (`FpuRR`): `sqrt` 674 (533), `fneg` 676 (541), `fabs` 678 (549) at the result's scalar
  size, `fpromote` 679 (554, `fcvt dd, sn`), `fdemote` 680 (559, `fcvt sd, dn`).

`fcmp` is outside this module: its `instData` arm and root `rule_lower_2176` are S11f's
(`IselFloatCmpEmit`); the theorems here keep the `hop : ∀ cc, op ≠ .fcmp cc` premise.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## Internal terms: `fpu_rrr`, `fpu_rr` -/

section Terms
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

set_option maxHeartbeats 1000000 in
include hp hc in
/-- `fpu_rrr` (`inst.isle:2591`): `MInst.FpuRRR` into a fresh float vreg. -/
theorem fpu_rrr_ok {n : Nat} (hn : 40 ≤ n) {op a b k : V} {st st' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 368 [op, a, b, k] st v st') :
    EmitOutC .float st.1 st'.1 v (fun rd => .data 58 52 [op, k, .reg rd, a, b]) := by
  isel_split hp hc h 368
  isel_inv [*, rule_inst_2591, ctor_emit_iff, ctor_writable_reg_to_reg'] at hm he
  obtain ⟨rfl, rfl⟩ :=
    (ctor_temp_writable_reg_f64_iff ctx _ _ _).mp ‹externCtor ctx T.temp_writable_reg _ _ = _›
  exact ⟨rfl, _, ‹_›, rfl⟩

set_option maxHeartbeats 1000000 in
include hp hc in
/-- `fpu_rr` (`inst.isle:2560`): `MInst.FpuRR` into a fresh float vreg. -/
theorem fpu_rr_ok {n : Nat} (hn : 40 ≤ n) {op a k : V} {st st' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 364 [op, a, k] st v st') :
    EmitOutC .float st.1 st'.1 v (fun rd => .data 58 51 [op, k, .reg rd, a]) := by
  isel_split hp hc h 364
  isel_inv [*, rule_inst_2560, ctor_emit_iff, ctor_writable_reg_to_reg'] at hm he
  obtain ⟨rfl, rfl⟩ :=
    (ctor_temp_writable_reg_f64_iff ctx _ _ _).mp ‹externCtor ctx T.temp_writable_reg _ _ = _›
  exact ⟨rfl, _, ‹_›, rfl⟩

end Terms

/-! ## Instruction data -/

theorem variantNames_Fadd : (variantNames 151)[113]? = some "Fadd" := rfl
theorem variantNames_Fsub : (variantNames 151)[114]? = some "Fsub" := rfl
theorem variantNames_Fmul : (variantNames 151)[115]? = some "Fmul" := rfl
theorem variantNames_Fdiv : (variantNames 151)[116]? = some "Fdiv" := rfl
theorem variantNames_Sqrt : (variantNames 151)[117]? = some "Sqrt" := rfl
theorem variantNames_Fneg : (variantNames 151)[119]? = some "Fneg" := rfl
theorem variantNames_Fabs : (variantNames 151)[120]? = some "Fabs" := rfl
theorem variantNames_Fmin : (variantNames 151)[122]? = some "Fmin" := rfl
theorem variantNames_Fmax : (variantNames 151)[123]? = some "Fmax" := rfl
theorem variantNames_Fpromote : (variantNames 151)[143]? = some "Fpromote" := rfl
theorem variantNames_Fdemote : (variantNames 151)[144]? = some "Fdemote" := rfl

/-- The opcode names of the float operations `instData` builds (`fOpc`). -/
@[expose] def fArithNames : List String :=
  ["Fadd", "Fsub", "Fmul", "Fdiv", "Fmin", "Fmax", "Sqrt", "Fneg", "Fabs", "Fpromote", "Fdemote",
    "Ceil", "Floor", "Trunc", "Nearest"]

/-- An instruction whose opcode name is a float operation's is that float operation. -/
theorem instNames_float {c : Clif.Inst} {s : String} (hs : s ∈ fArithNames)
    (h : (instNames c).2 = s) : ∃ op ty args, c = .float op ty args ∧ fOpc op = s := by
  cases c
  case float op ty args => exact ⟨op, ty, args, rfl, h⟩
  all_goals exfalso
  all_goals subst h
  all_goals simp only [instNames, fArithNames] at hs
  all_goals first
    | (simp at hs; done)
    | (rename_i op _ _; cases op <;> simp [unaryOpcode] at hs; done)
    | (rename_i op _ _ _; cases op <;> simp [binaryOpcode, divOpcode] at hs; done)
    | (rename_i op _ _ _ _; cases op <;> simp [loadOpcode] at hs; done)
    | (rename_i op _ _ _ _ _; cases op <;> simp [storeOpcode] at hs; done)

/-- A matched `Binary` of a float opcode `n` is the two-operand float operation named `n`, at a
type `instData` admits. -/
theorem instData_fbin_inv {f : Clif.Function} {cl : Clif.Inst} {ko : Nat} {fs : List V}
    {op : Clif.FOp} {n : String} (hop : fBinaryOpcode op = some n)
    (hko : (variantNames 151)[ko]? = some n)
    (h : instData f cl = .ok (.data 152 2 (.data 151 ko [] :: fs))) :
    ∃ ty x y, cl = .float op ty [x, y] ∧ fTyOk op ty = true ∧ fs = [.values [x, y]] := by
  obtain ⟨-, ho⟩ := instData_inv_names h
  rw [hko] at ho
  have hn : n ∈ fArithNames := by
    cases op <;> simp [fBinaryOpcode] at hop <;> subst hop <;> decide
  obtain ⟨op', ty, args, rfl, hop'⟩ := instNames_float hn (Option.some.inj ho).symm
  obtain rfl : op' = op := by
    cases op <;> simp [fBinaryOpcode] at hop <;> subst hop <;> cases op' <;> simp [fOpc] at hop' <;>
      rfl
  cases op' <;> simp [fBinaryOpcode] at hop <;> subst hop <;>
    rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;>
    simp only [instData, fBinaryOpcode, fUnaryOpcode, fCvtOpcode, fCvtTyOk, throw, throwThe,
      MonadExceptOf.throw, reduceCtorEq] at h
  all_goals
    split at h
    · rename_i hok
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
      simp only [List.cons.injEq] at h3
      exact ⟨ty, x, y, rfl, hok, h3.2⟩
    · simp only [reduceCtorEq] at h

/-- A matched `Unary` of a float opcode `n` is the one-operand float operation named `n`, at a
type `instData` admits. -/
theorem instData_fun_inv {f : Clif.Function} {cl : Clif.Inst} {ko : Nat} {fs : List V}
    {op : Clif.FOp} {n : String} (hop : fUnaryOpcode op = some n)
    (hko : (variantNames 151)[ko]? = some n)
    (h : instData f cl = .ok (.data 152 29 (.data 151 ko [] :: fs))) :
    ∃ ty x, cl = .float op ty [x] ∧ fTyOk op ty = true ∧ fs = [.value x] := by
  obtain ⟨-, ho⟩ := instData_inv_names h
  rw [hko] at ho
  have hn : n ∈ fArithNames := by
    cases op <;> simp [fUnaryOpcode] at hop <;> subst hop <;> decide
  obtain ⟨op', ty, args, rfl, hop'⟩ := instNames_float hn (Option.some.inj ho).symm
  obtain rfl : op' = op := by
    cases op <;> simp [fUnaryOpcode] at hop <;> subst hop <;> cases op' <;> simp [fOpc] at hop' <;>
      rfl
  cases op' <;> simp [fUnaryOpcode] at hop <;> subst hop <;>
    rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;>
    simp only [instData, fBinaryOpcode, fUnaryOpcode, fCvtOpcode, fCvtTyOk, throw, throwThe,
      MonadExceptOf.throw, reduceCtorEq] at h
  all_goals
    split at h
    · rename_i hok
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
      simp only [List.cons.injEq] at h3
      exact ⟨ty, x, rfl, hok, h3.2⟩
    · simp only [reduceCtorEq] at h

/-- The result type of a float operation (`CtxInvT.resTys`): its controlling type. -/
theorem float_resTy {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {ii : Nat}
    {info : IInfo} {op : Clif.FOp} {ty : Clif.Ty} {args : List Nat}
    (hop : ∀ cc, op ≠ .fcmp cc) (hi : ctx.insts[ii]? = some info)
    (hic : info.clif = some (.float op ty args)) :
    info.resTys.head?.getD .invalid = CTy.ofClif ty := by
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii info _ hi hic
  cases op
  case fcmp cc => exact absurd rfl (hop cc)
  all_goals
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
    subst htys
    rw [hres]; rfl

/-! ## The matched instruction -/

/-- The instruction a two-operand float root matched (`InstructionData::Binary`). -/
theorem fbin_front {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInvT f ctx) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hic : info.clif = some inst) {r : Rule}
    {tyPat xPat yPat : Pattern} {oT : TermId} {to : Term} {ko : Nat} {op : Clif.FOp} {n : String}
    (hargs : r.args = [.term 18 209 [tyPat, .term 152 2449 [.term 151 oT [],
      .term 147 1614 [xPat, yPat]]]])
    (hto : termOf p oT = .ok to) (hko : to.kind = .enumVariant ko)
    (hop : fBinaryOpcode op = some n) (hn : (variantNames 151)[ko]? = some n)
    {cfg : Config} {m : Nat} {s s1 : LState × Array RuleId} {env : Interp.Env V}
    (h : (matchRule p (sem ctx) cfg (m + 1) r [.inst ii]).run s = .ok (some env, s1)) :
    ∃ ty x y, inst = .float op ty [x, y] ∧ fTyOk op ty = true ∧
      info.data = .data 152 2 [.data 151 ko [], .values [x, y]] := by
  obtain ⟨info', fs, hi', hd⟩ := root_match_data hp ctx hargs hp.t2449 term_2449_kind hto hko h
  rw [hi] at hi'
  cases hi'
  have hdat := hctx.data ii info inst hi hic
  rw [hd] at hdat
  obtain ⟨ty, x, y, rfl, hok, rfl⟩ := instData_fbin_inv hop hn hdat
  exact ⟨ty, x, y, rfl, hok, hd⟩

/-- The instruction a one-operand float root matched (`InstructionData::Unary`). -/
theorem fun_front {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInvT f ctx) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hic : info.clif = some inst) {r : Rule}
    {tyPat xPat : Pattern} {oT : TermId} {to : Term} {ko : Nat} {op : Clif.FOp} {n : String}
    (hargs : r.args = [.term 18 209 [tyPat, .term 152 2476 [.term 151 oT [], xPat]]])
    (hto : termOf p oT = .ok to) (hko : to.kind = .enumVariant ko)
    (hop : fUnaryOpcode op = some n) (hn : (variantNames 151)[ko]? = some n)
    {cfg : Config} {m : Nat} {s s1 : LState × Array RuleId} {env : Interp.Env V}
    (h : (matchRule p (sem ctx) cfg (m + 1) r [.inst ii]).run s = .ok (some env, s1)) :
    ∃ ty x, inst = .float op ty [x] ∧ fTyOk op ty = true ∧
      info.data = .data 152 29 [.data 151 ko [], .value x] := by
  obtain ⟨info', fs, hi', hd⟩ := root_match_data hp ctx hargs hp.t2476 term_2476_kind hto hko h
  rw [hi] at hi'
  cases hi'
  have hdat := hctx.data ii info inst hi hic
  rw [hd] at hdat
  obtain ⟨ty, x, rfl, hok, rfl⟩ := instData_fun_inv hop hn hdat
  exact ⟨ty, x, rfl, hok, hd⟩

/-- The matched data is the instruction's (`inst_data_value` returned `info`). -/
theorem fdata_eq {ctx : Ctx} {ii : Nat} {info info' : IInfo} {d w : V}
    (hi : ctx.insts[ii]? = some info) (hd : info.data = d) (hi' : ctx.insts[ii]? = some info')
    (hw : w = info'.data) : info' = info ∧ w = d := by
  rw [hi] at hi'
  cases hi'
  exact ⟨rfl, hw.trans hd⟩

/-! ## CLIF semantics of the operations -/

/-- The `FPUOp2` and scalar size of a two-operand float operation at a type
(`lower.isle:485-525`: `scalar_size ty`). -/
def fpuOp2At : Clif.FOp → Clif.Ty → Option (FPUOp2 × ScalarSize)
  | .fadd, ty => szOf ty |>.map (.add, ·)
  | .fsub, ty => szOf ty |>.map (.sub, ·)
  | .fmul, ty => szOf ty |>.map (.mul, ·)
  | .fdiv, ty => szOf ty |>.map (.div, ·)
  | .fmin, ty => szOf ty |>.map (.min, ·)
  | .fmax, ty => szOf ty |>.map (.max, ·)
  | _, _ => none
where
  /-- The scalar size of a float type. -/
  szOf : Clif.Ty → Option ScalarSize
    | .f32 => some .size32
    | .f64 => some .size64
    | _ => none

/-- The `FPUOp1` and scalar size of a one-operand float operation at a type
(`lower.isle:533-559`): `fsqrt`/`fneg`/`fabs` at the type's size, `fcvt` from the operand's. -/
def fpuOp1At : Clif.FOp → Clif.Ty → Option (FPUOp1 × ScalarSize)
  | .sqrt, ty => fpuOp2At.szOf ty |>.map (.sqrt, ·)
  | .fneg, ty => fpuOp2At.szOf ty |>.map (.neg, ·)
  | .fabs, ty => fpuOp2At.szOf ty |>.map (.abs, ·)
  | .fpromote, .f64 => some (.cvt32To64, .size32)
  | .fdemote, .f32 => some (.cvt64To32, .size64)
  | _, _ => none

theorem val_at_ok {v : Clif.Val} {ty : Clif.Ty} {x : BitVec ty.width} (h : v.at ty = .ok x) :
    v = ⟨ty, x⟩ := by
  obtain ⟨vt, vb⟩ := v
  unfold Clif.Val.at Clif.Val.as? at h
  split at h
  · rename_i e
    subst e
    simp only [Clif.Res.ofOption, Clif.Res.ok.injEq] at h
    subst h
    rfl
  · simp [Clif.Res.ofOption] at h

theorem getMany_two {fr : Clif.Frame} {x y : Nat} {vs : List Clif.Val}
    (h : fr.getMany [x, y] = .ok vs) : ∃ a b, fr.regs x = some a ∧ fr.regs y = some b ∧ vs = [a, b] := by
  simp only [Clif.Frame.getMany, Clif.Frame.get] at h
  cases hx : fr.regs x with
  | none => rw [hx] at h; cases h
  | some a =>
    cases hy : fr.regs y with
    | none => rw [hx, hy] at h; cases h
    | some b =>
      rw [hx, hy] at h
      exact ⟨a, b, rfl, rfl, (Clif.Res.ok.inj h).symm⟩

theorem getMany_one {fr : Clif.Frame} {x : Nat} {vs : List Clif.Val}
    (h : fr.getMany [x] = .ok vs) : ∃ a, fr.regs x = some a ∧ vs = [a] := by
  simp only [Clif.Frame.getMany, Clif.Frame.get] at h
  cases hx : fr.regs x with
  | none => rw [hx] at h; cases h
  | some a =>
    rw [hx] at h
    exact ⟨a, rfl, (Clif.Res.ok.inj h).symm⟩

/-- CLIF `Inst.float`: the operand values, one result, memory unchanged. -/
theorem evalInst_float_ok {fr : Clif.Frame} {cm cm' : Clif.Mem} {op : Clif.FOp} {ty : Clif.Ty}
    {args : List Nat} {vals : List Clif.Val}
    (h : Clif.evalInst fr cm (.float op ty args) = .ok (vals, cm')) :
    ∃ vs r, fr.getMany args = .ok vs ∧ Clif.evalFloat op ty vs = .ok r ∧ vals = [r] ∧ cm' = cm := by
  simp only [Clif.evalInst] at h
  cases hv : fr.getMany args with
  | ok vs =>
    simp only [hv, bind, Clif.Res.bind] at h
    cases hr : Clif.evalFloat op ty vs with
    | ok r =>
      simp only [hr, pure, Clif.Res.ok.injEq, Prod.mk.injEq] at h
      exact ⟨vs, r, rfl, hr, h.1.symm, h.2.symm⟩
    | trap _ => simp [hr] at h
    | stuck _ => simp [hr] at h
  | trap _ => simp [hv, bind, Clif.Res.bind] at h
  | stuck _ => simp [hv, bind, Clif.Res.bind] at h

theorem vholds_f32' (a : BitVec 32) : VHolds ⟨.f32, a⟩ (a.setWidth 128) := by
  show (a.setWidth 128).setWidth 32 = a
  rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]

theorem vholds_f64' (a : BitVec 64) : VHolds ⟨.f64, a⟩ (a.setWidth 128) := by
  show (a.setWidth 128).setWidth 64 = a
  rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]

/-- **A two-operand float operation is the `FpuRRR` the rule emits**: on register values
holding the operands, `fpu2Out` holds CLIF's result. -/
theorem fbin_holds {op : Clif.FOp} {ty : Clif.Ty} {o : FPUOp2} {sz : ScalarSize}
    (hat : fpuOp2At op ty = some (o, sz)) {a b r : Clif.Val} {za zb : CV} (ha : VHolds a za)
    (hb : VHolds b zb) (h : Clif.evalFloat op ty [a, b] = .ok r) :
    ∃ z, fpu2Out o sz za zb = some z ∧ VHolds r z := by
  cases op <;> simp only [fpuOp2At, reduceCtorEq, Option.map_eq_some_iff, Prod.mk.injEq] at hat
  all_goals
    obtain ⟨sz', hsz, rfl, rfl⟩ := hat
    cases ty <;> simp only [fpuOp2At.szOf, reduceCtorEq, Option.some.injEq] at hsz <;> subst hsz <;>
      simp only [Clif.evalFloat, Clif.FSem.binary, bind, Clif.Res.bind] at h
    all_goals
      cases ha' : a.at _ with
      | ok xa =>
        rw [ha'] at h
        cases hb' : b.at _ with
        | ok xb =>
          rw [hb'] at h
          obtain rfl := val_at_ok ha'
          obtain rfl := val_at_ok hb'
          simp only [Clif.FSem.lift2, Clif.Res.ofOption, pure, Clif.Res.ok.injEq] at h
          subst h
          first
            | (have ha2 : za.setWidth 32 = xa := ha
               have hb2 : zb.setWidth 32 = xb := hb
               refine ⟨_, rfl, ?_⟩
               show VHolds _ ((fpu2Val _ .b32 (za.setWidth 32) (zb.setWidth 32)).setWidth 128)
               rw [ha2, hb2]
               exact vholds_f32' _)
            | (have ha2 : za.setWidth 64 = xa := ha
               have hb2 : zb.setWidth 64 = xb := hb
               refine ⟨_, rfl, ?_⟩
               show VHolds _ ((fpu2Val _ .b64 (za.setWidth 64) (zb.setWidth 64)).setWidth 128)
               rw [ha2, hb2]
               exact vholds_f64' _)
        | trap _ => rw [hb'] at h; cases h
        | stuck _ => rw [hb'] at h; cases h
      | trap _ => rw [ha'] at h; cases h
      | stuck _ => rw [ha'] at h; cases h

/-- **A one-operand float operation is the `FpuRR` the rule emits**: on a register value holding
the operand, `fpu1Val` holds CLIF's result. -/
theorem fun_holds {op : Clif.FOp} {ty : Clif.Ty} {o : FPUOp1} {sz : ScalarSize}
    (hat : fpuOp1At op ty = some (o, sz)) {a r : Clif.Val} {za : CV} (ha : VHolds a za)
    (h : Clif.evalFloat op ty [a] = .ok r) : ∃ z, fpu1Val o sz za = some z ∧ VHolds r z := by
  cases op <;> cases ty <;>
    simp only [fpuOp1At, fpuOp2At.szOf, reduceCtorEq, Option.map_some, Option.map_none,
      Option.some.injEq, Prod.mk.injEq] at hat <;> obtain ⟨rfl, rfl⟩ := hat <;>
    simp only [Clif.evalFloat, Clif.FSem.unary, bind, Clif.Res.bind, beq_self_eq_true,
      ↓reduceIte] at h
  all_goals
    first
      | (cases ha' : a.at .f32 with
         | ok xa =>
           obtain rfl := val_at_ok ha'
           simp only [ha', Clif.FSem.lift1, Clif.Res.ofOption, pure, Clif.Res.ok.injEq] at h
           subst h
           have ha2 : za.setWidth 32 = xa := ha
           refine ⟨_, rfl, ?_⟩
           first
             | (show VHolds _ ((IEEE.convert .b32 .b64 .rne (za.setWidth 32)).setWidth 128)
                rw [ha2]; exact vholds_f64' _)
             | (show VHolds _ ((IEEE.sqrt .b32 .rne (za.setWidth 32)).setWidth 128)
                rw [ha2]; exact vholds_f32' _)
             | (show VHolds _ ((IEEE.neg .b32 (za.setWidth 32)).setWidth 128)
                rw [ha2]; exact vholds_f32' _)
             | (show VHolds _ ((IEEE.abs .b32 (za.setWidth 32)).setWidth 128)
                rw [ha2]; exact vholds_f32' _)
         | trap _ => simp [ha'] at h
         | stuck _ => simp [ha'] at h)
      | (cases ha' : a.at .f64 with
         | ok xa =>
           obtain rfl := val_at_ok ha'
           simp only [ha', Clif.FSem.lift1, Clif.Res.ofOption, pure, Clif.Res.ok.injEq] at h
           subst h
           have ha2 : za.setWidth 64 = xa := ha
           refine ⟨_, rfl, ?_⟩
           first
             | (show VHolds _ ((IEEE.convert .b64 .b32 .rne (za.setWidth 64)).setWidth 128)
                rw [ha2]; exact vholds_f32' _)
             | (show VHolds _ ((IEEE.sqrt .b64 .rne (za.setWidth 64)).setWidth 128)
                rw [ha2]; exact vholds_f64' _)
             | (show VHolds _ ((IEEE.neg .b64 (za.setWidth 64)).setWidth 128)
                rw [ha2]; exact vholds_f64' _)
             | (show VHolds _ ((IEEE.abs .b64 (za.setWidth 64)).setWidth 128)
                rw [ha2]; exact vholds_f64' _)
         | trap _ => simp [ha'] at h
         | stuck _ => simp [ha'] at h)

/-! ## `LowerInstOk` of the emitted instruction -/

/-- **`LowerInstOk` of a two-operand float operation lowered to `FpuRRR`** into the fresh vreg
`st.nextVreg`. -/
theorem lowerInstOk_fbin {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} {ctx : Ctx} {op : Clif.FOp} {ty : Clif.Ty} {x y : Nat} {o : FPUOp2}
    {sz : ScalarSize} (hat : fpuOp2At op ty = some (o, sz)) {cx cy : RegClass}
    {results : List Nat} {st : LState} (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerInstOk isem MR env cp ctx (.float op ty [x, y]) results st [[.vreg st.nextVreg .float]]
      ((st.fresh .float).2.emit (.fpuRRR o sz (.vreg st.nextVreg .float) (.vreg x cx) (.vreg y cy)))
      [.fpuRRR o sz (.vreg st.nextVreg .float) (.vreg x cx) (.vreg y cy)] := by
  refine lowerInstOk_one_c hMR (by simp [LState.emit, LState.fresh]) ?_ rfl ?_
  · intro mi hmi e he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmi
    subst hmi
    have hv : vdefs (.fpuRRR o sz (.vreg st.nextVreg .float) (.vreg x cx) (.vreg y cy)) =
      [st.nextVreg] := rfl
    rw [hv, List.mem_singleton] at he
    subst he
    simp [LState.emit, LState.fresh]
  · intro fr cm ρ vals cm' _ hvals _ ho
    have ho' : Clif.evalInst fr cm (.float op ty [x, y]) = .ok (vals, cm') := ho
    obtain ⟨vs, r, hv, hr, rfl, rfl⟩ := evalInst_float_ok ho'
    obtain ⟨a, b, hx, hy, rfl⟩ := getMany_two hv
    obtain ⟨z, hz, hrz⟩ := fbin_holds hat (hvals x a hx) (hvals y b hy) hr
    refine ⟨rfl, ?_, .inl (Nat.le_refl _), r, upd ρ st.nextVreg z, rfl,
      prun_rrr_c (r := z) hR rfl (fun w => ?_) (prun_nil _), ?_⟩
    · refine usesOk_of [x, y] ?_ (by simp [hx, hy])
      intro mi hmi u hu
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmi
      subst hmi
      have hu' : vuseNums (.fpuRRR o sz (.vreg st.nextVreg .float) (.vreg x cx) (.vreg y cy)) =
        [x, y] := rfl
      rw [hu'] at hu
      exact .inr hu
    · first
        | (show ispecFP (.fpuRRR o sz (.vreg st.nextVreg .float) (.vreg x cx) (.vreg y cy))
            [ρ x, ρ y] w = _
           simp only [ispecFP, hz, Option.map_some]
           rfl)
        | (simp only [ispec, ispecFP, hz, Option.map_some]; rfl)
    · simp only [upd, ↓reduceIte]
      exact hrz

/-- **`LowerInstOk` of a one-operand float operation lowered to `FpuRR`** into the fresh vreg
`st.nextVreg`. -/
theorem lowerInstOk_fun {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} {ctx : Ctx} {op : Clif.FOp} {ty : Clif.Ty} {x : Nat} {o : FPUOp1}
    {sz : ScalarSize} (hat : fpuOp1At op ty = some (o, sz)) {cx : RegClass}
    {results : List Nat} {st : LState} (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerInstOk isem MR env cp ctx (.float op ty [x]) results st [[.vreg st.nextVreg .float]]
      ((st.fresh .float).2.emit (.fpuRR o sz (.vreg st.nextVreg .float) (.vreg x cx)))
      [.fpuRR o sz (.vreg st.nextVreg .float) (.vreg x cx)] := by
  refine lowerInstOk_one_c hMR (by simp [LState.emit, LState.fresh]) ?_ rfl ?_
  · intro mi hmi e he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmi
    subst hmi
    have hv : vdefs (.fpuRR o sz (.vreg st.nextVreg .float) (.vreg x cx)) = [st.nextVreg] := rfl
    rw [hv, List.mem_singleton] at he
    subst he
    simp [LState.emit, LState.fresh]
  · intro fr cm ρ vals cm' _ hvals _ ho
    have ho' : Clif.evalInst fr cm (.float op ty [x]) = .ok (vals, cm') := ho
    obtain ⟨vs, r, hv, hr, rfl, rfl⟩ := evalInst_float_ok ho'
    obtain ⟨a, hx, rfl⟩ := getMany_one hv
    obtain ⟨z, hz, hrz⟩ := fun_holds hat (hvals x a hx) hr
    refine ⟨rfl, ?_, .inl (Nat.le_refl _), r, upd ρ st.nextVreg z, rfl,
      prun_rr_c (r := z) hR rfl (fun w => ?_) (prun_nil _), ?_⟩
    · refine usesOk_of [x] ?_ (by simp [hx])
      intro mi hmi u hu
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmi
      subst hmi
      have hu' : vuseNums (.fpuRR o sz (.vreg st.nextVreg .float) (.vreg x cx)) = [x] := rfl
      rw [hu'] at hu
      exact .inr hu
    · first
        | (show ispecFP (.fpuRR o sz (.vreg st.nextVreg .float) (.vreg x cx)) [ρ x] w = _
           simp only [ispecFP, hz, Option.map_some]
           rfl)
        | (simp only [ispec, ispecFP, hz, Option.map_some]; rfl)
    · simp only [upd, ↓reduceIte]
      exact hrz

/-! ## The right-hand sides -/

/-- The variant index of an `FPUOp2` (`inst.isle`'s order). -/
def fpuOp2Idx : FPUOp2 → Nat
  | .add => 0 | .sub => 1 | .mul => 2 | .div => 3 | .max => 4 | .min => 5

/-- The variant index of an `FPUOp1` (`inst.isle`'s order). -/
def fpuOp1Idx : FPUOp1 → Nat
  | .abs => 0 | .neg => 1 | .sqrt => 2 | .cvt32To64 => 3 | .cvt64To32 => 4

/-- The `FpuRRR` an `fpu_rrr` of size index `s` emitted. -/
theorem ofV_fpuRRR {o : FPUOp2} {s : Nat} {sz : ScalarSize}
    (hs : (s = 2 ∧ sz = .size32) ∨ (s = 3 ∧ sz = .size64)) {rd rn rm : Reg} {m : MInst}
    (h : MInst.ofV (.data 58 52 [.data 99 (fpuOp2Idx o) [], .data 95 s [], .reg rd, .reg rn,
      .reg rm]) = some m) : m = .fpuRRR o sz rd rn rm := by
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases o <;> exact Option.some.inj (h.symm.trans rfl)

/-- The `FpuRR` an `fpu_rr` of size index `s` emitted. -/
theorem ofV_fpuRR {o : FPUOp1} {s : Nat} {sz : ScalarSize}
    (hs : (s = 2 ∧ sz = .size32) ∨ (s = 3 ∧ sz = .size64)) {rd rn : Reg} {m : MInst}
    (h : MInst.ofV (.data 58 51 [.data 98 (fpuOp1Idx o) [], .data 95 s [], .reg rd, .reg rn]) =
      some m) : m = .fpuRR o sz rd rn := by
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases o <;> exact Option.some.inj (h.symm.trans rfl)

theorem fpuOp2At_cases {op : Clif.FOp} {ty : Clif.Ty} {o : FPUOp2} {sz : ScalarSize}
    (hat : fpuOp2At op ty = some (o, sz)) : (ty = .f32 ∧ sz = .size32) ∨ (ty = .f64 ∧ sz = .size64) := by
  cases op <;> cases ty <;> simp [fpuOp2At, fpuOp2At.szOf] at hat <;> simp [hat]

theorem fpuOp1At_cases {op : Clif.FOp} {ty : Clif.Ty} {o : FPUOp1} {sz : ScalarSize}
    (hat : fpuOp1At op ty = some (o, sz)) (hop : op ≠ .fpromote ∧ op ≠ .fdemote) :
    (ty = .f32 ∧ sz = .size32) ∨ (ty = .f64 ∧ sz = .size64) := by
  cases op <;> cases ty <;> simp [fpuOp1At, fpuOp2At.szOf] at hat hop <;> simp [hat]

/-- At a type `instData` admits, a two-operand float operation has its `FPUOp2` at a size. -/
theorem fpuOp2At_ok {op : Clif.FOp} {ty : Clif.Ty} (hok : fTyOk op ty = true) {o : FPUOp2}
    (ho : fpuOp2At op .f32 = some (o, .size32)) : ∃ sz, fpuOp2At op ty = some (o, sz) := by
  cases op <;> cases ty <;> simp_all [fTyOk, fpuOp2At, fpuOp2At.szOf, Clif.Ty.isFloat]

/-- At a type `instData` admits, `sqrt`/`fneg`/`fabs` have their `FPUOp1` at a size. -/
theorem fpuOp1At_ok {op : Clif.FOp} {ty : Clif.Ty} (hok : fTyOk op ty = true) {o : FPUOp1}
    (ho : fpuOp1At op .f32 = some (o, .size32)) : ∃ sz, fpuOp1At op ty = some (o, sz) := by
  cases op <;> cases ty <;> simp_all [fTyOk, fpuOp1At, fpuOp2At.szOf, Clif.Ty.isFloat]

set_option maxHeartbeats 4000000 in
/-- **The right-hand side of a two-operand float root** (`output_reg (fpu_rrr op (put_in_reg x)
(put_in_reg y) (scalar_size ty))`), from the facts the inversion of its match and evaluation
leaves. -/
theorem fbin_rhs {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem) (hMR : MRStable F MR)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {cfg : Config}
    (hco : cfg.checkOverlap = false) {ii : Nat} {info w : IInfo} (hi : ctx.insts[ii]? = some info)
    {op : Clif.FOp} {ty : Clif.Ty} {x y : Nat} (hic : info.clif = some (.float op ty [x, y]))
    {o : FPUOp2} {sz : ScalarSize} (hat : fpuOp2At op ty = some (o, sz)) {ko : Nat}
    (hd : info.data = .data 152 2 [.data 151 ko [], .values [x, y]])
    {n1 n2 n3 : Nat} (hn1 : 40 ≤ n1) (hn2 : 40 ≤ n2) (hn3 : 40 ≤ n3)
    {st st' : LState} {tr tr' : Array RuleId} {out w11 w9 w8 w6 w3 w2 w1 : V}
    {w10 w4 : LState × Array RuleId} {w7 w5 : LState}
    (h172 : ApplyInternal p (sem ctx) cfg n1 25 172 [w11] w10 out (st', tr'))
    (h368 : ApplyInternal p (sem ctx) cfg n2 27 368 [.data 99 (fpuOp2Idx o) [], w9, w8, w6] w4 w11
      w10)
    (hva : externExtract ctx T.value_array_2 w3 st = .ok [w2, w1])
    (hi' : ctx.insts[ii]? = some w) (hw : V.data 152 2 [.data 151 ko [], w3] = w.data)
    (hpx : externCtor ctx T.put_in_reg [w2] st = .ok (w9, w7))
    (hpy : externCtor ctx T.put_in_reg [w1] w7 = .ok (w8, w5))
    (h307 : ApplyInternal p (sem ctx) cfg n3 95 307 [.ty (w.resTys.head?.getD .invalid)] (w5, tr)
      w6 w4) :
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx (.float op ty [x, y]) info.results st rss st' ms := by
  obtain ⟨hwi, hw3⟩ := fdata_eq hi hd hi' hw
  subst w
  simp only [V.data.injEq, List.cons.injEq, true_and, and_true] at hw3
  subst hw3
  rw [ext_value_array_2_iff] at hva
  simp only [List.cons.injEq, and_true] at hva
  obtain ⟨rfl, rfl⟩ := hva
  obtain ⟨rx, hrx, rfl, h7⟩ := (ctor_put_in_reg_iff ctx _ x _ _).mp hpx
  subst w7
  obtain ⟨ry, hry, rfl, h5⟩ := (ctor_put_in_reg_iff ctx _ y _ _).mp hpy
  subst w5
  obtain rfl := hctx.valueReg x rx hrx
  obtain rfl := hctx.valueReg y ry hry
  rw [float_resTy hctx (fun cc h => by subst h; simp [fpuOp2At] at hat) hi hic] at h307
  have hfin : ∀ (s : Nat), ((s = 2 ∧ sz = .size32) ∨ (s = 3 ∧ sz = .size64)) →
      w6 = .data 95 s [] → w4.1 = st →
      ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
        LowerInstOk isem MR env cp ctx (.float op ty [x, y]) info.results st rss st' ms := by
    intro s hs hw6 hs1
    subst hw6
    obtain ⟨w4s, w4t⟩ := w4
    simp only at hs1
    subst hs1
    obtain ⟨rfl, m1, hm1, hs2⟩ := fpu_rrr_ok hp hco hn2 h368
    obtain ⟨rfl, hs3⟩ := output_reg_ok hp hco hn1 h172
    simp only at hs2 hs3 hm1
    rw [hs2] at hs3
    subst hs3
    obtain rfl := ofV_fpuRRR hs hm1
    refine ⟨[.fpuRRR o sz (.vreg w4s.nextVreg .float) (.vreg x (valClassOf ctx x))
      (.vreg y (valClassOf ctx y))], [[.vreg w4s.nextVreg .float]], ?_, rfl,
      lowerInstOk_fbin hat hR hMR⟩
    simp [LState.emit, LState.fresh]
  rcases fpuOp2At_cases hat with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨h6, hs1⟩ := scalar_size_float_ok hp hco hn3 (.inl rfl) h307
    exact hfin 2 (.inl ⟨rfl, rfl⟩) h6 hs1
  · obtain ⟨h6, hs1⟩ := scalar_size_float_ok hp hco hn3 (.inr rfl) h307
    exact hfin 3 (.inr ⟨rfl, rfl⟩) h6 hs1

set_option maxHeartbeats 4000000 in
/-- The end of a one-operand float root's right-hand side: `output_reg (fpu_rr op x' size)` with
the operand's register `x'` and the size index `s` known. -/
theorem fun_core {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem) (hMR : MRStable F MR)
    {ctx : Ctx} {cfg : Config} (hco : cfg.checkOverlap = false) {results : List Nat}
    {op : Clif.FOp} {ty : Clif.Ty} {x : Nat} {o : FPUOp1} {sz : ScalarSize}
    (hat : fpuOp1At op ty = some (o, sz)) {s : Nat}
    (hs : (s = 2 ∧ sz = .size32) ∨ (s = 3 ∧ sz = .size64)) {n1 n2 : Nat} (hn1 : 40 ≤ n1)
    (hn2 : 40 ≤ n2) {st st' : LState} {tr' : Array RuleId} {out w7 : V}
    {w6 w2 : LState × Array RuleId}
    (h172 : ApplyInternal p (sem ctx) cfg n1 25 172 [w7] w6 out (st', tr'))
    (h364 : ApplyInternal p (sem ctx) cfg n2 27 364
      [.data 98 (fpuOp1Idx o) [], .reg (.vreg x (valClassOf ctx x)), .data 95 s []] w2 w7 w6)
    (hs1 : w2.1 = st) :
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx (.float op ty [x]) results st rss st' ms := by
  obtain ⟨w2s, w2t⟩ := w2
  simp only at hs1
  subst hs1
  obtain ⟨rfl, m1, hm1, hs2⟩ := fpu_rr_ok hp hco hn2 h364
  obtain ⟨rfl, hs3⟩ := output_reg_ok hp hco hn1 h172
  simp only at hs2 hs3 hm1
  rw [hs2] at hs3
  subst hs3
  obtain rfl := ofV_fpuRR hs hm1
  refine ⟨[.fpuRR o sz (.vreg w2s.nextVreg .float) (.vreg x (valClassOf ctx x))],
    [[.vreg w2s.nextVreg .float]], ?_, rfl, lowerInstOk_fun hat hR hMR⟩
  simp [LState.emit, LState.fresh]

set_option maxHeartbeats 4000000 in
/-- **The right-hand side of `sqrt`/`fneg`/`fabs`** (`output_reg (fpu_rr op (put_in_reg x)
(scalar_size ty))`), from the facts the inversion of its match and evaluation leaves. -/
theorem fun_rhs {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem) (hMR : MRStable F MR)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {cfg : Config}
    (hco : cfg.checkOverlap = false) {ii : Nat} {info w : IInfo} (hi : ctx.insts[ii]? = some info)
    {op : Clif.FOp} {ty : Clif.Ty} {x : Nat} (hic : info.clif = some (.float op ty [x]))
    (hop : op ≠ .fpromote ∧ op ≠ .fdemote)
    {o : FPUOp1} {sz : ScalarSize} (hat : fpuOp1At op ty = some (o, sz)) {ko : Nat}
    (hd : info.data = .data 152 29 [.data 151 ko [], .value x])
    {n1 n2 n3 : Nat} (hn1 : 40 ≤ n1) (hn2 : 40 ≤ n2) (hn3 : 40 ≤ n3)
    {st st' : LState} {tr tr' : Array RuleId} {out w7 w5 w4 w1 : V}
    {w6 w2 : LState × Array RuleId} {w3 : LState}
    (h172 : ApplyInternal p (sem ctx) cfg n1 25 172 [w7] w6 out (st', tr'))
    (h364 : ApplyInternal p (sem ctx) cfg n2 27 364 [.data 98 (fpuOp1Idx o) [], w5, w4] w2 w7 w6)
    (hi' : ctx.insts[ii]? = some w) (hw : V.data 152 29 [.data 151 ko [], w1] = w.data)
    (hpx : externCtor ctx T.put_in_reg [w1] st = .ok (w5, w3))
    (h307 : ApplyInternal p (sem ctx) cfg n3 95 307 [.ty (w.resTys.head?.getD .invalid)] (w3, tr)
      w4 w2) :
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx (.float op ty [x]) info.results st rss st' ms := by
  obtain ⟨hwi, hw1⟩ := fdata_eq hi hd hi' hw
  subst w
  simp only [V.data.injEq, List.cons.injEq, true_and, and_true] at hw1
  subst hw1
  obtain ⟨rx, hrx, rfl, h3⟩ := (ctor_put_in_reg_iff ctx _ x _ _).mp hpx
  subst w3
  obtain rfl := hctx.valueReg x rx hrx
  rw [float_resTy hctx (fun cc h => by subst h; simp [fpuOp1At] at hat) hi hic] at h307
  rcases fpuOp1At_cases hat hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨rfl, hs1⟩ := scalar_size_float_ok hp hco hn3 (.inl rfl) h307
    exact fun_core hp hR hMR hco hat (.inl ⟨rfl, rfl⟩) hn1 hn2 h172 h364 hs1
  · obtain ⟨rfl, hs1⟩ := scalar_size_float_ok hp hco hn3 (.inr rfl) h307
    exact fun_core hp hR hMR hco hat (.inr ⟨rfl, rfl⟩) hn1 hn2 h172 h364 hs1

set_option maxHeartbeats 4000000 in
/-- **The right-hand side of `fpromote`/`fdemote`** (`output_reg (fpu_rr cvt (put_in_reg x)
size)`, the operand's size a constant), from the facts the inversion leaves. -/
theorem fcvt_rhs {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem) (hMR : MRStable F MR)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {cfg : Config}
    (hco : cfg.checkOverlap = false) {ii : Nat} {info w : IInfo} (hi : ctx.insts[ii]? = some info)
    {op : Clif.FOp} {ty : Clif.Ty} {x : Nat} {o : FPUOp1} {sz : ScalarSize}
    (hat : fpuOp1At op ty = some (o, sz)) {s : Nat}
    (hs : (s = 2 ∧ sz = .size32) ∨ (s = 3 ∧ sz = .size64)) {ko : Nat}
    (hd : info.data = .data 152 29 [.data 151 ko [], .value x])
    {n1 n2 : Nat} (hn1 : 40 ≤ n1) (hn2 : 40 ≤ n2)
    {st st' : LState} {tr tr' : Array RuleId} {out w5 w3 w1 : V}
    {w4 : LState × Array RuleId} {w2 : LState}
    (h172 : ApplyInternal p (sem ctx) cfg n1 25 172 [w5] w4 out (st', tr'))
    (h364 : ApplyInternal p (sem ctx) cfg n2 27 364 [.data 98 (fpuOp1Idx o) [], w3, .data 95 s []]
      (w2, tr) w5 w4)
    (hi' : ctx.insts[ii]? = some w) (hw : V.data 152 29 [.data 151 ko [], w1] = w.data)
    (hpx : externCtor ctx T.put_in_reg [w1] st = .ok (w3, w2)) :
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx (.float op ty [x]) info.results st rss st' ms := by
  obtain ⟨hwi, hw1⟩ := fdata_eq hi hd hi' hw
  subst w
  simp only [V.data.injEq, List.cons.injEq, true_and, and_true] at hw1
  subst hw1
  obtain ⟨rx, hrx, rfl, h2⟩ := (ctor_put_in_reg_iff ctx _ x _ _).mp hpx
  subst w2
  obtain rfl := hctx.valueReg x rx hrx
  exact fun_core hp hR hMR hco hat hs hn1 hn2 h172 h364 rfl

/-! ## The eleven roots -/

set_option hygiene false in
/-- A two-operand float root (`fadd`..`fmax`): `fbin_front` (the matched instruction), the
inversion of the match and evaluation, `fbin_rhs`. Arguments: the opcode term's data fact and
kind, the CLIF operation, the opcode name fact, the `FPUOp2`. -/
macro "fbin_root " ht:term:max hk:term:max op:term:max hn:term:max o:term:max : tactic =>
  `(tactic| (
    intro f ctx hctx ii info inst hi hic _ cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch
      heval
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
    obtain ⟨N, rfl⟩ : ∃ N, n = N + 100 := ⟨n - 100, by omega⟩
    obtain ⟨ty, x, y, rfl, hok, hd⟩ := fbin_front hp hctx hi hic rfl $ht $hk (op := $op) rfl $hn
      (m := m' + 9) hmatch
    obtain ⟨sz, hat⟩ := fpuOp2At_ok hok (o := $o) rfl
    have hp' := hp
    isel_inv' hp [] at hmatch heval
    have h1 := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
    have h2 := ‹ApplyInternal _ _ _ _ 27 368 _ _ _ _›
    have h3 := ‹ApplyInternal _ _ _ _ 95 307 _ _ _ _›
    have h4 := ‹externExtract ctx T.value_array_2 _ _ = _›
    obtain ⟨ms, rss, e1, e2, e3⟩ := fbin_rhs hp' hR hMR hctx hco hi hic hat hd
      (by omega) (by omega) (by omega) h1 h2 h4 (by assumption) (by assumption)
      (by assumption) (by assumption) h3
    exact ⟨ms, e1, rss, e2, e3⟩))

set_option hygiene false in
/-- `sqrt`/`fneg`/`fabs`: `fun_front`, the inversion, `fun_rhs`. -/
macro "fun_root " ht:term:max hk:term:max op:term:max hn:term:max o:term:max : tactic =>
  `(tactic| (
    intro f ctx hctx ii info inst hi hic _ cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch
      heval
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
    obtain ⟨N, rfl⟩ : ∃ N, n = N + 100 := ⟨n - 100, by omega⟩
    obtain ⟨ty, x, rfl, hok, hd⟩ := fun_front hp hctx hi hic rfl $ht $hk (op := $op) rfl $hn
      (m := m' + 9) hmatch
    obtain ⟨sz, hat⟩ := fpuOp1At_ok hok (o := $o) rfl
    have hp' := hp
    isel_inv' hp [] at hmatch heval
    have h1 := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
    have h2 := ‹ApplyInternal _ _ _ _ 27 364 _ _ _ _›
    have h3 := ‹ApplyInternal _ _ _ _ 95 307 _ _ _ _›
    obtain ⟨ms, rss, e1, e2, e3⟩ := fun_rhs hp' hR hMR hctx hco hi hic ⟨by simp, by simp⟩ hat hd
      (by omega) (by omega) (by omega) h1 h2 (by assumption) (by assumption) (by assumption) h3
    exact ⟨ms, e1, rss, e2, e3⟩))

set_option hygiene false in
/-- `fpromote`/`fdemote`: `fun_front`, the inversion, `fcvt_rhs`. Arguments as `fun_root` (the
`FPUOp1` a conversion), then the result type and the operand's size index. -/
macro "fcvt_root " ht:term:max hk:term:max op:term:max hn:term:max o:term:max t:term:max
    s:term:max : tactic =>
  `(tactic| (
    intro f ctx hctx ii info inst hi hic _ cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch
      heval
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
    obtain ⟨N, rfl⟩ : ∃ N, n = N + 100 := ⟨n - 100, by omega⟩
    obtain ⟨ty, x, rfl, hok, hd⟩ := fun_front hp hctx hi hic rfl $ht $hk (op := $op) rfl $hn
      (m := m' + 9) hmatch
    obtain rfl : ty = $t := by
      cases ty <;> first | rfl | (simp [fTyOk] at hok)
    have hp' := hp
    isel_inv' hp [] at hmatch heval
    have h1 := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
    have h2 := ‹ApplyInternal _ _ _ _ 27 364 _ _ _ _›
    obtain ⟨ms, rss, e1, e2, e3⟩ := fcvt_rhs hp' hR hMR hctx hco hi (op := $op) (ty := $t) (o := $o)
      rfl $s hd
      (by omega) (by omega) h1 h2 (by assumption) (by assumption) (by assumption)
    exact ⟨ms, e1, rss, e2, e3⟩))

section Roots
variable {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem} (MR : MemRelT)
  (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR)
include hp hR hMR

set_option maxHeartbeats 8000000 in
/-- **`fadd` of `f32`/`f64`** (`rule_lower_485`, `lower.isle:485`): `fadd sd/dd`. -/
theorem fadd_okT : LowerRuleOkT isem MR env cp p rule_lower_485 := by
  fbin_root hp.t2397 term_2397_kind .fadd variantNames_Fadd .add

set_option maxHeartbeats 8000000 in
/-- **`fsub` of `f32`/`f64`** (`rule_lower_493`, `lower.isle:493`): `fsub sd/dd`. -/
theorem fsub_okT : LowerRuleOkT isem MR env cp p rule_lower_493 := by
  fbin_root hp.t2398 term_2398_kind .fsub variantNames_Fsub .sub

set_option maxHeartbeats 8000000 in
/-- **`fmul` of `f32`/`f64`** (`rule_lower_501`, `lower.isle:501`): `fmul sd/dd`. -/
theorem fmul_okT : LowerRuleOkT isem MR env cp p rule_lower_501 := by
  fbin_root hp.t2399 term_2399_kind .fmul variantNames_Fmul .mul

set_option maxHeartbeats 8000000 in
/-- **`fdiv` of `f32`/`f64`** (`rule_lower_509`, `lower.isle:509`): `fdiv sd/dd`. -/
theorem fdiv_okT : LowerRuleOkT isem MR env cp p rule_lower_509 := by
  fbin_root hp.t2400 term_2400_kind .fdiv variantNames_Fdiv .div

set_option maxHeartbeats 8000000 in
/-- **`fmin` of `f32`/`f64`** (`rule_lower_517`, `lower.isle:517`): `fmin sd/dd` (`FPMin`). -/
theorem fmin_okT : LowerRuleOkT isem MR env cp p rule_lower_517 := by
  fbin_root hp.t2406 term_2406_kind .fmin variantNames_Fmin .min

set_option maxHeartbeats 8000000 in
/-- **`fmax` of `f32`/`f64`** (`rule_lower_525`, `lower.isle:525`): `fmax sd/dd` (`FPMax`). -/
theorem fmax_okT : LowerRuleOkT isem MR env cp p rule_lower_525 := by
  fbin_root hp.t2407 term_2407_kind .fmax variantNames_Fmax .max

set_option maxHeartbeats 8000000 in
/-- **`sqrt` of `f32`/`f64`** (`rule_lower_533`, `lower.isle:533`): `fsqrt sd/dd`. -/
theorem sqrt_okT : LowerRuleOkT isem MR env cp p rule_lower_533 := by
  fun_root hp.t2401 term_2401_kind .sqrt variantNames_Sqrt .sqrt

set_option maxHeartbeats 8000000 in
/-- **`fneg` of `f32`/`f64`** (`rule_lower_541`, `lower.isle:541`): `fneg sd/dd`. -/
theorem fneg_okT : LowerRuleOkT isem MR env cp p rule_lower_541 := by
  fun_root hp.t2403 term_2403_kind .fneg variantNames_Fneg .neg

set_option maxHeartbeats 8000000 in
/-- **`fabs` of `f32`/`f64`** (`rule_lower_549`, `lower.isle:549`): `fabs sd/dd`. -/
theorem fabs_okT : LowerRuleOkT isem MR env cp p rule_lower_549 := by
  fun_root hp.t2404 term_2404_kind .fabs variantNames_Fabs .abs

set_option maxHeartbeats 8000000 in
/-- **`fpromote.f64`** (`rule_lower_554`, `lower.isle:554`): `fcvt dd, sn`. -/
theorem fpromote_okT : LowerRuleOkT isem MR env cp p rule_lower_554 := by
  fcvt_root hp.t2427 term_2427_kind .fpromote variantNames_Fpromote .cvt32To64 .f64
    (.inl ⟨rfl, rfl⟩)

set_option maxHeartbeats 8000000 in
/-- **`fdemote.f32`** (`rule_lower_559`, `lower.isle:559`): `fcvt sd, dn`. -/
theorem fdemote_okT : LowerRuleOkT isem MR env cp p rule_lower_559 := by
  fcvt_root hp.t2428 term_2428_kind .fdemote variantNames_Fdemote .cvt64To32 .f32
    (.inr ⟨rfl, rfl⟩)

end Roots

end Backend.Proof
