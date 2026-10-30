import FV.Opt.Proof.RuleInfraIcmp
import FV.Opt.Proof.RuleRestEmbedSshr
import FV.Opt.Proof.RuleRestEmbedRotl
import FV.Opt.Proof.RuleRestEmbedRotr
import FV.Opt.Proof.RuleSpaceshipUnsigned
import FV.Opt.Proof.RuleSpaceshipSigned

/-! Shared graph semantics of the two spaceship RHS forms. Type queries may fail;
poison results and exceptions do not produce a returned e-class. -/

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000
set_option Elab.async false

namespace Opt.Proof
open Isle Isle.Opt Clif
attribute [local implicit_reducible] Ty.width

private theorem spaceship_toInst_poison_left
    (tf : Nat → Option Ty) (t : Ty) (k op : Nat) (a : CTy) (y : V) :
    toInst tf (CTy.ofClif t) (.data 53 2 [.data k op [], .values [.poison a, y]]) = none := by
  cases t <;> rfl

private theorem spaceship_toInst_poison_right
    (tf : Nat → Option Ty) (t : Ty) (k op : Nat) (x : V) (a : CTy) :
    toInst tf (CTy.ofClif t) (.data 53 2 [.data k op [], .values [x, .poison a]]) = none := by
  cases t <;> cases x <;> rfl

private theorem spaceship_toInst_sub
    (tf : Nat → Option Ty) (t : Ty) (k x y : Nat) :
    toInst tf (CTy.ofClif t) (.data 53 2 [.data k 74 [], .values [.value x, .value y]]) =
      some (.binary .isub t x y) := by
  cases t <;> rfl

private theorem spaceship_toInst_poison_unary
    (tf : Nat → Option Ty) (t : Ty) (k op : Nat) (a : CTy) :
    toInst tf (CTy.ofClif t)
      (.data 53 VIdx.InstructionData.Unary [.data k op [], .poison a]) = none := by
  cases t <;> rfl

private theorem spaceship_extract_poison
    {σ : Type} (G : Isle.Opt.EGraph σ) (s : St σ) (t : CTy) :
    extractFn G "value_type" (.poison t) s = .ok (some [.ty t]) := rfl

private theorem spaceship_throw {ε α : Type} (e : ε) :
    (throw e : Except ε α) = Except.error e := rfl

attribute [local opt_monad ↓] spaceship_toInst_poison_left spaceship_toInst_poison_right
  spaceship_toInst_sub spaceship_toInst_poison_unary
attribute [local opt_monad] spaceship_extract_poison spaceship_throw

open Lean Meta Elab Tactic in
elab "spaceship_close_error " h:ident : tactic => withMainContext do
  let some ld := (← getLCtx).findFromUserName? h.getId | throwError "missing hypothesis"
  let some (_, lhs, rhs) := ld.type.eq? | throwError "not an equation"
  unless lhs.isAppOfArity ``Except.error 3 && rhs.isAppOfArity ``Except.ok 3 do
    throwError "not an impossible result"
  evalTactic (← `(tactic| cases $h:ident))

open Lean Meta Elab Tactic in
elab "spaceship_typeof " h:ident : tactic => withMainContext do
  let some ld := (← getLCtx).findFromUserName? h.getId | throwError "missing hypothesis"
  let ty ← instantiateMVars ld.type
  let some e := ty.find? fun e => e.isAppOfArity ``Isle.Opt.EGraph.typeOf 4 && !e.hasLooseBVars
    | throwError "no closed typeOf query"
  for fact in ← getLCtx do
    let ft ← instantiateMVars fact.type
    if ft.isAppOfArity ``Eq 3 && ft.getAppArgs[1]! == e then
      let hs ← Term.exprToSyntax (mkFVar fact.fvarId)
      evalTactic (← `(tactic| simp only [$hs:term] at $h:ident))
      return
  evalTactic (← `(tactic| opt_split_typeof $h:ident))

open Lean Elab Tactic in
elab "spaceship_noinfo " t:tacticSeq : tactic =>
  withEnableInfoTree false (evalTactic t)

set_option hygiene false in
macro "spaceship_rhs_eval" : tactic => `(tactic| (
  opt_norm hev
  repeat' (first
    | spaceship_close_error hev
    | (spaceship_typeof hev <;> (try opt_types_x) <;>
        try opt_norm hev [except_throw_bind', except_error_bind'])
    | (opt_split_ite hev <;>
        try opt_norm hev [except_throw_bind', except_error_bind'])
    | (opt_unfold hev
       opt_norm hev [except_throw_bind', except_error_bind']))
  all_goals rule_rhs_y))

set_option hygiene false in
macro "spaceship_rhs_proof " r:ident : tactic => `(tactic| (
  spaceship_noinfo
    have hle1 := Valuation.le_refl (den s3.inner)
    have hle3 := Valuation.le_refl (den s3.inner)
    unfold $r:ident at hev
    dsimp only at hev
    spaceship_rhs_eval
    all_goals opt_some_subst
    all_goals try opt_den_subst
    all_goals try opt_val_ty_subst
    all_goals try simp only [beq_iff_eq] at *
    all_goals subst_vars
    all_goals try dsimp only
    all_goals apply GraphOk.make_val hG (by opt_P)
    all_goals opt_node_x
    all_goals opt_cases_ty
    all_goals try contradiction
    all_goals try (first | apply val_congr | apply some_val_congr)
    all_goals try simp (disch := decide) only [Ty.width, spaceship_u_bits, spaceship_s_bits, Sem.binary, Sem.isub,
      Sem.sextend, BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_eq]
    all_goals try decide
))

-- The ISLE comparison type argument describes the result, not the operands.
-- Keep it independent of the width established by their valuations.
/-- The unsigned RHS evaluates to the sign-extended difference of its comparison flags. -/
theorem spaceship_rhs_unsigned {p : Isle.Program} (hd : Data p)
    {σ : Type} (G : Isle.Opt.EGraph σ) (P : σ → Prop) (den : σ → Valuation)
    (fr : Frame) (mem : Mem) (hG : GraphOk G P den fr mem)
    (s3 : St σ) (outTy cmpTy inTy : Ty) (x y : Nat) (a b : BitVec inTy.width)
    (hP3 : P s3.inner)
    (n : Nat) (tr3 : Array RuleId) (ws : List V) (s4 : St σ) (tr4 : Array RuleId)
    (hev : (Isle.Interp.evalExprN p (sem G) cfg (n + 1000) rule_spaceship_25.rhs
      (Array.setIfInBounds
        (Array.setIfInBounds
          (Array.setIfInBounds
            ((Array.replicate 4 (none : Option V)).setIfInBounds 0 (some (V.ty (CTy.ofClif outTy))))
            1 (some (V.ty (CTy.ofClif cmpTy))))
          2 (some (V.value x)))
        3 (some (V.value y)))).run
          (s3, tr3) = .ok (ws, (s4, tr4)))
    (ha : den s3.inner x = some ⟨inTy, a⟩)
    (hb : den s3.inner y = some ⟨inTy, b⟩)
    (m : Nat) (hm : V.value m ∈ ws) :
    den s4.inner m = some ⟨outTy, Sem.sextend outTy.width (spaceship_u_bits a b)⟩ := by
  spaceship_rhs_proof rule_spaceship_25

/-- The signed RHS evaluates to the sign-extended difference of its comparison flags. -/
theorem spaceship_rhs_signed {p : Isle.Program} (hd : Data p)
    {σ : Type} (G : Isle.Opt.EGraph σ) (P : σ → Prop) (den : σ → Valuation)
    (fr : Frame) (mem : Mem) (hG : GraphOk G P den fr mem)
    (s3 : St σ) (outTy cmpTy inTy : Ty) (x y : Nat) (a b : BitVec inTy.width)
    (hP3 : P s3.inner)
    (n : Nat) (tr3 : Array RuleId) (ws : List V) (s4 : St σ) (tr4 : Array RuleId)
    (hev : (Isle.Interp.evalExprN p (sem G) cfg (n + 1000) rule_spaceship_90.rhs
      (Array.setIfInBounds
        (Array.setIfInBounds
          (Array.setIfInBounds
            ((Array.replicate 4 (none : Option V)).setIfInBounds 0 (some (V.ty (CTy.ofClif outTy))))
            1 (some (V.ty (CTy.ofClif cmpTy))))
          2 (some (V.value x)))
        3 (some (V.value y)))).run
          (s3, tr3) = .ok (ws, (s4, tr4)))
    (ha : den s3.inner x = some ⟨inTy, a⟩)
    (hb : den s3.inner y = some ⟨inTy, b⟩)
    (m : Nat) (hm : V.value m ∈ ws) :
    den s4.inner m = some ⟨outTy, Sem.sextend outTy.width (spaceship_s_bits a b)⟩ := by
  spaceship_rhs_proof rule_spaceship_90

-- Both poison operand positions, a valid subtraction and a poison extension are inhabited.
example : toInst (fun _ => none) (CTy.ofClif .i8)
    (.data 53 2 [.data 52 74 [], .values [.poison (CTy.ofClif .i8), .value 0]]) = none := rfl
example : toInst (fun _ => none) (CTy.ofClif .i8)
    (.data 53 2 [.data 52 74 [], .values [.value 0, .poison (CTy.ofClif .i8)]]) = none := rfl
example : toInst (fun _ => none) (CTy.ofClif .i64)
    (.data 53 2 [.data 52 74 [], .values [.value 0, .value 1]]) =
      some (.binary .isub .i64 0 1) := rfl
example : toInst (fun _ => none) (CTy.ofClif .i32)
    (.data 53 VIdx.InstructionData.Unary [.data 52 0 [], .poison (CTy.ofClif .i8)]) = none := rfl
-- A poison value carries its type even when the graph has no type information.
example : extractFn ({
      enodes := fun _ _ => []
      typeOf := fun _ _ => none
      make := fun s _ => (0, s) } : Isle.Opt.EGraph Unit)
    "value_type" (.poison (CTy.ofClif .i32)) { inner := () } =
      .ok (some [.ty (CTy.ofClif .i32)]) := rfl
example : (throw "missing type" : Except String Nat) = .error "missing type" := rfl
-- All three RHS outcomes, including widening and the equal-width arm.
example : Sem.sextend 64 (spaceship_u_bits (0#8) 1) = BitVec.allOnes 64 ∧
    Sem.sextend 8 (spaceship_u_bits (7#8) 7) = 0 ∧
    Sem.sextend 128 (spaceship_u_bits (255#8) 0) = 1 := by decide
example : Sem.sextend 64 (spaceship_s_bits (128#8) 127) = BitVec.allOnes 64 ∧
    Sem.sextend 8 (spaceship_s_bits (255#8) 255) = 0 ∧
    Sem.sextend 128 (spaceship_s_bits (127#8) 128) = 1 := by decide

end Opt.Proof
