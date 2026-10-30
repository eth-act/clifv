import FV.Opt.Proof.RuleIcmpComposeEval
import FV.Opt.Proof.RuleRestEmbedSshr
import FV.Opt.Proof.RuleRestEmbedRotl
import FV.Opt.Proof.RuleRestEmbedRotr

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000
set_option Elab.async false

namespace Opt.Proof
open Isle Isle.Opt Clif
attribute [local implicit_reducible] Ty.width

set_option hygiene false in
local macro "compose_rhs_proof" : tactic => `(tactic| (
  have hle1 := Valuation.le_refl (den s3.inner)
  have hle3 := Valuation.le_refl (den s3.inner)
  rule_rhs_c [Rust.band64, Rust.bor64, Rust.asU64, Rust.asI64, BitVec.reduceOfInt,
    BitVec.reduceAnd, BitVec.reduceOr, BitVec.reduceToNat, BitVec.reduceToInt,
    Int.reduceNatCast, Int.reduceNatCast', Int.reduceOfNat, Int.reduceBEq, Int.reduceBNe,
    Bool.false_beq, Bool.true_beq, Bool.not_true, Bool.not_false,
    Interp.matchAll.eq_1, Interp.matchAll.eq_2]
  all_goals opt_some_subst
  all_goals try opt_den_subst
  all_goals (apply GraphOk.make_val hG (by opt_P); opt_node)
  all_goals rfl))

/-- Semantics of `compose_icmp` for relation mask 0. The ISLE result type is i8;
its operand type is independently determined by the graph valuations. -/
theorem compose_rhs_false {p : Isle.Program} (hd : Data p)
    {σ : Type} {G : Isle.Opt.EGraph σ} {P : σ → Prop} {den : σ → Valuation}
    {fr : Frame} {mem : Mem} (hG : GraphOk G P den fr mem)
    {s3 : St σ} {inTy : Ty} {x y : Nat} {a b : BitVec inTy.width}
    (hP3 : P s3.inner) {signed : Bool}
    {n : Nat} {tr3 : Array RuleId} {ws : List V} {s4 : St σ} {tr4 : Array RuleId}
    (hev : (Isle.Interp.applyTermN p (sem G) cfg (n + 64) 15 251
      [V.ty (CTy.ofClif .i8), V.int 0, V.bool signed, V.value x, V.value y]).run
        (s3, tr3) = .ok (ws, (s4, tr4)))
    (ha : den s3.inner x = some ⟨inTy, a⟩)
    (hb : den s3.inner y = some ⟨inTy, b⟩)
    {m : Nat} (hm : V.value m ∈ ws) :
    den s4.inner m = some ⟨.i8, 0#8⟩ := by
  compose_rhs_proof

/-- Semantics of `compose_icmp` for relation mask 1. The ISLE result type is i8;
its operand type is independently determined by the graph valuations. -/
theorem compose_rhs_eq {p : Isle.Program} (hd : Data p)
    {σ : Type} {G : Isle.Opt.EGraph σ} {P : σ → Prop} {den : σ → Valuation}
    {fr : Frame} {mem : Mem} (hG : GraphOk G P den fr mem)
    {s3 : St σ} {inTy : Ty} {x y : Nat} {a b : BitVec inTy.width}
    (hP3 : P s3.inner) {signed : Bool}
    {n : Nat} {tr3 : Array RuleId} {ws : List V} {s4 : St σ} {tr4 : Array RuleId}
    (hev : (Isle.Interp.applyTermN p (sem G) cfg (n + 64) 15 251
      [V.ty (CTy.ofClif .i8), V.int 1, V.bool signed, V.value x, V.value y]).run
        (s3, tr3) = .ok (ws, (s4, tr4)))
    (ha : den s3.inner x = some ⟨inTy, a⟩)
    (hb : den s3.inner y = some ⟨inTy, b⟩)
    {m : Nat} (hm : V.value m ∈ ws) :
    den s4.inner m = some ⟨.i8, Sem.icmp .eq a b⟩ := by
  compose_rhs_proof

/-- Semantics of `compose_icmp` for relation mask 2. The ISLE result type is i8;
its operand type is independently determined by the graph valuations. -/
theorem compose_rhs_lt {p : Isle.Program} (hd : Data p)
    {σ : Type} {G : Isle.Opt.EGraph σ} {P : σ → Prop} {den : σ → Valuation}
    {fr : Frame} {mem : Mem} (hG : GraphOk G P den fr mem)
    {s3 : St σ} {inTy : Ty} {x y : Nat} {a b : BitVec inTy.width}
    (hP3 : P s3.inner) {signed : Bool}
    {n : Nat} {tr3 : Array RuleId} {ws : List V} {s4 : St σ} {tr4 : Array RuleId}
    (hev : (Isle.Interp.applyTermN p (sem G) cfg (n + 64) 15 251
      [V.ty (CTy.ofClif .i8), V.int 2, V.bool signed, V.value x, V.value y]).run
        (s3, tr3) = .ok (ws, (s4, tr4)))
    (ha : den s3.inner x = some ⟨inTy, a⟩)
    (hb : den s3.inner y = some ⟨inTy, b⟩)
    {m : Nat} (hm : V.value m ∈ ws) :
    den s4.inner m = some ⟨.i8, Sem.icmp (if signed then .slt else .ult) a b⟩ := by
  cases signed <;> compose_rhs_proof

/-- Semantics of `compose_icmp` for relation mask 3. The ISLE result type is i8;
its operand type is independently determined by the graph valuations. -/
theorem compose_rhs_le {p : Isle.Program} (hd : Data p)
    {σ : Type} {G : Isle.Opt.EGraph σ} {P : σ → Prop} {den : σ → Valuation}
    {fr : Frame} {mem : Mem} (hG : GraphOk G P den fr mem)
    {s3 : St σ} {inTy : Ty} {x y : Nat} {a b : BitVec inTy.width}
    (hP3 : P s3.inner) {signed : Bool}
    {n : Nat} {tr3 : Array RuleId} {ws : List V} {s4 : St σ} {tr4 : Array RuleId}
    (hev : (Isle.Interp.applyTermN p (sem G) cfg (n + 64) 15 251
      [V.ty (CTy.ofClif .i8), V.int 3, V.bool signed, V.value x, V.value y]).run
        (s3, tr3) = .ok (ws, (s4, tr4)))
    (ha : den s3.inner x = some ⟨inTy, a⟩)
    (hb : den s3.inner y = some ⟨inTy, b⟩)
    {m : Nat} (hm : V.value m ∈ ws) :
    den s4.inner m = some ⟨.i8, Sem.icmp (if signed then .sle else .ule) a b⟩ := by
  cases signed <;> compose_rhs_proof

/-- Semantics of `compose_icmp` for relation mask 4. The ISLE result type is i8;
its operand type is independently determined by the graph valuations. -/
theorem compose_rhs_gt {p : Isle.Program} (hd : Data p)
    {σ : Type} {G : Isle.Opt.EGraph σ} {P : σ → Prop} {den : σ → Valuation}
    {fr : Frame} {mem : Mem} (hG : GraphOk G P den fr mem)
    {s3 : St σ} {inTy : Ty} {x y : Nat} {a b : BitVec inTy.width}
    (hP3 : P s3.inner) {signed : Bool}
    {n : Nat} {tr3 : Array RuleId} {ws : List V} {s4 : St σ} {tr4 : Array RuleId}
    (hev : (Isle.Interp.applyTermN p (sem G) cfg (n + 64) 15 251
      [V.ty (CTy.ofClif .i8), V.int 4, V.bool signed, V.value x, V.value y]).run
        (s3, tr3) = .ok (ws, (s4, tr4)))
    (ha : den s3.inner x = some ⟨inTy, a⟩)
    (hb : den s3.inner y = some ⟨inTy, b⟩)
    {m : Nat} (hm : V.value m ∈ ws) :
    den s4.inner m = some ⟨.i8, Sem.icmp (if signed then .sgt else .ugt) a b⟩ := by
  cases signed <;> compose_rhs_proof

/-- Semantics of `compose_icmp` for relation mask 5. The ISLE result type is i8;
its operand type is independently determined by the graph valuations. -/
theorem compose_rhs_ge {p : Isle.Program} (hd : Data p)
    {σ : Type} {G : Isle.Opt.EGraph σ} {P : σ → Prop} {den : σ → Valuation}
    {fr : Frame} {mem : Mem} (hG : GraphOk G P den fr mem)
    {s3 : St σ} {inTy : Ty} {x y : Nat} {a b : BitVec inTy.width}
    (hP3 : P s3.inner) {signed : Bool}
    {n : Nat} {tr3 : Array RuleId} {ws : List V} {s4 : St σ} {tr4 : Array RuleId}
    (hev : (Isle.Interp.applyTermN p (sem G) cfg (n + 64) 15 251
      [V.ty (CTy.ofClif .i8), V.int 5, V.bool signed, V.value x, V.value y]).run
        (s3, tr3) = .ok (ws, (s4, tr4)))
    (ha : den s3.inner x = some ⟨inTy, a⟩)
    (hb : den s3.inner y = some ⟨inTy, b⟩)
    {m : Nat} (hm : V.value m ∈ ws) :
    den s4.inner m = some ⟨.i8, Sem.icmp (if signed then .sge else .uge) a b⟩ := by
  cases signed <;> compose_rhs_proof

/-- Semantics of `compose_icmp` for relation mask 6. The ISLE result type is i8;
its operand type is independently determined by the graph valuations. -/
theorem compose_rhs_ne {p : Isle.Program} (hd : Data p)
    {σ : Type} {G : Isle.Opt.EGraph σ} {P : σ → Prop} {den : σ → Valuation}
    {fr : Frame} {mem : Mem} (hG : GraphOk G P den fr mem)
    {s3 : St σ} {inTy : Ty} {x y : Nat} {a b : BitVec inTy.width}
    (hP3 : P s3.inner) {signed : Bool}
    {n : Nat} {tr3 : Array RuleId} {ws : List V} {s4 : St σ} {tr4 : Array RuleId}
    (hev : (Isle.Interp.applyTermN p (sem G) cfg (n + 64) 15 251
      [V.ty (CTy.ofClif .i8), V.int 6, V.bool signed, V.value x, V.value y]).run
        (s3, tr3) = .ok (ws, (s4, tr4)))
    (ha : den s3.inner x = some ⟨inTy, a⟩)
    (hb : den s3.inner y = some ⟨inTy, b⟩)
    {m : Nat} (hm : V.value m ∈ ws) :
    den s4.inner m = some ⟨.i8, Sem.icmp .ne a b⟩ := by
  compose_rhs_proof

/-- Semantics of `compose_icmp` for relation mask 7. The ISLE result type is i8;
its operand type is independently determined by the graph valuations. -/
theorem compose_rhs_true {p : Isle.Program} (hd : Data p)
    {σ : Type} {G : Isle.Opt.EGraph σ} {P : σ → Prop} {den : σ → Valuation}
    {fr : Frame} {mem : Mem} (hG : GraphOk G P den fr mem)
    {s3 : St σ} {inTy : Ty} {x y : Nat} {a b : BitVec inTy.width}
    (hP3 : P s3.inner) {signed : Bool}
    {n : Nat} {tr3 : Array RuleId} {ws : List V} {s4 : St σ} {tr4 : Array RuleId}
    (hev : (Isle.Interp.applyTermN p (sem G) cfg (n + 64) 15 251
      [V.ty (CTy.ofClif .i8), V.int 7, V.bool signed, V.value x, V.value y]).run
        (s3, tr3) = .ok (ws, (s4, tr4)))
    (ha : den s3.inner x = some ⟨inTy, a⟩)
    (hb : den s3.inner y = some ⟨inTy, b⟩)
    {m : Nat} (hm : V.value m ∈ ws) :
    den s4.inner m = some ⟨.i8, 1#8⟩ := by
  compose_rhs_proof

end Opt.Proof
