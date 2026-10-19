import FV.Opt.Proof.InterpProv
import FV.Opt.Proof.RulesProv
import FV.Isle.Opt.Simplify

/-!
# The exported Cranelift rule sets meet the provenance obligations (M1, #24)

`simpRulesProv_isle` / `skelRulesProv_isle`: `Isle.Opt.simplify` and `Isle.Opt.simplifySkeleton`
(the exported ISLE program run by the interpreter, with any rule allow-list) satisfy
`SimpRulesProv` / `SkelRulesProv` (`FV/Opt/Proof/RulesProv.lean`).

Proof: an instance of the generic value invariant of the interpreter (`runMultiTerm_prov`,
`FV/Opt/Proof/InterpProv.lean`), for any program. "Good" is the deep predicate `VQ (Q s) QB`
on ISLE values: every CLIF value it mentions is in `Q s`, every block call is one of `QB` with
arguments in `Q s`, every skeleton instruction satisfies `SkelInstQ`. The embedding
`Isle.Opt.sem` keeps it: nodes are presented with their operands (`EnodesIn`), `make_inst`
builds nodes over good values (`MakeQ`), and the pure extern helpers return integers, booleans,
types, trap codes, their arguments repackaged, or block calls of a good jump table. The rule
data itself is never inspected.
-/

namespace Opt

open Clif Isle Isle.Opt Isle.Interp Opt.Proof

/-- A block call whose target is one of `QB` and whose arguments are in `Qv`. -/
def BCQ (Qv : ValueId → Prop) (QB : BlockCall → Prop) (b : BlockCall) : Prop :=
  QB b ∧ ∀ y ∈ b.args, Qv y

/-- Every CLIF value an ISLE value mentions is in `Qv`, every block call is a `BCQ` one, and
every skeleton instruction satisfies `SkelInstQ`. -/
inductive VQ (Qv : ValueId → Prop) (QB : BlockCall → Prop) : Isle.Opt.V → Prop
  | int (i : Int) : VQ Qv QB (.int i)
  | bool (b : Bool) : VQ Qv QB (.bool b)
  | ty (t : CTy) : VQ Qv QB (.ty t)
  | value (n : Nat) : Qv n → VQ Qv QB (.value n)
  | poison (t : CTy) : VQ Qv QB (.poison t)
  | values (vs : List Isle.Opt.V) : (∀ v ∈ vs, VQ Qv QB v) → VQ Qv QB (.values vs)
  | pair (t : CTy) (d : Isle.Opt.V) : VQ Qv QB d → VQ Qv QB (.pair t d)
  | data (ty : TypeId) (k : Nat) (fs : List Isle.Opt.V) : (∀ v ∈ fs, VQ Qv QB v) →
      VQ Qv QB (.data ty k fs)
  | instNone : VQ Qv QB (.inst none)
  | instSome (i : SkelInst) : SkelInstQ Qv QB i → VQ Qv QB (.inst (some i))
  | trapCode (c : TrapCode) : VQ Qv QB (.trapCode c)
  | blockCall (b : BlockCall) : BCQ Qv QB b → VQ Qv QB (.blockCall b)
  | jumpTable (d : BlockCall) (tbl : List BlockCall) : BCQ Qv QB d → (∀ b ∈ tbl, BCQ Qv QB b) →
      VQ Qv QB (.jumpTable d tbl)

section
variable {Qv Qv' : ValueId → Prop} {QB : BlockCall → Prop}

@[simp] theorem vq_int {i : Int} : VQ Qv QB (.int i) ↔ True := ⟨fun _ => trivial, fun _ => .int i⟩
@[simp] theorem vq_bool {b : Bool} : VQ Qv QB (.bool b) ↔ True :=
  ⟨fun _ => trivial, fun _ => .bool b⟩
@[simp] theorem vq_ty {t : CTy} : VQ Qv QB (.ty t) ↔ True := ⟨fun _ => trivial, fun _ => .ty t⟩
@[simp] theorem vq_value {n : Nat} : VQ Qv QB (.value n) ↔ Qv n :=
  ⟨fun h => by cases h; assumption, .value n⟩
@[simp] theorem vq_poison {t : CTy} : VQ Qv QB (.poison t) ↔ True :=
  ⟨fun _ => trivial, fun _ => .poison t⟩
@[simp] theorem vq_values {vs : List Isle.Opt.V} : VQ Qv QB (.values vs) ↔ ∀ v ∈ vs, VQ Qv QB v :=
  ⟨fun h => by cases h; assumption, .values vs⟩
@[simp] theorem vq_pair {t : CTy} {d : Isle.Opt.V} : VQ Qv QB (.pair t d) ↔ VQ Qv QB d :=
  ⟨fun h => by cases h; assumption, .pair t d⟩
@[simp] theorem vq_data {ty : TypeId} {k : Nat} {fs : List Isle.Opt.V} :
    VQ Qv QB (.data ty k fs) ↔ ∀ v ∈ fs, VQ Qv QB v :=
  ⟨fun h => by cases h; assumption, .data ty k fs⟩
@[simp] theorem vq_instNone : VQ Qv QB (.inst none) ↔ True := ⟨fun _ => trivial, fun _ => .instNone⟩
@[simp] theorem vq_instSome {i : SkelInst} : VQ Qv QB (.inst (some i)) ↔ SkelInstQ Qv QB i :=
  ⟨fun h => by cases h; assumption, .instSome i⟩
@[simp] theorem vq_trapCode {c : TrapCode} : VQ Qv QB (.trapCode c) ↔ True :=
  ⟨fun _ => trivial, fun _ => .trapCode c⟩
@[simp] theorem vq_blockCall {b : BlockCall} : VQ Qv QB (.blockCall b) ↔ BCQ Qv QB b :=
  ⟨fun h => by cases h; assumption, .blockCall b⟩
@[simp] theorem vq_jumpTable {d : BlockCall} {tbl : List BlockCall} :
    VQ Qv QB (.jumpTable d tbl) ↔ BCQ Qv QB d ∧ ∀ b ∈ tbl, BCQ Qv QB b :=
  ⟨fun h => by cases h; constructor <;> assumption, fun h => .jumpTable d tbl h.1 h.2⟩

theorem BCQ.mono (h : ∀ x, Qv x → Qv' x) {b : BlockCall} (hb : BCQ Qv QB b) : BCQ Qv' QB b :=
  ⟨hb.1, fun y hy => h y (hb.2 y hy)⟩

theorem SkelInstQ.mono (h : ∀ x, Qv x → Qv' x) {i : SkelInst} (hi : SkelInstQ Qv QB i) :
    SkelInstQ Qv' QB i := by
  cases i with
  | inst i => exact fun y hy => h y (hi y hy)
  | term t => exact ⟨fun y hy => h y (hi.1 y hy), hi.2⟩

theorem VQ.mono (h : ∀ x, Qv x → Qv' x) {v : Isle.Opt.V} (hv : VQ Qv QB v) : VQ Qv' QB v := by
  induction hv with
  | int => exact .int _
  | bool => exact .bool _
  | ty => exact .ty _
  | value n hn => exact .value n (h n hn)
  | poison => exact .poison _
  | values vs _ ih => exact .values vs ih
  | pair t d _ ih => exact .pair t d ih
  | data ty k fs _ ih => exact .data ty k fs ih
  | instNone => exact .instNone
  | instSome i hi => exact .instSome i (hi.mono h)
  | trapCode => exact .trapCode _
  | blockCall b hb => exact .blockCall b (hb.mono h)
  | jumpTable d tbl hd ht => exact .jumpTable d tbl (hd.mono h) fun b hb => (ht b hb).mono h

/-! ## The embedding's data conversions -/

theorem ofInst_good {i : Inst} {d : Isle.Opt.V} (hi : ∀ y ∈ operands i, Qv y)
    (h : ofInst i = some d) : VQ Qv QB d := by
  unfold ofInst at h
  split at h <;> (try cases h) <;> simp_all [operands, idata, opcode, cc]

theorem toInst_good {tf : Nat → Option Ty} {ty : CTy} {d : Isle.Opt.V} {i : Inst}
    (hd : VQ Qv QB d) (h : toInst tf ty d = some i) : ∀ y ∈ operands i, Qv y := by
  unfold toInst at h
  repeat' split at h
  all_goals first
    | (cases h <;> simp_all [operands])
    | (obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h; simp_all [operands])

theorem ofSkel_good {i : SkelInst} {d : Isle.Opt.V} (hi : SkelInstQ Qv QB i)
    (h : ofSkel i = some d) : VQ Qv QB d := by
  unfold ofSkel at h
  split at h <;> (try cases h) <;>
    simp_all [SkelInstQ, BCQ, operands, termOperands, termCalls, idata, opcode] <;>
    exact fun b hb y hy => hi.1.2 y (.inr ⟨b, hb, hy⟩)

theorem toSkel_good {d : Isle.Opt.V} {i : SkelInst} (hd : VQ Qv QB d) (h : toSkel d = some i) :
    SkelInstQ Qv QB i := by
  unfold toSkel at h
  repeat' split at h
  all_goals first
    | (cases h <;> simp_all [SkelInstQ, BCQ, operands, termOperands, termCalls, or_imp, forall_and])

theorem vq_inst_toSkel {d : Isle.Opt.V} (hd : VQ Qv QB d) : VQ Qv QB (.inst (toSkel d)) := by
  cases hs : toSkel d with
  | none => exact .instNone
  | some i => exact .instSome i (toSkel_good hd hs)

theorem skelSimp?_good {w : Isle.Opt.V} {ss : SkelSimp} (hw : VQ Qv QB w)
    (h : skelSimp? w = some ss) : SkelSimpQ Qv QB ss := by
  unfold skelSimp? at h
  repeat' split at h
  all_goals first
    | (cases h <;> simp_all [SkelSimpQ])

theorem bcq_getD {d : BlockCall} {tbl : List BlockCall} (k : Nat) (hd : BCQ Qv QB d)
    (ht : ∀ b ∈ tbl, BCQ Qv QB b) : BCQ Qv QB ((tbl[k]?).getD d) := by
  cases h : tbl[k]? with
  | none => exact hd
  | some b => exact ht b (List.mem_of_getElem? h)

end

/-! ## The extern helpers -/

/-- A `dite` equation as a disjunction (used to take the compiled string match of `ctorPure`
apart without generating its 96-alternative splitter). -/
theorem dite_eq_iff' {α : Type} {c : Prop} [d : Decidable c] {t : c → α} {e : ¬c → α} {r : α} :
    dite c t e = r ↔ (∃ hc, t hc = r) ∨ (∃ hc, e hc = r) := by
  cases d with
  | isFalse hc =>
    exact ⟨fun h => .inr ⟨hc, h⟩, fun h => h.elim (fun ⟨h1, _⟩ => absurd h1 hc) fun ⟨_, h2⟩ => h2⟩
  | isTrue hc =>
    exact ⟨fun h => .inl ⟨hc, h⟩, fun h => h.elim (fun ⟨_, h2⟩ => h2) fun ⟨h1, _⟩ => absurd hc h1⟩

/-- Evaluate the `Except` computation on the left of the hypothesis `h : x = .ok r` as far as
it goes, splitting on every match. -/
local macro "exc_norm " h:ident : tactic => `(tactic| repeat' (first
  | (simp only [bind, Except.bind, pure, Except.pure, panics, throw, throwThe,
      MonadExceptOf.throw, Except.ok.injEq, Option.some.injEq, reduceCtorEq] at $h:ident)
  | split at $h:ident))

section
variable {σ : Type} (G : EGraph σ) {Qv : ValueId → Prop} {QB : BlockCall → Prop}

theorem ctorPure_good {fn : String} {args : List Isle.Opt.V} {st : St σ} {v : Isle.Opt.V}
    (ha : ∀ a ∈ args, VQ Qv QB a) (h : ctorPure G fn args st = .ok (some v)) : VQ Qv QB v := by
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, rest⟩⟩⟩⟩⟩ <;>
  · unfold ctorPure at h
    delta Isle.Opt.ctorPure.match_5 at h
    dsimp only [V.beqList._sparseCasesOn_1, V.beqList._sparseCasesOn_2] at h
    simp (config := { maxSteps := 100000000 }) only [dite_eq_iff'] at h
    repeat (obtain ⟨hc, h⟩ | ⟨_, h⟩ := h; rotate_left)
    all_goals (try subst hc)
    all_goals (try dsimp only at h)
    all_goals exc_norm h
    all_goals first
      | (subst h; simp_all [dcm, cc])
      | (obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h; simp_all [dcm, cc])
      | (subst h; exact vq_inst_toSkel (ha _ (by simp)))
      | skip

end

end Opt
