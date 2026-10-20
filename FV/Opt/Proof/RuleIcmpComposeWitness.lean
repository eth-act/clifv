import FV.Opt.Proof.RuleIcmpComposeRhs

set_option maxRecDepth 8000
set_option maxHeartbeats 4000000
set_option Elab.async false

namespace Opt.Proof

open Isle Isle.Opt Clif

namespace ComposeWitness

private abbrev State := Nat × Valuation

private def frame : Frame := ⟨default, fun _ => none, [], [], .trap .stkOvf⟩
private def memory : Mem := default
private def invariant (s : State) : Prop := ∀ i, s.1 ≤ i → s.2 i = none
private def den (s : State) : Valuation := s.2

-- Allocate a genuinely fresh class and record the actual node evaluation. Failed
-- evaluation is stored as none, not replaced with a fabricated default value.
private def graph : EGraph State where
  enodes := fun _ _ => []
  typeOf := fun s i => (s.2 i).map Val.ty
  make := fun s node =>
    (s.1, (s.1 + 1, fun i => if i = s.1 then
      evalNode { frame with regs := s.2 } memory node else s.2 i))

private theorem graph_ok : GraphOk graph invariant den frame memory := by
  constructor
  · constructor
    · intro s x a hP ha node hn
      cases hn
    · intro s x t a hP ht ha
      change (s.2 x).map Val.ty = some t at ht
      change s.2 x = some a at ha
      rw [ha] at ht
      exact Option.some.inj ht
  · intro s node hP
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      change s.1 + 1 ≤ i at hi
      change (if i = s.1 then evalNode { frame with regs := s.2 } memory node
        else s.2 i) = none
      have hne : i ≠ s.1 := by omega
      rw [if_neg hne]
      exact hP i (by omega)
    · intro i a ha
      change (if i = s.1 then evalNode { frame with regs := s.2 } memory node
        else s.2 i) = some a
      have hne : i ≠ s.1 := by
        intro he
        subst i
        have hz := hP s.1 (Nat.le_refl _)
        change s.2 s.1 = some a at ha
        rw [hz] at ha
        cases ha
      rw [if_neg hne]
      exact ha
    · intro b hb
      change (if s.1 = s.1 then evalNode { frame with regs := s.2 } memory node
        else s.2 s.1) = some b
      rw [if_pos rfl]
      exact hb

private def initial (a b : BitVec 64) : St State :=
  { inner := (2, fun i => if i = 0 then some ⟨.i64, a⟩
      else if i = 1 then some ⟨.i64, b⟩ else none) }

private theorem initial_ok (a b : BitVec 64) : invariant (initial a b).inner := by
  intro i hi
  change 2 ≤ i at hi
  have h0 : i ≠ 0 := by omega
  have h1 : i ≠ 1 := by omega
  simp [initial, h0, h1]

private def run (mask : Int) (signed : Bool) (a b : BitVec 64) :=
  (Interp.applyTermN program (sem graph) cfg (0 + 64) 15 251
    [V.ty (CTy.ofClif .i8), V.int mask, V.bool signed, V.value 0, V.value 1]).run
      (initial a b, #[])

private def isResult : V → Bool
  | .value n => n == 2
  | _ => false

private def hit (mask : Int) (signed : Bool) (a b : BitVec 64) : Bool :=
  match run mask signed a b with
  | .ok (ws, _) => ws.any isResult
  | .error _ => false

private theorem member_of_hit {ws : List V} (h : ws.any isResult = true) :
    V.value 2 ∈ ws := by
  obtain ⟨v, hv, he⟩ := List.any_eq_true.mp h
  cases v <;> simp [isResult] at he
  subst_vars
  exact hv

private theorem success_of_hit {mask : Int} {signed : Bool} {a b : BitVec 64}
    (h : hit mask signed a b = true) :
    ∃ ws s tr, run mask signed a b = .ok (ws, (s, tr)) ∧ V.value 2 ∈ ws := by
  unfold hit at h
  cases he : run mask signed a b with
  | error e => simp only [he] at h; contradiction
  | ok result =>
    rcases result with ⟨ws, s, tr⟩
    simp only [he] at h
    exact ⟨ws, s, tr, rfl, member_of_hit h⟩

-- All assumptions of the RHS semantic theorem occur here, including successful
-- execution and membership in the actual returned result list.
private def Fixture (mask : Int) (signed : Bool) (a b : BitVec 64)
    (expected : BitVec 8) : Prop :=
  GraphOk graph invariant den frame memory ∧
  invariant (initial a b).inner ∧
  den (initial a b).inner 0 = some ⟨.i64, a⟩ ∧
  den (initial a b).inner 1 = some ⟨.i64, b⟩ ∧
  ∃ ws s tr, run mask signed a b = .ok (ws, (s, tr)) ∧
    V.value 2 ∈ ws ∧ den s.inner 2 = some ⟨.i8, expected⟩

set_option hygiene false in
local macro "compose_fixture " mask:term:max signed:term:max a:term:max b:term:max helper:ident : tactic =>
  `(tactic| (
    refine ⟨graph_ok, initial_ok _ _, rfl, rfl, ?_⟩
    have hhit : hit $mask $signed $a $b = true := by decide +kernel
    obtain ⟨ws, s, tr, he, hm⟩ := success_of_hit hhit
    refine ⟨ws, s, tr, he, hm, ?_⟩
    exact $helper data_program graph_ok (initial_ok _ _) he rfl rfl hm))

-- Inhabited instances of the local model/reflection lemmas.
example : GraphOk graph invariant den frame memory := graph_ok
example : invariant (initial (0x8000000000000000#64) 7).inner := initial_ok _ _
example : V.value 2 ∈ [V.value 2] := member_of_hit (by decide)
example : ∃ ws s tr, run 0 false (0x8000000000000000#64) 7 = .ok (ws, (s, tr)) ∧
    V.value 2 ∈ ws := success_of_hit (by decide +kernel)

-- High-bit order reverses between signed and unsigned modes. Each of the eight
-- relation masks is exercised in both modes; equality also has an equal fixture.
example : Fixture 0 false (0x8000000000000000#64) 7 0 := by
  compose_fixture 0 false (0x8000000000000000#64) 7 compose_rhs_false
example : Fixture 0 true (0x8000000000000000#64) 7 0 := by
  compose_fixture 0 true (0x8000000000000000#64) 7 compose_rhs_false
example : Fixture 1 false (0x8000000000000000#64) 7 0 := by
  compose_fixture 1 false (0x8000000000000000#64) 7 compose_rhs_eq
example : Fixture 1 true (0x8000000000000000#64) (0x8000000000000000#64) 1 := by
  compose_fixture 1 true (0x8000000000000000#64) (0x8000000000000000#64) compose_rhs_eq
example : Fixture 2 false (0x8000000000000000#64) 7 0 := by
  compose_fixture 2 false (0x8000000000000000#64) 7 compose_rhs_lt
example : Fixture 2 true (0x8000000000000000#64) 7 1 := by
  compose_fixture 2 true (0x8000000000000000#64) 7 compose_rhs_lt
example : Fixture 3 false (0x8000000000000000#64) 7 0 := by
  compose_fixture 3 false (0x8000000000000000#64) 7 compose_rhs_le
example : Fixture 3 true (0x8000000000000000#64) 7 1 := by
  compose_fixture 3 true (0x8000000000000000#64) 7 compose_rhs_le
example : Fixture 4 false (0x8000000000000000#64) 7 1 := by
  compose_fixture 4 false (0x8000000000000000#64) 7 compose_rhs_gt
example : Fixture 4 true (0x8000000000000000#64) 7 0 := by
  compose_fixture 4 true (0x8000000000000000#64) 7 compose_rhs_gt
example : Fixture 5 false (0x8000000000000000#64) 7 1 := by
  compose_fixture 5 false (0x8000000000000000#64) 7 compose_rhs_ge
example : Fixture 5 true (0x8000000000000000#64) 7 0 := by
  compose_fixture 5 true (0x8000000000000000#64) 7 compose_rhs_ge
example : Fixture 6 false (0x8000000000000000#64) (0x8000000000000000#64) 0 := by
  compose_fixture 6 false (0x8000000000000000#64) (0x8000000000000000#64) compose_rhs_ne
example : Fixture 6 true (0x8000000000000000#64) 7 1 := by
  compose_fixture 6 true (0x8000000000000000#64) 7 compose_rhs_ne
example : Fixture 7 false (0x8000000000000000#64) 7 1 := by
  compose_fixture 7 false (0x8000000000000000#64) 7 compose_rhs_true
example : Fixture 7 true (0x8000000000000000#64) 7 1 := by
  compose_fixture 7 true (0x8000000000000000#64) 7 compose_rhs_true

end ComposeWitness
end Opt.Proof
