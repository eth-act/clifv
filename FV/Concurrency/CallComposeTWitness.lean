import FV.Concurrency.CallComposeT
import FV.Concurrency.PrivCohTWitness

/-!
# Witnesses: calls with time-varying private sets (#473, (iv))

* `realizedT_trans0`: `RealizedT.trans` of two empty prefixes, the dirty set handed over;
* `funRealT_ext`: `link_composeT` with every callee external under a contract (here the empty
  prefix ending in a trivial end condition);
* `linkedT_ret`: `realizes_linkedT` on the two threads of `ProgWitness` with empty Arm runs —
  its program premises (well formed, SC per location, initial writes first, `StackDisjoint`)
  discharged; the CLIF threads run `CStepS`.
-/

namespace Concurrency.CallComposeT.Witness

open Arm ArmThread Prog ClifThread ProgE2E ThreadRefine ArmAllocThread CallCompose PrivCohT
  ProgWitness PrivCohT.Witness PrepThread

theorem realizedT_trans0 (env : Clif.Env) (p : Clif.Program) (Bnd : Nat → Prop) (ls : List Lab)
    (c : TState) (D : Nat → Prop) : RealizedT env p Bnd ls 0 c c D D := by
  have h := RealizedT.trans (RealizedT.zero (env := env) (p := p) (Bnd := Bnd) ls c D)
    (RealizedT.zero (ls.drop 0) c D)
  simpa using h

theorem funRealT_ext (env : Clif.Env) (p : Clif.Program) (Bnd : Nat → Prop)
    (M : ArmState → ArmState) (ok : ArmState → Lab → Prop) (u : AT) (c : TState × (Nat → Prop)) :
    FunRealG (RealT env p Bnd) M ok (fun _ _ _ _ => False) (fun _ _ => True) u c :=
  link_composeT (env := env) (p := p) (Bnd := Bnd) (M := M) (ok := ok) (G := Unit)
    (Ext := fun _ => True) (Ent := fun _ _ _ => True) (Ret := fun _ _ _ _ _ => False)
    (E := fun _ _ => True)
    (Inv := fun _ _ _ _ _ => True) (fun _ _ _ _ => trivial) (fun _ _ _ h => absurd trivial h)
    (fun _ h => absurd trivial h)
    (fun _ u c _ _ ls _ _ => ⟨0, c, RealizedT.zero ls c.1 c.2, .inr (.inl trivial)⟩) () u c trivial

/-- **Non-vacuity of `realizes_linkedT`**: the two threads of `ProgWitness` with empty Arm runs. -/
theorem linkedT_ret (M : Nat → ArmState → ArmState) (ok : Nat → ArmState → Lab → Prop)
    (sA : Nat → AT) :
    ∃ (PC' : Traces TState SKind BVal) (φ : PEv → PEv), PC'.n = 2 ∧
      (∀ i < 2, PC'.st i 0 = s0 i) ∧ PC'.Runs (CStepS env0 p0) ∧
      Realizes PA [] (fun _ => none) none2 none2 none2 PC' [] (fun _ => none) φ
        (fun _ _ _ => True) := by
  obtain ⟨k, -, h⟩ := realizes_linkedT (n := 2) (env := env0) (p := p0) (Bnd := fun _ _ => False)
    (M := M) (ok := ok) (cs := s0) (D0 := fun _ _ => False) (sA := sA)
    (fun i _ ls t' _ => ⟨0, s0 i, fun _ => False, RealizedT.zero ls (s0 i) _⟩)
    (ls := fun _ => []) (t' := sA) (fun _ _ => .nil)
  exact h PA [] [] (fun _ => none) (fun _ => none) none2 none2 none2 rfl
    (fun i _ => by simp [PA, evTr, conv]) wfA hintA (fun _ _ h => h)
    (fun i _ a b => ⟨fun h => h.elim, fun hm => by obtain ⟨⟨x, hx, _⟩, _⟩ := hm; simp [evTr, evAt] at hx⟩)
    (List.prefix_refl _) (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun i _ j _ _ q x hx => by simp [PA, evAt] at hx)

end Concurrency.CallComposeT.Witness
