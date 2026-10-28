import FV.E2E.CallPostExists

/-!
# Witness for `callPost_only_exists`

An environment with one extern `e` (no parameters, returns nothing, keeps the memory), restricted
to its invocation on the empty memory: every call has an accepted result, so any call semantics
guarded by `CallPost` meets the extern contract (`xCallsOk_guard`) for the declaration of `e`.
-/

namespace E2E.CallPostExistsWitness

open Backend Backend.Proof

def envE : Clif.Env where
  extern n := if n = "e" then some fun _ m => .returned [] m else none

def extE : Clif.ExtFunc := { name := "e", sig := default }

def A0 (n : String) (vals : List Clif.Val) (cm : Clif.Mem) : Prop :=
  n = "e" ∧ vals = [] ∧ cm = Clif.Mem.empty

theorem callPost_e (Γ : Rel) (f : Clif.Function) (c : BitVec 64) (sym : String → Int → BitVec 64) :
    ∀ d uses w, ∃ r, CallPost (envE.only A0) [extE] [] (RelW Γ f c) sym d uses w r := by
  refine callPost_only_exists (n0 := "e") (vals0 := []) (cm0 := Clif.Mem.empty)
    (fun n vals cm h => h) (sigRets extE.sig).length ?_
  intro g rvals cm' hg hret
  simp only [envE, ↓reduceIte] at hg
  cases hg
  cases hret
  exact ⟨fun _ _ h => h, rfl, Nat.zero_le _, fun ext hext _ _ => by
    simp only [List.mem_singleton] at hext; subst hext; rfl, fun _ h => nomatch h⟩

theorem guard_xCallsOk_e (X : ExtSem) (Γ : Rel) (f : Clif.Function) (c : BitVec 64) :
    XCallsOk (envE.only A0) [extE] (RelW Γ f c)
      (X.guard (CallPost (envE.only A0) [extE] [] (RelW Γ f c) X.sym)) :=
  xCallsOk_guard X (callPost_e Γ f c X.sym)

end E2E.CallPostExistsWitness
