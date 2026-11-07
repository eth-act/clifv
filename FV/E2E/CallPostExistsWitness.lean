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
    (fun n vals cm h => h) extE.sig.returns.length ?_
  intro g rvals cm' hg hret
  simp only [envE, ↓reduceIte] at hg
  cases hg
  cases hret
  exact ⟨fun _ _ h => h, rfl, Nat.zero_le _, fun ext hext _ _ _ => by
    simp only [List.mem_singleton] at hext; subst hext; rfl, fun _ h => nomatch h⟩

theorem guard_xCallsOk_e (X : ExtSem) (Γ : Rel) (f : Clif.Function) (c : BitVec 64) :
    XCallsOk (envE.only A0) [extE] (RelW Γ f c)
      (X.guard (CallPost (envE.only A0) [extE] [] (RelW Γ f c) X.sym)) :=
  xCallsOk_guard X (callPost_e Γ f c X.sym)

/-- A returning state (no extern invocation). -/
def sRet (fn : Clif.Function) : Clif.State :=
  { frame := { func := fn, regs := Clif.Regs.empty, slots := [], body := [], term := .ret [] },
    callers := [], mem := {} }

theorem invoked_sRet (fn : Clif.Function) (p : Clif.Program) (n : String)
    (vals : List Clif.Val) (m : Clif.Mem) : ¬ Clif.Invoked envE p (sRet fn) n vals m :=
  fun h => h.2

/-- `callPost_invoked_exists` applies at a state, here one that invokes nothing. -/
theorem callPost_sRet (fn : Clif.Function) (p : Clif.Program) (Γ : Rel) (f : Clif.Function)
    (c : BitVec 64) (sym : String → Int → BitVec 64) :
    ∀ d uses w, ∃ r, CallPost (envE.only (Clif.Invoked envE p (sRet fn))) [extE] [] (RelW Γ f c)
      sym d uses w r :=
  callPost_invoked_exists 0 fun n vals _ _ _ h => absurd h (invoked_sRet fn p n vals _)

/-- `xCallsOk_guard_only`: the guard accepting results for `A0` meets the contracts of the
restriction to `sRet`'s invocations (a subset of `A0`'s). -/
theorem guard_only_sRet (X : ExtSem) (fn : Clif.Function) (p : Clif.Program) (Γ : Rel)
    (f : Clif.Function) (c : BitVec 64) :
    XCallsOk (envE.only (Clif.Invoked envE p (sRet fn))) [extE] (RelW Γ f c)
      (X.guard (CallPost (envE.only A0) [extE] [] (RelW Γ f c) X.sym)) :=
  (xCallsOk_guard_only (fun n vals m h => absurd h (invoked_sRet fn p n vals m)) X
    (callPost_e Γ f c X.sym)).1

end E2E.CallPostExistsWitness
