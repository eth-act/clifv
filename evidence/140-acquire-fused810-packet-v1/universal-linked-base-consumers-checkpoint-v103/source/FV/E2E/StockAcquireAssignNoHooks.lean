import FV.E2E.StockAcquireBlockNoHooks
import FV.Backend.Proof.RegallocLemmas

namespace Backend.Proof
open Backend Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- This internal relation records only successful results of an operand visitor. -/
def VisitorResult {α : Type} (p : α → Prop) (run : StateT Nat (Except String) α) : Prop :=
  ∀ state value next, run.run state = .ok (value, next) → p value

theorem visitorResult_pure {α : Type} {p : α → Prop} {value : α} (holds : p value) :
    VisitorResult p (pure value) := by
  intro state value' next run
  change Except.ok (value, state) = Except.ok (value', next) at run
  cases run
  exact holds

theorem visitorResult_bind {α β : Type} {p : β → Prop}
    (first : StateT Nat (Except String) α) (rest : α → StateT Nat (Except String) β)
    (holds : ∀ value, VisitorResult p (rest value)) : VisitorResult p (first >>= rest) := by
  intro state value next run
  simp only [StateT.run_bind] at run
  obtain ⟨⟨middle, middleState⟩, _, tail⟩ := Except.bind_ok run
  exact holds middle middleState value next tail

theorem visitorResult_of_run {α : Type} {p : α → Prop}
    {run : StateT Nat (Except String) α} {state next : Nat} {value : α}
    (holds : VisitorResult p run) (eq : run.run state = .ok (value, next)) : p value :=
  holds state value next eq

attribute [local irreducible] VisitorResult

/-- Operand replacement preserves every non-hook instruction family, irrespective of registers. -/
theorem visitOperands_no_hooks (visit : OpSpec → Reg → StateT Nat (Except String) Reg)
    {inst : MInst} (noHook : NoHookInst inst) :
    VisitorResult NoHookInst (inst.visitOperands visit) := by
  cases inst <;> simp only [NoHookInst] at noHook
  all_goals try contradiction
  all_goals simp only [MInst.visitOperands]
  all_goals repeat' first
    | (apply visitorResult_pure; trivial)
    | (apply visitorResult_bind; intro)

/-- Successful allocator substitution cannot create a model hook. -/
theorem assign_no_hooks {inst assigned : MInst} {registers : Array Reg}
    (noHook : NoHookInst inst) (run : inst.assign registers = .ok assigned) :
    NoHookInst assigned := by
  unfold MInst.assign at run
  obtain ⟨⟨result, count⟩, visited, rest⟩ := Except.bind_ok run
  dsimp only at rest
  simp only [bind, Except.bind, pure, Except.pure] at rest
  split at rest
  · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at rest
    cases rest
  · have eq : result = assigned := Except.ok.inj rest
    subst assigned
    exact visitorResult_of_run (visitOperands_no_hooks _ noHook) visited

end Backend.Proof
