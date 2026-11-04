import FV.E2E.StockVoidCallEntry
import FV.E2E.StockResultCallSource

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- Original XNI keeps explicit scalar outputs equal across the two original worlds. -/
theorem result_call_pair {Γ : Rel} {f : Clif.Function} {c : BitVec 64}
    {env : Clif.Env} {exts : List Clif.ExtFunc} {sigs : List Clif.Signature} {X : ExtSem}
    (calls : XCallsOk env exts (RelW Γ f c) X)
    (ni : XNI Γ.F Γ.syms exts sigs c (CallLg env exts sigs) X)
    {ext : Clif.ExtFunc} (member : ext ∈ exts) {result : Clif.AbiParam}
    (returns : ext.sig.returns = [result])
    {g : List Clif.Val → Clif.Mem → Clif.Outcome} (found : env.extern ext.name = some g)
    {vals : List Clif.Val} {value : Clif.Val} {cm after : Clif.Mem}
    (returned : g vals cm = .returned [value] after)
    {slots : List (Clif.SlotId × Nat)} {uses : List CV} {w w' : Arm.ArmState}
    (memory : RelW Γ f c slots cm w) (memory' : RelW Γ f c slots cm w')
    (arguments : ArgsAt ext.sig vals uses w) (arguments' : ArgsAt ext.sig vals uses w')
    {Z : BitVec 64 → Prop} (covers : ∀ a,Γ.F a → Z a) (worlds : SameWorld Z w w') :
    ∃ output out out',X.call (some ext.name) uses w = some ([output],out) ∧
      X.call (some ext.name) uses w' = some ([output],out') ∧ VHolds value output ∧
      RelW Γ f c slots after out ∧ RelW Γ f c slots after out' ∧ SameWorld Z out out' := by
  obtain ⟨actual,out,run,arity,held,related⟩ := calls ext member g slots cm w (some ext.name) uses uses
    vals [value] after found (Or.inl ⟨rfl,rfl⟩) arguments memory returned (by rw [returns]; rfl)
  obtain ⟨actual',out',run',arity',held',related'⟩ := calls ext member g slots cm w' (some ext.name) uses uses
    vals [value] after found (Or.inl ⟨rfl,rfl⟩) arguments' memory' returned (by rw [returns]; rfl)
  have legitimate : CallLg env exts sigs ext.name ext.sig vals cm :=
    ⟨Or.inl ⟨ext,member,rfl,rfl⟩,g,[value],after,found,returned⟩
  have paired := ni ext.name ext.sig vals cm uses (some ext.name) uses Z w w' actual out actual' out'
    legitimate (Or.inl ⟨rfl,rfl⟩) covers worlds memory.1.1 memory'.1.1 memory.2.1 memory'.2.1
    (Or.inl ⟨⟨ext,member,rfl,rfl⟩,arguments,arguments'⟩) run run'
  rw [returns] at arity
  cases actual with
  | nil => cases arity
  | cons output tail =>
    have empty : tail = [] := by simpa using arity
    subst tail
    have shape : actual' = [output] := paired.1.symm
    refine ⟨output,out,out',run,?_,held.2 0 value output rfl rfl,related,related',paired.2⟩
    simpa only [shape] using run'

end E2E
