import FV.Backend.Proof.StockAcquireEntryPrefixFault

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- A successful external direct-call outcome itself excludes an internal program target. -/
theorem instOutcome_ok_direct_external {env : Clif.Env} {program : Clif.Program}
    {frame : Clif.Frame} {memory nextMemory : Clif.Mem} {fn : Nat} {args : List Clif.ValueId}
    {values : List Clif.Val} {ext : Clif.ExtFunc}
    (declared : frame.func.extern? fn = some ext)
    (successful : instOutcome env program frame memory (.call fn args) = .ok (values,nextMemory)) :
    program.func? ext.name = none := by
  simp only [instOutcome,res_bind_eq_ok',Driver.res_bind_eq_ok,res_ofOption_eq_ok] at successful
  obtain ⟨⟨actual,vs⟩,⟨found,present,actualArgs,argRun,checked,checkedEq,pair⟩,outcome⟩ := successful
  simp only [Clif.Res.pure_eq,Clif.Res.ok.injEq,Prod.mk.injEq] at pair
  obtain ⟨rfl,rfl⟩ := pair
  have extEq := Option.some.inj (present.symm.trans declared)
  subst found
  cases target : program.func? ext.name with
  | none => rfl
  | some callee => simp only [target] at outcome;cases outcome

/-- A successful indirect outcome derives the original no-internal-target condition. -/
theorem instOutcome_ok_indirect_external {env : Clif.Env} {program : Clif.Program}
    {frame : Clif.Frame} {memory nextMemory : Clif.Mem} {sig callee : Nat} {args : List Clif.ValueId}
    {values : List Clif.Val} {cv : Clif.Val}
    (located : frame.get callee = .ok cv)
    (successful : instOutcome env program frame memory (.callIndirect sig callee args) = .ok (values,nextMemory)) :
    ∀ g ∈ program.funcs,memory.symbols g.name ≠ some cv.toNat := by
  simp only [instOutcome] at successful
  obtain ⟨⟨declared,address,vs⟩,arguments,outcome⟩ := res_bind_eq_ok'.mp successful
  obtain ⟨signature,signatureAt,arguments⟩ := res_bind_eq_ok.mp arguments
  obtain ⟨actual,actualAt,arguments⟩ := res_bind_eq_ok.mp arguments
  obtain ⟨bits,bitsAt,arguments⟩ := res_bind_eq_ok.mp arguments
  obtain ⟨actualArgs,argsAt,arguments⟩ := res_bind_eq_ok.mp arguments
  simp only [Clif.Res.pure_eq,Clif.Res.ok.injEq,Prod.mk.injEq] at arguments
  obtain ⟨rfl,rfl,rfl⟩ := arguments
  have cvEq := Clif.Res.ok.inj (actualAt.symm.trans located)
  subst actual
  rw [res_ofOption_eq_ok] at bitsAt
  have typed := val_as_i64 bitsAt
  subst cv
  cases found : program.funcs.find? (fun g => memory.symbols g.name == some bits.toNat) with
  | some g => simp only [found] at outcome;cases outcome
  | none =>
    intro g member equal
    have absent := List.find?_eq_none.mp found g member
    apply absent
    change memory.symbols g.name = some bits.toNat at equal
    rw [equal]
    simp only [beq_self_eq_true]

end Backend.Stock.Proof.Acquire810
