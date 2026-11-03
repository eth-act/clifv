import FV.Backend.Proof.StockAcquireSourceRead
import FV.Backend.Proof.StockLocalSourceTrap
import FV.Clif.MemTrap

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- A real atomic read fault retains its exact address, alignment, size, and original flag code. -/
theorem atomic_source_eval_trap {fr : Clif.Frame} {cm : Clif.Mem} {ty : Clif.Ty}
    {flags : Clif.MemFlags} {pointer : Nat} {code : Clif.TrapCode}
    (failed : Clif.evalInst fr cm (.atomicLoad ty flags pointer) = .trap code) :
    ∃ pv,fr.get pointer = .ok pv ∧ Clif.effAddr pv 0 % ty.bytes = 0 ∧
      cm.valid (Clif.effAddr pv 0) ty.bytes = false ∧ flags.trapCode = some code := by
  simp only [Clif.evalInst] at failed
  rcases Clif.res_bind_eq_trap failed with impossible | ⟨pv,found,failed⟩
  · exact False.elim (fr.get_ne_trap pointer code impossible)
  rcases Clif.res_bind_eq_trap failed with impossible | ⟨unit,checked,failed⟩
  · exact False.elim (Clif.Res.check_ne_trap _ _ code impossible)
  have aligned : Clif.effAddr pv 0 % ty.bytes = 0 := by
    unfold Clif.Res.check at checked
    split at checked
    · rename_i same
      simpa using same
    · cases checked
  rcases Clif.res_bind_eq_trap failed with memory | ⟨bits,loaded,impossible⟩
  · obtain ⟨invalid,flag⟩ := Clif.Mem.load_trap memory
    exact ⟨pv,found,aligned,invalid,flag⟩
  · cases impossible

/-- The actual original source trap derives its access shape; no initial heap validity is assumed. -/
theorem indexed_source_atomic_trap {f : Clif.Function} {ctx : Ctx} {bi producer : Nat} {info : IInfo}
    {env : Clif.Env} {p : Clif.Program} {s : SourcePoint} {code : Clif.TrapCode}
    {ty : Clif.Ty} {flags : Clif.MemFlags} {pointer : Nat}
    (installed : ctx.insts[producer]? = some info)
    (original : info.clif = some (.atomicLoad ty flags pointer))
    (failed : LocalBody.IndexedSourceTrap env p f ctx bi producer s code) :
    ∃ pv,s.2.1.get pointer = .ok pv ∧
      Clif.Access s.2.1 (.atomicLoad ty flags pointer) (Clif.effAddr pv 0) ty.bytes ∧
      Clif.effAddr pv 0 % ty.bytes = 0 ∧ s.2.2.valid (Clif.effAddr pv 0) ty.bytes = false ∧
      flags.trapCode = some code := by
  obtain ⟨index,actual,inst,rest,present,source,remaining,outcome⟩ := failed
  have same : actual = info := Option.some.inj (present.symm.trans installed)
  subst actual
  have instruction : inst = .atomicLoad ty flags pointer := Option.some.inj (source.symm.trans original)
  subst inst
  obtain ⟨pv,found,aligned,invalid,flag⟩ := atomic_source_eval_trap outcome
  exact ⟨pv,found,.atomicLoad found,aligned,invalid,flag⟩

end Backend.Stock.Proof.Acquire810
