import FV.Backend.Proof.StockMemoryAccessTrap
import FV.Backend.Proof.StockLocalSourceTrap

/-! Draft: source proofs are staged, but no kernel command ran. -/
namespace Backend.Stock.Proof.MemoryFaults
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Invert the actual source load fault without assuming a valid initial heap. -/
theorem source_load_trap {fr : Clif.Frame} {cm : Clif.Mem} {op : Clif.LoadOp}
    {ty : Clif.Ty} {flags : Clif.MemFlags} {pointer : Nat} {offset : Int} {code : Clif.TrapCode}
    (failed : Clif.evalInst fr cm (.load op ty flags pointer offset) = .trap code) :
    ∃ value,fr.get pointer = .ok value ∧
      cm.valid (Clif.effAddr value offset) (op.size ty) = false ∧ flags.trapCode = some code := by
  simp only [Clif.evalInst] at failed
  rcases Clif.res_bind_eq_trap failed with impossible | ⟨value,found,failed⟩
  · exact False.elim (fr.get_ne_trap pointer code impossible)
  rcases Clif.res_bind_eq_trap failed with impossible | ⟨unit,checked,failed⟩
  · exact False.elim (Clif.Res.check_ne_trap _ _ code impossible)
  rcases Clif.res_bind_eq_trap failed with memory | ⟨bits,loaded,impossible⟩
  · obtain ⟨invalid,flag⟩ := Clif.Mem.load_trap memory
    exact ⟨value,found,invalid,flag⟩
  · cases impossible

/-- Invert a source store fault after evaluating its value and actual pointer. -/
theorem source_store_trap {fr : Clif.Frame} {cm : Clif.Mem} {op : Clif.StoreOp}
    {ty : Clif.Ty} {flags : Clif.MemFlags} {value pointer : Nat} {offset : Int} {code : Clif.TrapCode}
    (failed : Clif.evalInst fr cm (.store op ty flags value pointer offset) = .trap code) :
    ∃ bits address,fr.getAs value ty = .ok bits ∧ fr.get pointer = .ok address ∧
      cm.valid (Clif.effAddr address offset) (op.size ty) = false ∧ flags.trapCode = some code := by
  simp only [Clif.evalInst] at failed
  rcases Clif.res_bind_eq_trap failed with impossible | ⟨bits,storedValue,failed⟩
  · exact False.elim (fr.getAs_ne_trap value ty code impossible)
  rcases Clif.res_bind_eq_trap failed with impossible | ⟨address,found,failed⟩
  · exact False.elim (fr.get_ne_trap pointer code impossible)
  rcases Clif.res_bind_eq_trap failed with impossible | ⟨unit,checked,failed⟩
  · exact False.elim (Clif.Res.check_ne_trap _ _ code impossible)
  rcases Clif.res_bind_eq_trap failed with memory | ⟨next,stored,impossible⟩
  · obtain ⟨invalid,flag⟩ := Clif.Mem.store_trap memory
    exact ⟨bits,address,storedValue,found,invalid,flag⟩
  · cases impossible

/-- Actual original indexed load traps expose their real source address and size. -/
theorem indexed_source_load_trap {f : Clif.Function} {ctx : Ctx} {bi i : Nat} {info : IInfo}
    {env : Clif.Env} {cp : Clif.Program} {s : SourcePoint} {code : Clif.TrapCode}
    {op : Clif.LoadOp} {ty : Clif.Ty} {flags : Clif.MemFlags} {pointer : Nat} {offset : Int}
    (found : ctx.insts[i]? = some info)
    (source : info.clif = some (.load op ty flags pointer offset))
    (failed : LocalBody.IndexedSourceTrap env cp f ctx bi i s code) :
    ∃ value,s.2.1.get pointer = .ok value ∧
      Clif.Access s.2.1 (.load op ty flags pointer offset) (Clif.effAddr value offset) (op.size ty) ∧
      s.2.2.valid (Clif.effAddr value offset) (op.size ty) = false ∧ flags.trapCode = some code := by
  obtain ⟨index,actual,inst,rest,present,original,remaining,outcome⟩ := failed
  have same : actual = info := Option.some.inj (present.symm.trans found)
  subst actual
  have instEq : inst = .load op ty flags pointer offset := Option.some.inj (original.symm.trans source)
  subst inst
  obtain ⟨value,pointerValue,invalid,flag⟩ := source_load_trap outcome
  exact ⟨value,pointerValue,.load pointerValue,invalid,flag⟩

/-- Store fault addressing retains the pointer separately from the stored value. -/
theorem indexed_source_store_trap {f : Clif.Function} {ctx : Ctx} {bi i : Nat} {info : IInfo}
    {env : Clif.Env} {cp : Clif.Program} {s : SourcePoint} {code : Clif.TrapCode}
    {op : Clif.StoreOp} {ty : Clif.Ty} {flags : Clif.MemFlags} {value pointer : Nat} {offset : Int}
    (found : ctx.insts[i]? = some info)
    (source : info.clif = some (.store op ty flags value pointer offset))
    (failed : LocalBody.IndexedSourceTrap env cp f ctx bi i s code) :
    ∃ address,s.2.1.get pointer = .ok address ∧
      Clif.Access s.2.1 (.store op ty flags value pointer offset)
        (Clif.effAddr address offset) (op.size ty) ∧
      s.2.2.valid (Clif.effAddr address offset) (op.size ty) = false ∧ flags.trapCode = some code := by
  obtain ⟨index,actual,inst,rest,present,original,remaining,outcome⟩ := failed
  have same : actual = info := Option.some.inj (present.symm.trans found)
  subst actual
  have instEq : inst = .store op ty flags value pointer offset := Option.some.inj (original.symm.trans source)
  subst inst
  obtain ⟨bits,address,storedValue,pointerValue,invalid,flag⟩ := source_store_trap outcome
  exact ⟨address,pointerValue,.store pointerValue,invalid,flag⟩

end Backend.Stock.Proof.MemoryFaults
