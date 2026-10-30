import FV.Backend.Proof.StockValues
import FV.Backend.Proof.IselExtern
import FV.Backend.Proof.LowerSim
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192

/-- Correct ABI argument copies preserve all source values already held in the
initial virtual file, including parameters omitted from the copy list. -/
theorem entry_args_preserve_values {ctx : Ctx} {fr : Clif.Frame}
    {isem : Backend.Proof.Sem} (driver : DriverSem isem)
    (pairs : List (Nat × Reg)) (nodup : (pairs.map (·.1)).Nodup)
    {ρ : Nat → CV} {w : Arm.ArmState} (held : ValuesHeld (fun _ => True) ctx fr ρ)
    (physical : ∀ x v key p, fr.regs x = some v →
      ctx.valueReg? x = some (.vreg key .int) → (key,p) ∈ pairs → VHolds v (regVal w p)) :
    ∃ ρ', seqRun isem [.args (argPairs pairs)] ρ w = some (.fall ρ' w) ∧
      ValuesHeld (fun _ => True) ctx fr ρ' := by
  have defs : (argOps pairs).filter Operand.isDef = argOps pairs := by
    apply List.filter_eq_self.mpr
    intro o member
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp member
    rfl
  have uses : vuses (argOps pairs).toArray ρ = [] := by
    simp only [vuses,List.map_eq_nil_iff,List.filter_eq_nil_iff]
    intro o member
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp member
    simp [Operand.isUse]
  let outs := (argPairs pairs).map (fun d => regVal w d.2)
  let ρ' := vdefUpd (argOps pairs).toArray outs ρ
  have length : outs.length = ((argOps pairs).toArray.toList.filter Operand.isDef).length := by
    change outs.length = ((argOps pairs).filter Operand.isDef).length
    rw [defs]
    simp only [outs,argPairs,argOps,List.length_map]
  refine ⟨ρ',?_,?_⟩
  · simp only [seqRun,operands_args pairs,uses,driver.args,length,ite_true,
      Option.map_some,SeqEnd.succ,ρ',outs]
  · intro x _ v found
    obtain ⟨key,mapped,value⟩ := held x trivial v found
    refine ⟨key,mapped,?_⟩
    by_cases copied : key ∈ pairs.map (·.1)
    · obtain ⟨q,member,equal⟩ := List.mem_map.mp copied
      obtain ⟨i,lookup⟩ := List.mem_iff_getElem?.mp member
      have output : outs[i]? = some (regVal w q.2) := by
        simp only [outs,argPairs,List.map_map,List.getElem?_map,lookup,Option.map_some,Function.comp_def]
      have updated := vdefUpd_argOps (ρ := ρ) nodup (by simp [outs,argPairs]) i lookup output
      have update : ρ' key = regVal w q.2 := by rw [← equal]; exact updated
      rw [update]
      apply physical x v key q.2 found mapped
      have pair : (key,q.2) = q := Prod.ext equal.symm rfl
      rw [pair]
      exact member
    · have unchanged : ρ' key = ρ key := by
        apply vdefUpd_other
        change key ∉ ((argOps pairs).filter Operand.isDef).map (·.vreg)
        rw [defs]
        simpa only [argOps,List.map_map,Function.comp_def] using copied
      rw [unchanged]
      exact value
end Backend.Stock.Proof
