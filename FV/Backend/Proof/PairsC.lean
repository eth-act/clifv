module

import FV.Backend.Proof.LowerLemmas
public import FV.Backend.Proof.LowerRename
import FV.Backend.Proof.IselGeneric
import FV.Arm.MinTheory

public section

/-!
# Class-general `Args`/`Rets` pairs (S11e5 Stage C)

`argPairsC ns`: the `(vreg n c, p)` pairs of an `Args` or a `Rets` with vregs of either class
(`Driver.argPairs`, `retPairs`: int vregs). Their operands are fixed late defs (`argOpsC`, an
`Args`) or fixed early uses (`retOpsC`, a `Rets`): `operands_argsC`, `operands_retsC`.
`argPairsC_of`: every list of pairs whose first components are vregs is an `argPairsC`.
-/

namespace Backend.Proof

open Backend Backend.Proof.Driver

/-- `(vreg n c, p)` pairs of an `Args` or a `Rets`, of either class (`argPairs`, `retPairs`: int
vregs). -/
@[expose] def argPairsC (ns : List (Nat × RegClass × Reg)) : List (Reg × Reg) :=
  ns.map fun q => (Reg.vreg q.1 q.2.1, q.2.2)

/-- The operands of `Args (argPairsC ns)`: fixed late defs. -/
@[expose] def argOpsC (ns : List (Nat × RegClass × Reg)) : List Operand :=
  ns.map fun q => (⟨q.1, q.2.1, .def, .late, .fixed q.2.2⟩ : Operand)

/-- The operands of `Rets (argPairsC ns)`: fixed early uses. -/
@[expose] def retOpsC (ns : List (Nat × RegClass × Reg)) : List Operand :=
  ns.map fun q => (⟨q.1, q.2.1, .use, .early, .fixed q.2.2⟩ : Operand)

theorem mapM_fixedDefC (ns : List (Nat × RegClass × Reg)) : ∀ (s : Array Operand),
    ((argPairsC ns).mapM
      (fun (x : Reg × Reg) => do let r ← collectOp (OpSpec.fixedDef x.2) x.1; pure (r, x.2))).run s =
      .ok (argPairsC ns, s ++ (argOpsC ns).toArray) := by
  induction ns with
  | nil => intro s; simp [argPairsC, argOpsC] <;> rfl
  | cons q ns ih =>
    intro s
    simp only [argPairsC, argOpsC, List.map_cons, List.mapM_cons, StateT.run_bind] at ih ⊢
    have h1 : (collectOp (OpSpec.fixedDef q.2.2) (Reg.vreg q.1 q.2.1)).run s =
        .ok (Reg.vreg q.1 q.2.1, s.push ⟨q.1, q.2.1, .def, .late, .fixed q.2.2⟩) := rfl
    rw [h1, except_ok_bind, StateT.run_pure, except_pure, except_ok_bind, ih, except_ok_bind,
      StateT.run_pure, except_pure]
    simp

theorem mapM_fixedUseC (ns : List (Nat × RegClass × Reg)) : ∀ (s : Array Operand),
    ((argPairsC ns).mapM
      (fun (x : Reg × Reg) => do let r ← collectOp (OpSpec.fixedUse x.2) x.1; pure (r, x.2))).run s =
      .ok (argPairsC ns, s ++ (retOpsC ns).toArray) := by
  induction ns with
  | nil => intro s; simp [argPairsC, retOpsC] <;> rfl
  | cons q ns ih =>
    intro s
    simp only [argPairsC, retOpsC, List.map_cons, List.mapM_cons, StateT.run_bind] at ih ⊢
    have h1 : (collectOp (OpSpec.fixedUse q.2.2) (Reg.vreg q.1 q.2.1)).run s =
        .ok (Reg.vreg q.1 q.2.1, s.push ⟨q.1, q.2.1, .use, .early, .fixed q.2.2⟩) := rfl
    rw [h1, except_ok_bind, StateT.run_pure, except_pure, except_ok_bind, ih, except_ok_bind,
      StateT.run_pure, except_pure]
    simp

theorem operands_argsC (ns : List (Nat × RegClass × Reg)) :
    (MInst.args (argPairsC ns)).operands = .ok (argOpsC ns).toArray := by
  rw [operands_eq]
  simp only [MInst.visitOperands, StateT.run_bind, mapM_fixedDefC]
  simp [bind, Except.bind, StateT.run, pure, StateT.pure, Except.pure]

theorem operands_retsC (ns : List (Nat × RegClass × Reg)) :
    (MInst.rets (argPairsC ns)).operands = .ok (retOpsC ns).toArray := by
  rw [operands_eq]
  simp only [MInst.visitOperands, StateT.run_bind, mapM_fixedUseC]
  simp [bind, Except.bind, StateT.run, pure, StateT.pure, Except.pure]

theorem filter_isDef_retOpsC (ns : List (Nat × RegClass × Reg)) :
    (retOpsC ns).filter Operand.isDef = [] := by
  rw [List.filter_eq_nil_iff]
  intro o ho
  simp only [retOpsC, List.mem_map] at ho
  obtain ⟨q, -, rfl⟩ := ho
  simp [Operand.isDef]

theorem argPairsC_of {ds : List (Reg × Reg)} (h : ∀ p ∈ ds, ∃ n c, p.1 = .vreg n c) :
    ∃ ns : List (Nat × RegClass × Reg), ds = argPairsC ns ∧ ns.map (·.2.2) = ds.map (·.2) := by
  induction ds with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons p ds ih =>
    obtain ⟨ns, h1, h2⟩ := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    obtain ⟨n, c, hn⟩ := h p (by simp)
    refine ⟨(n, c, p.2) :: ns, ?_, by simp [h2]⟩
    obtain ⟨r, q⟩ := p
    simp only at hn
    subst hn
    simp [argPairsC, h1]

end Backend.Proof
