import FV.Concurrency.CallRetPremises
import FV.Concurrency.CallResumeChecks

/-!
# The call's arguments in their fixed registers at the `bl` (#473, (2b), layers 3–4b)

The callee's `ArgsAtEntry` (register arguments only, `IselCheck.callOkB`) needs the call's
argument values in the ABI argument registers on the machine at the `bl`. At a direct `call`
item of the allocated code with virtual use registers (`CallUsesVirt`, a check like
`CallResumeChecks.callDefsVirtB`):

* `useOps_eq`: the use operands are one fixed early use `useOp u` per use `u`, in order;
* **`call_uses_q`**: with layer 4b's `Q` and the allocation checker's `MatchRun` at the item, the
  `j`-th use `(v, p)` of the call has, in register `p` of the machine state, the `j`-th VCode use
  value (`vuses ops ρ`), which is `ρ n` for `v = .vreg n _`.

Layer 2's side (the VCode use values hold the CLIF argument values, in the order of the callee
signature's argument locations) is open.
-/

namespace Concurrency.CallArgsAt

open Arm Backend Backend.Proof Backend.Proof.Driver E2E VCodeThread CallRetResume

/-- Every call instruction uses virtual registers only. -/
def CallUsesVirt (vc : VCode) : Prop :=
  CallResumeChecks.CallsAll vc fun info => ∀ u ∈ info.uses, ∃ (n : Nat) (c : RegClass), u.1 = .vreg n c

/-- The check of `CallUsesVirt`. -/
def callUsesVirtB (vc : VCode) : Bool :=
  CallResumeChecks.callsAllB vc fun info => info.uses.all (CallResumeChecks.isVReg ·.1)

/-- **The check is sound and complete.** -/
theorem callUsesVirtB_iff (vc : VCode) : callUsesVirtB vc = true ↔ CallUsesVirt vc := by
  unfold callUsesVirtB CallUsesVirt
  rw [CallResumeChecks.callsAllB_iff]
  simp only [List.all_eq_true, CallResumeChecks.isVReg_iff]

/-- The operand a virtual use register `(v, p)` of a call contributes. -/
def useOp (u : Reg × Reg) : Operand :=
  match u.1 with
  | .vreg n c => ⟨n, c, .use, .early, .fixed u.2⟩
  | _ => default

theorem useOp_eq {u : Reg × Reg} {n : Nat} {c : RegClass} (h : u.1 = .vreg n c) :
    useOp u = ⟨n, c, .use, .early, .fixed u.2⟩ := by
  simp [useOp, h]

theorem mapM_usesV : ∀ (U : List (Reg × Reg)), (∀ u ∈ U, ∃ n c, u.1 = .vreg n c) →
    ∀ (s : Array Operand),
    (U.mapM (fun (x : Reg × Reg) => do
        let r ← collectOp (OpSpec.fixedUse x.2) x.1; pure (r, x.2))).run s =
      .ok (U, s ++ (U.map useOp).toArray)
  | [], _, s => by simp
  | u :: U, hv, s => by
    obtain ⟨n, c, hu⟩ := hv u (List.mem_cons_self ..)
    obtain ⟨v, p⟩ := u
    simp only at hu
    subst hu
    simp only [List.mapM_cons, StateT.run_bind]
    have h1 : (collectOp (OpSpec.fixedUse p) (Reg.vreg n c)).run s =
        .ok (Reg.vreg n c, s.push ⟨n, c, .use, .early, .fixed p⟩) := rfl
    rw [h1, Driver.except_ok_bind, StateT.run_pure, Driver.except_pure, Driver.except_ok_bind,
      mapM_usesV U (fun u hu => hv u (List.mem_cons_of_mem _ hu)), Driver.except_ok_bind,
      StateT.run_pure, Driver.except_pure]
    simp [useOp]

/-- **The use operands of a direct call with virtual use and def registers**: one `useOp` per
use, in order. -/
theorem useOps_eq {n : String} {us ds : List (Reg × Reg)}
    (hu : ∀ u ∈ us, ∃ n c, u.1 = .vreg n c) (hd : ∀ d ∈ ds, ∃ n c, d.2 = .vreg n c)
    {ops : Array Operand} (h : (MInst.call ⟨.sym n, us, ds⟩).operands = .ok ops) :
    ops.toList.filter Operand.isUse = us.map useOp := by
  have e : (MInst.call ⟨.sym n, us, ds⟩).operands =
      .ok (#[] ++ (us.map useOp).toArray ++ (ds.map defOp).toArray) := by
    rw [operands_eq]
    simp only [MInst.visitOperands, StateT.run_bind, StateT.run_pure, Driver.except_pure,
      Driver.except_ok_bind]
    rw [mapM_usesV us hu, Driver.except_ok_bind, mapM_defsV ds hd, Driver.except_ok_bind]
    rfl
  rw [e] at h
  cases h
  rw [Array.toList_append, Array.toList_append, List.filter_append, List.filter_append,
    List.toList_toArray, List.toList_toArray]
  have h1 : (ds.map defOp).filter Operand.isUse = [] := by
    rw [List.filter_eq_nil_iff]
    intro o ho
    obtain ⟨d, hd', rfl⟩ := List.mem_map.mp ho
    obtain ⟨m, c, hdv⟩ := hd d hd'
    simp [defOp_eq hdv, Operand.isUse]
  have h2 : (us.map useOp).filter Operand.isUse = us.map useOp := by
    rw [List.filter_eq_self]
    intro o ho
    obtain ⟨u, hu', rfl⟩ := List.mem_map.mp ho
    obtain ⟨m, c, huv⟩ := hu u hu'
    simp [useOp_eq huv, Operand.isUse]
  simp [h1, h2]

/-- **The call's arguments in their fixed registers at a `call` item** (module doc). -/
theorem call_uses_q {R : RL} {s : ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {cc : CheckCtx}
    {ins : Array (Option AState)} {a0 : AState} (hc : CheckedAt R.vc R.rf cc ins a0)
    {r₀ : Reg → CV} {vs : VState CV ArmState}
    (hm : MatchRun cc ins ckeep r₀ ⟨b, .op k allocs :: its, m, w⟩ vs)
    {vb : VBlock} {n : String} {us ds : List (Reg × Reg)} (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.call ⟨.sym n, us, ds⟩))
    (hu : ∀ u ∈ us, ∃ n c, u.1 = .vreg n c) (hd : ∀ d ∈ ds, ∃ n c, d.2 = .vreg n c)
    {ops : Array Operand} (hops : (MInst.call ⟨.sym n, us, ds⟩).operands = .ok ops) :
    ∀ (j : Nat) (v p : Reg) (x : CV), us[j]? = some (v, p) → (vuses ops vs.ρ)[j]? = some x →
      regVal s p = x := by
  intro j v p x hj hx
  obtain ⟨hb, -, vb', a, out, hvb', hrun, hinv, -⟩ := hm
  simp only at hb hvb' hrun
  subst hb
  rw [hc.vc_eq, hvb] at hvb'
  cases hvb'
  obtain ⟨-, rfl, i, ops', a', hi', hops', hstep, -⟩ := Backend.Proof.runItems_op hrun
  rw [hi] at hi'
  cases hi'
  rw [hops] at hops'
  cases hops'
  obtain ⟨hst, hE, -, -, -⟩ := Backend.Proof.stepOp_ok hstep
  obtain ⟨hsz, hloc, -, -⟩ := checkStatic_facts hst
  have hU := useOps_eq hu hd hops
  -- the j-th use operand and its allocation
  obtain ⟨nj, cj, hvj⟩ := hu (v, p) (List.mem_of_getElem? hj)
  have hopj : (ops.toList.filter Operand.isUse)[j]? = some ⟨nj, cj, .use, .early, .fixed p⟩ := by
    rw [hU, List.getElem?_map, hj]
    simp [useOp_eq (u := (v, p)) hvj]
  have hfst := pairs_fst hsz Operand.isUse
  rw [← hfst] at hopj
  rw [List.getElem?_map] at hopj
  obtain ⟨q, hq', hq1⟩ := Option.map_eq_some_iff.mp hopj
  have hqmem := List.mem_filter.mp (List.mem_of_getElem? hq')
  have hq2 : q.2 = .reg p := (hloc q hqmem.1).2 p (by rw [hq1])
  have hal : p.allocatable = true := by
    have := (hloc q hqmem.1).1
    rw [hq2] at this
    simp only [CheckCtx.locOk, Bool.and_eq_true] at this
    exact this.2
  -- the checker's invariant at the early use
  have hmq : m q.2 = vs.ρ nj := by
    have hin : q ∈ atPos (ops.zip allocs).toList .use .early :=
      List.mem_filter.mpr ⟨hqmem.1, by simp [hq1]⟩
    have := hinv _ _ (hE q hin)
    rw [hq1] at this
    exact this
  have hxj : x = vs.ρ nj := by
    unfold vuses at hx
    rw [List.getElem?_map] at hx
    rw [← hfst, List.getElem?_map, hq'] at hx
    simp only [Option.map_some, Option.some.injEq] at hx
    rw [← hx, hq1]
  have hst' := q_stRel hq
  rw [hxj, ← hmq, hq2, hst'.store (.reg p) (fun r e => by cases e; exact hal) trivial]
  rfl

end Concurrency.CallArgsAt
