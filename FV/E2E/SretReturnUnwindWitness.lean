import FV.E2E.SretReturnUnwind
import FV.E2E.SretReturnWitness

/-!
# Non-vacuity of `backend_correct_final_unwind_abi` / `backend_correct_final_unwind_sret` (S7)

`SretReturnWitness.sw` (`function %sret_witness(i64 sret, i64) { block0(v0, v1): store v1, v0;
return }`) compiled through lowering, preparation, the spill allocation, emission and layout
(`vcW` … `fbW`), with its unwinding tables (`TW`: the emitted CIE and FDE rows, its LSDA). `sw`
passes `sretStableXB` and the exceptional-edge validator `unwCheck`, and the table checks pass
(`checks_true`, the closed test receipt). `sw_returns_sret_unwind`: with the witness callees
(`NonVacuity`), no raising callees (`XRaise.none`, `Unw.UnwHooks.none`), every premise of
`backend_correct_final_unwind_sret` but the run's own is discharged: a return of a run with
unwinding of `sw` leaves the pointer `p` in x8 (until #587: x0).
-/

namespace E2E.SretReturnUnwindWitness

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.UnwindTables E2E.SretReturnWitness

/-- The compilation of `sw` (`default` where a stage fails; `checks_true` shows none does). -/
def vcW : VCode := (lowerFunction sw).toOption.getD default
def vcpW : VCode := (Backend.prepare vcW).toOption.getD default
def afW : AFunc := (lowerRFunc vcpW (spillAlloc vcpW)).toOption.getD default
def faW : FnAsm := (emitFunc 0 afW).toOption.getD default
def fbW : FnBin := faW.layout.toOption.getD default
def lsdaW : Option (List CallSite) := (callSites afW faW).toOption.getD none
def rowsW : List (Nat × Cfi) := (unwindRows afW faW).toOption.getD []

/-- The tables the unwinder reads for `sw`: the emitted CIE and FDE rows and its LSDA. -/
def TW : Unw.FnTables := ⟨cieInsns, insnsFrom 0 rowsW, lsdaW.map (List.map (·.entry))⟩

/-- The closed checks: every stage of the compilation succeeds, `sretStableXB`, `unwCheck`, the
prepared forms covered, and the unwinding-table checks. -/
def checks : Bool :=
  (lowerFunction sw).toBool && (Backend.prepare vcW).toBool &&
    (lowerRFunc vcpW (spillAlloc vcpW)).toBool && (emitFunc 0 afW).toBool && faW.layout.toBool &&
    lowerCheck sw vcW && prepCheck vcW vcpW && (checkAlloc vcpW (spillAlloc vcpW)).isOk &&
    formsCoveredB ⟨faW.k, afW.slotBase⟩ vcpW &&
    sretStableXB sw && unwCheck sw vcW &&
    (callSites afW faW).toBool && padsNonzeroB afW faW && lastCallsOk afW faW &&
    (unwindRows afW faW).toBool && savedCheck vcpW (spillAlloc vcpW)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The closed test receipt (not used by any compiler correctness theorem). -/
theorem checks_true : checks = true := by native_decide

/-- **`sw` meets the compile-time premises of `backend_correct_final_unwind_sret`** (`i = 0`). -/
theorem compiled_exists :
    InSubset ({ funcs := [] } : Clif.Program) sw ∧ sretStableXB sw = true ∧
    unwCheck sw vcW = true ∧
    Compiled sw 0 vcW vcpW (spillAlloc vcpW) afW faW fbW ∧
    FormsCovered ⟨faW.k, afW.slotBase⟩ vcpW ∧
    callSites afW faW = .ok lsdaW ∧ TW.lsda = lsdaW.map (List.map (·.entry)) ∧
    padsNonzeroB afW faW = true ∧ lastCallsOk afW faW = true ∧
    unwindRows afW faW = .ok rowsW ∧ TW.cie = cieInsns ∧ TW.fde = insnsFrom 0 rowsW ∧
    savedCheck vcpW (spillAlloc vcpW) = true := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hl, hp⟩, ha⟩, he⟩, hb⟩, hlo⟩, hpr⟩, hck⟩, hcov⟩, hS⟩, hunw⟩, hcs⟩,
    hpad⟩, hlast⟩, hrows⟩, hsaved⟩ := h
  have hc : checkAlloc vcpW (spillAlloc vcpW) = .ok () := by
    cases he : checkAlloc vcpW (spillAlloc vcpW) with
    | error e => rw [he] at hck; cases hck
    | ok u => cases u; rfl
  obtain ⟨hv, -⟩ := SretReturnWitness.compiled_exists
  exact ⟨hv, hS, hunw,
    ⟨RegLevelCorrectUWitness.ok_getD hl, hlo, RegLevelCorrectUWitness.ok_getD hp, hpr, hc,
      RegLevelCorrectUWitness.ok_getD ha, RegLevelCorrectUWitness.ok_getD he,
      RegLevelCorrectUWitness.ok_getD hb⟩,
    (formsCoveredB_iff _ _).1 hcov, RegLevelCorrectUWitness.ok_getD hcs, rfl, hpad, hlast,
    RegLevelCorrectUWitness.ok_getD hrows, rfl, rfl, hsaved⟩

/-- **`backend_correct_final_unwind_sret` applies to `sw`**: for its compilation and tables,
with the witness callees (`NonVacuity`: every contract premise discharged; `sw` makes no calls)
and no raising callees (`XRaise.none`, `Unw.UnwHooks.none`), a CLIF return of a run with
unwinding of `sw` on `[p, v]` is matched by an Arm return on the machine with unwinding with the
struct pointer `p` in x8. -/
theorem sw_returns_sret_unwind :
    Compiled sw 0 vcW vcpW (spillAlloc vcpW) afW faW fbW ∧
      ∀ {syms : String → Option Nat} {K : Nat} {env : Clif.XEnv} (_ : 32 ≤ K) (g h tp : BitVec 64)
        {base ra : BitVec 64} {s w₀ : Arm.ArmState} {p v : Clif.Val} {cs : Clif.State},
        AbiEntry fbW base ra s → StackAvail K afW s → BodyEntry afW s w₀ →
        ArgsIn sw.sig [p, v] s → ClifEntry sw [p, v] cs →
        Rel.holds ⟨frameW K (RAFrame.compute vcpW (spillAlloc vcpW)).intBase
          (RAFrame.compute vcpW (spillAlloc vcpW)).size afW s, syms, afW.slotBase,
          (RAFrame.compute vcpW (spillAlloc vcpW)).intBase⟩ sw cs.frame.slots cs.mem w₀ →
        TrapsExplicitX env { funcs := [] } cs → ∀ fuel vals cm,
        Clif.runLoopX env { funcs := [] } fuel cs.toX = .returned vals cm →
        ∃ n, ArmRet ra s (runX (Unw.ArmStepU (witnessX (witnessSym syms) tp)
            (witnessHooks g h (witnessSym syms) tp) Unw.UnwHooks.none TW faW) n s) ∧
          XHolds p (xreg 8 (runX (Unw.ArmStepU (witnessX (witnessSym syms) tp)
            (witnessHooks g h (witnessSym syms) tp) Unw.UnwHooks.none TW faW) n s)) ∧
          MemAgree cm (runX (Unw.ArmStepU (witnessX (witnessSym syms) tp)
            (witnessHooks g h (witnessSym syms) tp) Unw.UnwHooks.none TW faW) n s) := by
  obtain ⟨hsub, hS, hunw, hc, hcov, hsites, hlsda, hpad, hlast, hrows, hcie, hfde, hsaved⟩ :=
    compiled_exists
  refine ⟨hc, ?_⟩
  intro syms K env hK g h tp base ra s w₀ p v cs hent hres hbe hargs hcs hrel htr fuel vals cm hrun
  obtain ⟨hC, hTls, hX, hXI, hsym⟩ :=
    final_contracts_witness (f := sw) (vcp := vcpW) (rf := spillAlloc vcpW) (af := afW)
      (slotOff := afW.slotBase) (syms := syms) (env := env.toEnv) hK g h tp
      (by simp [sw]) (by simp [indSigs, sw]) (by simp [sw]) (by simp [indSigs, sw])
  have hnx : sw.externs.map (·.2) = [] := by simp [sw]
  have hni : indSigs sw = [] := by simp [indSigs, sw]
  exact backend_correct_final_unwind_sret (XR := XRaise.none) hsub hc hunw hS
    (show sw.sig.params.findIdx? (·.purpose == .sret) = some 0 by decide) rfl hcov hC
    (fun ⟨B, hB, ht⟩ => absurd ht (by simp [sw] at hB; subst hB; decide)) (fun _ => hTls)
    hX hXI (fun _ => by rw [hnx]; exact fun _ h => nomatch h)
    (fun _ => by rw [hni]; exact fun _ h => nomatch h)
    (fun _ => by rw [hnx, hni]; exact ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩) hsym rfl
    (fun _ _ => calleeUnwOkG_none _ _ _ _ _ _ _ _) hsites hlsda hpad hlast hrows hcie hfde hsaved
    hent hres hbe hargs hcs hrel htr fuel hrun (v := p) rfl

end E2E.SretReturnUnwindWitness
