import FV.E2E.DeadCleanupUnwindFinal
import FV.E2E.DeadCleanupUnwindWitness
import FV.Backend.Proof.EhFrameDecode

/-!
# The per-function theorem with unwinding, on the tables decoded from the object (S10f)

`E2E.backend_correct_final_cleanup_unwind` assumes the unwinder's tables `T` of the function
(`hcie`, `hfde`, `hlsda`). Here `T` is what the unwinder's model (`Unw.tablesAt`,
`FV/Unw/EhFrame.lean`) decodes from the `.eh_frame` `Backend.ehFrame` writes and the
`.gcc_except_table` holding the function's `lsdaBytes`, placed and relocated by the linker
(`Backend.Proof.EhFrameDecode.tablesAt_ehFrame`): those premises are discharged.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup Backend.Proof.UnwindTables
  Backend.Proof.EhFrameDecode

/-- **The per-function theorem with unwinding on the linked tables.** The function's FDE entry
`(b, sz, rows, lo?)` is in the `.eh_frame` the backend writes (`fdes = pre ++ _ :: post`), the
section placed at `ehAddr` and relocated (`Fits`: `.text` symbol 1, `.gcc_except_table` symbol
`gcc`); its LSDA, if any (`lo?`, exactly when the function has a call-site table), is the
`lsdaBytes` at offset `lo` of `.gcc_except_table` (`gccB`). For a `pc` of the function that no
earlier FDE covers, the unwinder's lookup finds the function's address and tables `T`, and the
function refines its CLIF semantics on the machine whose unwinder reads `T`. -/
theorem backend_correct_final_cleanup_unwind_eh {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hlU : lowerCheckU f vc = true)
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks}
    {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv} {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hU : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite)
    (hX : ∀ s, XCallsOk env.toEnv (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env.toEnv (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXR : ∀ s, XRaiseOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hXRi : ∀ s, XRaiseIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    {rows : List (Nat × Cfi)} (hrows : unwindRows af fa = .ok rows)
    (hpad : padsNonzeroB af fa = true) (hlast : lastCallsOk af fa = true)
    (hsaved : savedCheck vcp rf = true)
    -- the linked `.eh_frame` and `.gcc_except_table`
    (fdes : List (Nat × Nat × List (Nat × Cfi) × Option Nat)) (gcc dwref ehAddr : Nat)
    (symAddr : Nat → Nat) (hok : ∀ x ∈ fdes, RowsOk x.2.2.1)
    (hb : ∀ x ∈ fdes, (cfiProgram x.2.2.1).data.toList.length + 24 < 0xffffffff)
    (hsz : (ehFrame fdes gcc dwref).1.size < 2 ^ 32)
    (hfit : ∀ r ∈ (ehFrame fdes gcc dwref).2, Fits ehAddr symAddr r)
    {pre post : List (Nat × Nat × List (Nat × Cfi) × Option Nat)} {b sz : Nat} {lo? : Option Nat}
    (hfd : fdes = pre ++ (b, sz, rows, lo?) :: post) {pc : Nat}
    (hpc : symAddr 1 + b ≤ pc ∧ pc < symAddr 1 + b + sz % 2 ^ 32)
    (hpre : ∀ y ∈ pre, ¬ (symAddr 1 + y.1 ≤ pc ∧ pc < symAddr 1 + y.1 + y.2.1 % 2 ^ 32))
    (gccB : List UInt8) (hL : lo?.isSome = lsda.isSome)
    (hG : ∀ lo sites, lo? = some lo → lsda = some sites →
      ∃ rest, gccB.drop lo = (lsdaBytes sites).data.toList ++ rest)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    ∃ T, Unw.tablesAt (linkSection (ehFrame fdes gcc dwref).1.data.toList (ehFrame fdes gcc dwref).2
        ehAddr symAddr) ehAddr gccB (symAddr gcc) pc = some (symAddr 1 + b, T) ∧
      ArmRefinesU fb base ra (Unw.ArmStepU X H U T fa) s (Clif.runLoopX env p fuel cs.toX) :=
  ⟨⟨cieInsns, insnsFrom 0 rows, lsda.map (List.map (·.entry))⟩,
    tablesAt_ehFrame fdes gcc dwref ehAddr symAddr hok hb hsz hfit hfd hpc hpre gccB hL hG,
    backend_correct_final_cleanup_unwind hsub hc hlU hcov hC hCT hTls hU hX hXI hXR hXRi hsym hslot
      hsites rfl hrows rfl rfl hpad hlast hsaved hent hres hbe hargs hcs hrel htr fuel⟩

/-! ## Witness: the compiled `try_call` function of `DeadCleanupUnwindWitness`, linked -/

namespace EhFrameFinalWitness

open DeadCleanupUnwindWitness

/-- Its `.eh_frame` (the function at offset 0 of `.text`, its LSDA at offset 0 of
`.gcc_except_table`), placed as in `EhFrameDecode.EhWitness`. -/
def fdes : List (Nat × Nat × List (Nat × Cfi) × Option Nat) := [(0, fb.size, rows, some 0)]
def gccB : List UInt8 := (lsdaBytes (lsda.getD [])).data.toList

/-- The decidable placement facts of the linked section (a closed receipt, as
`DeadCleanupUnwindWitness.checks_true`). -/
theorem placed :
    af.frame = true ∧
    (∀ x ∈ fdes, (cfiProgram x.2.2.1).data.toList.length + 24 < 0xffffffff) ∧
    (ehFrame fdes 2 3).1.size < 2 ^ 32 ∧
    (∀ r ∈ (ehFrame fdes 2 3).2, Fits 0x480000 EhWitness.symAddr r) ∧
    0 < fb.size % 2 ^ 32 := by
  simp only [Fits]; native_decide

/-- **`backend_correct_final_cleanup_unwind_eh` applies**: at the function's first instruction
the unwinder's lookup in the linked sections finds the function and tables for which the
function refines its CLIF semantics (open premises: those of `final_applies`). -/
theorem final_applies_eh {X0 : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {K : Nat}
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K (Xr X0) H
      vcp.CallSite)
    (hCT : ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) (Xr X0) H
      vcp.TrySite)
    (hsym : ∀ n b, syms n = some b → (Xr X0).sym n 0 = BitVec.ofNat 64 b)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn source.sig args s) (hcs : ClifEntry source args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, af.slotBase, (RAFrame.compute vcp rf).intBase⟩ source cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX IselSimUWitness.env { funcs := [] } cs) (fuel : Nat) :
    ∃ T, Unw.tablesAt (linkSection (ehFrame fdes 2 3).1.data.toList (ehFrame fdes 2 3).2 0x480000
        EhWitness.symAddr) 0x480000 gccB 0x500000 0x400000 = some (0x400000, T) ∧
      ArmRefinesU fb base ra (Unw.ArmStepU (Xr X0) H Uw T fa) s
        (Clif.runLoopX IselSimUWitness.env { funcs := [] } fuel cs.toX) := by
  obtain ⟨hv, hs, ht, hc, hlU, hsv, hpad, hlast, hcs', hsome, hrows⟩ := facts
  obtain ⟨hf, hb, hsz, hfit, hpos⟩ := placed
  exact backend_correct_final_cleanup_unwind_eh (InSubset.of_verifiable hv (fun _ => rfl)) hc hlU
    (formsCovered_cleanup_complete (lowerScope_of hs) hc.lower hc.prepare _) hC (fun _ => hCT)
    (fun h => absurd h (by rw [ht]; decide))
    (fun base s => calleeUnwOkG_raise _ _ _ s _ X0 _)
    (fun _ => xCallsOk_env _ _ _) (fun _ => xCallsIndOk_env _ _ _)
    (fun _ => IselSimUWitness.xRaiseOk _ _ _) (fun _ => IselSimUWitness.xRaiseIndOk _ _ _)
    hsym rfl hcs' hrows hpad hlast hsv fdes 2 3 0x480000 EhWitness.symAddr
    (by simp only [fdes, List.mem_singleton, forall_eq]; exact (unwindRows_frame hrows hf).1)
    hb hsz hfit (pre := []) (post := []) rfl ⟨Nat.le_refl _, by simp [EhWitness.symAddr]; omega⟩
    (by simp) gccB (by rw [hsome]; rfl)
    (fun lo sites h1 h2 => ⟨[], by cases h1; simp [gccB, h2]⟩)
    hent hres hbe hargs hcs hrel htr fuel

end EhFrameFinalWitness

end E2E

