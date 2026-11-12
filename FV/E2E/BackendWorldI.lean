import FV.E2E.IselSimITry
import FV.E2E.GotFlowI
import FV.E2E.PrepareSoundW
import FV.E2E.RegLevelCorrectPRS

/-!
# The per-function theorem with the final world, counted (SEM1, `docs/plans/uninit.md` §5.9)

`backend_correct_world` (`FV/E2E/LinkWorld.lean`) for the counted VCode run, the pipeline the
linking with byte and register prophecies needs (`thmPR_of`, item (a) of §5.8's remaining list):

* CLIF → counted VCode: `iselSim_relWI` (the callee contract of call number `n` only at the CLIF
  states reached after `n` extern calls, for the environment restricted to their invocation);
* `prepare`: `prep_soundW` for `csemI` (`DriverSemG.csemI`);
* the GOT sites: `vRetFrom_gotVI`/`vTrapFrom_gotVI`;
* VCode → Arm: `regLevelCorrect_worldPRS` (the machine contract of call `n` only at the
  activation's own call-`n` states, with the byte prophecy `P n` and register prophecy `R n`).

`ActEntryPR`: `ActEntry` with the prophecies and the indexed contracts.
**`backend_correct_worldPRI`**: for a returning CLIF run, one counted VCode outcome that every
`ActEntryPR` activation realises (`ActRet`, `PostTrace`); for a trapping run, every such
activation reaches a trap site. Legacy path (`Compiled`); the cleanup path (`CompiledCleanup`)
is the next item.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **`ActEntry` with the prophecies of the machine run** (bytes `P`, masked registers `R`, at the
body `sp` `c` with the callees' region `Kp`) and the callee contracts of each call index needed
only at the activation's call states of that index. -/
structure ActEntryPR (vcp : VCode) (rf : RFunc) (af : AFunc) (fa : FnAsm) (fb : FnBin) (K : Nat)
    (F G : BitVec 64 → Prop) (XI : ExtSemI) (H : ArmHooks) (base ra : BitVec 64)
    (Kp : Nat) (c : BitVec 64) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState)
    (s w₀ : Arm.ArmState) : Prop where
  abi : AbiCall fb base ra s
  stack : StackAvail K af s
  gfree : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a
  hF : frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s = F
  proph : ProphOk Kp c (ArmStepX (XI.at 0) H fa) fa base s P
  regp : ProphRegOkM c (ArmStepX (XI.at 0) H fa) fa base s R
  calls : ∀ n, CalleeOkGP (fun u => OnCallPR Kp c P R (ArmStepX (XI.at 0) H fa) fa base s n u ∧
      spOf u = spv s - BitVec.ofNat 64 (frameDrop af))
    F K G s (CallAt fa base) (XI.at n) H vcp.CallSite (GotV vcp)
  tries : vcp.hasTryCall = true → ∀ n, CalleeTryOkGP (fun u =>
      OnCallPR Kp c P R (ArmStepX (XI.at 0) H fa) fa base s n u ∧
        spOf u = spv s - BitVec.ofNat 64 (frameDrop af))
    F K G s (CallAt fa base) (XI.at n) H vcp.TrySite (GotV vcp)
  tls : vcp.hasTls = true → ∀ n, TlsOk F K (XI.at n) H
  body : BodyEntryW F vcp.EntryArg af s w₀

/-- **The per-function theorem with the final world, counted** (see the module doc). -/
theorem backend_correct_worldPRI {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetPins vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat) (cc : BitVec 64)
          (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
          ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX (XI.at 0) H fa) n s) ∧
            PostTrace fa af base (ArmStepX (XI.at 0) H fa) s n) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat) (cc : BitVec 64)
        (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
        ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX (XI.at 0) H fa) n s)) := by
  have hI := iselSim_relWI hsub hc hone htc hX hsym hslot (fun _ => 0) hcs hrel hargs htr fuel
  have hP := prep_soundW (DriverSemG.csemI fun m =>
    (driverSem_csem F ⟨fa.k, af.slotBase⟩ (XI.at m)).toDriverSemG) hc.prepOk (fun _ => 0) (w₀, 0)
  have hM6 : ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat)
      (cc : BitVec 64) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
      ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ → _ :=
    fun H G base ra Kp cc P R s he => by
      have h := regLevelCorrect_worldPRS hc.check hc.alloc hc.emit hc.layout (XI := XI) (H := H)
        (K := K) (G := G) (gv := GotV vcp) hcov he.abi he.stack he.gfree he.proph he.regp
        (by rw [he.hF]; exact he.calls) (by rw [he.hF]; exact he.tries)
        (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body) (fun _ => 0)
      rw [he.hF] at h
      exact h
  refine ⟨fun vals cm hrun => ?_, fun c' hrun H G base ra Kp cc P R s he => ?_⟩
  · obtain ⟨us, outs, ⟨w, nc⟩, hv, hus, hlen, hhold, hmemR⟩ := hI.1 vals cm hrun
    have hrs : vc.RetsSite us := by
      obtain ⟨b, k, ρ, w₁, vb, ops, outs', -, hvb, hk, -⟩ := hv
      exact ⟨b, vb, k, hvb, hk⟩
    refine ⟨us, outs, w, hus, hlen, hhold, hmemR, hrs, fun H G base ra Kp cc P R s he => ?_⟩
    obtain ⟨n, h1, h2, h3, h4, h5, h6, h7⟩ :=
      (hM6 H G base ra Kp cc P R s he).1 us outs w nc (vRetFrom_gotVI (hP.1 _ _ _ hv))
    exact ⟨n, ⟨h1, h2, h3, h4, h5, h6⟩, h7⟩
  · exact (hM6 H G base ra Kp cc P R s he).2 c' (vTrapFrom_gotVI (hP.2 c' (hI.2 c' hrun)))

end E2E
