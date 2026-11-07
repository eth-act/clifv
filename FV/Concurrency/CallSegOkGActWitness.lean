import FV.Concurrency.CallSegOkG
import FV.Concurrency.CallEntryLinkWitness
import FV.Concurrency.CallRetLinkWitness
import FV.Concurrency.ArmAllocPauseWitness
import FV.Concurrency.CallResumeChecksWitness
import FV.Concurrency.CallArgsL2Witness

/-!
# Witnesses for `CallSegOkG`'s activations (#473, step (4))

On the link of the compiled caller and the compiled `atomic_load` (`LinkedMachine.Witness.link2`):

* **`statOk_C`**: the caller's activation at its ABI entry `sC0` (its CLIF function `fC`) has its
  `StatOk`, for every memory relation base `c` 16-aligned, slots, callers and open activations;
* `chainP_entry_C`, `chainP_resume_C`: `chainP_entry`/`chainP_resume` on it (from its ABI entry
  with the CLIF entry state related to the body-entry world `w₀C`; from every paused
  configuration related to a CLIF state);
* `ret_seg_ld`: `ret_seg` for every activation of `atomic_load` entered by the caller's `bl`
  (return address `RC.pcOf 15 + 4`) below the caller's suspended frame `extC`, at its done
  `return` with its contract.

Checks by `native_decide` (witness only).
-/

namespace Concurrency.CallSegOkG.Witness

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck ThreadRefine IselCall IselCallRet ArmAllocThread E2E
  ClifCStepTerm IselThread CallRetsEnd CallRetsN CallSegAbi LinkedMachine LinkedMachine.Link
  LinkedMachine.Witness CallComposeT CallSeg.WitnessC CallEntry.Witness CallResumeL.Witness

/-- **The caller's activation is statically checked** (module doc). -/
theorem statOk_C {env : Clif.Env} (henv : env.extern "ld" = none) {c : BitVec 64}
    (hc : c.toNat % 16 = 0) (slots : List (Clif.SlotId × Nat))
    (ext : List (Clif.Frame × List Clif.ValueId)) (caller : LFn) (opens : List (Clif.Mem × Nat)) :
    ∃ g : Act, g.nm = "f" ∧ g.F = callerF ∧ g.s0 = sC0 ∧ g.K = 0 ∧ g.G = GL ∧
      g.ra = 0x4000#64 ∧ g.f = fC ∧ g.vc = vcC ∧ g.Γ = ΓC ∧ g.c = c ∧ g.slots = slots ∧
      g.ext = ext ∧ g.caller = caller ∧ g.opens = opens ∧ StatOk link2 env pCL g := by
  obtain ⟨ctx, st0, R, gn, bl, A, H, hchk, har, hcu⟩ := driverA_fC henv c
  obtain ⟨Lp, ss, ss', H3, hm3⟩ := CallLayers.prep_init (vc := vcC) (vcp := RC.vc) prepC
  obtain ⟨cc, ins, a0, hat, hm4⟩ := CallLayers.alloc_init (vc := RC.vc) (rf := RC.rf) allocC ckeep
  obtain ⟨hlow, -, -, hnames, hind, hv, hnt, -, hout0, -, hexts⟩ := IselCall.Witness.checksFC
  refine ⟨⟨"f", callerF, sC0, 0, GL, 0x4000#64, fC, vcC, ctx, st0, R, gn, bl, A, ΓC, c, Lp, ss,
    ss', cc, ins, a0, slots, ext, caller, opens, fun _ => False, []⟩, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, ?_⟩
  exact {
    mem := by simp [link2]
    wf := wf_C
    scope := scopeRC
    abi := abiRC
    H := H
    chk := hchk
    ΓF := rfl
    align := hc
    tls := VCodeThread.Witness.X0_tls
    noCall := fun _ _ _ => rfl
    H3 := H3
    checked := hat
    ok := ok2
    slot := rfl
    sym := fun _ _ h => by cases h
    reg := IselCall.Witness.fC_reg
    pinit := hm3 _ _
    minit := hm4
    res := CallArgsL2.Witness.resLen_fC
    cu := hcu
    ar := har
    low := hlow
    ind := List.isEmpty_iff.mp hind
    ver := hv
    nt := hnt
    out0 := hout0
    uv := Concurrency.CallArgsAt.Witness.usesV_fC
    dv := CallResumeAll.Witness.defs_fC.1
    uniq := fun e he e' he' _ => by
      rw [hexts, List.mem_singleton] at he he'; rw [he, he']
    envx := fun e he => by
      have : e.2.name ∈ fC.externs.map (·.2.name) := List.mem_map_of_mem he
      rw [hnames, List.mem_singleton] at this
      rw [this]; exact henv
    sigs := fun e he callee hp => by
      rw [hexts, List.mem_singleton] at he
      subst he
      obtain ⟨-, hf, -⟩ := clifC
      rw [hf] at hp; cases hp
      exact LinkedMachine.Witness.sig_fL
    probe := ArmAllocThread.ProbeF.of_small (show callerF.af.frameSize + 16 < 4096 by
      rw [show callerF.af.frameSize = 160 from spC.2.2.2.2.2.2.2.1]; decide) }

/-- **Non-vacuity of `chainP_entry`**: the caller from its ABI entry, every premise holding but
the CLIF entry state, its relation to the body-entry world `w₀C` and the arguments. -/
theorem chainP_entry_C {env : Clif.Env} (henv : env.extern "ld" = none) {c : BitVec 64}
    (hc : c.toNat % 16 = 0) (slots : List (Clif.SlotId × Nat)) :
    ∃ g : Act, g.F = callerF ∧ g.s0 = sC0 ∧ g.f = fC ∧ g.slots = slots ∧
      StatOk link2 env pCL g ∧
      ∀ (cs : Clif.State) (B0 : Clif.Block) (args : List Clif.Val) (mon : Mon),
        fC.blocks[0]? = some B0 → cs.callers = [] → cs.frame.func = fC →
        cs.frame.slots = slots → cs.frame.body = B0.body → cs.frame.term = B0.term →
        Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs →
        args.map (·.ty) = B0.params.map (·.2) → args.map (·.ty) = fC.sig.params.map (·.ty) →
        RelW ΓC fC c slots cs.mem w₀C → ArgsAtEntry RC.F fC.sig args w₀C →
        ChainP link2 env pCL g (g.r0 link2) (sC0, mon) cs := by
  obtain ⟨g, -, hF, hs0, hK, hG, hra, hf, -, hΓ, hcg, hsl, -, -, -, hS⟩ :=
    statOk_C henv hc slots [] callerF []
  refine ⟨g, hF, hs0, hf, hsl, hS, fun cs B0 args mon hB0 hcall hfunc hslots hbody hterm hregs hty
    hsig hmr hargs => ?_⟩
  obtain ⟨g⟩ := g
  simp only at hF hs0 hK hG hra hf hΓ hcg hsl
  subst hF hs0 hK hG hra hf hΓ hcg hsl
  obtain ⟨-, hq, hA⟩ := q_init_lines (R := link2.act callerF sC0 0 GL) wf_C abiRC bodyRC
  exact chainP_entry hS hB0 hcall hfunc hslots hbody hterm hregs hty hsig hmr hargs hq hA

/-- **Non-vacuity of `chainP_resume`**: the caller from every paused configuration related to a
CLIF state. -/
theorem chainP_resume_C {env : Clif.Env} (henv : env.extern "ld" = none) {c : BitVec 64}
    (hc : c.toNat % 16 = 0) (slots : List (Clif.SlotId × Nat)) :
    ∃ g : Act, g.F = callerF ∧ g.s0 = sC0 ∧ g.f = fC ∧ StatOk link2 env pCL g ∧
      ∀ (r₀ : Reg → CV) (s : Clif.State) (vV vP : VState CV ArmState) (cM : MState CV ArmState)
        (x : ArmState) (mon : Mon),
        (∀ r ∈ (g.RL link2).af.saves, ckeep r (r₀ r) = ckeep r (regVal (g.RL link2).s0 r)) →
        Match g.f g.ctx g.R g.gn g.bl g.A (RelW g.Γ g.f g.c) g.slots s vV →
        PMatch g.vc g.F.vc (csem (g.RL link2).F (g.RL link2).ctx (g.RL link2).X)
          (cEvs (g.RL link2).F (g.RL link2).ctx) g.Lp g.ss' (.run vV) (.run vP) →
        MatchRun g.cc g.ins ckeep r₀ cM vP → Q (g.RL link2) x (.run cM) →
        AInv (g.RL link2) (.run cM) → ChainP link2 env pCL g r₀ (x, mon) s := by
  obtain ⟨g, -, hF, hs0, -, -, -, hf, -, -, -, -, -, -, -, hS⟩ :=
    statOk_C henv hc slots [] callerF []
  exact ⟨g, hF, hs0, hf, hS, fun r₀ s vV vP cM x mon hr₀ hm2 hm3 hm4 hq hA =>
    chainP_resume hS hr₀ hm2 hm3 hm4 hq hA⟩

open RealizeCompiled.WitnessL in
/-- `atomic_load`'s activation entered at `s0` by the caller's `bl`, below `extC`. -/
def actL (s0 : ArmState) : Act where
  nm := "ld"
  F := ldF
  s0 := s0
  K := 0
  G := RC.F
  ra := RC.pcOf 15 + 4#64
  f := fL
  vc := vcL
  ctx := { func := fL, insts := #[], valTy := #[], valDef := #[], valReg := #[], slotOff := [] }
  st0 := default
  R := id
  gn := id
  bl := []
  A := fun _ _ => []
  Γ := ΓL
  c := 0
  Lp := fun _ => False
  ss := #[]
  ss' := #[]
  cc := ⟨vcpL, #[], rfL, 0⟩
  ins := #[]
  a0 := default
  slots := []
  ext := extC
  caller := callerF
  opens := []

/-- **Non-vacuity of `ret_seg`**: every activation of `atomic_load` entered by the caller's `bl`
at its done `return` with its contract, below the caller's suspended frame. -/
theorem ret_seg_ld {s0 : ArmState} {env : Clif.Env} {p : Clif.Program}
    (hRB : (link2.act ldF s0 0 RC.F).Wf) (hent : AbiCall ldF.fb ldF.base (RC.pcOf 15 + 4#64) s0)
    {x : ArmState} {sR : Clif.State}
    (hret : RetEnd ((actL s0).RL link2) (actL s0).ra env p (RelW (actL s0).Γ (actL s0).f (actL s0).c)
      (actL s0).slots ((actL s0).r0 link2) x sR)
    (hat : AtRetS sR) (hcall : sR.callers = []) (U D : Nat → Prop) {mon : Mon} {ls : List Lab}
    {t' : ArmState × Mon} (hr : PRun Policy.arm link2.M (OkPriv ((actL s0).RL link2)) (x, mon) ls t') :
    ∃ k d', RealT env p (fun _ => True) ls k (encT U (.run (ClifLift.pushC extC sR)), D) d' ∧
      (k = ls.length ∨
        (∃ vals cm, Clif.step env p sR = .done vals cm ∧
          ({ csC.frame with body := [] } : Clif.Frame).regs.setMany [1] vals = none ∧
          k = 0 ∧ d' = (encT U (.run (ClifLift.pushC extC sR)), D)) ∨
        ∃ vals cm regs v, Clif.step env p sR = .done vals cm ∧
          ({ csC.frame with body := [] } : Clif.Frame).regs.setMany [1] vals = some regs ∧
          RetC ((actL s0).RL link2) (RC.pcOf 15 + 4#64) ((actL s0).r0 link2)
            (iterN ((actL s0).RL link2).step k x) ∧
          PRun Policy.arm link2.M (OkPriv ((actL s0).RL link2)) (x, mon) (ls.take k) v ∧
          v.1 = set_program (iterN ((actL s0).RL link2).step k x) (callerF.fb.program callerF.base) ∧
          d' = (encT U (.run ⟨{ ({ csC.frame with body := [] } : Clif.Frame) with regs := regs }, [],
            cm⟩), fun a => D a ∨ PrivA ((actL s0).RL link2) a)) :=
  ret_seg (g := actL s0) (Bnd := fun _ => True) ok2 (by simp [actL, link2]) hRB hent
    (fun _ _ => trivial) (cnm := "f") (by simp [actL, link2]) ra_in ra_out rfl hret hat hcall U D hr

end Concurrency.CallSegOkG.Witness
