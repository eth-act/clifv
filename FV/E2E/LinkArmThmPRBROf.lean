import FV.E2E.LinkArmStage2Y
import FV.E2E.BackendWorldPRGY
import FV.E2E.LinkArmThmPRBR
import FV.E2E.LinkArmProgCallPRBRL
import FV.E2E.LinkArmEnvOfB

/-!
# The induction step of `ThmPRBRL` from the pipeline (SEM1 #537, #680 (3), `thmPRBRL_of`)

`thm_of` (`LinkArm`) for the slot-byte statement: the activation runs under `envOfB`
(`runLoop_envOfB`), `backend_correct_world_pipelinePRGY` with `XI := XPBTI` (guarded:
`XPBTGY`, #692) gives the outcome, its `ActEntryPR` is built from `MachEntryPR` with the call
contracts `calleeOkXPBTGY` at the activation's call states, and the table up to the return is the
caller's (`TableOf`, `noRetAt_of`). Three per-activation facts stay premises of this step, each
stated for the activations of depth `M` (`ThmPRBRL`'s premises; `ThmPRBRL` is `ThmPRBR` with the
advance from the popped entry, #694):

* `RetOkPRB κ M`: the scope fact `InvokedRetOk` of the activation's run under `envOfB` (the
  invoked externs keep validity and symbols and agree on ABI return counts);
* `Stage2PRB κ M`: stage 2 at the activation's call-`n` states (`Stage2Y`);
* `CountPRB κ M`: the CLIF counter advance of the run is the machine table's count up to the
  return.

**`thmPRBRL_of`**: `ThmPRBRL κ M` from `ThmPRBRL κ (M - 1)`, `DetPRB κ (M - 1)` and the three;
**`thmPRBRL_of_thm`**: `ThmPRBRL` from `Thm` without program callees with slots.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- The register prophecy of `g`'s machine run from `s`. -/
noncomputable abbrev RP (M : Nat) (g : Clif.Function) (s : Arm.ArmState) : Nat → Arm.ArmState :=
  prophStOf (L.mach M g) (L.A g).fa (L.A g).base s

/-- The byte prophecy of `g`'s machine run from `s`. -/
noncomputable abbrev BP (M : Nat) (g : Clif.Function) (s : Arm.ArmState) :
    Nat → BitVec 64 → BitVec 8 :=
  prophOf (L.mach M g) (L.A g).fa (L.A g).base s

/-- The activation's call-`n` states (`ActEntryPR.calls`). -/
def CallStPRB (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function) (s w₀ : Arm.ArmState)
    (n : Nat) (u : Arm.ArmState) : Prop :=
  OnCallPR (κ M g) (spv w₀) (L.BP M g s) (L.RP M g s) (L.mach M g) (L.A g).fa (L.A g).base s n u ∧
    spOf u = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af)

/-- **The scope fact of the activations' runs under `envOfB`.** -/
def RetOkPRB (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (ini : Clif.SlotInit), L.WorldEntryB κ M g F vals cs w₀ ini →
    InvokedRetOk (L.envOfB M g (spv w₀)) L.P.bare cs (g.externs.map (·.2)) (indSigs g)

/-- **Stage 2 at the activations' call states.** -/
def Stage2PRB (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (ini : Clif.SlotInit) (G : BitVec 64 → Prop) (ra : BitVec 64)
    (s : Arm.ArmState),
    L.WorldEntryB κ M g F vals cs w₀ ini →
    L.MachEntryPR κ M g F G ra s w₀ (L.BP M g s) (L.RP M g s) →
    RaOk (L.A g) (ra - 4) → L.TableOf M g s ini →
    ∀ n, L.Stage2Y κ M g F (L.BP M g s) (L.RP M g s) (L.envOfB M g (spv w₀)) cs (spv w₀)
      (L.CallStPRB κ M g s w₀ n) n

/-- **The CLIF counter advance of a returning run is the machine table's count to the return.** -/
def CountPRB (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (fuel : Nat) (rvals : List Clif.Val) (cm' : Clif.Mem)
    (ini : Clif.SlotInit) (G : BitVec 64 → Prop) (ra : BitVec 64) (s : Arm.ArmState),
    L.WorldEntryB κ M g F vals cs w₀ ini →
    L.MachEntryPR κ M g F G ra s w₀ (L.BP M g s) (L.RP M g s) →
    RaOk (L.A g) (ra - 4) → L.TableOf M g s ini →
    Clif.runLoop (L.envR M g) L.P.bare fuel cs = .returned rvals cm' →
    ∀ (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState) (n e : Nat),
      ActRet ra F G us outs wf s (runX (L.mach M g) n s) →
      PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s n →
      L.TabUpTo M g s ini.bytes ini.next n e → L.NeedSlots → Clif.NextAdv cs.mem.leave cm' e

/-- The activation's call states see the prophecies (`calleeOkPRBRL`'s `hQ`). -/
theorem callStPRB_q {M : Nat} {g : Clif.Function} {s w₀ : Arm.ArmState}
    (hsp : spv w₀ = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af)) (n : Nat) :
    ∀ t, L.CallStPRB κ M g s w₀ n t → CallPc (L.A g).fa (L.A g).base (Arm.r .PC t) →
      (∀ f, MaskedReg f → Arm.r f t = Arm.r f (L.RP M g s n)) ∧
        ∀ a, StackBelow (κ M g) (spv t) a → t.mem a = L.BP M g s n a := by
  intro t ⟨⟨⟨_, hb⟩, hr⟩, hst⟩ hpc
  have e : spv t = spv w₀ := by rw [hsp]; exact hst
  refine ⟨fun f hf => hr hpc e f hf.1 hf.2, fun a ha => ?_⟩
  rw [e] at ha
  exact hb hpc e a ha

/-- **The induction step of `ThmPRBRL`** (module doc). -/
theorem thmPRBRL_of (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1)) (hdet : 0 < M → L.DetPRB κ (M - 1))
    (hret : L.RetOkPRB κ M) (h2 : L.Stage2PRB κ M) (hcnt : L.CountPRB κ M) :
    L.ThmPRBRL κ M := by
  intro g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra htab hrun
  have hc := hL.compiled g hg
  have hI : Clif.LInv (L.P.only g) cs := runInv_entry (by simp [Clif.Program.only]) hWE.clif
  have hJ : L.ActInvB g (spv w₀) cs := ⟨hI, hWE.clif.callers, fun hN => ⟨ini, hWE.place hN⟩⟩
  have hrun' : Clif.runLoop (L.envOfB M g (spv w₀)) L.P.bare fuel cs = .returned rvals cm' := by
    rw [L.runLoop_envOfB hL hg fuel cs hJ]; exact hrun
  have hPf : ∀ f ∈ (L.P.only g).funcs, Clif.LinkFree f := fun f hf => by
    simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf; exact hL.free f hg
  have hnrc : NoRetCall (L.envOfB M g (spv w₀)) L.P.bare cs :=
    noRetCall_of_linv hPf (fun _ h => by simp at h) hI
  have h := backend_correct_world_pipelinePRGY (hL.subset g hg) hc
    (XI := L.XPBTI κ M g F (L.BP M g s) (L.RP M g s)) (syms := L.syms)
    (env := L.envOfB M g (spv w₀)) (K := κ M g) (F := F) (c := spv w₀) (hL.covered g hg)
    hnrc (hret g hg F vals cs w₀ ini hWE) (fun n b hn => hL.symOk n b hn) rfl hWE.clif hWE.rel
    hWE.args (trapsExplicit_of_returned hrun') fuel
  obtain ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall⟩ := h.1 rvals cm' hrun'
  have he := hME.entryP.entry
  have hQ := L.callStPRB_q (κ := κ) (M := M) he.body.sp
  have hAE : ActEntryPR (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb (κ M g) F G
      (L.XPBTGY κ M g F (L.BP M g s) (L.RP M g s) (L.envOfB M g (spv w₀)) cs (spv w₀))
      (L.hooks M) (L.A g).base ra (κ M g) (spv w₀) (L.BP M g s) (L.RP M g s) s w₀ :=
    ⟨he.abi, he.stack, he.gfree, he.hF, hME.entryP.proph, hME.reg,
      fun n => L.calleeOkXPBTGY hL hκ ih hdet hg he (hQ n)
        (h2 g hg F vals cs w₀ ini G ra s hWE hME hra htab n),
      fun _ n => L.calleeTryOkXPBTGY hL hκ ih hdet hg he (hQ n)
        (h2 g hg F vals cs w₀ ini G ra s hWE hME hra htab n),
      fun ht _ => by
        have h0 := hL.baseTls g hg (hasTls_of_vcode_pipeline hc ht) F (κ M g)
        cases M <;> exact ⟨h0.pc, h0.seq, h0.flags⟩,
      he.body⟩
  obtain ⟨n, hret', htr⟩ := hall (L.hooks M) G (L.A g).base ra (κ M g) (spv w₀) (L.BP M g s)
    (L.RP M g s) s hAE
  have hnr := L.noRetAt_of hL hg he hra htr hret'.ret.err
  obtain ⟨e, hte⟩ := htab n hnr
  exact ⟨us, outs, wf, n, e, hus, hlen, hhold, hmem, hrs, hret', htr, hte,
    hcnt g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra htab hrun us outs wf n e hret' htr
      hte⟩

/-- **`ThmPRBRL` from `Thm` without program callees with slots** (`thmPRBR_of_thm`). -/
theorem thmPRBRL_of_thm (hL : L.Ok) (hN : ¬ L.NeedSlots) {M : Nat} (hT : L.Thm κ M) :
    L.ThmPRBRL κ M := by
  intro g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra htab hrun
  obtain ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall, -⟩ :=
    hT g hg F vals cs w₀ fuel rvals cm' (hWE.toWorldEntry L hN) hrun
  obtain ⟨n, hret, htr⟩ := hall G ra s hME.entryP.entry
  obtain ⟨e, he⟩ := htab n (L.noRetAt_of hL hg hME.entryP.entry hra htr hret.ret.err)
  exact ⟨us, outs, wf, n, e, hus, hlen, hhold, hmem, hrs, hret, htr, he, fun h => absurd h hN⟩

end LinkSys

end E2E
