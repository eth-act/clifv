import FV.E2E.LinkArmStage2Zero

/-!
# Stage 2 for returning runs (SEM1 #537, #680 (3): `Stage2PRB` reconsidered)

`Stage2PRB κ M` asks stage 2 (`Stage2Y`) at every call-`n` state of every activation entry,
without the activation's CLIF run returning. The way to discharge it at `M > 0` (strong
induction on `n`, `docs/plans/uninit.md` §5.9) needs the CLIF/machine call correspondence up to
call `n` (`prefix_relatedPRI`, extended to the call itself), whose premises include
`TrapsExplicit` of the CLIF run (`trapsExplicit_of_returned`): available only for returning runs,
which is where `thmPRBRL_of` uses stage 2. The states `CallStPRB … n` also include states after
the activation's return (the machine keeps running the caller's code when the return address is
in `g`'s code, `RaOk`); for a returning CLIF run with `K` calls those carry counts `≥` the
machine's return count, and at counts `n` with no CLIF invocation stage 2 holds vacuously
(`stage2Y_of_not_invoked`: `CallPost` of a restriction to no invocation accepts every result).
Decision (new names, `Stage2PRB` kept): `Stage2PRBR`, stage 2 under the activation's returning
CLIF run (as `CountPRB`); `Stage2PRB.toR`; **`thmPRBRL_ofR`** (`thmPRBRL_of` with `Stage2PRBR`);
`stage2PRBR_zero`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **Stage 2 at the call states of activations whose CLIF run returns.** -/
def Stage2PRBR (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (fuel : Nat) (rvals : List Clif.Val) (cm' : Clif.Mem)
    (ini : Clif.SlotInit) (G : BitVec 64 → Prop) (ra : BitVec 64) (s : Arm.ArmState),
    L.WorldEntryB κ M g F vals cs w₀ ini →
    L.MachEntryPR κ M g F G ra s w₀ (L.BP M g s) (L.RP M g s) →
    RaOk (L.A g) (ra - 4) → L.TableOf M g s ini →
    Clif.runLoop (L.envR M g) L.P.bare fuel cs = .returned rvals cm' →
    ∀ n, L.Stage2Y κ M g F (L.BP M g s) (L.RP M g s) (L.envOfB M g (spv w₀)) cs (spv w₀)
      (L.CallStPRB κ M g s w₀ n) n

theorem Stage2PRB.toR {M : Nat} (h : L.Stage2PRB κ M) : L.Stage2PRBR κ M :=
  fun g hg F vals cs w₀ _ _ _ ini G ra s hWE hME hra htab _ n =>
    h g hg F vals cs w₀ ini G ra s hWE hME hra htab n

theorem stage2PRBR_zero (hL : L.Ok) [L.CrunOk] : L.Stage2PRBR κ 0 :=
  (L.stage2PRB_zero hL).toR

/-- **Stage 2 is vacuous at a count without a CLIF invocation**: the restriction to no
invocation answers no call, so `CallPost` accepts every result. -/
theorem stage2Y_of_not_invoked {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop}
    {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {env : Clif.Env}
    {cs : Clif.State} {c : BitVec 64} {Q : Arm.ArmState → Prop} {n : Nat}
    (hno : ∀ nm vals m, ¬ InvokedN env L.P.bare cs n nm vals m) :
    L.Stage2Y κ M g F P R env cs c Q n := by
  intro u w _ _ d uses hnv
  refine absurd (fun r => ⟨fun ext _ G sl cm args vals rvals cm' hG _ _ _ hret _ => ?_,
    fun sig _ m G sl cm u args vals rvals cm' _ _ hG _ _ _ _ hret _ _ => ?_⟩) hnv
  · obtain ⟨G1, -, rfl⟩ := Clif.Env.only_extern_eq hG
    rw [Clif.onlyFn_of_not (hno _ _ _)] at hret
    cases hret
  · obtain ⟨G1, -, rfl⟩ := Clif.Env.only_extern_eq hG
    rw [Clif.onlyFn_of_not (hno _ _ _)] at hret
    cases hret

/-- **`thmPRBRL_of` with stage 2 for returning runs** (the same proof; stage 2 is used only at
the activation at hand, whose run returns). -/
theorem thmPRBRL_ofR (hL : L.Ok) [L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1)) (hdet : 0 < M → L.DetPRB κ (M - 1))
    (hret : L.RetOkPRB κ M) (h2 : L.Stage2PRBR κ M) (hcnt : L.CountPRB κ M) :
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
        (h2 g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra htab hrun n),
      fun _ n => L.calleeTryOkXPBTGY hL hκ ih hdet hg he (hQ n)
        (h2 g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra htab hrun n),
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

end LinkSys

end E2E
