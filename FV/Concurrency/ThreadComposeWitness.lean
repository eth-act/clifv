import FV.Concurrency.ThreadCompose
import FV.Concurrency.IselRefinesWitness
import FV.Backend.SpillAlloc

/-!
# Witnesses: composing the per-thread layers (T2h, #311)

* `thin_take_w`, `refines_take_w`: `Thin.take` and `Refines.take` cutting real traces (a
  spill and an `ldar` after an atomic load's source step);
* **`isel_alloc_refines_fA`**: layers 2, 3 and 4a composed on the atomics function
  `SegShape.Witness.fA` as the pipeline compiles it: its lowering `vcA`, `prepare`'s output
  `vcpA` (`prepCheck` accepts), the spill allocation `rfA` (`checkAlloc` accepts); every premise
  of `ThreadCompose.isel_alloc_refines` but the CLIF entry state, its relation to the entry world,
  the arguments and the run of the allocated code is discharged. Checks by `native_decide`
  (witness only).
-/

namespace Concurrency.ThreadCompose.Witness

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselThread ThreadRefine E2E IselThread.Witness SegShape.Witness
  ClifCStepTerm IselRefines.Witness

/-! ## Cutting traces -/

/-- `Thin.take` keeps the step with the event and the empty target step before it. -/
theorem thin_take_w : ∃ m ≤ 3, Thin (([[1], [2]] : List (List Nat)).take 1)
    (([[], [1], [2]] : List (List Nat)).take m) := by
  obtain ⟨m, hm, ht, -⟩ := Thin.take (.tgt (.both (.both .nil)) :
    Thin ([[1], [2]] : List (List Nat)) [[], [1], [2]]) 1
  exact ⟨m, hm, ht⟩

/-- The source: an atomic load of `x` (address 8) reading 1, then a plain load of it. -/
def tS : List (List (Ev SKind BVal)) := [[⟨.scR, .R, 8, 1, [some 1]⟩], [⟨.naR, .R, 8, 1, [some 1]⟩]]
/-- The target: a spill to the thread's frame (address 100), the `ldar`, the `ldr`. -/
def tT : List (List (Ev AKind BVal)) :=
  [[⟨.plainW, .W, 100, 8, []⟩], [⟨.acqR, .R, 8, 1, [some 1]⟩], [⟨.plainR, .R, 8, 1, [some 1]⟩]]

theorem evAt_tS {p : Nat × Nat} {x : Ev SKind BVal} (h : evAt tS p = some x) :
    (p = (0, 0) ∧ x = ⟨.scR, .R, 8, 1, [some 1]⟩) ∨ (p = (1, 0) ∧ x = ⟨.naR, .R, 8, 1, [some 1]⟩) := by
  obtain ⟨j, k⟩ := p
  rcases j with _ | _ | j <;> rcases k with _ | k <;> simp [evAt, tS] at h ⊢
  · exact h.symm
  · exact h.symm

theorem evAt_tT {p : Nat × Nat} {y : Ev AKind BVal} (h : evAt tT p = some y) :
    (p = (0, 0) ∧ y = ⟨.plainW, .W, 100, 8, []⟩) ∨ (p.1 = 1 ∨ p.1 = 2) ∧ y.dir = .R := by
  obtain ⟨j, k⟩ := p
  rcases j with _ | _ | _ | j <;> rcases k with _ | k <;> simp [evAt, tT] at h ⊢
  · exact h.symm
  · rw [← h]
  · rw [← h]

/-- The full refinement: source step `j` is target step `j + 1`. -/
theorem refines_tT : Refines Maps (fun l => l = 100) (fun _ _ => False) tS tT
    (fun p => (p.1 + 1, p.2)) where
  ev p x h := by
    rcases evAt_tS h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨⟨.acqR, .R, 8, 1, [some 1]⟩, by simp [evAt, tT], .inl rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨⟨.plainR, .R, 8, 1, [some 1]⟩, by simp [evAt, tT], rfl, rfl, rfl, rfl, rfl⟩
  mono p q hp hq hl := by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hp
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hq
    rcases evAt_tS hx with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rcases evAt_tS hy with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
      simp [Lt] at hl ⊢
  shared p x h _ := by
    rcases evAt_tS h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
  priv p y h hW _ := by
    rcases evAt_tT h with ⟨-, rfl⟩ | ⟨-, hd⟩
    · rfl
    · rw [hd] at hW; cases hW
  len j h := by
    have : j < 2 := by simpa [tS] using h
    rcases j with _ | _ | j <;> simp [tS]; omega
  pair j h h2 := by
    have : j < 2 := by simpa [tS] using h
    rcases j with _ | _ | j <;> simp [tS] at h2 ⊢; omega
  pair_inv p q _ _ hpr := hpr.elim

/-- **`Refines.take`**: the atomic load alone refines a prefix of the spill, the `ldar` and the
`ldr` (the `ldr`, image of the dropped plain load, is cut). -/
theorem refines_take_w : ∃ k ≤ 3,
    Refines Maps (fun l => l = 100) (fun _ _ => False) (tS.take 1) (tT.take k)
      (fun p => (p.1 + 1, p.2)) := by
  obtain ⟨k, hk, href, -⟩ := Refines.take refines_tT (fun j hj => by
    have : j < 3 := by simpa [tT] using hj
    rcases j with _ | _ | _ | j <;> simp [tT]; omega) 1
  exact ⟨k, hk, href⟩

/-! ## Layers 2, 3 and 4a on `fA` -/

/-- `prepare`'s output on `fA`'s lowering. -/
def vcpA : VCode := match Backend.prepare vcA with
  | .ok vcp => vcp
  | .error _ => default

/-- The spill allocation of `vcpA`. -/
def rfA : RFunc := spillAlloc vcpA

/-- `prepare` and the allocation of `fA`'s lowering are accepted. -/
theorem checks3A : prepCheck vcA vcpA = true ∧ (checkAlloc vcpA rfA).isOk = true := by
  native_decide

theorem allocA : checkAlloc vcpA rfA = .ok () := by
  have h := checks3A.2
  revert h
  cases checkAlloc vcpA rfA with
  | ok u => intro _; rfl
  | error e => intro h; cases h

/-- **Layers 2, 3 and 4a on `fA`** (module doc). -/
theorem isel_alloc_refines_fA {Γ : E2E.Rel} {fctx : FnCtx} {c : BitVec 64} {env : Clif.Env}
    {p : Clif.Program} (hc : c.toNat % 16 = 0) (hslot : fctx.slotBase = Γ.slotOff)
    (hsym : ∀ n b, Γ.syms n = some b → VCodeThread.Witness.X0.sym n 0 = BitVec.ofNat 64 b)
    {keep : Reg → CV → CV} :
    ∀ (slots : List (Clif.SlotId × Nat)) (cs : Clif.State) (B0 : Clif.Block)
      (args : List Clif.Val) (m₀ : Loc → CV) (w₀ : ArmState) (trM : List (List Ev))
      (cM : MConf CV ArmState),
      fA.blocks[0]? = some B0 → cs.callers = [] → cs.frame.func = fA →
      cs.frame.slots = slots → cs.frame.body = B0.body → cs.frame.term = B0.term →
      Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs →
      args.map (·.ty) = B0.params.map (·.2) → args.map (·.ty) = fA.sig.params.map (·.ty) →
      RelW Γ fA c slots cs.mem w₀ → ArgsAtEntry Γ.F fA.sig args w₀ →
      MTRun vcpA rfA (csem Γ.F fctx VCodeThread.Witness.X0) keep (cEvs Γ.F fctx)
        (MConf.init rfA m₀ w₀) trM cM →
      ∃ m trS t ψ, m ≤ trM.length ∧ CRun env p (.run cs) trS t ∧
        Refines Maps (fun _ => False) (StepPair (conv (trM.take m))) trS (conv (trM.take m)) ψ ∧
        (m = trM.length ∨ Stop env p t) := by
  intro slots cs B0 args m₀ w₀ trM cM hB0 hcall hfunc hslots hbody hterm hregs hty hsig hmr
    hargs hr
  obtain ⟨ctx, st0, R, gn, bl, A, H, hchk⟩ := driverHypA (env := env) (p := p) (c := c) hslot hsym
  exact isel_alloc_refines H hchk (memRelOk_relW Γ fA c) (relW_wf hc) VCodeThread.Witness.X0_tls
    (memRefines_csem Γ.F fctx _ hslot hsym) (mrStable_relW Γ fA c) fA_reg checks3A.1 allocA hB0
    hcall hfunc hslots hbody hterm hregs hty hsig (fun _ => 0) hmr hargs hr

end Concurrency.ThreadCompose.Witness
