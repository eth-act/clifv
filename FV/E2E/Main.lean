import FV.E2E.Compose

/-!
# M7: `backend_correct`

The end-to-end theorem from the layer hypotheses: M4's rule theorems (`LowerRulesCorrect`,
`ExcludedUnmatchable`, and the terminator calls `TermCalls`), M6+M5's register-level theorem
(`RegLevelCorrect`), the semantics facts `Refines`/`DriverSem` of the shared VCode semantics,
and M7's own remaining obligations (`LoweringObligations`, `PrepareCorrect`). The CLIF → VCode
driver simulation (`driver_correct`) and the composition (`backend_correct_of_layers`) are
proven.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

theorem memRel_free {F : BitVec 64 → Prop} {syms} {cm : Clif.Mem} {w : Arm.ArmState}
    (h : MemRel F syms cm w) (bases : List Nat) : MemRel F syms (cm.free bases) w := by
  have hv : ∀ a n, (cm.free bases).valid a n = true → cm.valid a n = true := by
    intro a n hv
    simp only [Clif.Mem.valid, Clif.Mem.free, List.any_eq_true, List.mem_filter] at hv ⊢
    obtain ⟨x, ⟨hx, -⟩, hc⟩ := hv
    exact ⟨x, hx, hc⟩
  exact ⟨fun a b ha hb => h.bytes a b (hv a 1 ha) hb, fun a n ha => h.valid a n (hv a n ha),
    h.symbols⟩

/-- The CLIF ↔ VCode relation only looks at memory outside `F` and at `sp`: M4's `MRStable`. -/
theorem mrStable_holds (Γ : Rel) (f : Clif.Function) :
    MRStable Γ.F (fun sl cm w => Γ.holds f sl cm w) := by
  intro sl cm w w' hsw ⟨hm, hs⟩
  have hsp : spv w' = spv w := by
    simp only [spv]
    exact hsw.1 (.GPR 31#5) (by simp [Masked]) (fun fl h => by cases h)
  refine ⟨⟨fun a b ha hb => ?_, hm.valid, hm.symbols⟩, ?_⟩
  · have hF := (hm.valid a 1 ha).2 0 (by omega)
    simp only [Nat.add_zero] at hF
    rw [← hm.bytes a b ha hb]
    simp only [Arm.read_mem, Arm.read_store]
    rw [hsw.2.1 _ hF]
  · simpa [Rel.slotReg, hsp] using hs

theorem noTail_of_subset {p : Clif.Program} {f : Clif.Function} (h : InSubset p f) :
    ∀ B ∈ f.blocks, ∀ fn args, B.term ≠ .returnCall fn args := by
  intro B hB fn args ht
  have := h.subsetE
  simp only [Compile.functionE, Bool.and_eq_true, List.all_eq_true] at this
  have := (this.2 B hB).2
  rw [ht] at this
  simp [Compile.termE] at this

theorem cfg_of_prepare {vc vcp : VCode} (h : prepare vc = .ok vcp) :
    ∃ ss ps, vc.cfg = .ok (ss, ps) := by
  unfold prepare at h
  cases hc : vc.cfg with
  | ok r => exact ⟨r.1, r.2, rfl⟩
  | error e => rw [hc] at h; cases h

/-- **CLIF → VCode** from the driver simulation. -/
theorem iselSim_of_driver {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
    {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    {sem : Sem} {Γ : Rel} {env : Clif.Env} {p : Clif.Program}
    (H : DriverHyp f vc ctx st0 R gn bl A sem (fun sl cm w => Γ.holds f sl cm w) env p) :
    IselSim sem Γ env p f vc := by
  intro args cs w₀ ρ₀ hce hrel hargs htr fuel
  obtain ⟨B0, hent, hbody, hterm, -, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hrun := driver_correct H hB0 hce.callers hce.func rfl hbody hterm hregs (ρ₀ := ρ₀) hrel
    (fun i v h => hargs i v h) htr fuel
  refine ⟨fun vals cm h => ?_, fun c h => ?_⟩
  · rw [h] at hrun
    obtain ⟨us, outs, w, cm0, hret, h1, h2, h3, h4, h5⟩ := hrun
    exact ⟨us, outs, w, hret, h1, h2, h3, h5 ▸ memRel_free h4.1 _⟩
  · rw [h] at hrun
    exact hrun

/-- **`backend_correct` (M7).** For an in-subset CLIF function `f` of `p`, compiled by the
Lean backend (`Compiled`) and loaded at `base`, an Arm execution from an ABI entry state with
enough stack, whose CLIF counterpart `cs` has its stack slots at the Arm frame's slot region
and its memory related to the Arm memory, refines the CLIF run: returns with the same values
(low bits) and memory, traps at a trap site with the same code (explicit traps). Hypotheses:
M4 (`hrules`, `hex`, `hterms`), M6+M5 (`hM6`), the shared VCode semantics (`hRef`, `hds`),
M7's remaining obligations (`hlow`, `hprep`). -/
theorem backend_correct {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    {sem : Sem} {F : Arm.ArmState → BitVec 64 → Prop} {syms : String → Option Nat}
    {slotOff : Nat} {astep : Arm.ArmState → Arm.ArmState} {env : Clif.Env}
    -- M4
    (hrules : LowerRulesCorrect Isle.Aarch64.program)
    (hex : ExcludedUnmatchable Isle.Aarch64.program)
    (hterms : ∀ s, TermCalls sem (fun sl cm w => Rel.holds ⟨F s, syms, slotOff⟩ f sl cm w))
    -- M6 + M5
    (hM6 : RegLevelCorrect sem F astep vcp af fb)
    -- the shared VCode semantics (M6's `csem`)
    (hRef : ∀ s, Refines (F s) sem) (hds : DriverSem sem)
    -- M7, remaining
    (hlow : LoweringObligations f vc) (hprep : PrepareCorrect sem vc vcp)
    -- the run
    {base ra : BitVec 64} {s : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail af s) (hargs : ArgsIn args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff⟩ f cs.frame.slots cs.mem s)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra astep s (Clif.runLoop env p fuel cs) := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert⟩ := hlow
  refine backend_correct_of_layers (fun s' => iselSim_of_driver (ctx := ctx) (st0 := st0) (R := R)
    (gn := gn) (bl := bl) (A := A) ?_) hprep hM6 hent hres hargs hcs
    hrel htr fuel
  exact {
    shape := hshape
    cert := hcert
    dsem := hds
    insts := instCalls_of_rules hrules hex (hRef s') (mrStable_holds ⟨F s', syms, slotOff⟩ f)
    terms := hterms s'
    ext := fun B hB st hst fn args hi e he => hsub.externCalls B hB st hst fn args hi e he
    noTail := noTail_of_subset hsub
    cfg := cfg_of_prepare hc.prepare }

end E2E
