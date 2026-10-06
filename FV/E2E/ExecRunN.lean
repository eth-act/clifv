import FV.E2E.ExecFrameSim

/-! # The error-guarded per-state hypothesis `RunOkN` (L3 (c))

`binary_correct_exec_static` assumes `RunOkD`: `StepOkD` at every `Reach` state. That includes
the states of an activation after a trap (`StepOkD.err` fails there) and the states of a callee
that never returns (whose caller's step is the error `junkAt`). Neither is needed by the
simulation: it only ever looks at a state whose step ends without error, and it enters a nested
activation only at a call whose step ends without error (the callee returned).

`ReachN` is `Reach` with that guard on nesting, `RunOkN` asks `StepOkD` only at the `ReachN`
states whose step ends without error. `RunOkD.n`: the old hypothesis gives the new one. The
simulation (`act_simN`, `ActSimN`: `ActSim` for target states without error) and the transfer
(`exec_of_modelN`) are re-proven under it, and `binary_correct_exec_staticN` is
`binary_correct_exec_static` under `RunOkN`.
-/

namespace E2E.ExecBytes

open Backend Backend.Proof E2E.LinkCheck E2E.Binary E2E.BinCheck

section Defs

variable (I : LinkInput) (B : BaseEnv) (file : ByteArray)

/-- `Reach` where a nested activation is entered only at a call whose step ends without error
(the callee returned). -/
inductive ReachN : Nat → Clif.Function → Arm.ArmState → Nat → Clif.Function → Arm.ArmState → Prop
  | act {M g c k} : (∀ j ≤ k, ¬ Returned (art I g) c (runX ((sys I B).mach M g) j c)) →
      ReachN M g c M g (runX ((sys I B).mach M g) k c)
  | nest {M g c k h M' g' t} :
      (∀ j ≤ k, ¬ Returned (art I g) c (runX ((sys I B).mach (M + 1) g) j c)) →
      CallsAt I B g (runX ((sys I B).mach (M + 1) g) k c) h →
      Arm.r .ERR (runX ((sys I B).mach (M + 1) g) (k + 1) c) = .None →
      ReachN M h (enterAt (art I h) (runX ((sys I B).mach (M + 1) g) k c)) M' g' t →
      ReachN (M + 1) g c M' g' t

/-- **The error-guarded per-state hypothesis**: `StepOkD` at the states of `ReachN` whose step
ends without error. -/
def RunOkN (M : Nat) (f : Clif.Function) (c : Arm.ArmState) : Prop :=
  ∀ M' g t, ReachN I B M f c M' g t → Arm.r .ERR ((sys I B).mach M' g t) = .None →
    StepOkD I B file M' g t

/-- `StepOk` at the states of `ReachN` whose step ends without error (what the simulation
uses). -/
def RunOkSN (M : Nat) (f : Clif.Function) (c : Arm.ArmState) : Prop :=
  ∀ M' g t, ReachN I B M f c M' g t → Arm.r .ERR ((sys I B).mach M' g t) = .None →
    StepOk I B file M' g t

/-- **The simulation of the model's activations at depth `M`** (`ActSim`) at the target states
without error. -/
def ActSimN (M : Nat) : Prop :=
  ∀ g c e, g ∈ (prog I).funcs → Arm.r .PC c = (art I g).base → Sim I c e →
    RunOkSN I B file M g c →
    ∀ k, (∀ j < k, ¬ Returned (art I g) c (runX ((sys I B).mach M g) j c)) →
    ¬ Second I g (Arm.r .PC (runX ((sys I B).mach M g) k c)) →
    Arm.r .ERR (runX ((sys I B).mach M g) k c) = .None →
    ∃ k', Sim I (runX ((sys I B).mach M g) k c) (runX (step I B file) k' e)

end Defs

section Lemmas

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- A `ReachN` state is a `Reach` state. -/
theorem ReachN.reach {M : Nat} {f : Clif.Function} {c : Arm.ArmState} {M' : Nat}
    {g : Clif.Function} {t : Arm.ArmState} (h : ReachN I B M f c M' g t) :
    Reach I B M f c M' g t := by
  induction h with
  | act hj => exact .act hj
  | nest hj hc _ _ ih => exact .nest hj hc ih

theorem RunOk.n {M : Nat} {f : Clif.Function} {c : Arm.ArmState} (h : RunOk I B file M f c) :
    RunOkSN I B file M f c :=
  fun M' g t hR _ => h M' g t hR.reach

/-- `RunOkD` gives `RunOkN` (`binary_correct_exec_static` is an instance of
`binary_correct_exec_staticN`). -/
theorem RunOkD.n {M : Nat} {f : Clif.Function} {c : Arm.ArmState} (h : RunOkD I B file M f c) :
    RunOkN I B file M f c :=
  fun M' g t hR _ => h M' g t hR.reach

/-- The states of the run are of functions of the program. -/
theorem reachN_mem {M : Nat} {f : Clif.Function} {c : Arm.ArmState} {M' : Nat}
    {g : Clif.Function} {t : Arm.ArmState} (h : ReachN I B M f c M' g t)
    (hf : f ∈ (prog I).funcs) : g ∈ (prog I).funcs :=
  reach_mem h.reach hf

theorem runOkSN_of_n (hI : okB I = true) (hc : codeMapB I (tabOf I.results) = true)
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) (hH : HooksSim I B) {M : Nat}
    {f : Clif.Function} (hf : f ∈ (prog I).funcs) {c : Arm.ArmState}
    (h : RunOkN I B file M f c) : RunOkSN I B file M f c :=
  fun M' g t hR he => stepOk_of_d hI hc hF hH (reachN_mem hR hf) (h M' g t hR he)

theorem junkAt_err (s : Arm.ArmState) : Arm.r .ERR (junkAt s) ≠ .None := by
  simp [junkAt, Arm.r_of_w_same]

/-- `ret_not_second` under `RunOkSN`. -/
theorem ret_not_secondN (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {M M' : Nat}
    {g h : Clif.Function} (hg : g ∈ (prog I).funcs) (hh : h ∈ (prog I).funcs) {m : Arm.ArmState}
    (hok0 : StepOk I B file M g m) (hc : CallsAt I B g m h)
    (hrun' : RunOkSN I B file M' h (enterAt (art I h) m)) {N : Nat}
    (hN : RetOf (art I h) m (runX ((sys I B).mach M' h) N (enterAt (art I h) m)))
    (hmin : ∀ j < N, ¬ RetOf (art I h) m (runX ((sys I B).mach M' h) j (enterAt (art I h) m))) :
    ¬ Second I h (Arm.r .PC (runX ((sys I B).mach M' h) N (enterAt (art I h) m))) := by
  rintro ⟨rl, hrl, ht, he⟩
  have hFh := hF h hh
  cases N with
  | zero => exact not_second_base hFh ⟨rl, hrl, ht, (pc_enterAt (art I h) m).symm.trans he⟩
  | succ N1 =>
  have hokc := hrun' _ _ _
    (ReachN.act (k := N1) fun j hj => fun hr => hmin j (by omega) (returned_iff.2 hr))
    (by rw [← runX_succ' ((sys I B).mach M' h)]; exact hN.2.1)
  have hpc1 := hokc.cf rl hrl ht (by rw [← runX_succ' ((sys I B).mach M' h) N1]; exact he)
  -- the first word's instruction
  obtain ⟨j, i1, t, hj, hi, ho⟩ := (FnAsm.layout_relocs hFh.layout rl).1 hrl
  have hins1 : insnAt (art I h).fa (art I h).base (wAt (art I h) rl.offset) = some i1 := by
    rw [← ho]; exact insnAt_of_line hFh hj
  have hs1 : siteAt I (wAt (art I h) rl.offset) = some (siteOf (prog I) i1) := by
    rw [← hpc1] at hins1 ⊢; exact siteAt_of hokc hins1
  -- the call's word is there
  have hpcm : Arm.r .PC m = wAt (art I h) rl.offset := by
    have h2 : Arm.r .PC m + 4 = wAt (art I h) rl.offset + 4 := by rw [← hN.1, he, wAt_add4]
    exact (BitVec.add_left_inj _).mp h2
  obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets (hF g hg).layout
  obtain ⟨i0, hi0, hs0, -⟩ := hok0.site
  obtain ⟨j0, t0, hj0, -⟩ := insnAt_spec hi0
  have hb := progBase_of (hF g hg) hm hok0.program hj0
  simp only [CallsAt, hb] at hc
  rw [hpcm, hs1, siteOf_pairFirst hi ht] at hs0
  rcases hc with ⟨n, hins, hn⟩ | ⟨⟨x, hins⟩, -⟩ <;> rw [hins] at hi0 <;> cases hi0
  · simp [siteOf, hn] at hs0
  · simp [siteOf] at hs0

end Lemmas

/-! ## The simulation -/

section Core

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

theorem act_coreN (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) (M : Nat)
    (hcall : ∀ M', M = M' + 1 → ActSimN I B file M') : ActSimN I B file M := by
  intro g c e hg hpc hsim hrun k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro hret hsec herr
  have hFg := hF g hg
  have hok : ∀ j, (∀ j' ≤ j, ¬ Returned (art I g) c (runX ((sys I B).mach M g) j' c)) →
      Arm.r .ERR (runX ((sys I B).mach M g) (j + 1) c) = .None →
      StepOk I B file M g (runX ((sys I B).mach M g) j c) := fun j hj he =>
    hrun _ _ _ (ReachN.act hj) (by rw [← runX_succ' ((sys I B).mach M g)]; exact he)
  cases k with
  | zero => exact ⟨0, hsim⟩
  | succ k0 =>
  have hok0 : StepOk I B file M g (runX ((sys I B).mach M g) k0 c) :=
    hok k0 (fun j hj => hret j (by omega)) herr
  rw [runX_succ'] at hsec herr ⊢
  by_cases hs : Second I g (Arm.r .PC (runX ((sys I B).mach M g) k0 c))
  · -- the second word of a pair: two steps from its first word
    obtain ⟨rl, hrl, ht, he⟩ := hs
    cases k0 with
    | zero => exact (not_second_base hFg ⟨rl, hrl, ht, hpc.symm.trans he⟩).elim
    | succ k1 =>
    have hok1 : StepOk I B file M g (runX ((sys I B).mach M g) k1 c) :=
      hok k1 (fun j hj => hret j (by omega)) hok0.err
    have hpc1 := hok1.cf rl hrl ht (by rw [← runX_succ' ((sys I B).mach M g) k1]; exact he)
    obtain ⟨k', hk'⟩ := ih k1 (by omega) (fun j hj => hret j (by omega))
      (by rw [hpc1]; exact first_not_second hFg hrl ht) hok1.err
    refine ⟨k' + 2, ?_⟩
    rw [runX_succ', runX_add (step I B file) k' 2]
    exact pair_step hFg hrl ht hpc1 hok1
      (by rw [← runX_succ' ((sys I B).mach M g) k1]; exact hok0) hk'
  · obtain ⟨k', hk'⟩ := ih k0 (by omega) (fun j hj => hret j (by omega)) hs hok0.err
    obtain ⟨i, hins, -, -⟩ := hok0.site
    obtain ⟨lm, hm⟩ := FnAsm.layout_labelOffsets hFg.layout
    obtain ⟨j0, t0, hj0, -⟩ := insnAt_spec hins
    have hb := progBase_of hFg hm hok0.program hj0
    -- a call of a function of the program
    have hprog : ∀ h, CallsAt I B g (runX ((sys I B).mach M g) k0 c) h →
        ∃ k'', Sim I ((sys I B).mach M g (runX ((sys I B).mach M g) k0 c))
          (runX (step I B file) k'' e) := by
      intro h hc
      have hh := callee_mem hc
      rw [mach_call hc] at herr ⊢
      cases M with
      | zero => exact absurd herr (junkAt_err _)
      | succ M' =>
      have hrun' : RunOkSN I B file M' h
          (enterAt (art I h) (runX ((sys I B).mach (M' + 1) g) k0 c)) :=
        fun M'' g' t hr he => hrun _ _ _ (ReachN.nest (fun j hj => hret j (by omega)) hc
          (by rw [runX_succ', mach_call hc]; exact herr) hr) he
      simp only [LinkSys.pcall] at herr ⊢
      have hent := call_enter hFg (hF h hh) hok0 hk' hc
      unfold linkedCall at herr ⊢
      split
      · rename_i hex
        obtain ⟨hN, hmin⟩ := firstNat_spec _ hex
        obtain ⟨k2, hk2⟩ := hcall M' rfl h _ _ hh (pc_enterAt _ _) hent hrun' _
          (fun j hj hr => hmin j hj (returned_iff.2 hr))
          (ret_not_secondN hF hg hh hok0 hc hrun' hN hmin) hN.2.1
        exact ⟨k' + 1 + k2, by rw [runX_add, runX_add]; exact sim_set_program _ hk2⟩
      · simp [‹¬ _›, junkAt, Arm.r_of_w_same] at herr
    by_cases hhk : i.hooked = false
    · exact ⟨k' + 1, by rw [runX_succ']; exact plain_step hFg hok0 hk' hins hhk⟩
    · cases i <;> simp only [Insn.hooked, Bool.true_eq_false, not_false_eq_true, not_true_eq_false] at hhk
      case bl n =>
        cases hn : (prog I).func? n with
        | none => exact ⟨k' + 1, by rw [runX_succ']; exact hook_step hFg hok0 hk' hins (.inl ⟨n, rfl, hn⟩)⟩
        | some h => exact hprog h (.inl ⟨n, by rw [hb]; exact hins, hn⟩)
      case blr x =>
        cases hn : (blrTarget (runX ((sys I B).mach M g) k0 c)).bind (symCallee (sys I B).Xb (prog I)) with
        | none => exact ⟨k' + 1, by rw [runX_succ']; exact hook_step hFg hok0 hk' hins (.inr (.inl ⟨x, rfl, hn⟩))⟩
        | some h => exact hprog h (.inr ⟨⟨x, by rw [hb]; exact hins⟩, hn⟩)
      case adrpGot a b => exact absurd (adrp_lands hFg hok0 hins (.inl ⟨a, b, rfl⟩)) hsec
      case adrp a b d => exact absurd (adrp_lands hFg hok0 hins (.inr ⟨a, b, d, rfl⟩)) hsec
      case ldrGotLo12 a b d => exact absurd (second_of_lo12 hFg hins (.inl ⟨a, b, d, rfl⟩)) hs
      case addLo12 a b d f => exact absurd (second_of_lo12 hFg hins (.inr ⟨a, b, d, f, rfl⟩)) hs
      case adrpTlsDesc a b =>
        exact ⟨k' + 1, by rw [runX_succ']; exact hook_step hFg hok0 hk' hins (.inr (.inr (.inl ⟨a, b, rfl⟩)))⟩
      case ldrTlsDescLo12 a b d =>
        exact ⟨k' + 1, by rw [runX_succ']; exact hook_step hFg hok0 hk' hins (.inr (.inr (.inr ⟨a, b, d, rfl⟩)))⟩

end Core

/-- **The simulation at every depth** (target states without error). -/
theorem act_simN {I : LinkInput} {B : BaseEnv} {file : ByteArray}
    (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) : ∀ M, ActSimN I B file M
  | 0 => act_coreN hF 0 fun _ h => by cases h
  | M + 1 => act_coreN hF (M + 1) fun M' h => by
    obtain rfl : M = M' := Nat.succ.inj h
    exact act_simN hF M

/-! ## The theorem about the executable -/

section Transfer

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- **The model's outcome transfers to the executable machine** (`exec_of_model`) under
`RunOkSN`. -/
theorem exec_of_modelN (hF : ∀ g ∈ (prog I).funcs, FnOk I file g) {M : Nat} {f : Clif.Function}
    (hf : f ∈ (prog I).funcs) {r : Arm.ArmState} (hpc : Arm.r .PC r = (art I f).base)
    (hra : ∀ k < (art I f).fb.words.size, xreg 30 r ≠ (art I f).base + BitVec.ofNat 64 (4 * k))
    (hd : ∀ a, (modelOf I f r).mem a ≠ r.mem a → RelocAt I a)
    (hrun : RunOkSN I B file M f (modelOf I f r)) {o : Clif.Outcome}
    (h : ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r) o) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (RelocAt I) o := by
  have hFf := hF f hf
  have hsim := sim_modelOf hd
  have hra' : ∀ k < (art I f).fb.words.size,
      xreg 30 (modelOf I f r) ≠ (art I f).base + BitVec.ofNat 64 (4 * k) := by
    simp only [xreg, r_modelOf]; exact hra
  have hpc' : Arm.r .PC (modelOf I f r) = (art I f).base := by rw [r_modelOf]; exact hpc
  have hsimN := act_simN (B := B) hF M f _ r hf hpc' hsim hrun
  cases o with
  | returned vals cm =>
    obtain ⟨n, hret, hx, hmem⟩ := h
    obtain ⟨k', hk'⟩ := hsimN n (no_return hFf hra' hret.err) (fun hs => by
      obtain ⟨k, hk, he⟩ := second_code hFf hs
      exact hra k hk (by rw [← he, hret.pc])) hret.err
    refine ⟨k', ⟨?_, ?_, ?_, fun n hn => ?_, fun n h8 h16 => ?_⟩, fun j v hv => ?_, fun a b hv hb hR => ?_⟩
    · rw [hk'.1, hret.pc]
    · rw [hk'.1, hret.err]
    · simp only [spv]; rw [hk'.1]; exact (hret.sp.trans (spv_modelOf I f r))
    · simp only [xreg]; rw [hk'.1]; exact (hret.savedX n hn).trans (r_modelOf I f r _)
    · rw [hk'.1, hret.savedV n h8 h16, r_modelOf]
    · simp only [xreg]; rw [hk'.1]; exact hx j v hv
    · show Arm.read_store _ _ = b
      rw [show Arm.read_store (BitVec.ofNat 64 a) (runX (step I B file) k' r).mem =
        (runX (step I B file) k' r).mem (BitVec.ofNat 64 a) from rfl, hk'.2 _ hR]
      exact hmem a b hv hb
  | trapped c0 =>
    obtain ⟨n, htrap⟩ := h
    have hguard := no_return (B := B) hFf hra' htrap.err
    by_cases hs : Second I f (Arm.r .PC (runX ((sys I B).mach M f) n (modelOf I f r)))
    · -- a trap at a second word: one executable step after the first word
      obtain ⟨rl, hrl, ht, he⟩ := hs
      cases n with
      | zero => exact (not_second_base hFf ⟨rl, hrl, ht, hpc'.symm.trans he⟩).elim
      | succ n1 =>
      have hok1 := hrun _ _ _ (ReachN.act (k := n1) fun j hj => hguard j (by omega))
        (by rw [← runX_succ' ((sys I B).mach M f)]; exact htrap.err)
      have hpc1 := hok1.cf rl hrl ht (by rw [← runX_succ' ((sys I B).mach M f) n1]; exact he)
      obtain ⟨k', hk'⟩ := hsimN n1 (fun j hj => hguard j (by omega))
        (by rw [hpc1]; exact first_not_second hFf hrl ht) hok1.err
      obtain ⟨hpcE, herrE⟩ := pair_first_pc hFf hrl ht hpc1 hok1 hk'
      refine ⟨k' + 1, ?_⟩
      rw [runX_succ'] at htrap ⊢
      exact ⟨by rw [← herrE]; exact htrap.err, by rw [← hpcE]; exact htrap.site⟩
    · obtain ⟨k', hk'⟩ := hsimN n hguard hs htrap.err
      exact ⟨k', by rw [hk'.1]; exact htrap.err, by rw [hk'.1]; exact htrap.site⟩
  | stuck _ => trivial
  | outOfFuel => trivial

end Transfer

/-- **`binary_correct_exec_static` under the error-guarded hypothesis `RunOkN`**: under the
premises of `binary_correct_of_checks_acyclic`, the outside-code contract `HooksSim`, the code
map check `codeMapB` and `StepOkD` at the states of the model's run whose step ends without error
(nested only into calls that return), the executable machine run from `r` refines the
whole-program CLIF run. -/
theorem binary_correct_exec_staticN {I : LinkInput} {D : List Clif.DataObject} {file : ByteArray}
    (hI : okB I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOk I D file) (B : BaseEnv) (hB : BaseOk (sys I B)) (hH : HooksSim I B)
    {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls I I.results) f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (StackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) ((prog I).only f) cs)
    (hrun : RunOkN I B file M f (modelOf I f r)) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r (RelocAt I)
      (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  have hn := (StackBound.goodN_iff hI).2 ⟨f, hf, hc⟩
  obtain ⟨h1, h2⟩ := binary_correct_of_checks hI hbin B hB hn hf M hX ho hr htr
  have hfm := (Clif.Program.func?_some hf).1
  have hB' : BaseOk (LinkSys.ofInput I B (worldF I f (StackBound.bud I f) r)) := baseOk_F hB
  have hL := okB_sound hI hB' fun _ h => .inr h
  have hfacts := binFacts_of_checks hI hbin
  have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
    hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, -⟩ := premises hL hfm hro ho hr
  have hL' := okB_sound hI (baseOk_F (F' := img I) hB) fun _ h => h
  have hF : ∀ g ∈ (prog I).funcs, FnOk I file g := fun g hg => fnOk hI hbin hL' hg
  exact exec_of_modelN hF hfm (by rw [← r_modelOf I f r]; exact hent.pc) hent.raOutside h2
    (runOkSN_of_n hI hcm hF hH hfm hrun) h1

end E2E.ExecBytes
