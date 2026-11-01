import FV.E2E.WorldUnwind
import FV.E2E.PairDriverU

/-!
# The per-function world theorem with unwinding and non-interference (S10f, #233)

`backend_correct_world_ni_pipeline` (`FV/E2E/CompiledEither.lean`, the non-interference clause
`FV/E2E/LinkArm.lean` links when `NeedNI`) for the runs with unwinding and the machine with
unwinding: `backend_correct_world_pipelineU` (`FV/E2E/WorldUnwind.lean`), whose returning and
exceptional clauses also give, under the callees' non-interference on returns (`XNI`, `XTls`)
and on raises (`XRNI`, `FV/E2E/PairRaise.lean`), that the one outcome of the body-entry world
`w₀` — the same `rets` and values, resp. the same exception object, and the final world `w` —
is realised by every activation entered with a body-entry world `w₀'` related to the same CLIF
entry, agreeing with `w₀` outside `F ∪ D` (with the same argument registers and stack-passed
argument bytes), up to the addresses `F ∪ D` (`ActRet`, resp. `ActUnw`, with `F ∪ D`).

* `vUnwFrom_det`: the exceptional end of a VCode run is unique (as `vRetFrom_det`).
* `backend_correct_world_ni_cleanupU` (dead-cleanup pipeline, `vcode_niU_value`),
  `backend_correct_world_niU` (legacy, `vcode_niU`), **`backend_correct_world_ni_pipelineU`**
  (`CompiledEither`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.UnwindTables Backend.DeadCleanup

/-- From a state whose step halts, the run reaches no other running state. -/
theorem star_halt {V W : Type} {vc : VCode} {sem : ISem V W} {b k : Nat} {ρ : Nat → V} {w : W}
    {vb : VBlock} {i : MInst} {ops : Array Operand} {outs : List V} {w' : W}
    (hvb : vc.blocks[b]? = some vb) (hk : vb.insts[k]? = some i) (hops : i.operands = .ok ops)
    (hsem : sem i (vuses ops ρ) w = some (outs, w', .halt)) {T : VState V W}
    (h : Star (VStep vc sem) (.run ⟨b, k, ρ, w⟩) (.run T)) : T = ⟨b, k, ρ, w⟩ := by
  cases h with
  | refl => rfl
  | step h1 h2 =>
    cases h1 with
    | step hvb' hi' hops' hsem' hlen' hn' =>
      rw [hvb] at hvb'; cases hvb'
      rw [hk] at hi'; cases hi'
      rw [hops] at hops'; cases hops'
      have hs : sem i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) w =
          some (outs, w', .halt) := hsem
      rw [hs] at hsem'; cases hsem'
      cases hn' with
      | halt =>
        cases h2 with
        | step h _ => cases h

/-- **The exceptional end of a VCode run is unique**: the raising call, its object and the
world after the unwinder. -/
theorem vUnwFrom_det {vc : VCode} {sem : Sem} {XR : XRaise} {vs : VState CV Arm.ArmState}
    {obj obj' : BitVec 64} {w w' : Arm.ArmState} (h : VUnwFrom vc sem XR vs obj w)
    (h' : VUnwFrom vc sem XR vs obj' w') : obj = obj' ∧ w = w' := by
  obtain ⟨b, k, ρ, w₁, vb, info, ops, outs, hs, hvb, hk, hops, hr, hsem, -⟩ := h
  obtain ⟨b', k', ρ', w₁', vb', info', ops', outs', hs', hvb', hk', hops', hr', hsem', -⟩ := h'
  have hst : (⟨b', k', ρ', w₁'⟩ : VState CV Arm.ArmState) = ⟨b, k, ρ, w₁⟩ := by
    rcases star_det (r := VStep vc sem) (fun _ _ _ h1 h2 => vstep_det h1 h2) hs hs' with h1 | h1
    · exact star_halt hvb hk hops hsem h1
    · exact (star_halt hvb' hk' hops' hsem' h1).symm
  cases hst
  rw [hvb] at hvb'; cases hvb'
  rw [hk] at hk'; cases hk'
  rw [hops] at hops'; cases hops'
  rw [hr] at hr'; cases hr'
  exact ⟨rfl, rfl⟩

/-- **The per-function world theorem with unwinding and non-interference** (the shipped
dead-cleanup pipeline): `backend_correct_world_cleanupU`, and for a returning or exceptional
CLIF run the outcome of `w₀` realised, up to `F ∪ D`, by every activation entered with a related
body-entry world `w₀'` (under `XNI`, `XTls`, `XRNI`). -/
theorem backend_correct_world_ni_cleanupU {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hlU : lowerCheckU f vc = true)
    {X : ExtSem} {XR : XRaise} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv}
    {K : Nat} {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env.toEnv (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env.toEnv (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXR : XRaiseOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hXRi : XRaiseIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hexcl : ∀ d uses w, X.call d uses w ≠ none → XR.raise d uses w = none)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    -- the tables the unwinder reads (the emitted ones) and the decidable checks
    {T : Unw.FnTables} {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry))) {rows : List (Nat × Cfi)}
    (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hpad : padsNonzeroB af fa = true)
    (hlast : lastCallsOk af fa = true) (hsaved : savedCheck vcp rf = true)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoopX env p fuel cs.toX = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
          (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
            PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧
            ¬ UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s)) ∧
        (XNI F syms (f.externs.map (·.2)) (indSigs f) c
            (CallLg env.toEnv (f.externs.map (·.2)) (indSigs f)) X → XTls F X →
          XRNI F syms (f.externs.map (·.2)) (indSigs f) c
            (CallLgR env (f.externs.map (·.2)) (indSigs f)) X XR →
          ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
            (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
              PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧
              ¬ UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s))) ∧
    (∀ c', Clif.runLoopX env p fuel cs.toX = .trapped c' →
      ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
        (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (Unw.ArmStepU X H U T fa) n s)) ∧
    (∀ e cm, Clif.runLoopX env p fuel cs.toX = .unwound e cm →
      ∃ (obj : BitVec 64) (w : Arm.ArmState), ExnRel e obj ∧ MemRel F syms cm w ∧
        (∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
          (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
          ∃ n, ActUnw ra F G obj w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
            PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧ 0 < n ∧
            UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s)) ∧
        (XNI F syms (f.externs.map (·.2)) (indSigs f) c
            (CallLg env.toEnv (f.externs.map (·.2)) (indSigs f)) X → XTls F X →
          XRNI F syms (f.externs.map (·.2)) (indSigs f) c
            (CallLgR env (f.externs.map (·.2)) (indSigs f)) X XR →
          ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
            (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀' →
            ∃ n, ActUnw ra (fun a => F a ∨ D a) G obj w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
              PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧ 0 < n ∧
              UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s))) := by
  have hI := iselSimU_relW_cleanup_stage hsub hc hlU hX hXI hXR hXRi hexcl hsym hslot (fun _ => 0)
    hcs
    hrel hargs htr fuel
  have hP := prepareCorrectU_cleanup (vc := skipStage f vc)
    (driverSem_valueSemU F ⟨fa.k, af.slotBase⟩ X XR)
    (fun _ _ _ _ _ _ hp he => valueSemU_pure hp he) (valueSemU_cmpOverwrite _ _ _ _) hc.prepOk XR
  have hM6 : ∀ (w₀ : Arm.ArmState) (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop)
      (base ra : BitVec 64) (s : Arm.ArmState),
      ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ → _ :=
    fun w₀ H U G base ra s he => by
      have h := regLevelCorrect_worldUT hc.check hc.alloc hc.emit hc.layout (X := X) (H := H)
        (XR := XR) (U := U) (T := T) (K := K) (G := G) (gv := GotV vcp) he.abi he.stack he.gfree
        (gotSem_valueSemVU _ _ _ _ _)
        (realizes_valueU_world hcov (by rw [he.hF]; exact he.calls) (by rw [he.hF]; exact he.tries)
          (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.unw) hsites hlsda hpad hlast)
        (fun us uses w => by rw [valueSemVU_rets])
        (fun _ _ _ _ _ ht h => valueSemVU_halt_trap ht h) (by rw [he.hF]; exact he.unw)
        hsites hlsda hlast hrows hcie hfde hsaved (by rw [he.hF]; exact he.body) (fun _ => 0)
      rw [he.hF] at h
      exact h
  have hNIv := fun hNI hTls hRNI D w₀' hrel' hsw hreg hstk =>
    vcode_niU_value_stage hsub hc hlU hX hXI hXR hXRi hexcl hsym hslot hNI hTls hRNI (D := D)
      (w₀' := w₀')
      (fun _ => 0) hcs hrel hrel' hargs hsw hreg hstk htr fuel
  refine ⟨fun vals cm hrun => ?_,
    (backend_correct_world_cleanupU hsub hc hlU hcov hX hXI hXR hXRi hexcl hsym hslot hsites hlsda hrows hcie hfde
      hpad hlast hsaved hcs hrel hargs htr fuel).2.1, fun e cm hrun => ?_⟩
  · obtain ⟨us, outs, w, hv, hus, hlen, hhold, hmemR⟩ := hI.1 vals cm hrun
    have hrs : vc.RetsSite us := by
      obtain ⟨b, k, ρ, w₁, vb, ops, outs', -, hvb, hk, -⟩ := hv
      exact retsSite_of_skipStage ⟨b, vb, k, hvb, hk⟩
    refine ⟨us, outs, w, hus, hlen, hhold, hmemR, hrs, fun H U G base ra s he => ?_,
      fun hNI hTls hRNI D w₀' hrel' hsw hreg hstk H U G base ra s he => ?_⟩
    · exact (hM6 w₀ H U G base ra s he).1 us outs w
        (vReturns_gotV_gen (gotPair_valueU _ _ _) ((hP.1 _ _).1 _ _ _ hv))
    · obtain ⟨us', outs', w1, w2, hv1, hv2, hsw12⟩ :=
        (hNIv hNI hTls hRNI D w₀' hrel' hsw hreg hstk).1 vals cm hrun
      obtain ⟨rfl, rfl, rfl⟩ := vRetFrom_det (vs := ⟨0, 0, fun _ => 0, w₀⟩) hv1 hv
      obtain ⟨n, ⟨h1, h2, h3, h4, h5, h6⟩, h7, h8⟩ := (hM6 w₀' H U G base ra s he).1 us' outs' w2
        (vReturns_gotV_gen (gotPair_valueU _ _ _) ((hP.1 _ _).1 _ _ _ hv2))
      refine ⟨n, ⟨h1, h2, fun a ha => ?_, fun g hg h29 h31 => ?_, h5, h6⟩, h7, h8⟩
      · rw [h3 a (fun hf => ha (.inl hf))]
        exact (hsw12.2.1 a ha).symm
      · rw [h4 g hg h29 h31]
        exact (hsw12.1 g hg).symm
  · obtain ⟨obj, w, hv, hex, hmemR⟩ := hI.2.2 e cm hrun
    refine ⟨obj, w, hex, hmemR, fun H U G base ra s he =>
      (hM6 w₀ H U G base ra s he).2.2 obj w
        (vUnwinds_gotV_gen (gotPair_valueU _ _ _) (hP.2 _ _ _ _ hv)),
      fun hNI hTls hRNI D w₀' hrel' hsw hreg hstk H U G base ra s he => ?_⟩
    obtain ⟨obj', w1, w2, hv1, hv2, hsw12⟩ :=
      (hNIv hNI hTls hRNI D w₀' hrel' hsw hreg hstk).2 e cm hrun
    obtain ⟨rfl, rfl⟩ := vUnwFrom_det hv1 hv
    obtain ⟨n, ⟨h1, h2, h3, h4, h5, h6⟩, h7, h8, h9⟩ := (hM6 w₀' H U G base ra s he).2.2 obj' w2
      (vUnwinds_gotV_gen (gotPair_valueU _ _ _) (hP.2 _ _ _ _ hv2))
    refine ⟨n, ⟨h1, h2, fun a ha => ?_, h4, h5, fun g hg h29 h31 => ?_⟩, h7, h8, h9⟩
    · rw [h3 a (fun hf => ha (.inl hf))]
      exact (hsw12.2.1 a ha).symm
    · rw [h6 g hg h29 h31]
      exact (hsw12.1 g hg).symm

/-- **The per-function world theorem with unwinding and non-interference** (the shipped
dead-cleanup pipeline): `backend_correct_world_cleanupU`, and for a returning or exceptional
CLIF run the outcome of `w₀` realised, up to `F ∪ D`, by every activation entered with a related
body-entry world `w₀'` (under `XNI`, `XTls`, `XRNI`). -/
theorem backend_correct_world_ni_cleanupUG {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hlU : lowerCheckU f vc = true)
    {X : ExtSem} {XR : XRaise} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv}
    {K : Nat} {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env.toEnv (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env.toEnv (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXR : XRaiseOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hXRi : XRaiseIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hexcl : ∀ d uses w, X.call d uses w ≠ none → XR.raise d uses w = none)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    -- the tables the unwinder reads (the emitted ones) and the decidable checks
    {T : Unw.FnTables} {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry))) {rows : List (Nat × Cfi)}
    (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hpad : padsNonzeroB af fa = true)
    (hlast : lastCallsOk af fa = true) (hsaved : savedCheck vcp rf = true)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoopX env p fuel cs.toX = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
          (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
            PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧
            ¬ UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s) ∧
            ∀ i < n, actGoodXU vcp rf af fa fb base s X H XR U T K G (GotV vcp)
              (runX (Unw.ArmStepU X H U T fa) i s)) ∧
        (XNI F syms (f.externs.map (·.2)) (indSigs f) c
            (CallLg env.toEnv (f.externs.map (·.2)) (indSigs f)) X → XTls F X →
          XRNI F syms (f.externs.map (·.2)) (indSigs f) c
            (CallLgR env (f.externs.map (·.2)) (indSigs f)) X XR →
          ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
            (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
              PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧
              ¬ UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s) ∧
              ∀ i < n, actGoodXU vcp rf af fa fb base s X H XR U T K G (GotV vcp)
                (runX (Unw.ArmStepU X H U T fa) i s))) ∧
    (∀ c', Clif.runLoopX env p fuel cs.toX = .trapped c' →
      ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
        (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (Unw.ArmStepU X H U T fa) n s) ∧
          (∀ i < n, actGoodXU vcp rf af fa fb base s X H XR U T K G (GotV vcp)
            (runX (Unw.ArmStepU X H U T fa) i s)) ∧
          ∀ m, Arm.r .ERR (runX (Unw.ArmStepU X H U T fa) (n + m + 1) s) ≠ .None) ∧
    (∀ e cm, Clif.runLoopX env p fuel cs.toX = .unwound e cm →
      ∃ (obj : BitVec 64) (w : Arm.ArmState), ExnRel e obj ∧ MemRel F syms cm w ∧
        (∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
          (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
          ∃ n, ActUnw ra F G obj w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
            PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧ 0 < n ∧
            UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s) ∧
            ∀ i < n, actGoodXU vcp rf af fa fb base s X H XR U T K G (GotV vcp)
              (runX (Unw.ArmStepU X H U T fa) i s)) ∧
        (XNI F syms (f.externs.map (·.2)) (indSigs f) c
            (CallLg env.toEnv (f.externs.map (·.2)) (indSigs f)) X → XTls F X →
          XRNI F syms (f.externs.map (·.2)) (indSigs f) c
            (CallLgR env (f.externs.map (·.2)) (indSigs f)) X XR →
          ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
            (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀' →
            ∃ n, ActUnw ra (fun a => F a ∨ D a) G obj w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
              PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧ 0 < n ∧
              UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s) ∧
              ∀ i < n, actGoodXU vcp rf af fa fb base s X H XR U T K G (GotV vcp)
                (runX (Unw.ArmStepU X H U T fa) i s))) := by
  have hI := iselSimU_relW_cleanup_stage hsub hc hlU hX hXI hXR hXRi hexcl hsym hslot (fun _ => 0)
    hcs
    hrel hargs htr fuel
  have hP := prepareCorrectU_cleanup (vc := skipStage f vc)
    (driverSem_valueSemU F ⟨fa.k, af.slotBase⟩ X XR)
    (fun _ _ _ _ _ _ hp he => valueSemU_pure hp he) (valueSemU_cmpOverwrite _ _ _ _) hc.prepOk XR
  have hM6 : ∀ (w₀ : Arm.ArmState) (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop)
      (base ra : BitVec 64) (s : Arm.ArmState),
      ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ → _ :=
    fun w₀ H U G base ra s he => by
      have h := regLevelCorrect_worldUTG hc.check hc.alloc hc.emit hc.layout (X := X) (H := H)
        (XR := XR) (U := U) (T := T) (K := K) (G := G) (gv := GotV vcp) he.abi he.stack he.gfree
        (gotSem_valueSemVU _ _ _ _ _)
        (realizes_valueU_worldF hcov (by rw [he.hF]; exact he.calls) (by rw [he.hF]; exact he.tries)
          (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.unw) hsites hlsda hpad hlast)
        (fun us uses w => by rw [valueSemVU_rets])
        (fun _ _ _ _ _ ht h => valueSemVU_halt_trap ht h) (by rw [he.hF]; exact he.unw)
        hsites hlsda hlast hrows hcie hfde hsaved (by rw [he.hF]; exact he.body) (fun _ => 0)
      rw [he.hF] at h
      exact h
  have hNIv := fun hNI hTls hRNI D w₀' hrel' hsw hreg hstk =>
    vcode_niU_value_stage hsub hc hlU hX hXI hXR hXRi hexcl hsym hslot hNI hTls hRNI (D := D)
      (w₀' := w₀')
      (fun _ => 0) hcs hrel hrel' hargs hsw hreg hstk htr fuel
  refine ⟨fun vals cm hrun => ?_,
    (backend_correct_world_cleanupUG hsub hc hlU hcov hX hXI hXR hXRi hexcl hsym hslot hsites hlsda hrows hcie hfde
      hpad hlast hsaved hcs hrel hargs htr fuel).2.1, fun e cm hrun => ?_⟩
  · obtain ⟨us, outs, w, hv, hus, hlen, hhold, hmemR⟩ := hI.1 vals cm hrun
    have hrs : vc.RetsSite us := by
      obtain ⟨b, k, ρ, w₁, vb, ops, outs', -, hvb, hk, -⟩ := hv
      exact retsSite_of_skipStage ⟨b, vb, k, hvb, hk⟩
    refine ⟨us, outs, w, hus, hlen, hhold, hmemR, hrs, fun H U G base ra s he => ?_,
      fun hNI hTls hRNI D w₀' hrel' hsw hreg hstk H U G base ra s he => ?_⟩
    · exact (hM6 w₀ H U G base ra s he).1 us outs w
        (vReturns_gotV_gen (gotPair_valueU _ _ _) ((hP.1 _ _).1 _ _ _ hv))
    · obtain ⟨us', outs', w1, w2, hv1, hv2, hsw12⟩ :=
        (hNIv hNI hTls hRNI D w₀' hrel' hsw hreg hstk).1 vals cm hrun
      obtain ⟨rfl, rfl, rfl⟩ := vRetFrom_det (vs := ⟨0, 0, fun _ => 0, w₀⟩) hv1 hv
      obtain ⟨n, ⟨h1, h2, h3, h4, h5, h6⟩, h7, h8, h9⟩ := (hM6 w₀' H U G base ra s he).1 us' outs'
        w2 (vReturns_gotV_gen (gotPair_valueU _ _ _) ((hP.1 _ _).1 _ _ _ hv2))
      refine ⟨n, ⟨h1, h2, fun a ha => ?_, fun g hg h29 h31 => ?_, h5, h6⟩, h7, h8, h9⟩
      · rw [h3 a (fun hf => ha (.inl hf))]
        exact (hsw12.2.1 a ha).symm
      · rw [h4 g hg h29 h31]
        exact (hsw12.1 g hg).symm
  · obtain ⟨obj, w, hv, hex, hmemR⟩ := hI.2.2 e cm hrun
    refine ⟨obj, w, hex, hmemR, fun H U G base ra s he =>
      (hM6 w₀ H U G base ra s he).2.2 obj w
        (vUnwinds_gotV_gen (gotPair_valueU _ _ _) (hP.2 _ _ _ _ hv)),
      fun hNI hTls hRNI D w₀' hrel' hsw hreg hstk H U G base ra s he => ?_⟩
    obtain ⟨obj', w1, w2, hv1, hv2, hsw12⟩ :=
      (hNIv hNI hTls hRNI D w₀' hrel' hsw hreg hstk).2 e cm hrun
    obtain ⟨rfl, rfl⟩ := vUnwFrom_det hv1 hv
    obtain ⟨n, ⟨h1, h2, h3, h4, h5, h6⟩, h7, h8, h9, h10⟩ := (hM6 w₀' H U G base ra s he).2.2 obj'
      w2 (vUnwinds_gotV_gen (gotPair_valueU _ _ _) (hP.2 _ _ _ _ hv2))
    refine ⟨n, ⟨h1, h2, fun a ha => ?_, h4, h5, fun g hg h29 h31 => ?_⟩, h7, h8, h9, h10⟩
    · rw [h3 a (fun hf => ha (.inl hf))]
      exact (hsw12.2.1 a ha).symm
    · rw [h6 g hg h29 h31]
      exact (hsw12.1 g hg).symm

/-- **The per-function world theorem with unwinding and non-interference, legacy pipeline**
(`csemU`). -/
theorem backend_correct_world_niU {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    (hlU : lowerCheckU f vc = true)
    {X : ExtSem} {XR : XRaise} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv}
    {K : Nat} {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env.toEnv (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env.toEnv (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXR : XRaiseOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hXRi : XRaiseIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hexcl : ∀ d uses w, X.call d uses w ≠ none → XR.raise d uses w = none)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {T : Unw.FnTables} {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry))) {rows : List (Nat × Cfi)}
    (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hpad : padsNonzeroB af fa = true)
    (hlast : lastCallsOk af fa = true) (hsaved : savedCheck vcp rf = true)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoopX env p fuel cs.toX = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
          (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
            PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧
            ¬ UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s)) ∧
        (XNI F syms (f.externs.map (·.2)) (indSigs f) c
            (CallLg env.toEnv (f.externs.map (·.2)) (indSigs f)) X → XTls F X →
          XRNI F syms (f.externs.map (·.2)) (indSigs f) c
            (CallLgR env (f.externs.map (·.2)) (indSigs f)) X XR →
          ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
            (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
              PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧
              ¬ UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s))) ∧
    (∀ c', Clif.runLoopX env p fuel cs.toX = .trapped c' →
      ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
        (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (Unw.ArmStepU X H U T fa) n s)) ∧
    (∀ e cm, Clif.runLoopX env p fuel cs.toX = .unwound e cm →
      ∃ (obj : BitVec 64) (w : Arm.ArmState), ExnRel e obj ∧ MemRel F syms cm w ∧
        (∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
          (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
          ∃ n, ActUnw ra F G obj w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
            PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧ 0 < n ∧
            UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s)) ∧
        (XNI F syms (f.externs.map (·.2)) (indSigs f) c
            (CallLg env.toEnv (f.externs.map (·.2)) (indSigs f)) X → XTls F X →
          XRNI F syms (f.externs.map (·.2)) (indSigs f) c
            (CallLgR env (f.externs.map (·.2)) (indSigs f)) X XR →
          ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
            (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀' →
            ∃ n, ActUnw ra (fun a => F a ∨ D a) G obj w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
              PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧ 0 < n ∧
              UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s))) := by
  have hI := iselSimU_relW hsub hc hlU hX hXI hXR hXRi hexcl hsym hslot (fun _ => 0) hcs
    hrel hargs htr fuel
  have hP := prepareCorrectU_of_check (driverSem_csemU F ⟨fa.k, af.slotBase⟩ X XR) hc.prepOk XR
  have hnc : ∀ {i : MInst}, trapCode? i ≠ none → ∀ info,
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) → False := fun ht _ h => by
    rcases h with rfl | ⟨_, rfl⟩ <;> simp [trapCode?] at ht
  have hM6 : ∀ (w₀ : Arm.ArmState) (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop)
      (base ra : BitVec 64) (s : Arm.ArmState),
      ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ → _ :=
    fun w₀ H U G base ra s he => by
      have h := regLevelCorrect_worldUT hc.check hc.alloc hc.emit hc.layout (X := X) (H := H)
        (XR := XR) (U := U) (T := T) (K := K) (G := G) (gv := GotV vcp) he.abi he.stack he.gfree
        (gotSem_csemVU _ _ _ _ _)
        (realizes_csemU_world hcov (by rw [he.hF]; exact he.calls) (by rw [he.hF]; exact he.tries)
          (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.unw) hsites hlsda hpad hlast)
        (fun us uses w => by
          rw [csemVU_eq fun _ h => by rcases h with h | ⟨_, h⟩ <;> cases h]
          exact csemU_rets us uses w)
        (fun i uses w outs w' ht h => by
          rw [csemVU_eq fun info h => (hnc ht info h).elim] at h
          rwa [← csemU_trap ht])
        (by rw [he.hF]; exact he.unw)
        hsites hlsda hlast hrows hcie hfde hsaved (by rw [he.hF]; exact he.body) (fun _ => 0)
      rw [he.hF] at h
      exact h
  have hNIv := fun hNI hTls hRNI D w₀' hrel' hsw hreg hstk =>
    vcode_niU hsub hc hlU hX hXI hXR hXRi hexcl hsym hslot hNI hTls hRNI (D := D) (w₀' := w₀')
      (fun _ => 0) hcs hrel hrel' hargs hsw hreg hstk htr fuel
  refine ⟨fun vals cm hrun => ?_,
    (backend_correct_worldU hsub hc hlU hcov hX hXI hXR hXRi hexcl hsym hslot hsites hlsda hrows hcie hfde
      hpad hlast hsaved hcs hrel hargs htr fuel).2.1, fun e cm hrun => ?_⟩
  · obtain ⟨us, outs, w, hv, hus, hlen, hhold, hmemR⟩ := hI.1 vals cm hrun
    have hrs : vc.RetsSite us := by
      obtain ⟨b, k, ρ, w₁, vb, ops, outs', -, hvb, hk, -⟩ := hv
      exact ⟨b, vb, k, hvb, hk⟩
    refine ⟨us, outs, w, hus, hlen, hhold, hmemR, hrs, fun H U G base ra s he => ?_,
      fun hNI hTls hRNI D w₀' hrel' hsw hreg hstk H U G base ra s he => ?_⟩
    · exact (hM6 w₀ H U G base ra s he).1 us outs w
        (vReturns_gotV_gen (gotPair_csemU _ _ _) ((hP.1 _ _).1 _ _ _ hv))
    · obtain ⟨us', outs', w1, w2, hv1, hv2, hsw12⟩ :=
        (hNIv hNI hTls hRNI D w₀' hrel' hsw hreg hstk).1 vals cm hrun
      obtain ⟨rfl, rfl, rfl⟩ := vRetFrom_det (vs := ⟨0, 0, fun _ => 0, w₀⟩) hv1 hv
      obtain ⟨n, ⟨h1, h2, h3, h4, h5, h6⟩, h7, h8⟩ := (hM6 w₀' H U G base ra s he).1 us' outs' w2
        (vReturns_gotV_gen (gotPair_csemU _ _ _) ((hP.1 _ _).1 _ _ _ hv2))
      refine ⟨n, ⟨h1, h2, fun a ha => ?_, fun g hg h29 h31 => ?_, h5, h6⟩, h7, h8⟩
      · rw [h3 a (fun hf => ha (.inl hf))]
        exact (hsw12.2.1 a ha).symm
      · rw [h4 g hg h29 h31]
        exact (hsw12.1 g hg).symm
  · obtain ⟨obj, w, hv, hex, hmemR⟩ := hI.2.2 e cm hrun
    refine ⟨obj, w, hex, hmemR, fun H U G base ra s he =>
      (hM6 w₀ H U G base ra s he).2.2 obj w
        (vUnwinds_gotV_gen (gotPair_csemU _ _ _) (hP.2 _ _ _ _ hv)),
      fun hNI hTls hRNI D w₀' hrel' hsw hreg hstk H U G base ra s he => ?_⟩
    obtain ⟨obj', w1, w2, hv1, hv2, hsw12⟩ :=
      (hNIv hNI hTls hRNI D w₀' hrel' hsw hreg hstk).2 e cm hrun
    obtain ⟨rfl, rfl⟩ := vUnwFrom_det hv1 hv
    obtain ⟨n, ⟨h1, h2, h3, h4, h5, h6⟩, h7, h8, h9⟩ := (hM6 w₀' H U G base ra s he).2.2 obj' w2
      (vUnwinds_gotV_gen (gotPair_csemU _ _ _) (hP.2 _ _ _ _ hv2))
    refine ⟨n, ⟨h1, h2, fun a ha => ?_, h4, h5, fun g hg h29 h31 => ?_⟩, h7, h8, h9⟩
    · rw [h3 a (fun hf => ha (.inl hf))]
      exact (hsw12.2.1 a ha).symm
    · rw [h6 g hg h29 h31]
      exact (hsw12.1 g hg).symm

/-- **The per-function world theorem with unwinding and non-interference, legacy pipeline**
(`csemU`). -/
theorem backend_correct_world_niUG {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    (hlU : lowerCheckU f vc = true)
    {X : ExtSem} {XR : XRaise} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv}
    {K : Nat} {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env.toEnv (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env.toEnv (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXR : XRaiseOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hXRi : XRaiseIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hexcl : ∀ d uses w, X.call d uses w ≠ none → XR.raise d uses w = none)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {T : Unw.FnTables} {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry))) {rows : List (Nat × Cfi)}
    (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hpad : padsNonzeroB af fa = true)
    (hlast : lastCallsOk af fa = true) (hsaved : savedCheck vcp rf = true)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoopX env p fuel cs.toX = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
          (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
            PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧
            ¬ UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s) ∧
            ∀ i < n, actGoodXU vcp rf af fa fb base s X H XR U T K G (GotV vcp)
              (runX (Unw.ArmStepU X H U T fa) i s)) ∧
        (XNI F syms (f.externs.map (·.2)) (indSigs f) c
            (CallLg env.toEnv (f.externs.map (·.2)) (indSigs f)) X → XTls F X →
          XRNI F syms (f.externs.map (·.2)) (indSigs f) c
            (CallLgR env (f.externs.map (·.2)) (indSigs f)) X XR →
          ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
            (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
              PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧
              ¬ UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s) ∧
              ∀ i < n, actGoodXU vcp rf af fa fb base s X H XR U T K G (GotV vcp)
                (runX (Unw.ArmStepU X H U T fa) i s))) ∧
    (∀ c', Clif.runLoopX env p fuel cs.toX = .trapped c' →
      ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
        (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (Unw.ArmStepU X H U T fa) n s) ∧
          (∀ i < n, actGoodXU vcp rf af fa fb base s X H XR U T K G (GotV vcp)
            (runX (Unw.ArmStepU X H U T fa) i s)) ∧
          ∀ m, Arm.r .ERR (runX (Unw.ArmStepU X H U T fa) (n + m + 1) s) ≠ .None) ∧
    (∀ e cm, Clif.runLoopX env p fuel cs.toX = .unwound e cm →
      ∃ (obj : BitVec 64) (w : Arm.ArmState), ExnRel e obj ∧ MemRel F syms cm w ∧
        (∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
          (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
          ∃ n, ActUnw ra F G obj w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
            PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧ 0 < n ∧
            UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s) ∧
            ∀ i < n, actGoodXU vcp rf af fa fb base s X H XR U T K G (GotV vcp)
              (runX (Unw.ArmStepU X H U T fa) i s)) ∧
        (XNI F syms (f.externs.map (·.2)) (indSigs f) c
            (CallLg env.toEnv (f.externs.map (·.2)) (indSigs f)) X → XTls F X →
          XRNI F syms (f.externs.map (·.2)) (indSigs f) c
            (CallLgR env (f.externs.map (·.2)) (indSigs f)) X XR →
          ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
            (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀' →
            ∃ n, ActUnw ra (fun a => F a ∨ D a) G obj w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
              PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧ 0 < n ∧
              UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s) ∧
              ∀ i < n, actGoodXU vcp rf af fa fb base s X H XR U T K G (GotV vcp)
                (runX (Unw.ArmStepU X H U T fa) i s))) := by
  have hI := iselSimU_relW hsub hc hlU hX hXI hXR hXRi hexcl hsym hslot (fun _ => 0) hcs
    hrel hargs htr fuel
  have hP := prepareCorrectU_of_check (driverSem_csemU F ⟨fa.k, af.slotBase⟩ X XR) hc.prepOk XR
  have hnc : ∀ {i : MInst}, trapCode? i ≠ none → ∀ info,
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) → False := fun ht _ h => by
    rcases h with rfl | ⟨_, rfl⟩ <;> simp [trapCode?] at ht
  have hM6 : ∀ (w₀ : Arm.ArmState) (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop)
      (base ra : BitVec 64) (s : Arm.ArmState),
      ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ → _ :=
    fun w₀ H U G base ra s he => by
      have h := regLevelCorrect_worldUTG hc.check hc.alloc hc.emit hc.layout (X := X) (H := H)
        (XR := XR) (U := U) (T := T) (K := K) (G := G) (gv := GotV vcp) he.abi he.stack he.gfree
        (gotSem_csemVU _ _ _ _ _)
        (realizes_csemU_worldF hcov (by rw [he.hF]; exact he.calls) (by rw [he.hF]; exact he.tries)
          (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.unw) hsites hlsda hpad hlast)
        (fun us uses w => by
          rw [csemVU_eq fun _ h => by rcases h with h | ⟨_, h⟩ <;> cases h]
          exact csemU_rets us uses w)
        (fun i uses w outs w' ht h => by
          rw [csemVU_eq fun info h => (hnc ht info h).elim] at h
          rwa [← csemU_trap ht])
        (by rw [he.hF]; exact he.unw)
        hsites hlsda hlast hrows hcie hfde hsaved (by rw [he.hF]; exact he.body) (fun _ => 0)
      rw [he.hF] at h
      exact h
  have hNIv := fun hNI hTls hRNI D w₀' hrel' hsw hreg hstk =>
    vcode_niU hsub hc hlU hX hXI hXR hXRi hexcl hsym hslot hNI hTls hRNI (D := D) (w₀' := w₀')
      (fun _ => 0) hcs hrel hrel' hargs hsw hreg hstk htr fuel
  refine ⟨fun vals cm hrun => ?_,
    (backend_correct_worldUG hsub hc hlU hcov hX hXI hXR hXRi hexcl hsym hslot hsites hlsda hrows hcie hfde
      hpad hlast hsaved hcs hrel hargs htr fuel).2.1, fun e cm hrun => ?_⟩
  · obtain ⟨us, outs, w, hv, hus, hlen, hhold, hmemR⟩ := hI.1 vals cm hrun
    have hrs : vc.RetsSite us := by
      obtain ⟨b, k, ρ, w₁, vb, ops, outs', -, hvb, hk, -⟩ := hv
      exact ⟨b, vb, k, hvb, hk⟩
    refine ⟨us, outs, w, hus, hlen, hhold, hmemR, hrs, fun H U G base ra s he => ?_,
      fun hNI hTls hRNI D w₀' hrel' hsw hreg hstk H U G base ra s he => ?_⟩
    · exact (hM6 w₀ H U G base ra s he).1 us outs w
        (vReturns_gotV_gen (gotPair_csemU _ _ _) ((hP.1 _ _).1 _ _ _ hv))
    · obtain ⟨us', outs', w1, w2, hv1, hv2, hsw12⟩ :=
        (hNIv hNI hTls hRNI D w₀' hrel' hsw hreg hstk).1 vals cm hrun
      obtain ⟨rfl, rfl, rfl⟩ := vRetFrom_det (vs := ⟨0, 0, fun _ => 0, w₀⟩) hv1 hv
      obtain ⟨n, ⟨h1, h2, h3, h4, h5, h6⟩, h7, h8, h9⟩ := (hM6 w₀' H U G base ra s he).1 us' outs'
        w2 (vReturns_gotV_gen (gotPair_csemU _ _ _) ((hP.1 _ _).1 _ _ _ hv2))
      refine ⟨n, ⟨h1, h2, fun a ha => ?_, fun g hg h29 h31 => ?_, h5, h6⟩, h7, h8, h9⟩
      · rw [h3 a (fun hf => ha (.inl hf))]
        exact (hsw12.2.1 a ha).symm
      · rw [h4 g hg h29 h31]
        exact (hsw12.1 g hg).symm
  · obtain ⟨obj, w, hv, hex, hmemR⟩ := hI.2.2 e cm hrun
    refine ⟨obj, w, hex, hmemR, fun H U G base ra s he =>
      (hM6 w₀ H U G base ra s he).2.2 obj w
        (vUnwinds_gotV_gen (gotPair_csemU _ _ _) (hP.2 _ _ _ _ hv)),
      fun hNI hTls hRNI D w₀' hrel' hsw hreg hstk H U G base ra s he => ?_⟩
    obtain ⟨obj', w1, w2, hv1, hv2, hsw12⟩ :=
      (hNIv hNI hTls hRNI D w₀' hrel' hsw hreg hstk).2 e cm hrun
    obtain ⟨rfl, rfl⟩ := vUnwFrom_det hv1 hv
    obtain ⟨n, ⟨h1, h2, h3, h4, h5, h6⟩, h7, h8, h9, h10⟩ := (hM6 w₀' H U G base ra s he).2.2 obj'
      w2 (vUnwinds_gotV_gen (gotPair_csemU _ _ _) (hP.2 _ _ _ _ hv2))
    refine ⟨n, ⟨h1, h2, fun a ha => ?_, h4, h5, fun g hg h29 h31 => ?_⟩, h7, h8, h9, h10⟩
    · rw [h3 a (fun hf => ha (.inl hf))]
      exact (hsw12.2.1 a ha).symm
    · rw [h6 g hg h29 h31]
      exact (hsw12.1 g hg).symm

/-- **The per-function world theorem with unwinding and non-interference for either
pipeline** (`backend_correct_world_ni_pipeline`'s counterpart with unwinding;
`backend_correct_world_pipelineU` with the non-interference clauses). -/
theorem backend_correct_world_ni_pipelineU {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledEither f k vc vcp rf af fa fb)
    (hlU : lowerCheckU f vc = true)
    {X : ExtSem} {XR : XRaise} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv}
    {K : Nat} {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env.toEnv (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env.toEnv (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXR : XRaiseOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hXRi : XRaiseIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hexcl : ∀ d uses w, X.call d uses w ≠ none → XR.raise d uses w = none)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {T : Unw.FnTables} {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry))) {rows : List (Nat × Cfi)}
    (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hpad : padsNonzeroB af fa = true)
    (hlast : lastCallsOk af fa = true) (hsaved : savedCheck vcp rf = true)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoopX env p fuel cs.toX = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
          (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
            PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧
            ¬ UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s)) ∧
        (XNI F syms (f.externs.map (·.2)) (indSigs f) c
            (CallLg env.toEnv (f.externs.map (·.2)) (indSigs f)) X → XTls F X →
          XRNI F syms (f.externs.map (·.2)) (indSigs f) c
            (CallLgR env (f.externs.map (·.2)) (indSigs f)) X XR →
          ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
            (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
              PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧
              ¬ UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s))) ∧
    (∀ c', Clif.runLoopX env p fuel cs.toX = .trapped c' →
      ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
        (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (Unw.ArmStepU X H U T fa) n s)) ∧
    (∀ e cm, Clif.runLoopX env p fuel cs.toX = .unwound e cm →
      ∃ (obj : BitVec 64) (w : Arm.ArmState), ExnRel e obj ∧ MemRel F syms cm w ∧
        (∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
          (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
          ∃ n, ActUnw ra F G obj w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
            PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧ 0 < n ∧
            UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s)) ∧
        (XNI F syms (f.externs.map (·.2)) (indSigs f) c
            (CallLg env.toEnv (f.externs.map (·.2)) (indSigs f)) X → XTls F X →
          XRNI F syms (f.externs.map (·.2)) (indSigs f) c
            (CallLgR env (f.externs.map (·.2)) (indSigs f)) X XR →
          ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
            (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀' →
            ∃ n, ActUnw ra (fun a => F a ∨ D a) G obj w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
              PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧ 0 < n ∧
              UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s))) := by
  cases hc with
  | legacy hc =>
    exact backend_correct_world_niU hsub hc hlU hcov hX hXI hXR hXRi hexcl hsym hslot
      hsites hlsda hrows hcie hfde hpad hlast hsaved hcs hrel hargs htr fuel
  | cleanup hc =>
    exact backend_correct_world_ni_cleanupU hsub hc hlU hcov hX hXI hXR hXRi hexcl hsym
      hslot hsites hlsda hrows hcie hfde hpad hlast hsaved hcs hrel hargs htr fuel

/-- **The per-function world theorem with unwinding and non-interference for either
pipeline** (`backend_correct_world_ni_pipeline`'s counterpart with unwinding;
`backend_correct_world_pipelineU` with the non-interference clauses). -/
theorem backend_correct_world_ni_pipelineUG {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledEither f k vc vcp rf af fa fb)
    (hlU : lowerCheckU f vc = true)
    {X : ExtSem} {XR : XRaise} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv}
    {K : Nat} {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env.toEnv (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env.toEnv (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXR : XRaiseOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hXRi : XRaiseIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hexcl : ∀ d uses w, X.call d uses w ≠ none → XR.raise d uses w = none)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {T : Unw.FnTables} {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry))) {rows : List (Nat × Cfi)}
    (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hpad : padsNonzeroB af fa = true)
    (hlast : lastCallsOk af fa = true) (hsaved : savedCheck vcp rf = true)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoopX env p fuel cs.toX = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
          (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
            PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧
            ¬ UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s) ∧
            ∀ i < n, actGoodXU vcp rf af fa fb base s X H XR U T K G (GotV vcp)
              (runX (Unw.ArmStepU X H U T fa) i s)) ∧
        (XNI F syms (f.externs.map (·.2)) (indSigs f) c
            (CallLg env.toEnv (f.externs.map (·.2)) (indSigs f)) X → XTls F X →
          XRNI F syms (f.externs.map (·.2)) (indSigs f) c
            (CallLgR env (f.externs.map (·.2)) (indSigs f)) X XR →
          ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
            (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
              PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧
              ¬ UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s) ∧
              ∀ i < n, actGoodXU vcp rf af fa fb base s X H XR U T K G (GotV vcp)
                (runX (Unw.ArmStepU X H U T fa) i s))) ∧
    (∀ c', Clif.runLoopX env p fuel cs.toX = .trapped c' →
      ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
        (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (Unw.ArmStepU X H U T fa) n s) ∧
          (∀ i < n, actGoodXU vcp rf af fa fb base s X H XR U T K G (GotV vcp)
            (runX (Unw.ArmStepU X H U T fa) i s)) ∧
          ∀ m, Arm.r .ERR (runX (Unw.ArmStepU X H U T fa) (n + m + 1) s) ≠ .None) ∧
    (∀ e cm, Clif.runLoopX env p fuel cs.toX = .unwound e cm →
      ∃ (obj : BitVec 64) (w : Arm.ArmState), ExnRel e obj ∧ MemRel F syms cm w ∧
        (∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
          (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀ →
          ∃ n, ActUnw ra F G obj w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
            PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧ 0 < n ∧
            UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s) ∧
            ∀ i < n, actGoodXU vcp rf af fa fb base s X H XR U T K G (GotV vcp)
              (runX (Unw.ArmStepU X H U T fa) i s)) ∧
        (XNI F syms (f.externs.map (·.2)) (indSigs f) c
            (CallLg env.toEnv (f.externs.map (·.2)) (indSigs f)) X → XTls F X →
          XRNI F syms (f.externs.map (·.2)) (indSigs f) c
            (CallLgR env (f.externs.map (·.2)) (indSigs f)) X XR →
          ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
            (s : Arm.ArmState), ActEntryU vcp rf af fa fb K F G X H XR U base ra s w₀' →
            ∃ n, ActUnw ra (fun a => F a ∨ D a) G obj w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
              PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧ 0 < n ∧
              UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s) ∧
              ∀ i < n, actGoodXU vcp rf af fa fb base s X H XR U T K G (GotV vcp)
                (runX (Unw.ArmStepU X H U T fa) i s))) := by
  cases hc with
  | legacy hc =>
    exact backend_correct_world_niUG hsub hc hlU hcov hX hXI hXR hXRi hexcl hsym hslot
      hsites hlsda hrows hcie hfde hpad hlast hsaved hcs hrel hargs htr fuel
  | cleanup hc =>
    exact backend_correct_world_ni_cleanupUG hsub hc hlU hcov hX hXI hXR hXRi hexcl hsym
      hslot hsites hlsda hrows hcie hfde hpad hlast hsaved hcs hrel hargs htr fuel

end E2E
