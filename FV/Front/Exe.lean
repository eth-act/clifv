import FV.Front.BundleProof
import FV.Front.RenameRun
import FV.Link.DeadCleanupExeSource

/-!
# The executable compiler refines the frontend bundle's program (T7e, docs/contracts/frontend.md)

The compiler's executable theorems (`Link.DeadCleanup.compileExe_correct_source{,_peak}`, the
shipped compiler; `Link.compileExe_correct_source{,_peak}`, the baseline) are about the source
program of the `LinkSpec` they compile: its parsed functions, under the names the program is
linked with. `lake exe lean-link` builds that `LinkSpec` from the frontend bundle in Lean
(`Front.buildSpec`), and its source program is the bundle's units' program under the linked
names (`Front.buildSpec_srcProg`), a scoping of the units, alpha-equivalent to the units' program
under any scoping `sc` (`Front.link_alpha`: a bijection `σ` of names with
`link us (finOf us) = (link us sc).rename σ.fwd`). Here the theorems are composed with the
renaming (`Clif.runLoop_ren`): they hold for **the runs of the units' program under `sc`** in an
environment `E` of the outside code under `sc`'s names, the executable's base environment `B`
being `E` renamed (`B.env = E.ren σ`).

* `bundle_correct_source` (the shipped compiler, entries without a reachable call cycle),
  `bundle_correct_source_peak` (any entry, the stack from the source run's depth);
* `bundle_correct_source_baseline`, `bundle_correct_source_peak_baseline` (the baseline
  compiler).

The premises about the source run (`ClifEntry`, `SReach`/`MemBounded`, `NoMemTrap`,
`DepthLe`) are stated on the units' program and transported (`ren_*`); those about the
executable, the outside code and the target run are the compiler theorems', unchanged.
-/

namespace Front

open Clif E2E.LinkCheck Link

/-! ## Transporting run facts through a renaming -/

theorem step_ren_next {σ : Ren} {E : Env} {p : Program} {s t : State}
    (h : step (E.ren σ) (p.rename σ.fwd) (s.ren σ) = .next t) :
    ∃ s', step E p s = .next s' ∧ t = s'.ren σ := by
  have := step_ren σ E p s
  rw [h] at this
  cases hs : step E p s <;> rw [hs] at this <;> simp [StepResult.ren, StepResult.erase] at this
  exact ⟨_, rfl, this⟩

theorem step_ren_trapped {σ : Ren} {E : Env} {p : Program} {s : State} {c : TrapCode}
    (h : step (E.ren σ) (p.rename σ.fwd) (s.ren σ) = .trapped c) : step E p s = .trapped c := by
  have := step_ren σ E p s
  rw [h] at this
  cases hs : step E p s <;> rw [hs] at this <;> simp [StepResult.ren, StepResult.erase] at this
  rw [this]

theorem sreach_ren {σ : Ren} {E : Env} {p : Program} {s t : State}
    (h : Opt.Legal.SReach (E.ren σ) (p.rename σ.fwd) (s.ren σ) t) :
    ∃ s', Opt.Legal.SReach E p s s' ∧ t = s'.ren σ := by
  generalize hx : s.ren σ = x at h
  induction h generalizing s with
  | refl => exact ⟨s, .refl _, hx.symm⟩
  | step hst _ ih =>
    subst hx
    obtain ⟨s1, hs1, rfl⟩ := step_ren_next hst
    obtain ⟨s2, h2, rfl⟩ := ih rfl
    exact ⟨s2, .step hs1 h2, rfl⟩

theorem reaches_ren {σ : Ren} {E : Env} {p : Program} {s t : State}
    (h : Reaches (E.ren σ) (p.rename σ.fwd) (s.ren σ) t) :
    ∃ s', Reaches E p s s' ∧ t = s'.ren σ := by
  generalize hx : s.ren σ = x at h
  induction h generalizing s with
  | refl => exact ⟨s, .refl _, hx.symm⟩
  | next hst _ ih =>
    subst hx
    obtain ⟨s1, hs1, rfl⟩ := step_ren_next hst
    obtain ⟨s2, h2, rfl⟩ := ih rfl
    exact ⟨s2, .next hs1 h2, rfl⟩

theorem memBounded_ren {σ : Ren} {m : Mem} (h : Opt.Legal.MemBounded m) :
    Opt.Legal.MemBounded (m.ren σ) := fun a n hv => h a n (by simpa [Mem.valid] using hv)

/-- The source memory bound, transported. -/
theorem bnd_ren {σ : Ren} {E : Env} {p : Program} {s : State}
    (h : ∀ s', Opt.Legal.SReach E p s s' → Opt.Legal.MemBounded s'.mem) :
    ∀ t, Opt.Legal.SReach (E.ren σ) (p.rename σ.fwd) (s.ren σ) t → Opt.Legal.MemBounded t.mem := by
  intro t ht
  obtain ⟨s', hs', rfl⟩ := sreach_ren ht
  exact memBounded_ren (h s' hs')

/-- No load/store trap, transported. -/
theorem noMemTrap_ren {σ : Ren} {E : Env} {p : Program} {s : State}
    (h : Opt.Legal.NoMemTrap E p s) : Opt.Legal.NoMemTrap (E.ren σ) (p.rename σ.fwd) (s.ren σ) := by
  intro t ht c st rest htr hb
  obtain ⟨s', hs', rfl⟩ := sreach_ren ht
  exact h s' hs' c st rest (step_ren_trapped htr) (by simpa using hb)

/-- The call-depth bound, transported. -/
theorem depthLe_ren {σ : Ren} {E : Env} {p : Program} {d : Nat} {s : State}
    (h : DepthLe E p d s) : DepthLe (E.ren σ) (p.rename σ.fwd) d (s.ren σ) := by
  intro t ht
  obtain ⟨s', hs', rfl⟩ := reaches_ren ht
  simpa using h s' hs'

/-- An entry state, transported. -/
theorem clifEntry_ren {σ : Ren} {f : Clif.Function} {args : List Val} {cs : State}
    (h : E2E.ClifEntry f args cs) : E2E.ClifEntry (f.rename σ.fwd) args (cs.ren σ) where
  callers := by simp [h.callers]
  func := by simp [h.func]
  sig := by simpa using h.sig
  entry := by
    obtain ⟨b, hb, h1, h2, h3, h4⟩ := h.entry
    exact ⟨b, by simpa using hb, by simpa using h1, by simpa using h2, h3, by simpa using h4⟩
  slotIds := by simpa using h.slotIds

/-! ## Renaming back -/

theorem GlobalValue.rename_id' (v : GlobalValue) : v.rename (fun x => x) = v := by
  cases v <;> rfl

/-- Renaming by the identity. -/
theorem Function.rename_id' (f : Clif.Function) : f.rename (fun x => x) = f := by
  cases f
  simp only [Clif.Function.rename, ExtFunc.rename, RunCommand.rename, GlobalValue.rename_id']
  congr <;> simp

theorem Function.rename_symm (σ : Ren) (f : Clif.Function) :
    (f.rename σ.bwd).rename σ.fwd = f := by
  rw [Function.rename_rename]
  simp only [σ.fwd_bwd]
  exact Function.rename_id' f

theorem Mem.ren_symm_ren (σ : Ren) (m : Mem) : (m.ren σ.symm).ren σ = m :=
  Mem.ren_ren_symm σ.symm m

theorem Outcome.ren_symm_ren (σ : Ren) (o : Outcome) : (o.ren σ.symm).ren σ = o := by
  cases o <;> simp [Outcome.ren, Mem.ren_symm_ren]

/-- **Renaming an environment back and forth.** -/
theorem Env.ren_symm_ren (σ : Ren) (E : Env) : (E.ren σ.symm).ren σ = E := by
  cases E with
  | mk ext names sigOf =>
    simp only [Env.ren, Ren.symm_fwd, Ren.symm_bwd, σ.fwd_bwd, List.map_map,
      Function.comp_def, List.map_id']
    congr 1
    funext n
    cases ext n with
    | none => rfl
    | some g =>
      simp only [Option.map_some]
      congr 1
      funext vals m
      rw [show (m.ren σ.symm).ren σ.symm.symm = m from Mem.ren_ren_symm σ.symm m,
        Outcome.ren_symm_ren]

/-- **Renaming a state back and forth.** -/
theorem State.ren_symm_ren (σ : Ren) (s : State) : (s.ren σ.symm).ren σ = s := by
  have hf : ∀ fr : Frame, (fr.ren σ.symm).ren σ = fr := fun fr => by
    cases fr; simp only [Frame.ren, Ren.symm_fwd, Function.rename_symm]
  cases s with
  | mk fr cs m =>
    simp only [State.ren, List.map_map, Function.comp_def, hf, Mem.ren_symm_ren]
    simp

section Cleanup

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes
  E2E.LegalProgram Backend Opt.Legalize128

/-- **The shipped executable compiler refines the frontend bundle's program** (T7e):
`Link.DeadCleanup.compileExe_correct_source` for the `LinkSpec` `lean-link` builds from the
bundle (`buildSpec b = .ok S`), about the runs of the units' program under a scoping `sc`
(`link us sc`, alpha-equivalent to the linked one by `σ`: `link_alpha`) in the environment `E`
(the executable's `B.env = E.ren σ`): a return of the source run from `f`'s entry `cs` is the
executable's return of the split results, the memory renamed to the linked names; a trap (of a
source run without load/store traps) is the same trap. -/
theorem bundle_correct_source {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S) (h : Link.DeadCleanup.compileExe S file0 = .ok file)
    (hsrc : SrcScopeB S.inputCleanup = true)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} {σ : Clif.Ren}
    (hσ : link us (finOf us) = (link us sc).rename σ.fwd)
    (E : Clif.Env) (B : BaseEnv) (hE : B.env = E.ren σ)
    (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
    (hlegal : (∃ f ∈ S.inputCleanup.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : (link us sc).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls S.inputCleanup S.inputCleanup.resultsCleanup) (legalize (f.rename σ.fwd)))
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) (legalize (f.rename σ.fwd))
      (DeadCleanupStackBound.stackFn S.inputCleanup (legalize (f.rename σ.fwd))) r args' cs'.mem)
    (hr : ClifRun S.inputCleanup B (legalize (f.rename σ.fwd)) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem.ren σ)
    (hbnd : ∀ s', Opt.Legal.SReach E (link us sc) cs s' → Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop E (link us sc) M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.inputCleanup (legalize (f.rename σ.fwd))).fb (art S.inputCleanup (legalize (f.rename σ.fwd))).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' (cm.ren σ))) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog S.inputCleanup) B.env M) (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap E (link us sc) cs → ∀ c,
      Clif.runLoop E (link us sc) M cs = .trapped c →
      ExecRefines (art S.inputCleanup (legalize (f.rename σ.fwd))).fb (art S.inputCleanup (legalize (f.rename σ.fwd))).base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  have hP : S.inputCleanup.srcProg = (link us sc).rename σ.fwd := by
    obtain ⟨us', hus', -, hs⟩ := buildSpec_srcProg hb
    rw [hus] at hus'; cases hus'
    rw [← hσ, ← hs]; rfl
  have hf' : S.inputCleanup.srcProg.func? (σ.fwd n) = some (f.rename σ.fwd) := by
    rw [hP, Clif.Program.rename_func?, hf]; rfl
  have H := Link.DeadCleanup.compileExe_correct_source (cs := cs.ren σ) h hsrc B hB hH hlegal hsig hf' hc hX ho hr
    (clifEntry_ren hcs) (by simpa using hexp) (by simpa using hsl) hmem
    (by rw [hP, hE]; exact bnd_ren hbnd) M
  simp only [Clif.Function.rename_sig] at H
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · have := Clif.runLoop_ren_returned σ E (link us sc) M cs hrun
    rw [← hE, ← hP] at this
    exact H.1 vals (cm.ren σ) this
  · have := Clif.runLoop_ren_trapped σ E (link us sc) M cs hrun
    rw [← hE, ← hP] at this
    exact H.2 htr (by have := noMemTrap_ren (σ := σ) hnmt; rwa [← hE, ← hP] at this) c this

/-- **The shipped executable compiler refines the frontend bundle's program, recursive
programs included** (T7e): `Link.DeadCleanup.compileExe_correct_source_peak` composed as in
`bundle_correct_source`; the stack `frameDrop + (D * d + pbMax)` (#581: the deepest activation's
stack probes write up to `pbMax` bytes below its frame) from the source run's call depth `d` (`Clif.DepthLe` of the
units' program). -/
theorem bundle_correct_source_peak {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S) (h : Link.DeadCleanup.compileExe S file0 = .ok file)
    (hsrc : SrcScopeB S.inputCleanup = true)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} {σ : Clif.Ren}
    (hσ : link us (finOf us) = (link us sc).rename σ.fwd)
    (E : Clif.Env) (B : BaseEnv) (hE : B.env = E.ren σ)
    (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
    (hlegal : (∃ f ∈ S.inputCleanup.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : (link us sc).func? n = some f) (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) (legalize (f.rename σ.fwd))
      (frameDrop (art S.inputCleanup (legalize (f.rename σ.fwd))).af +
        (S.inputCleanup.D * d + pbMax S.inputCleanup)) r args' cs'.mem)
    (hr : ClifRun S.inputCleanup B (legalize (f.rename σ.fwd)) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem.ren σ)
    (hbnd : ∀ s', Opt.Legal.SReach E (link us sc) cs s' → Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe E (link us sc) d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop E (link us sc) M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.inputCleanup (legalize (f.rename σ.fwd))).fb (art S.inputCleanup (legalize (f.rename σ.fwd))).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' (cm.ren σ))) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.inputCleanup) B.env F d) (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap E (link us sc) cs → ∀ c,
      Clif.runLoop E (link us sc) M cs = .trapped c →
      ExecRefines (art S.inputCleanup (legalize (f.rename σ.fwd))).fb (art S.inputCleanup (legalize (f.rename σ.fwd))).base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  have hP : S.inputCleanup.srcProg = (link us sc).rename σ.fwd := by
    obtain ⟨us', hus', -, hs⟩ := buildSpec_srcProg hb
    rw [hus] at hus'; cases hus'
    rw [← hσ, ← hs]; rfl
  have hf' : S.inputCleanup.srcProg.func? (σ.fwd n) = some (f.rename σ.fwd) := by
    rw [hP, Clif.Program.rename_func?, hf]; rfl
  have H := Link.DeadCleanup.compileExe_correct_source_peak (cs := cs.ren σ) h hsrc B hB hH hlegal hsig hf' d hX ho hr
    (clifEntry_ren hcs) (by simpa using hexp) (by simpa using hsl) hmem
    (by rw [hP, hE]; exact bnd_ren hbnd) (by rw [hP, hE]; exact depthLe_ren hd) M
  simp only [Clif.Function.rename_sig] at H
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · have := Clif.runLoop_ren_returned σ E (link us sc) M cs hrun
    rw [← hE, ← hP] at this
    exact H.1 vals (cm.ren σ) this
  · have := Clif.runLoop_ren_trapped σ E (link us sc) M cs hrun
    rw [← hE, ← hP] at this
    exact H.2 htr (by have := noMemTrap_ren (σ := σ) hnmt; rwa [← hE, ← hP] at this) c this

end Cleanup

section Baseline

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.Binary E2E.ExecBytes E2E.LegalProgram Backend
  Opt.Legalize128

/-- **The baseline executable compiler refines the frontend bundle's program** (T7e):
`Link.compileExe_correct_source` composed as in `bundle_correct_source`. -/
theorem bundle_correct_source_baseline {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S) (h : Link.compileExe S file0 = .ok file)
    (hsrc : SrcScopeB S.input = true)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} {σ : Clif.Ren}
    (hσ : link us (finOf us) = (link us sc).rename σ.fwd)
    (E : Clif.Env) (B : BaseEnv) (hE : B.env = E.ren σ)
    (hB : BaseOk (sys S.input B)) (hH : HooksSim S.input B)
    (hlegal : (∃ f ∈ S.input.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : (link us sc).func? n = some f)
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls S.input S.input.results) (legalize (f.rename σ.fwd)))
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) (legalize (f.rename σ.fwd))
      (StackBound.stackFn S.input (legalize (f.rename σ.fwd))) r args' cs'.mem)
    (hr : ClifRun S.input B (legalize (f.rename σ.fwd)) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem.ren σ)
    (hbnd : ∀ s', Opt.Legal.SReach E (link us sc) cs s' → Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop E (link us sc) M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.input (legalize (f.rename σ.fwd))).fb (art S.input (legalize (f.rename σ.fwd))).base
          (xreg 30 r) (step S.input B file) r
          (RelocAt S.input) (.returned vals' (cm.ren σ))) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog S.input) B.env M) (prog S.input).bare cs') →
      Opt.Legal.NoMemTrap E (link us sc) cs → ∀ c,
      Clif.runLoop E (link us sc) M cs = .trapped c →
      ExecRefines (art S.input (legalize (f.rename σ.fwd))).fb (art S.input (legalize (f.rename σ.fwd))).base
        (xreg 30 r) (step S.input B file) r
        (RelocAt S.input) (.trapped c)) := by
  have hP : S.input.srcProg = (link us sc).rename σ.fwd := by
    obtain ⟨us', hus', -, hs⟩ := buildSpec_srcProg hb
    rw [hus] at hus'; cases hus'
    rw [← hσ, ← hs]; rfl
  have hf' : S.input.srcProg.func? (σ.fwd n) = some (f.rename σ.fwd) := by
    rw [hP, Clif.Program.rename_func?, hf]; rfl
  have H := Link.compileExe_correct_source (cs := cs.ren σ) h hsrc B hB hH hlegal hsig hf' hc hX ho hr
    (clifEntry_ren hcs) (by simpa using hexp) (by simpa using hsl) hmem
    (by rw [hP, hE]; exact bnd_ren hbnd) M
  simp only [Clif.Function.rename_sig] at H
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · have := Clif.runLoop_ren_returned σ E (link us sc) M cs hrun
    rw [← hE, ← hP] at this
    exact H.1 vals (cm.ren σ) this
  · have := Clif.runLoop_ren_trapped σ E (link us sc) M cs hrun
    rw [← hE, ← hP] at this
    exact H.2 htr (by have := noMemTrap_ren (σ := σ) hnmt; rwa [← hE, ← hP] at this) c this

/-- **The baseline executable compiler refines the frontend bundle's program, recursive
programs included** (T7e): `Link.compileExe_correct_source_peak` composed as in
`bundle_correct_source`. -/
theorem bundle_correct_source_peak_baseline {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S) (h : Link.compileExe S file0 = .ok file)
    (hsrc : SrcScopeB S.input = true)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} {σ : Clif.Ren}
    (hσ : link us (finOf us) = (link us sc).rename σ.fwd)
    (E : Clif.Env) (B : BaseEnv) (hE : B.env = E.ren σ)
    (hB : BaseOk (sys S.input B)) (hH : HooksSim S.input B)
    (hlegal : (∃ f ∈ S.input.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : (link us sc).func? n = some f) (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) (legalize (f.rename σ.fwd))
      (frameDrop (art S.input (legalize (f.rename σ.fwd))).af + (S.input.D * d + pbMax S.input)) r
      args' cs'.mem)
    (hr : ClifRun S.input B (legalize (f.rename σ.fwd)) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem.ren σ)
    (hbnd : ∀ s', Opt.Legal.SReach E (link us sc) cs s' → Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe E (link us sc) d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop E (link us sc) M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.input (legalize (f.rename σ.fwd))).fb (art S.input (legalize (f.rename σ.fwd))).base
          (xreg 30 r) (step S.input B file) r
          (RelocAt S.input) (.returned vals' (cm.ren σ))) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.input) B.env F d) (prog S.input).bare cs') →
      Opt.Legal.NoMemTrap E (link us sc) cs → ∀ c,
      Clif.runLoop E (link us sc) M cs = .trapped c →
      ExecRefines (art S.input (legalize (f.rename σ.fwd))).fb (art S.input (legalize (f.rename σ.fwd))).base
        (xreg 30 r) (step S.input B file) r
        (RelocAt S.input) (.trapped c)) := by
  have hP : S.input.srcProg = (link us sc).rename σ.fwd := by
    obtain ⟨us', hus', -, hs⟩ := buildSpec_srcProg hb
    rw [hus] at hus'; cases hus'
    rw [← hσ, ← hs]; rfl
  have hf' : S.input.srcProg.func? (σ.fwd n) = some (f.rename σ.fwd) := by
    rw [hP, Clif.Program.rename_func?, hf]; rfl
  have H := Link.compileExe_correct_source_peak (cs := cs.ren σ) h hsrc B hB hH hlegal hsig hf' d hX ho hr
    (clifEntry_ren hcs) (by simpa using hexp) (by simpa using hsl) hmem
    (by rw [hP, hE]; exact bnd_ren hbnd) (by rw [hP, hE]; exact depthLe_ren hd) M
  simp only [Clif.Function.rename_sig] at H
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · have := Clif.runLoop_ren_returned σ E (link us sc) M cs hrun
    rw [← hE, ← hP] at this
    exact H.1 vals (cm.ren σ) this
  · have := Clif.runLoop_ren_trapped σ E (link us sc) M cs hrun
    rw [← hE, ← hP] at this
    exact H.2 htr (by have := noMemTrap_ren (σ := σ) hnmt; rwa [← hE, ← hP] at this) c this

end Baseline

end Front
