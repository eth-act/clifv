import FV.E2E.ExecTlsSim
import FV.E2E.ExecProven

/-! # The binary theorem without the TLS hook (T1)

`binary_correct_exec_proven_tls` is `binary_correct_exec_proven` for the hook-free executable
machine `stepT` (the processor on every word of the program, lld's local-exec TLS words
included; only calls of code outside the program are hooks). The TLS hook and its trusted
contract `TlsOk` are gone: the model machine of the proof uses the base environment
`leBase I B file`, whose TLS hook meets `TlsOk` and `HooksSim` by construction (`tlsOk_le`,
`hooksSim_le`); what remains is the loader's thread-pointer contract `TlsLoader` (the entry
state's `TPIDR_EL0`, kept by code outside the program, and the running thread's instance of each
thread-local variable at `TPIDR_EL0 + TpOff`, where the CLIF semantics has it).
-/

namespace E2E.ExecBytes

open Backend Backend.Proof E2E.LinkCheck E2E.Binary E2E.BinCheck

/-- **The binary theorem about the executable's own words, TLS included** (T1;
`docs/contracts/e2e.md`): under the premises of `binary_correct_exec_proven` — with the base
environment `leBase I B file` (`B` whose TLS hook is what lld's local-exec words do; its
`BaseOk`'s TLS clause holds by `tlsOk_le`), `HooksSim` only for the calls of code outside the
program — and the loader's thread-pointer contract `TlsLoader`, the hook-free executable machine
`stepT` (the processor on the executable's words, the TLS sequence included) run from `r`
refines the whole-program CLIF run. -/
theorem binary_correct_exec_proven_tls {I : LinkInput} {D : List Clif.DataObject}
    {file : ByteArray} (hI : okB I = true) (hcm : codeMapB I (tabOf I.results) = true)
    (hbin : BinCheck.BinOk I D file) (hgot : GotOk I file) (B : BaseEnv)
    (hB : BaseOk (sys I (leBase I B file)))
    (hHc : ∀ d m e, Sim I m e → Sim I (B.hooks.call d m) (B.hooks.call d e))
    {n : String} {f : Clif.Function} (hf : (prog I).func? n = some f)
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls I I.results) f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (StackBound.stackFn I f) r args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (StackBound.stackFn I f) r args cs.mem)
    (hr : ClifRun I B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs)
    (hL : TlsLoader I B file r) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (stepT I B file) r (RelocAt I)
      (Clif.runLoop B.env (prog I) (M + 1) cs) := by
  have hr' : ClifRun I (leBase I B file) f r args cs := hr
  have htr' : TrapsExplicit (Clif.linkEnvN (prog I) (leBase I B file).env M) (prog I).bare cs := htr
  have hH := hooksSim_le (file := file) hHc
  have hn := (StackBound.goodN_iff hI).2 ⟨f, hf, hc⟩
  by_cases hout : (∃ vals cm, Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) ∨
      (∃ c, Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c)
  · obtain ⟨-, -, hG⟩ := binary_correct_of_checksX hI hbin _ hB hn hf M hX ho hr' htr'
    obtain ⟨h1, h2⟩ := binary_correct_of_checks hI hbin _ hB hn hf M hX ho hr' htr'
    have hgS := runGood_sysS hI hbin hB hn hf M hX ho hav hr' htr' hout
    have hfm := (Clif.Program.func?_some hf).1
    have hL' := okB_sound hI (baseOk_F (F' := img I) hB) fun _ h => h
    have hF : ∀ g ∈ (prog I).funcs, FnOk I file g := fun g hg => fnOk hI hbin hL' hg
    have hB'' : BaseOk (LinkSys.ofInput I (leBase I B file) (worldF I f (StackBound.bud I f) r)) :=
      baseOk_F hB
    have hL0 := okB_sound hI hB'' fun _ h => .inr h
    have hfacts := binFacts_of_checks hI hbin
    have hro : ∀ a b, BinCheck.roByte I D a = some b → r.mem a = b := fun a b h =>
      hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
    obtain ⟨hent, -⟩ := premises hL0 hfm hro ho hr'
    have hra : ∀ k < (art I f).fb.words.size,
        xreg 30 (modelOf I f r) ≠ (art I f).base + BitVec.ofNat 64 (4 * k) := by
      simp only [xreg, r_modelOf]; exact hent.raOutside
    -- D2 (`insn_of_good`) and D4 (`got_of_good`) at the model's states, as in
    -- `binary_correct_exec_proven`
    have hreads : RunReadsN I (leBase I B file) file M f (modelOf I f r) := fun M' g t hR he => by
      obtain ⟨c', hRL, -⟩ := reachL_of_reachN hI hcm hF hR hfm (hG hout) (raNotSecond_top (hF f hfm) hra)
      refine ⟨insn_of_good hI hcm hF (reachN_mem hR hfm) (hG hout _ _ _ _ hRL he), ?_⟩
      have hRL' : (sysS I (leBase I B file) f (StackBound.bud I f) r (GotSlot I file)).ReachL M f
          (modelOf I f r) M' g c' t := by
        exact LinkSys.reachL_extImg (F := worldFS I f (StackBound.bud I f) r (GotSlot I file))
          (S := GotSlot I file) (m := (modelOf I f r).mem)
          (Binary.reachL_F (F := worldF I f (StackBound.bud I f) r) (F' := fun _ => False) hRL)
      have hg := reachN_mem hR hfm
      exact got_of_good hI hbin hgot hX hg (hF g hg)
        (hgS _ _ _ _ hRL' (by rw [mach_sysS]; exact he))
    have hrunN := runOkN_of_good hI hcm hF (fun g hg => destsInt_of_ok hL' hg) hfm hra (hG hout)
      hreads
    have hrunS := runOkSN_of_n hI hcm hF hH hfm hrunN
    have htls := runTlsN_of_good hI hcm hF hfm hra (hG hout)
    exact exec_of_modelT hF (fun g hg => tlsClosed_art hI hg)
      (fun g hg a i hi => siteAt_static hI hcm hF hg hi) hL hfm
      (by rw [← r_modelOf I f r]; exact hent.pc) hent.raOutside h2 hrunS htls h1
  · cases h : Clif.runLoop B.env (prog I) (M + 1) cs with
    | returned vals cm => exact absurd (.inl ⟨vals, cm, h⟩) hout
    | trapped c => exact absurd (.inr ⟨c, h⟩) hout
    | stuck _ => trivial
    | outOfFuel => trivial

end E2E.ExecBytes
