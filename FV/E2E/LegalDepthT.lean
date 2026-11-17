import FV.E2E.LegalDepth
import FV.E2E.LegalProgramT

/-!
# Whole-program refinement keeping the call depth, `try_call_indirect` included (#1076)

`legalProg_refines_depthT`: `legalProg_refines_depth` (`FV/E2E/LegalDepth.lean`) on the source
domain `ProgCtxT` (every function in `legalOkTB`; `FV/E2E/LegalProgramT.lean`). The proof is the
old one with `legalize_refines2W` and `Complete.indTB_indSite` for the legalised activations.
-/

namespace E2E.LegalProgram

open Clif Opt.Legal Opt.Legalize128

section Induction

variable {P : Program} {B : Env} {syms : String → Option Nat} (hC : ProgCtxT P B syms)
  {M : Nat} (ih : RefinesD B P syms M) (d : Nat)
include hC ih

/-- A callee run of the guarded environment at depth `d` and the target's: related by the
induction hypothesis at depth `d - 1`. -/
theorem prog_callDT {n : String} {h2 : Function} (hp : P.func? n = some h2)
    {vals vals' : List Val} {m : Mem}
    (hexp : ExpRel ((groups h2.sig.params).getD []) vals vals') :
    (∀ rv m', guardFunD B P (SomeInd (legalProg P)) syms M d h2 n vals m = .returned rv m' →
      ∃ rv', ExpRel ((groups h2.sig.returns).getD []) rv rv' ∧
        tgtFunD B (legalProg P) d n vals' m = .returned rv' m') ∧
    (∀ c, guardFunD B P (SomeInd (legalProg P)) syms M d h2 n vals m = .trapped c →
      tgtFunD B (legalProg P) d n vals' m = .trapped c) := by
  obtain ⟨hh2, rfl⟩ := Program.func?_some hp
  have hp' := hC.func?_some hp
  have key : ∀ o, guardFunD B P (SomeInd (legalProg P)) syms M d h2 h2.name vals m = o →
      (∀ msg, o ≠ .stuck msg) → ∃ fr m1 fr', enterFunc h2 vals m = .ok (fr, m1) ∧
        enterFunc (legalize h2) vals' m = .ok (fr', m1) ∧
        GoodFrom B P (SomeInd (legalProg P)) syms ⟨fr, [], m1⟩ ∧ 0 < d ∧
        DepthLe B P (d - 1) ⟨fr, [], m1⟩ ∧ Clif.runLoop B P M ⟨fr, [], m1⟩ = o := by
    intro o ho hs
    obtain ⟨⟨hgood, hdep⟩, hl⟩ := guardFunD_cases ho hs
    unfold linkFun at hl
    cases hi : initState P h2.name vals m with
    | ok s =>
      rw [hi] at hl
      obtain ⟨fr, m1, he, rfl⟩ := (initState_ok_iff hp).mp hi
      obtain ⟨fr', he'⟩ := enterFunc_legalT (hC.ok h2 hh2) he hexp
      obtain ⟨hd0, hdl⟩ := hdep fr m1 he
      exact ⟨fr, m1, fr', he, he', hgood fr m1 he, hd0, hdl, hl⟩
    | trap c => exact absurd hi (initState_not_trap P h2.name vals m c)
    | stuck msg => rw [hi] at hl; exact absurd hl.symm (hs msg)
  have tgt : ∀ fr' m1 o k, enterFunc (legalize h2) vals' m = .ok (fr', m1) →
      Clif.runLoop B (legalProg P) k ⟨fr', [], m1⟩ = o → o ≠ .outOfFuel → 0 < d →
      DepthLe B (legalProg P) (d - 1) ⟨fr', [], m1⟩ →
      tgtFunD B (legalProg P) d h2.name vals' m = o := by
    intro fr' m1 o k he' hr ho hd0 hdl
    unfold tgtFunD
    rw [(initState_ok_iff hp').mpr ⟨fr', m1, he', rfl⟩]
    dsimp only
    simp only [hd0, hdl, and_self, ↓reduceIte]
    rw [runLim_eq (by rw [hr]; exact ho), hr]
  refine ⟨fun rv m' ho => ?_, fun c ho => ?_⟩
  · obtain ⟨fr, m1, fr', he, he', hG, hd0, hdl, hr⟩ := key _ ho (fun _ h => by cases h)
    obtain ⟨rv', hrel, ⟨k, hk⟩, hdt⟩ :=
      (ih (d - 1) h2 hh2 vals vals' m fr m1 fr' he he' hexp hG hdl).1 rv m' hr
    exact ⟨rv', hrel, tgt fr' m1 _ k he' hk (fun h => by cases h) hd0 hdt⟩
  · obtain ⟨fr, m1, fr', he, he', hG, hd0, hdl, hr⟩ := key _ ho (fun _ h => by cases h)
    obtain ⟨⟨k, hk⟩, hdt⟩ := (ih (d - 1) h2 hh2 vals vals' m fr m1 fr' he he' hexp hG hdl).2 c hr
    exact tgt fr' m1 _ k he' hk (fun h => by cases h) hd0 hdt

/-- `extRel_prog` at call depth `d`. -/
theorem extRel_progDT {n : String} {h2 : Function} (hp : P.func? n = some h2) {sig : Signature}
    (hsig : h2.sig = sig) :
    ExtRelAt (guardEnvD B P (SomeInd (legalProg P)) syms M d) (tgtEnvD B P (legalProg P) d) n
      sig := by
  intro hs he
  rw [guardEnvD_some hp] at he
  cases he
  refine ⟨_, tgtEnvD_some (hC.func?_some hp), fun gs rg hgs hrg vals vals' m hty hexp => ?_⟩
  have hexp' : ExpRel ((groups h2.sig.params).getD []) vals vals' := by
    rw [hsig, hgs]; exact hexp
  obtain ⟨h1, h2'⟩ := prog_callDT hC ih d hp hexp'
  refine ⟨fun rv m' ho _ => ?_, fun c ho => h2' c ho⟩
  obtain ⟨rv', hrel, ht⟩ := h1 rv m' ho
  refine ⟨rv', ht, ?_⟩
  rw [hsig, hrg] at hrel
  exact hrel

/-- `sameAt_link` at call depth `d`. -/
theorem sameAt_linkDT {n : String} {sig : Signature} (hd : sig128 sig = false)
    (hdecl : ∀ h2, P.func? n = some h2 → h2.sig = sig) :
    SameAt (guardEnvD B P (SomeInd (legalProg P)) syms M d) (tgtEnvD B P (legalProg P) d) n
      sig := by
  intro hs he
  cases hpn : P.func? n with
  | some h2 =>
    rw [guardEnvD_some hpn] at he
    cases he
    have hs2 := hdecl h2 hpn
    have hd2 : sig128 h2.sig = false := by rw [hs2]; exact hd
    refine ⟨_, tgtEnvD_some (hC.func?_some hpn), fun vals m hv => ?_⟩
    obtain ⟨gs, hgs, hG⟩ := groups_plain (sig128_params hd2)
    have hexp : ExpRel ((groups h2.sig.params).getD []) vals vals := by
      rw [hgs, Option.getD_some]
      refine expRel_refl_plain hG (sig128_params hd2) ?_
      have := congrArg List.length hv
      rw [hs2]
      simpa [AbiParam.tys] using this
    obtain ⟨h1, h2'⟩ := prog_callDT hC ih d hpn hexp
    refine ⟨fun rv m' ho _ => ?_, fun c ho => h2' c ho⟩
    obtain ⟨rv', hrel, ht⟩ := h1 rv m' ho
    obtain ⟨rg, hrg, hR⟩ := groups_plain (sig128_returns hd2)
    rw [hrg, Option.getD_some] at hrel
    rw [← expRel_val hR (sig128_returns hd2) hrel]
    exact ht
  | none =>
    rw [guardEnvD_none hpn] at he
    exact ⟨hs, by rw [tgtEnvD_none (hC.func?_none hpn)]; exact he,
      fun vals m _ => ⟨fun rv m' ho _ => ho, fun c ho => ho⟩⟩

/-- `callIndRel_link` at call depth `d`. -/
theorem callIndRel_linkDT {dsig : Signature} (hd : sig128 dsig = false) :
    CallIndRel (guardEnvD B P (SomeInd (legalProg P)) syms M d) (tgtEnvD B P (legalProg P) d)
      P.bare (legalProg P).bare dsig := by
  intro mem a vals
  have hnames : ((guardEnvD B P (SomeInd (legalProg P)) syms M d).names ++ P.bare.externNames) =
      ((tgtEnvD B P (legalProg P) d).names ++ (legalProg P).bare.externNames) := by
    simp [guardEnvD, tgtEnvD, linkEnvN_names]
  have hfun : ∀ n h2, P.func? n = some h2 →
      ((guardEnvD B P (SomeInd (legalProg P)) syms M d).sigOf n).all dsig.abiMatch = true →
      ((tgtEnvD B P (legalProg P) d).sigOf n).all dsig.abiMatch = true ∧ sig128 h2.sig = false ∧
        AbiParam.tys dsig.params = AbiParam.tys h2.sig.params := by
    intro n h2 hpn hs
    have hs' : dsig.abiMatch h2.sig = true := by
      simpa [guardEnvD, linkEnvN_sigOf, hpn] using hs
    have hm := Signature.abiMatch_eq_true.mp hs'
    have h2p : sig128 h2.sig = false := sig128_of_tys hd hm.1 hm.2.2
    have hl2 : (legalize h2).sig = h2.sig := by
      have := (legalFactsT (hC.ok h2 (Program.func?_some hpn).1)).sig
      rw [Complete.sigExp_plain h2p] at this
      exact (Option.some.inj this).symm
    refine ⟨?_, h2p, hm.1⟩
    simp [tgtEnvD, hC.func?_some hpn, hl2, hs']
  have hexpOf : ∀ n h2, P.func? n = some h2 → sig128 h2.sig = false →
      AbiParam.tys dsig.params = AbiParam.tys h2.sig.params →
      vals.map (·.ty) = AbiParam.tys dsig.params →
      ExpRel ((groups h2.sig.params).getD []) vals vals := by
    intro n h2 _ h2p htp hv
    obtain ⟨gs, hgs, hG⟩ := groups_plain (sig128_params h2p)
    rw [hgs, Option.getD_some]
    refine expRel_refl_plain hG (sig128_params h2p) ?_
    have := congrArg List.length (hv.trans htp)
    simpa [AbiParam.tys] using this
  constructor
  · intro r hr
    obtain ⟨n, g, h1, hg, hs, hv, rv, m', ho, hrt, rfl⟩ := callExternAt_ok_iff.mp hr
    rw [hnames] at h1
    cases hpn : P.func? n with
    | some h2 =>
      rw [guardEnvD_some hpn] at hg
      cases hg
      obtain ⟨hs', h2p, htp⟩ := hfun n h2 hpn hs
      obtain ⟨h1', -⟩ := prog_callDT hC ih d hpn (hexpOf n h2 hpn h2p htp hv)
      obtain ⟨rv', hrel, ht⟩ := h1' rv m' ho
      obtain ⟨rg, hrg, hR⟩ := groups_plain (sig128_returns h2p)
      rw [hrg, Option.getD_some] at hrel
      rw [expRel_val hR (sig128_returns h2p) hrel] at ht
      exact callExternAt_ok_iff.mpr ⟨n, _, h1, tgtEnvD_some (hC.func?_some hpn), hs', hv, rv, m',
        ht, hrt, rfl⟩
    | none =>
      rw [guardEnvD_none hpn] at hg
      have hsN : (tgtEnvD B P (legalProg P) d).sigOf n = none := by
        simp [tgtEnvD, hC.func?_none hpn]
      exact callExternAt_ok_iff.mpr ⟨n, g, h1, by rw [tgtEnvD_none (hC.func?_none hpn)]; exact hg,
        by rw [hsN]; rfl, hv, rv, m', ho, hrt, rfl⟩
  · intro c hr
    obtain ⟨n, g, h1, hg, hs, hv, ho⟩ := callExternAt_trap_iff.mp hr
    rw [hnames] at h1
    cases hpn : P.func? n with
    | some h2 =>
      rw [guardEnvD_some hpn] at hg
      cases hg
      obtain ⟨hs', h2p, htp⟩ := hfun n h2 hpn hs
      obtain ⟨-, h2'⟩ := prog_callDT hC ih d hpn (hexpOf n h2 hpn h2p htp hv)
      exact callExternAt_trap_iff.mpr ⟨n, _, h1, tgtEnvD_some (hC.func?_some hpn), hs', hv,
        h2' c ho⟩
    | none =>
      rw [guardEnvD_none hpn] at hg
      have hsN : (tgtEnvD B P (legalProg P) d).sigOf n = none := by
        simp [tgtEnvD, hC.func?_none hpn]
      exact callExternAt_trap_iff.mpr ⟨n, g, h1, by rw [tgtEnvD_none (hC.func?_none hpn)]; exact hg,
        by rw [hsN]; rfl, hv, ho⟩

end Induction

/-- **The refinement of one activation at fuel `M + 1` and call depth `d`** (`root_refines` with
the call depth): the callees related at fuel `M` and every depth (`RefinesD`). -/
theorem root_refinesDT {P : Program} {B : Env} {syms : String → Option Nat}
    (hC : ProgCtxT P B syms) {M : Nat} (ih : RefinesD B P syms M) (d : Nat) {h : Function}
    (hh : h ∈ P.funcs) {args args' : List Val} {fr fr' : Frame} {m1 : Mem}
    (hE : EntryRel h args args' fr fr')
    (hG : GoodFrom B P (SomeInd (legalProg P)) syms ⟨fr, [], m1⟩)
    (hd : DepthLe B P d ⟨fr, [], m1⟩) :
    (∀ rv m2, Clif.runLoop B P (M + 1) ⟨fr, [], m1⟩ = .returned rv m2 →
      ∃ rv', ExpRel ((groups h.sig.returns).getD []) rv rv' ∧
        (∃ k, Clif.runLoop B (legalProg P) k ⟨fr', [], m1⟩ = .returned rv' m2) ∧
        DepthLe B (legalProg P) d ⟨fr', [], m1⟩) ∧
    (∀ c, Clif.runLoop B P (M + 1) ⟨fr, [], m1⟩ = .trapped c →
      (∃ k, Clif.runLoop B (legalProg P) k ⟨fr', [], m1⟩ = .trapped c) ∧
        DepthLe B (legalProg P) d ⟨fr', [], m1⟩) := by
  have hF := hC.facts
  have hF' := hC.facts'
  have hhP' : legalize h ∈ (legalProg P).funcs := List.mem_map_of_mem hh
  have hio : ¬ IndFree h → SomeInd (legalProg P) := fun hn => hC.someInd hh hn
  have hLe : LInv P ⟨fr, [], m1⟩ := ⟨hE.lframe hh, fun _ h => nomatch h⟩
  have hLeh : LInv (P.only h) ⟨fr, [], m1⟩ :=
    ⟨hE.lframe (by simp [Program.only]), fun _ h => nomatch h⟩
  have hsym : ¬ IndFree h → m1.symbols = syms := fun hn => (hG _ (.refl _)).2.2 (hio hn)
  have hUI : UInv P h syms ⟨fr, [], m1⟩ := ⟨rfl, hLeh.1, hsym⟩
  have hioE : ¬ IndFree h → UnlinkInd (linkEnvN P B M) P B syms := fun hn =>
    unlinkInd_linked (hC.indSrc (hio hn)) (hC.ind (hio hn)).2 rfl
  have hioG : ¬ IndFree h →
      UnlinkInd (guardEnvD B P (SomeInd (legalProg P)) syms M d) P B syms := fun hn =>
    unlinkInd_linked (hC.indSrc (hio hn)) (hC.ind (hio hn)).2 rfl
  -- the source run is a per-function run under the guarded linked environment
  have hlink : ∀ o, Clif.runLoop B P (M + 1) ⟨fr, [], m1⟩ = o → (∀ msg, o ≠ .stuck msg) →
      o ≠ .outOfFuel → ∃ n, Clif.runLoop (linkEnvN P B M) P.bare n ⟨fr, [], m1⟩ = o := by
    intro o ho hs hof
    obtain ⟨n, hn⟩ := runLoop_linkN (P := P) (base := B) (f := h) (syms := syms) M hC.nd hh
      hC.free (fun hn => hC.indSrc (hio hn)) (E := linkEnvN P B M) rfl rfl (fun _ _ => rfl)
      (fun _ _ _ => rfl) (M + 1) ⟨fr, [], m1⟩ (Nat.le_refl _) hLe hLeh hsym
      (by rw [ho]; exact hs) (by rw [ho]; exact hof)
    exact ⟨n, hn.trans ho⟩
  have hguard := guard_runD (G := SomeInd (legalProg P)) hF M d hh hioE
  -- the target's per-function run is a whole-program run of call depth at most `d`
  have hUIt : UInv (legalProg P) (legalize h) syms ⟨fr', [], m1⟩ :=
    ⟨rfl, hE.lframe' (by simp [Program.only]), fun hn => (hG _ (.refl _)).2.2 ⟨_, hhP', hn⟩⟩
  have hioT : ¬ IndFree (legalize h) →
      UnlinkInd (tgtEnvD B P (legalProg P) d) (legalProg P) B syms :=
    fun hn => unlinkInd_tgtD (hC.ind ⟨_, hhP', hn⟩).1 (hC.ind ⟨_, hhP', hn⟩).2 hC.names
      (fun _ h => hC.externNames h)
  have hwhole := fun n =>
    unlink_run (unlink_tgtD (B := B) (P := P) (d := d) hF') hhP' hioT (n := n) hUIt
  have hdepth := fun n => unlink_depth (unlink_tgtD (B := B) (P := P) (d := d) hF')
    (unlinkD_tgtD hF') hhP' hioT n _ hUIt
  -- the per-activation refinement under the two environments
  have hact : (∀ n rv m2, Clif.runLoop (guardEnvD B P (SomeInd (legalProg P)) syms M d) P.bare n
        ⟨fr, [], m1⟩ = .returned rv m2 → rv.map (·.ty) = AbiParam.tys h.sig.returns →
        ∃ rv', ExpRel ((groups h.sig.returns).getD []) rv rv' ∧
          ∃ k, Clif.runLoop (tgtEnvD B P (legalProg P) d) (legalProg P).bare k ⟨fr', [], m1⟩ =
            .returned rv' m2) ∧
      (∀ n c, Clif.runLoop (guardEnvD B P (SomeInd (legalProg P)) syms M d) P.bare n
        ⟨fr, [], m1⟩ = .trapped c →
        ∃ k, Clif.runLoop (tgtEnvD B P (legalProg P) d) (legalProg P).bare k ⟨fr', [], m1⟩ =
          .trapped c) := by
    obtain ⟨b, hb, h2, h3, h4, h5⟩ := hE.entry
    obtain ⟨b', hb', h2', h3', h5'⟩ := hE.entry'
    rcases Complete.legalOkTB_cases (hC.ok h hh) with ⟨hm, -, hl⟩ | ⟨hp, hTB, cert, hc⟩
    · -- the identity: the same code, related environments
      obtain ⟨hs, hes, hds⟩ := not_mentions hm
      obtain ⟨gs, hgs, hGs⟩ := groups_plain (sig128_params hs)
      have hexp := hE.exp
      rw [hgs, Option.getD_some] at hexp
      have hvv : args' = args := expRel_val hGs (sig128_params hs) hexp
      have hfe : fr' = fr := by
        rw [hl] at hb'
        rw [hb] at hb'
        cases hb'
        obtain ⟨func, regs, slots, body, term⟩ := fr
        obtain ⟨func', regs', slots', body', term'⟩ := fr'
        have e1 : func' = func := by
          have := hE.func'; have := hE.func; simp_all
        simp only at h2 h3 h5 h2' h3' h5' e1
        rw [hvv, h5] at h5'
        cases h5'
        have e2 := hE.slots
        simp only at e2
        subst e1 e2
        rw [h2, h2', h3, h3']
      subst hfe
      have hrun := ident_run (E := guardEnvD B P (SomeInd (legalProg P)) syms M d)
        (E' := tgtEnvD B P (legalProg P) d) (P := P) (P' := legalProg P) (f := h)
        (fun fn ex hfe => sameAt_linkDT hC ih d (by
          obtain ⟨fn', hmem⟩ := lookup_mem hfe
          exact hes _ hmem) (fun h2 hpn => hC.decl h hh fn ex hfe h2 hpn))
        (fun i dsig hd => callIndRel_linkDT hC ih d (by
          obtain ⟨i', hmem⟩ := lookup_mem hd
          exact hds _ hmem))
        (hC.free h hh)
      refine ⟨fun n rv m2 hr hty => ⟨rv, ?_, n, (hrun n _ rfl hLeh.1).1 rv m2 hr⟩,
        fun n c hr => ⟨n, (hrun n _ rfl hLeh.1).2 c hr⟩⟩
      obtain ⟨rg, hrg, hR⟩ := groups_plain (sig128_returns hs)
      rw [hrg, Option.getD_some]
      refine expRel_refl_plain hR (sig128_returns hs) ?_
      have := congrArg List.length hty
      simpa [AbiParam.tys] using this
    · -- a legalisation: `legalize_refines2W` with the two environments
      have hbase := hC.base ⟨h, hh, hp.mentions⟩
      have hE2 : EnvOk2 (guardEnvD B P (SomeInd (legalProg P)) syms M d)
          (tgtEnvD B P (legalProg P) d) ⟨h, legalize h, cert⟩ P.bare (legalProg P).bare :=
        { src := fun _ _ _ => rfl
          tgt := fun _ _ _ => rfl
          helper := fun op => by
            obtain ⟨hf, hB, hsem⟩ := hbase.1 op
            exact ⟨hf, by rw [tgtEnvD_none (hC.func?_none (hC.helpers op))]; exact hB, hsem⟩
          ext := fun fn ex hfe => by
            cases hpn : P.func? ex.name with
            | some h2 => exact extRel_progDT hC ih d hpn (hC.decl h hh fn ex hfe h2 hpn)
            | none =>
              intro hs he
              rw [guardEnvD_none hpn] at he
              obtain ⟨h', hb', hrel⟩ := hbase.2.1.at ex.name ex.sig hs he
              exact ⟨h', by rw [tgtEnvD_none (hC.func?_none hpn)]; exact hb', hrel⟩
          keep := keep_guardD hF hbase.2.2
          ind := fun _ => ⟨rfl, fun sig dsig hs hd =>
            have hd128 := Complete.indTB_indSite hTB hs hd
            callIndRel2_of_plain hd128 (callIndRel_linkDT hC ih d hd128)⟩ }
      have hT := noMemTrap_guardD hF M d hh hioG hUI hG
      have hI : NoIndInternal (guardEnvD B P (SomeInd (legalProg P)) syms M d) P.bare h
          ⟨fr, [], m1⟩ := fun _ _ => ⟨(fun _ _ _ _ _ _ _ _ _ _ g hg => nomatch hg),
            (fun _ _ _ _ _ _ _ _ g hg => nomatch hg)⟩
      have href := fun n => legalize_refines2W hp hc hE2 hb hb' hE.func h2 h3 h4 h5 hE.func' h2'
        h3' h5' hE.slots hE.exp (hG _ (.refl _)).1 hT hI n
      exact ⟨fun n rv m2 hr _ => (href n).1 rv m2 hr, fun n c hr => (href n).2 c hr⟩
  refine ⟨fun rv m2 hr => ?_, fun c hr => ?_⟩
  · obtain ⟨n, hn⟩ := hlink _ hr (fun _ h => by cases h) (fun h => by cases h)
    have hn'' := (hguard n _ hUI hG hd).1 rv m2 hn
    have hty : rv.map (·.ty) = AbiParam.tys h.sig.returns := by
      have := runLoop_returned_tys hC.free (M + 1) _ rv m2 hLe hr
      simpa [State.bottom, hE.func] using this
    obtain ⟨rv', hrel, k, hk⟩ := hact.1 n rv m2 hn'' hty
    obtain ⟨k', hk'⟩ := (hwhole k).1 rv' m2 hk
    exact ⟨rv', hrel, ⟨k', hk'⟩, hdepth k (.inl ⟨rv', m2, hk⟩)⟩
  · obtain ⟨n, hn⟩ := hlink _ hr (fun _ h => by cases h) (fun h => by cases h)
    have hn'' := (hguard n _ hUI hG hd).2 c hn
    obtain ⟨k, hk⟩ := hact.2 n c hn''
    exact ⟨(hwhole k).2 c hk, hdepth k (.inr ⟨c, hk⟩)⟩

/-- **The callees are related at every fuel and call depth** (by induction on the fuel). -/
theorem prog_refinesDT {P : Program} {B : Env} {syms : String → Option Nat}
    (hC : ProgCtxT P B syms) : ∀ M, RefinesD B P syms M := by
  intro M
  induction M with
  | zero =>
    intro _ h _ vals vals' m fr m1 fr' _ _ _ _ _
    exact ⟨fun _ _ h => by simp at h, fun _ h => by simp at h⟩
  | succ M ih =>
    intro d h hh vals vals' m fr m1 fr' hent hent' hexp hG hd
    have hfacts := legalFactsT (hC.ok h hh)
    exact root_refinesDT hC ih d hh
      (EntryRel.of_enter ⟨hfacts.name, hfacts.slots⟩ hent hent' hexp) hG hd

/-- **Whole-program refinement of the original program keeping the call depth** (S3, L1d):
`legalProg_refines`, and if the source run from `h`'s entry has call depth at most `d`
(`Clif.DepthLe`: no state it reaches has more than `d` callers), so has the legalised program's
run from the entry with the ABI-split arguments. -/
theorem legalProg_refines_depthT {P : Program} {B : Env} {syms : String → Option Nat}
    (hC : ProgCtxT P B syms) {h : Function} (hh : h ∈ P.funcs) {args args' : List Val}
    {fr fr' : Frame} {m1 : Mem} (hE : EntryRel h args args' fr fr')
    (hG : GoodFrom B P (SomeInd (legalProg P)) syms ⟨fr, [], m1⟩) {d : Nat}
    (hd : DepthLe B P d ⟨fr, [], m1⟩) (M : Nat) :
    (∀ rv m2, Clif.runLoop B P M ⟨fr, [], m1⟩ = .returned rv m2 →
      ∃ rv', ExpRel ((groups h.sig.returns).getD []) rv rv' ∧
        (∃ k, Clif.runLoop B (legalProg P) k ⟨fr', [], m1⟩ = .returned rv' m2) ∧
        DepthLe B (legalProg P) d ⟨fr', [], m1⟩) ∧
    (∀ c, Clif.runLoop B P M ⟨fr, [], m1⟩ = .trapped c →
      (∃ k, Clif.runLoop B (legalProg P) k ⟨fr', [], m1⟩ = .trapped c) ∧
        DepthLe B (legalProg P) d ⟨fr', [], m1⟩) := by
  cases M with
  | zero => exact ⟨fun _ _ h => by simp at h, fun _ h => by simp at h⟩
  | succ M => exact root_refinesDT hC (prog_refinesDT hC M) d hh hE hG hd

end E2E.LegalProgram
