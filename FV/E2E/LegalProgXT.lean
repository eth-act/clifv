import FV.E2E.LegalProgX
import FV.E2E.LegalProgramT
import FV.Opt.Proof.LegalSimX2T

/-!
# Whole-program refinement with unwinding, `try_call_indirect` included (#1076)

`legalProg_refinesXT`: `legalProg_refinesX` (`FV/E2E/LegalProgX.lean`) on the source domain with
unwinding `ProgCtxXT`: `ProgCtxT` (every function in `legalOkTB`, `FV/E2E/LegalProgramT.lean`),
the unwinding contracts of `ProgCtxX`, and the handler-edge check `exnOkT` (`try_call_indirect`
included) of every legalisation. The proof is the old one with each legalised activation by
`Opt.Legal.X.checkW_refinesX2T` (the environments' new clause `indXT` at `try_call_indirect`
sites from `callIndRelX_linkT`, the call-site signatures `i128`-free by `indTB`).
-/

namespace E2E.LegalProgram

open Clif Opt.Legal Opt.Legal.X Opt.Legalize128

/-! ## The source domain with unwinding, `try_call_indirect` included -/

/-- **The source domain of a program `P` with unwinding, `try_call_indirect` included** over the base environment `B`: `ProgCtxT` of `B` without unwinding; where a function mentions `i128`, `B`'s contracts for its
unwinding externs (`ExtLegalX`: an extern unwinds alike on the split arguments;
`EnvKeepsAllocsX`; `ExnArityOk`); where the legalised program has indirect calls, `IndScopeX`
(the externs keep the symbols when they unwind too); and the handler-edge check `exnOkT`
(`try_call_indirect` included) of every legalisation. `ProgCtxX` with `ProgCtxT`. -/
structure ProgCtxXT (P : Program) (B : XEnv) (syms : String → Option Nat) : Prop where
  ctx : ProgCtxT P B.toEnv syms
  baseX : (∃ f ∈ P.funcs, mentions128 f = true) →
    ExtLegalX B ∧ EnvKeepsAllocsX B ∧ ExnArityOk B
  indX : SomeInd (legalProg P) → IndScopeX (legalProg P) B syms
  exn : ∀ f ∈ P.funcs, mentions128 f = true → ∀ g cert, function128Cert f = .ok (g, cert) →
    exnOkT f g cert = true


namespace ProgCtxXT

variable {P : Program} {B : XEnv} {syms : String → Option Nat} (hC : ProgCtxXT P B syms)
include hC

theorem indSrcX (hI : SomeInd (legalProg P)) : UnlinkIndX P B syms :=
  ⟨indScopeX_src (hC.indX hI) hC.ctx.names (fun _ h => hC.ctx.externNames h)
    (fun _ h => hC.ctx.func?_none h), (hC.ctx.ind hI).2⟩

theorem indTgtX (hI : SomeInd (legalProg P)) : UnlinkIndX (legalProg P) B syms :=
  ⟨hC.indX hI, (hC.ctx.ind hI).2⟩

end ProgCtxXT

/-! ## The induction -/

section Induction

variable {P : Program} {B : XEnv} {syms : String → Option Nat} (hC : ProgCtxXT P B syms)
  {M : Nat} (ih : RefinesX B P syms M)
include hC ih

/-- A callee run of the guarded environment and the target's: related by the induction
hypothesis. -/
theorem prog_callXT {n : String} {h2 : Function} (hp : P.func? n = some h2)
    {vals vals' : List Val} {m : Mem}
    (hexp : ExpRel ((groups h2.sig.params).getD []) vals vals') :
    (∀ rv m', guardFunX B P (SomeInd (legalProg P)) syms M n vals m = .returned rv m' →
      ∃ rv', ExpRel ((groups h2.sig.returns).getD []) rv rv' ∧
        tgtFunX B (legalProg P) n vals' m = .returned rv' m') ∧
    (∀ c, guardFunX B P (SomeInd (legalProg P)) syms M n vals m = .trapped c →
      tgtFunX B (legalProg P) n vals' m = .trapped c) ∧
    (∀ e m', guardFunX B P (SomeInd (legalProg P)) syms M n vals m = .unwound e m' →
      tgtFunX B (legalProg P) n vals' m = .unwound e m') := by
  obtain ⟨hh2, rfl⟩ := Program.func?_some hp
  have hp' := hC.ctx.func?_some hp
  have key : ∀ o, guardFunX B P (SomeInd (legalProg P)) syms M h2.name vals m = o →
      (∀ msg, o ≠ .stuck msg) → ∃ fr m1 fr', enterFunc h2 vals m = .ok (fr, m1) ∧
        enterFunc (legalize h2) vals' m = .ok (fr', m1) ∧
        GoodFromX B P (SomeInd (legalProg P)) syms ⟨⟨fr, [], m1⟩, []⟩ ∧
        runLoopX B P M ⟨⟨fr, [], m1⟩, []⟩ = o := by
    intro o ho hs
    unfold guardFunX at ho
    cases hi : initState P h2.name vals m with
    | ok s =>
      obtain ⟨fr, m1, he, rfl⟩ := (initState_ok_iff hp).mp hi
      obtain ⟨fr', he'⟩ := enterFunc_legalT (hC.ctx.ok h2 hh2) he hexp
      simp only [hi] at ho
      by_cases hgd : GoodFromX B P (SomeInd (legalProg P)) syms (State.toX ⟨fr, [], m1⟩)
      · simp only [guardRX, hgd, ↓reduceIte] at ho; exact ⟨fr, m1, fr', he, he', hgd, ho⟩
      · simp only [guardRX, hgd, ↓reduceIte] at ho; exact absurd ho.symm (hs _)
    | trap c => exact absurd hi (initState_not_trap P h2.name vals m c)
    | stuck msg => rw [hi] at ho; exact absurd ho.symm (hs msg)
  have tgt : ∀ fr' m1 o k, enterFunc (legalize h2) vals' m = .ok (fr', m1) →
      runLoopX B (legalProg P) k ⟨⟨fr', [], m1⟩, []⟩ = o → o ≠ .outOfFuel →
      tgtFunX B (legalProg P) h2.name vals' m = o := by
    intro fr' m1 o k he' hr ho
    unfold tgtFunX
    rw [(initState_ok_iff hp').mpr ⟨fr', m1, he', rfl⟩]
    show runLimX B (legalProg P) ⟨⟨fr', [], m1⟩, []⟩ = o
    rw [runLimX_eq (by rw [hr]; exact ho), hr]
  refine ⟨fun rv m' ho => ?_, fun c ho => ?_, fun e m' ho => ?_⟩
  · obtain ⟨fr, m1, fr', he, he', hG, hr⟩ := key _ ho (fun _ h => by cases h)
    obtain ⟨rv', hrel, k, hk⟩ := (ih h2 hh2 vals vals' m fr m1 fr' he he' hexp hG).1 rv m' hr
    exact ⟨rv', hrel, tgt fr' m1 _ k he' hk (fun h => by cases h)⟩
  · obtain ⟨fr, m1, fr', he, he', hG, hr⟩ := key _ ho (fun _ h => by cases h)
    obtain ⟨k, hk⟩ := (ih h2 hh2 vals vals' m fr m1 fr' he he' hexp hG).2.1 c hr
    exact tgt fr' m1 _ k he' hk (fun h => by cases h)
  · obtain ⟨fr, m1, fr', he, he', hG, hr⟩ := key _ ho (fun _ h => by cases h)
    obtain ⟨k, hk⟩ := (ih h2 hh2 vals vals' m fr m1 fr' he he' hexp hG).2.2 e m' hr
    exact tgt fr' m1 _ k he' hk (fun h => by cases h)

/-- At the declaration `n` of a function of `P` (with its signature): the environments without
unwinding are related (`ExtRelAt`), and an exception is raised alike (`ExtRaiseRel`). -/
theorem extRel_progXT {n : String} {h2 : Function} (hp : P.func? n = some h2) {sig : Signature}
    (hsig : h2.sig = sig) :
    ExtRelAt (guardEnvX B P (SomeInd (legalProg P)) syms M).toEnv
      (tgtEnvX B P (legalProg P)).toEnv n sig ∧
    ExtRaiseRel (guardEnvX B P (SomeInd (legalProg P)) syms M) (tgtEnvX B P (legalProg P)) n sig := by
  have hgs := guardEnvX_some (B := B) (G := SomeInd (legalProg P)) (syms := syms) (M := M) hp
  have hts := tgtEnvX_some (B := B) (P := P) (hC.ctx.func?_some hp)
  constructor
  · intro hs he
    rw [toEnv_extern_some hgs] at he
    cases he
    refine ⟨_, toEnv_extern_some hts, fun gs rg hgs' hrg vals vals' m hty hexp => ?_⟩
    have hexp' : ExpRel ((groups h2.sig.params).getD []) vals vals' := by
      rw [hsig, hgs']; exact hexp
    obtain ⟨h1, h2', -⟩ := prog_callXT hC ih hp hexp'
    refine ⟨fun rv m' ho _ => ?_, fun c ho => ?_⟩
    · obtain ⟨rv', hrel, ht⟩ := h1 rv m' (toOutcome_returned ho)
      refine ⟨rv', by simp only [ht, XOutcome.toOutcome], ?_⟩
      rw [hsig, hrg] at hrel
      exact hrel
    · simp only [h2' c (toOutcome_trapped ho), XOutcome.toOutcome]
  · intro hs he
    rw [hgs] at he
    cases he
    refine ⟨_, hts, fun gs hgs' vals vals' m hty hexp e m' ho => ?_⟩
    have hexp' : ExpRel ((groups h2.sig.params).getD []) vals vals' := by
      rw [hsig, hgs']; exact hexp
    exact (prog_callXT hC ih hp hexp').2.2 e m' ho

/-- At a declaration without `i128` (of a function of `P`, with its signature, or of `B`), the
two environments end alike. -/
theorem sameAtX_linkT {n : String} {sig : Signature} (hd : sig128 sig = false)
    (hdecl : ∀ h2, P.func? n = some h2 → h2.sig = sig) :
    SameAtX (guardEnvX B P (SomeInd (legalProg P)) syms M) (tgtEnvX B P (legalProg P)) n sig := by
  intro hs he
  cases hpn : P.func? n with
  | some h2 =>
    rw [guardEnvX_some hpn] at he
    cases he
    have hs2 := hdecl h2 hpn
    have hd2 : sig128 h2.sig = false := by rw [hs2]; exact hd
    refine ⟨_, tgtEnvX_some (hC.ctx.func?_some hpn), fun vals m hv => ?_⟩
    obtain ⟨gs, hgs, hG⟩ := groups_plain (sig128_params hd2)
    have hexp : ExpRel ((groups h2.sig.params).getD []) vals vals := by
      rw [hgs, Option.getD_some]
      refine expRel_refl_plain hG (sig128_params hd2) ?_
      have := congrArg List.length hv
      rw [hs2]
      simpa [AbiParam.tys] using this
    obtain ⟨h1, h2', h3⟩ := prog_callXT hC ih hpn hexp
    refine ⟨fun rv m' ho _ => ?_, fun c ho => h2' c ho, fun e m' ho => h3 e m' ho⟩
    obtain ⟨rv', hrel, ht⟩ := h1 rv m' ho
    obtain ⟨rg, hrg, hR⟩ := groups_plain (sig128_returns hd2)
    rw [hrg, Option.getD_some] at hrel
    rw [← expRel_val hR (sig128_returns hd2) hrel]
    exact ht
  | none =>
    rw [guardEnvX_none hpn] at he
    exact ⟨hs, by rw [tgtEnvX_none (hC.ctx.func?_none hpn)]; exact he,
      fun vals m _ => ⟨fun rv m' ho _ => ho, fun c ho => ho, fun e m' ho => ho⟩⟩

/-- An indirect call with a call-site signature without `i128`: the two environments resolve the
address to the same name and end alike. -/
theorem callIndRelX_linkT {d : Signature} (hd : sig128 d = false) :
    CallIndRelX (guardEnvX B P (SomeInd (legalProg P)) syms M) (tgtEnvX B P (legalProg P))
      P.bare (legalProg P).bare d := by
  have hnames : (guardEnvX B P (SomeInd (legalProg P)) syms M).names =
      (tgtEnvX B P (legalProg P)).names := rfl
  -- a function of `P` reached with a signature without `i128` has none either
  have hfun : ∀ n h2, P.func? n = some h2 →
      ((guardEnvX B P (SomeInd (legalProg P)) syms M).sigOf n).all d.abiMatch = true →
      ((tgtEnvX B P (legalProg P)).sigOf n).all d.abiMatch = true ∧ sig128 h2.sig = false ∧
        AbiParam.tys d.params = AbiParam.tys h2.sig.params := by
    intro n h2 hpn hs
    have hs' : d.abiMatch h2.sig = true := by
      simpa [guardEnvX, hpn] using hs
    have hm := Signature.abiMatch_eq_true.mp hs'
    have h2p : sig128 h2.sig = false := sig128_of_tys hd hm.1 hm.2.2
    have hl2 : (legalize h2).sig = h2.sig := by
      have := (legalFactsT (hC.ctx.ok h2 (Program.func?_some hpn).1)).sig
      rw [Complete.sigExp_plain h2p] at this
      exact (Option.some.inj this).symm
    refine ⟨?_, h2p, hm.1⟩
    simp [tgtEnvX, hC.ctx.func?_some hpn, hl2, hs']
  have hexpOf : ∀ vals n h2, P.func? n = some h2 → sig128 h2.sig = false →
      AbiParam.tys d.params = AbiParam.tys h2.sig.params →
      vals.map (·.ty) = AbiParam.tys d.params → ExpRel ((groups h2.sig.params).getD []) vals vals := by
    intro vals n h2 _ h2p htp hv
    obtain ⟨gs, hgs, hG⟩ := groups_plain (sig128_params h2p)
    rw [hgs, Option.getD_some]
    refine expRel_refl_plain hG (sig128_params h2p) ?_
    have := congrArg List.length (hv.trans htp)
    simpa [AbiParam.tys] using this
  have hsN : ∀ n, P.func? n = none → (tgtEnvX B P (legalProg P)).sigOf n = none := fun n hpn => by
    simp [tgtEnvX, hC.ctx.func?_none hpn]
  have hsNg : ∀ n, P.func? n = none →
      (guardEnvX B P (SomeInd (legalProg P)) syms M).sigOf n = none := fun n hpn => by
    simp [guardEnvX, hpn]
  refine ⟨fun mem a vals => ⟨fun r hr => ?_, fun c hr => ?_⟩, fun mem a vals r hr => ?_⟩
  · obtain ⟨n, g, h1, hg, hs, hv, rv, m', ho, hrt, rfl⟩ := callExternAt_ok_iff.mp hr
    have h1' : ((tgtEnvX B P (legalProg P)).toEnv.names ++ (legalProg P).bare.externNames).find?
        (fun n => mem.symbols n == some a) = some n := h1
    cases hpn : P.func? n with
    | some h2 =>
      obtain ⟨gx, hgx, rfl⟩ := toEnv_extern_some_inv hg
      rw [guardEnvX_some hpn] at hgx
      cases hgx
      obtain ⟨hs', h2p, htp⟩ := hfun n h2 hpn hs
      obtain ⟨h1'', -, -⟩ := prog_callXT hC ih hpn (hexpOf vals n h2 hpn h2p htp hv)
      obtain ⟨rv', hrel, ht⟩ := h1'' rv m' (toOutcome_returned ho)
      obtain ⟨rg, hrg, hR⟩ := groups_plain (sig128_returns h2p)
      rw [hrg, Option.getD_some] at hrel
      rw [expRel_val hR (sig128_returns h2p) hrel] at ht
      exact callExternAt_ok_iff.mpr ⟨n, _, h1', toEnv_extern_some (tgtEnvX_some
        (hC.ctx.func?_some hpn)), hs', hv, rv, m', by simp [ht, XOutcome.toOutcome], hrt, rfl⟩
    | none =>
      have hgE : (tgtEnvX B P (legalProg P)).toEnv.extern n =
          (guardEnvX B P (SomeInd (legalProg P)) syms M).toEnv.extern n := by
        simp only [XEnv.toEnv, tgtEnvX_none (hC.ctx.func?_none hpn), guardEnvX_none hpn]
      exact callExternAt_ok_iff.mpr ⟨n, g, h1', by rw [hgE]; exact hg,
        by simp [XEnv.toEnv, hsN n hpn], hv, rv, m', ho, hrt, rfl⟩
  · obtain ⟨n, g, h1, hg, hs, hv, ho⟩ := callExternAt_trap_iff.mp hr
    have h1' : ((tgtEnvX B P (legalProg P)).toEnv.names ++ (legalProg P).bare.externNames).find?
        (fun n => mem.symbols n == some a) = some n := h1
    cases hpn : P.func? n with
    | some h2 =>
      obtain ⟨gx, hgx, rfl⟩ := toEnv_extern_some_inv hg
      rw [guardEnvX_some hpn] at hgx
      cases hgx
      obtain ⟨hs', h2p, htp⟩ := hfun n h2 hpn hs
      obtain ⟨-, h2', -⟩ := prog_callXT hC ih hpn (hexpOf vals n h2 hpn h2p htp hv)
      exact callExternAt_trap_iff.mpr ⟨n, _, h1', toEnv_extern_some (tgtEnvX_some
        (hC.ctx.func?_some hpn)), hs', hv, by rw [h2' c (toOutcome_trapped ho)]; rfl⟩
    | none =>
      have hgE : (tgtEnvX B P (legalProg P)).toEnv.extern n =
          (guardEnvX B P (SomeInd (legalProg P)) syms M).toEnv.extern n := by
        simp only [XEnv.toEnv, tgtEnvX_none (hC.ctx.func?_none hpn), guardEnvX_none hpn]
      exact callExternAt_trap_iff.mpr ⟨n, g, h1', by rw [hgE]; exact hg,
        by simp [XEnv.toEnv, hsN n hpn], hv, ho⟩
  · unfold externAtRaise at hr ⊢
    simp only [Program.bare_externNames, List.append_nil] at hr ⊢
    rw [← hnames]
    cases hf : (guardEnvX B P (SomeInd (legalProg P)) syms M).names.find?
        (fun n => mem.symbols n == some a) with
    | none => rw [hf] at hr; cases hr
    | some n =>
      rw [hf] at hr
      dsimp only at hr ⊢
      cases hpn : P.func? n with
      | some h2 =>
        rw [guardEnvX_some hpn] at hr
        rw [tgtEnvX_some (hC.ctx.func?_some hpn)]
        dsimp only at hr ⊢
        split at hr
        · rename_i hck
          simp only [Bool.and_eq_true, beq_iff_eq] at hck
          obtain ⟨hs', h2p, htp⟩ := hfun n h2 hpn hck.1
          simp only [hs', hck.2, beq_self_eq_true, Bool.and_self, ↓reduceIte]
          cases ho : guardFunX B P (SomeInd (legalProg P)) syms M n vals mem with
          | unwound e m' =>
            rw [ho] at hr
            rw [(prog_callXT hC ih hpn (hexpOf vals n h2 hpn h2p htp hck.2)).2.2 e m' ho]
            exact hr
          | _ => rw [ho] at hr; cases hr
        · cases hr
      | none =>
        rw [guardEnvX_none hpn] at hr
        rw [tgtEnvX_none (hC.ctx.func?_none hpn), hsN n hpn]
        rw [hsNg n hpn] at hr
        exact hr

end Induction

/-! ## Entries and the refinement -/

/-- **The refinement of one activation with unwinding at fuel `M + 1`** from entry frames
(`EntryRel`), the callees related at fuel `M` (`RefinesX`). -/
theorem root_refinesXT {P : Program} {B : XEnv} {syms : String → Option Nat}
    (hC : ProgCtxXT P B syms) {M : Nat} (ih : RefinesX B P syms M) {h : Function} (hh : h ∈ P.funcs)
    {args args' : List Val} {fr fr' : Frame} {m1 : Mem} (hE : EntryRel h args args' fr fr')
    (hG : GoodFromX B P (SomeInd (legalProg P)) syms ⟨⟨fr, [], m1⟩, []⟩) :
    (∀ rv m2, runLoopX B P (M + 1) ⟨⟨fr, [], m1⟩, []⟩ = .returned rv m2 →
      ∃ rv', ExpRel ((groups h.sig.returns).getD []) rv rv' ∧
        ∃ k, runLoopX B (legalProg P) k ⟨⟨fr', [], m1⟩, []⟩ = .returned rv' m2) ∧
    (∀ c, runLoopX B P (M + 1) ⟨⟨fr, [], m1⟩, []⟩ = .trapped c →
      ∃ k, runLoopX B (legalProg P) k ⟨⟨fr', [], m1⟩, []⟩ = .trapped c) ∧
    (∀ e m2, runLoopX B P (M + 1) ⟨⟨fr, [], m1⟩, []⟩ = .unwound e m2 →
      ∃ k, runLoopX B (legalProg P) k ⟨⟨fr', [], m1⟩, []⟩ = .unwound e m2) := by
  have hF := hC.ctx.facts
  have hF' := hC.ctx.facts'
  have hhP' : legalize h ∈ (legalProg P).funcs := List.mem_map_of_mem hh
  have hio : ¬ IndFree h → SomeInd (legalProg P) := fun hn => hC.ctx.someInd hh hn
  have hLeh : LFrame (P.only h) fr := hE.lframe (by simp [Program.only])
  have hsym : ¬ IndFree h → m1.symbols = syms := fun hn => (hG _ (.refl _)).2.2 (hio hn)
  have hUI : UInv P h syms ⟨fr, [], m1⟩ := ⟨rfl, hLeh, hsym⟩
  have hioS : ¬ IndFree h → UnlinkIndX P B syms := fun hn => hC.indSrcX (hio hn)
  have hXI : XInv P ⟨⟨fr, [], m1⟩, []⟩ := ⟨⟨hE.lframe hh, fun _ h => nomatch h⟩, rfl⟩
  -- the source run is a per-function run under the guarded environment
  have hlink : ∀ o, runLoopX B P (M + 1) ⟨⟨fr, [], m1⟩, []⟩ = o → (∀ msg, o ≠ .stuck msg) →
      o ≠ .outOfFuel → ∃ n, runLoopX (guardEnvX B P (SomeInd (legalProg P)) syms M) P.bare n
        ⟨⟨fr, [], m1⟩, []⟩ = o := by
    intro o ho hs hof
    obtain ⟨n, hn⟩ := runLoopX_linkR (P := P) (env := B) (f := h) (syms := syms)
      (guardRX B P (SomeInd (legalProg P)) syms M) M ⟨⟨fr, [], m1⟩, []⟩ hF.nd hh hF.free
      (fun hn => (hioS hn).scope) (E := guardEnvX B P (SomeInd (legalProg P)) syms M) rfl rfl
      (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun t0 K T n hK hI0 hr hn _ hof' => by
        have hg := hG.callee hF.free hI0 hr
        simp only [guardRX, hg, ↓reduceIte]
        have := runLoopX_add B P n t0.toX hof' (M - n)
        rwa [Nat.add_sub_cancel' hn] at this)
      (M + 1) _ (Nat.le_refl _) (.refl _) hXI ⟨hLeh, fun _ h => nomatch h⟩ hsym
      (by rw [ho]; exact hs) (by rw [ho]; exact hof)
    exact ⟨n, hn.trans ho⟩
  -- the target's per-function run is a whole-program run
  have hUt := unlinkX_tgt (B := B) hF' hC.ctx.names (fun _ h => hC.ctx.externNames h)
  have hUIt : UInv (legalProg P) (legalize h) syms ⟨fr', [], m1⟩ :=
    ⟨rfl, hE.lframe' (by simp [Program.only]), fun hn => (hG _ (.refl _)).2.2 ⟨_, hhP', hn⟩⟩
  have hioT : ¬ IndFree (legalize h) → UnlinkIndX (legalProg P) B syms :=
    fun hn => hC.indTgtX ⟨_, hhP', hn⟩
  have hwhole : ∀ k o, runLoopX (tgtEnvX B P (legalProg P)) (legalProg P).bare k
      ⟨⟨fr', [], m1⟩, []⟩ = o → (∀ msg, o ≠ .stuck msg) → o ≠ .outOfFuel →
      ∃ k', runLoopX B (legalProg P) k' ⟨⟨fr', [], m1⟩, []⟩ = o :=
    fun k o hk hs hof => unlinkX_run hUt hhP' hioT k _ hUIt o hk hs hof
  -- the per-activation refinement under the two environments
  have hact : (∀ n rv m2, runLoopX (guardEnvX B P (SomeInd (legalProg P)) syms M) P.bare n
        ⟨⟨fr, [], m1⟩, []⟩ = .returned rv m2 → rv.map (·.ty) = AbiParam.tys h.sig.returns →
        ∃ rv', ExpRel ((groups h.sig.returns).getD []) rv rv' ∧
          ∃ k, runLoopX (tgtEnvX B P (legalProg P)) (legalProg P).bare k ⟨⟨fr', [], m1⟩, []⟩ =
            .returned rv' m2) ∧
      (∀ n c, runLoopX (guardEnvX B P (SomeInd (legalProg P)) syms M) P.bare n
        ⟨⟨fr, [], m1⟩, []⟩ = .trapped c →
        ∃ k, runLoopX (tgtEnvX B P (legalProg P)) (legalProg P).bare k ⟨⟨fr', [], m1⟩, []⟩ =
          .trapped c) ∧
      (∀ n e m2, runLoopX (guardEnvX B P (SomeInd (legalProg P)) syms M) P.bare n
        ⟨⟨fr, [], m1⟩, []⟩ = .unwound e m2 →
        ∃ k, runLoopX (tgtEnvX B P (legalProg P)) (legalProg P).bare k ⟨⟨fr', [], m1⟩, []⟩ =
          .unwound e m2) := by
    obtain ⟨b, hb, h2, h3, h4, h5⟩ := hE.entry
    obtain ⟨b', hb', h2', h3', h5'⟩ := hE.entry'
    rcases Complete.legalOkTB_cases (hC.ctx.ok h hh) with ⟨hm, -, hl⟩ | ⟨hp, hTB, cert, hc⟩
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
      have hrun := identX_run (E := guardEnvX B P (SomeInd (legalProg P)) syms M)
        (E' := tgtEnvX B P (legalProg P)) (P := P) (P' := legalProg P) (f := h)
        (fun fn ex hfe => sameAtX_linkT hC ih (by
          obtain ⟨fn', hmem⟩ := lookup_mem hfe
          exact hes _ hmem) (fun h2 hpn => hC.ctx.decl h hh fn ex hfe h2 hpn))
        (fun i d hd => callIndRelX_linkT hC ih (by
          obtain ⟨i', hmem⟩ := lookup_mem hd
          exact hds _ hmem))
        (hC.ctx.free h hh)
      refine ⟨fun n rv m2 hr hty => ⟨rv, ?_, n, hrun n _ rfl hLeh _ hr (fun _ h => by cases h)⟩,
        fun n c hr => ⟨n, hrun n _ rfl hLeh _ hr (fun _ h => by cases h)⟩,
        fun n e m2 hr => ⟨n, hrun n _ rfl hLeh _ hr (fun _ h => by cases h)⟩⟩
      obtain ⟨rg, hrg, hR⟩ := groups_plain (sig128_returns hs)
      rw [hrg, Option.getD_some]
      refine expRel_refl_plain hR (sig128_returns hs) ?_
      have := congrArg List.length hty
      simpa [AbiParam.tys] using this
    · -- a legalisation: `checkW_refinesX2T` with the two environments
      have hbase := hC.ctx.base ⟨h, hh, hp.mentions⟩
      have hbaseX := hC.baseX ⟨h, hh, hp.mentions⟩
      have hE2 : EnvOkX2T (guardEnvX B P (SomeInd (legalProg P)) syms M) (tgtEnvX B P (legalProg P))
          ⟨h, legalize h, cert⟩ P.bare (legalProg P).bare :=
        { base :=
            { src := fun _ _ _ => rfl
              tgt := fun _ _ _ => rfl
              helper := fun op => by
                obtain ⟨hf, hB, hsem⟩ := hbase.1 op
                refine ⟨hf, ?_, hsem⟩
                have : (tgtEnvX B P (legalProg P)).toEnv.extern (divHelper op) =
                    B.toEnv.extern (divHelper op) := by
                  simp only [XEnv.toEnv, tgtEnvX_none (hC.ctx.func?_none (hC.ctx.helpers op))]
                rw [this]; exact hB
              ext := fun fn ex hfe => by
                cases hpn : P.func? ex.name with
                | some h2 => exact (extRel_progXT hC ih hpn (hC.ctx.decl h hh fn ex hfe h2 hpn)).1
                | none =>
                  intro hs he
                  have hgE : (guardEnvX B P (SomeInd (legalProg P)) syms M).toEnv.extern ex.name =
                      B.toEnv.extern ex.name := by
                    simp only [XEnv.toEnv, guardEnvX_none hpn]
                  have htE : (tgtEnvX B P (legalProg P)).toEnv.extern ex.name =
                      B.toEnv.extern ex.name := by
                    simp only [XEnv.toEnv, tgtEnvX_none (hC.ctx.func?_none hpn)]
                  rw [hgE] at he
                  obtain ⟨h', hb', hrel⟩ := hbase.2.1.at ex.name ex.sig hs he
                  exact ⟨h', by rw [htE]; exact hb', hrel⟩
              keep := keep_guardX hF hbase.2.2
              ind := fun _ => ⟨rfl, fun sig d hs hd =>
                have hd128 := Complete.indTB_indSite hTB hs hd
                callIndRel2_of_plain hd128 (callIndRelX_linkT hC ih hd128).1⟩ }
          extX := fun fn ex hfe => by
            cases hpn : P.func? ex.name with
            | some h2 => exact (extRel_progXT hC ih hpn (hC.ctx.decl h hh fn ex hfe h2 hpn)).2
            | none =>
              intro hs he
              rw [guardEnvX_none hpn] at he
              exact ⟨hs, by rw [tgtEnvX_none (hC.ctx.func?_none hpn)]; exact he,
                fun gs hgs vals vals' m hty hexp e m' hu =>
                  hbaseX.1 ex.name hs he ex.sig gs hgs vals vals' m hty hexp e m' hu⟩
          keepX := keepX_guardX hbaseX.2.1
          arity := arity_guardX hbaseX.2.2
          indX := fun _ B hB st hst sig callee args d hi hd =>
            (callIndRelX_linkT hC ih
              (Complete.indTB_indSite hTB (.inl ⟨B, hB, st, hst, callee, args, hi⟩) hd)).2
          indXT := fun B hB c args et d ht hd =>
            (callIndRelX_linkT hC ih
              (Complete.indTB_indSite hTB (.inr ⟨B, hB, c, args, et, ht, rfl⟩) hd)).2 }
      have hT := noMemTrapX_guard (G := SomeInd (legalProg P)) (M := M) hF hh hioS hUI hG
      have hI : NoIndInternalX (guardEnvX B P (SomeInd (legalProg P)) syms M) P.bare h
          ⟨fr, [], m1⟩ := fun _ _ => ⟨(fun _ _ _ _ _ _ _ _ _ _ g hg => nomatch hg),
            (fun _ _ _ _ _ _ _ _ g hg => nomatch hg)⟩
      have hx := hC.exn h hh hp.mentions (legalize h) cert hc
      have href := fun n => checkW_refinesX2T (C := ⟨h, legalize h, cert⟩)
        (Complete.checkW_complete hp hc) hx hTB hE2 hb hb' hE.func h2 h3 h4 h5 hE.func' h2' h3' h5'
        hE.slots hE.exp (hG _ (.refl _)).1 hT hI n
      exact ⟨fun n rv m2 hr _ => (href n).1 rv m2 hr, fun n c hr => (href n).2.1 c hr,
        fun n e m2 hr => (href n).2.2 e m2 hr⟩
  refine ⟨fun rv m2 hr => ?_, fun c hr => ?_, fun e m2 hr => ?_⟩
  · obtain ⟨n, hn⟩ := hlink _ hr (fun _ h => by cases h) (fun h => by cases h)
    have hty : rv.map (·.ty) = AbiParam.tys h.sig.returns := by
      have := runLoopX_returned_tys hF.free (M + 1) _ rv m2 hXI hr
      simpa [State.bottom, hE.func] using this
    obtain ⟨rv', hrel, k, hk⟩ := hact.1 n rv m2 hn hty
    obtain ⟨k', hk'⟩ := hwhole k _ hk (fun _ h => by cases h) (fun h => by cases h)
    exact ⟨rv', hrel, k', hk'⟩
  · obtain ⟨n, hn⟩ := hlink _ hr (fun _ h => by cases h) (fun h => by cases h)
    obtain ⟨k, hk⟩ := hact.2.1 n c hn
    exact hwhole k _ hk (fun _ h => by cases h) (fun h => by cases h)
  · obtain ⟨n, hn⟩ := hlink _ hr (fun _ h => by cases h) (fun h => by cases h)
    obtain ⟨k, hk⟩ := hact.2.2 n e m2 hn
    exact hwhole k _ hk (fun _ h => by cases h) (fun h => by cases h)

/-- **The callees are related at every fuel** (by induction on the fuel). -/
theorem prog_refinesXT {P : Program} {B : XEnv} {syms : String → Option Nat}
    (hC : ProgCtxXT P B syms) : ∀ M, RefinesX B P syms M := by
  intro M
  induction M with
  | zero =>
    intro h _ vals vals' m fr m1 fr' _ _ _ _
    exact ⟨fun _ _ h => by simp [runLoopX] at h, fun _ h => by simp [runLoopX] at h,
      fun _ _ h => by simp [runLoopX] at h⟩
  | succ M ih =>
    intro h hh vals vals' m fr m1 fr' hent hent' hexp hG
    have hfacts := legalFactsT (hC.ctx.ok h hh)
    exact root_refinesXT hC ih hh (EntryRel.of_enter ⟨hfacts.name, hfacts.slots⟩ hent hent' hexp) hG

/-- **Whole-program refinement of the original program with unwinding** (S10f): on the source
domain with unwinding (`ProgCtxXT`), a whole-program run with unwinding of a function `h` of `P`
from entry frames (`EntryRel`: the target's on the ABI-split arguments, the same slots) and a
memory all of whose whole-program successors are good (`GoodFromX`) that returns within `M` steps
is a return of the legalised program's run with the results split by `h`'s return groups and the
same memory; a trap is the same trap; an exception leaving `h` is the same exception leaving
`legalize h`, with the same memory. -/
theorem legalProg_refinesXT {P : Program} {B : XEnv} {syms : String → Option Nat}
    (hC : ProgCtxXT P B syms) {h : Function} (hh : h ∈ P.funcs) {args args' : List Val}
    {fr fr' : Frame} {m1 : Mem} (hE : EntryRel h args args' fr fr')
    (hG : GoodFromX B P (SomeInd (legalProg P)) syms ⟨⟨fr, [], m1⟩, []⟩) (M : Nat) :
    (∀ rv m2, runLoopX B P M ⟨⟨fr, [], m1⟩, []⟩ = .returned rv m2 →
      ∃ rv', ExpRel ((groups h.sig.returns).getD []) rv rv' ∧
        ∃ k, runLoopX B (legalProg P) k ⟨⟨fr', [], m1⟩, []⟩ = .returned rv' m2) ∧
    (∀ c, runLoopX B P M ⟨⟨fr, [], m1⟩, []⟩ = .trapped c →
      ∃ k, runLoopX B (legalProg P) k ⟨⟨fr', [], m1⟩, []⟩ = .trapped c) ∧
    (∀ e m2, runLoopX B P M ⟨⟨fr, [], m1⟩, []⟩ = .unwound e m2 →
      ∃ k, runLoopX B (legalProg P) k ⟨⟨fr', [], m1⟩, []⟩ = .unwound e m2) := by
  cases M with
  | zero =>
    exact ⟨fun _ _ h => by simp [runLoopX] at h, fun _ h => by simp [runLoopX] at h,
      fun _ _ h => by simp [runLoopX] at h⟩
  | succ M => exact root_refinesXT hC (prog_refinesXT hC M) hh hE hG

end E2E.LegalProgram
