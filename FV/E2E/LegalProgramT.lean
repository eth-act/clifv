import FV.E2E.LegalProgram
import FV.Opt.Proof.LegalPreT

/-!
# Whole-program refinement of the original `i128` program, `try_call_indirect` included (#1076)

`legalProg_refinesT`: S3's `legalProg_refines` (`FV/E2E/LegalProgram.lean`) on the source domain
`ProgCtxT`, `ProgCtx` with every function in `legalOkTB` instead of `legalOkB`: a function that
mentions `i128` may have `try_call_indirect` terminators, and its indirect calls have `i128`-free
call-site signatures (`indTB`; Rust's `Box<dyn Any>::downcast`). The proof is S3's, each
legalised activation by `legalize_refines2W` (the validator `checkW`, `checkW_complete` on
`PreW`) instead of `legalize_refines2` (`check` on `Pre`), its indirect call sites' signatures
`i128`-free by `indTB` (`Complete.indTB_indSite`) instead of `Pre`. `ProgCtx.toT`: the old domain
is inside the new one (`legalOkTB_of_legalOkB`).
-/

namespace E2E.LegalProgram

open Clif Opt.Legal Opt.Legalize128

/-- **The facts of the legalisation of a function of `legalOkTB`** (`legalFacts`). -/
theorem legalFactsT {f : Function} (h : legalOkTB f = true) : LegalFacts f := by
  rcases Complete.legalOkTB_cases h with ⟨hm, -, hl⟩ | ⟨hp, -, cert, hc⟩
  · obtain ⟨hs, he, -⟩ := not_mentions hm
    refine ⟨by rw [hl], by rw [hl], by rw [hl]; exact Complete.sigExp_plain hs, fun fn e hfe => ?_,
      ⟨[], by rw [hl, List.append_nil], fun _ h => by cases h⟩, fun h1 => by rw [hl]; exact h1⟩
    refine ⟨e.sig, ?_, by rw [hl]; exact hfe⟩
    obtain ⟨fn', hmem⟩ := lookup_mem hfe
    exact Complete.sigExp_plain (he _ hmem)
  · have hchk := Complete.checkW_complete hp hc
    have hG := checkW_good hchk
    obtain ⟨es, ds, hes, hds, he, hd⟩ := function128Cert_spec hp.mentions hc
    have hO := Complete.gok_of hes hds he hd cert
    refine ⟨hG.name, hG.slots, hG.sig, fun fn e hfe => hO.ext fn e hfe,
      ⟨helperNames f, by rw [he, List.map_append, expandExterns_names hes, helperExts_names],
        fun _ h => h⟩, fun hnf hif => ?_⟩
    -- an indirect call of `f`: a `call_indirect` statement or a `try_call_indirect` terminator,
    -- both kept by the legalisation
    by_cases hci : ∃ B ∈ f.blocks, ∃ st ∈ B.body, ∃ sig callee args,
        st.inst = .callIndirect sig callee args
    · obtain ⟨B, hB, st, hst, sig, callee, args, hi⟩ := checkW_callInd hchk hci
      exact (hif B hB).1 st hst sig callee args hi
    · have hti : ∃ B ∈ f.blocks, ∃ c args et, B.term = .tryCallIndirect c args et :=
        Classical.byContradiction fun hno => hnf fun B hB => ⟨fun st hst sig callee args hi =>
          hci ⟨B, hB, st, hst, sig, callee, args, hi⟩, fun c args et ht => hno ⟨B, hB, c, args, et, ht⟩⟩
      obtain ⟨B, hB, c, args, et, ht⟩ := checkW_tryInd hchk hti
      exact (hif B hB).2 c args et ht

/-- The entry of the legalisation of a function of `legalOkTB` on the ABI-split
arguments: the same slots and memory. -/
theorem enterFunc_legalT {f : Function} (hok : legalOkTB f = true) {vals vals' : List Val}
    {mem mem1 : Mem} {fr : Frame} (he : enterFunc f vals mem = .ok (fr, mem1))
    (hexp : ExpRel ((groups f.sig.params).getD []) vals vals') :
    ∃ fr', enterFunc (legalize f) vals' mem = .ok (fr', mem1) := by
  rcases Complete.legalOkTB_cases hok with ⟨hm, -, hl⟩ | ⟨hp, -, cert, hc⟩
  · obtain ⟨hs, -, -⟩ := not_mentions hm
    obtain ⟨gs, hgs, hG⟩ := groups_plain (sig128_params hs)
    rw [hgs, Option.getD_some] at hexp
    rw [expRel_val hG (sig128_params hs) hexp, hl]
    exact ⟨fr, he⟩
  · have hchk := Complete.checkW_complete hp hc
    have hG : Good ⟨f, legalize f, cert⟩ := by
      rw [Complete.legalize_of_ok hc]; exact checkW_good hchk
    obtain ⟨b, regs, hb, hty, hbt, hr, hsl, -⟩ := Opt.enterFunc_ok he
    obtain ⟨b0, bs, b0', bs', hf, hg, -, hok0, -⟩ := hG.blocks
    simp only [Function.entry?] at hb
    rw [show f = (⟨f, legalize f, cert⟩ : Ctx).f from rfl, hf] at hb
    simp only [List.head?_cons, Option.some.injEq] at hb
    subst hb
    simp only [blockOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, ite_true] at hok0
    obtain ⟨⟨-, -⟩, hok0⟩ := hok0
    split at hok0
    · rename_i gs z rest hgs hbody'
      simp only [Bool.and_eq_true, beq_iff_eq] at hok0
      obtain ⟨⟨hep, -⟩, -⟩ := hok0
      have hgs' : groups f.sig.params = some gs := hgs
      rw [hgs', Option.getD_some] at hexp
      obtain ⟨hty', -, -⟩ := entry_bind hep hexp hbt
      obtain ⟨gs0, rg0, hgs0, -, hpar', -⟩ := sigExp_spec hG.sig
      rw [hgs'] at hgs0
      cases hgs0
      have htyS : vals'.map (·.ty) = AbiParam.tys (legalize f).sig.params := by
        have := expRel_tys (groups_spec hgs') hexp (by rw [hty]; rfl)
        rw [this, hpar']
        rfl
      obtain ⟨regs', hr'⟩ := setMany_of_len Regs.empty (rs := b0'.params.map (·.1)) (vs := vals')
        (by have := congrArg List.length hty'; simpa using this.symm)
      have hb' : (legalize f).entry? = some b0' := by
        simp only [Function.entry?]
        rw [show legalize f = (⟨f, legalize f, cert⟩ : Ctx).g from rfl, hg]
        rfl
      have hslots : enterSlots (legalize f) mem = enterSlots f mem :=
        Opt.enterSlots_congr hG.name hG.slots mem
      refine ⟨⟨legalize f, regs', fr.slots, b0'.body, b0'.term⟩, ?_⟩
      rw [Opt.enterFunc_of hb' htyS hty' hr', hslots, hsl]
    · cases hok0

/-! ## The source domain of a program, `try_call_indirect` included -/

/-- **The source domain of a program `P` over the base environment `B`** (link-time symbols
`syms`), indirect calls at `i128`-free signatures (`try_call_indirect` included): every function in
`legalOkTB` (identity, or `PreW`, `indTB` and a successful legalisation; `ProgCtx` with
`legalOkB`),
distinct names, no `return_call` (in `P` and its legalisation), declarations of the program's
functions with their signatures (in `P` and its legalisation), no function named like a
`__*ti3` helper; where a function mentions `i128`, the base environment's contracts (`HelperOk`:
the helpers divide; `ExtLegal`: an extern called with split arguments returns split results;
`EnvKeepsBounded`); where the legalised program has indirect calls, `IndScope` and no signature
known to `B`. -/
structure ProgCtxT (P : Program) (B : Env) (syms : String → Option Nat) : Prop where
  ok : ∀ f ∈ P.funcs, legalOkTB f = true
  nd : (P.funcs.map (·.name)).Nodup
  free : ∀ f ∈ P.funcs, LinkFree f
  free' : ∀ f ∈ P.funcs, LinkFree (legalize f)
  decl : ∀ g ∈ P.funcs, ∀ fn e, g.extern? fn = some e → ∀ h, P.func? e.name = some h → h.sig = e.sig
  decl' : ∀ g ∈ (legalProg P).funcs, ∀ fn e, g.extern? fn = some e → ∀ h,
    (legalProg P).func? e.name = some h → h.sig = e.sig
  helpers : ∀ op, P.func? (divHelper op) = none
  base : (∃ f ∈ P.funcs, mentions128 f = true) → HelperOk B ∧ ExtLegal B ∧ EnvKeepsBounded B
  ind : SomeInd (legalProg P) → IndScope (legalProg P) B syms ∧ ∀ n, B.sigOf n = none

/-- **The old source domain is inside the new one** (`legalOkTB_of_legalOkB`). -/
theorem ProgCtx.toT {P : Program} {B : Env} {syms : String → Option Nat} (hC : ProgCtx P B syms) :
    ProgCtxT P B syms where
  ok f hf := Complete.legalOkTB_of_legalOkB (hC.ok f hf)
  nd := hC.nd
  free := hC.free
  free' := hC.free'
  decl := hC.decl
  decl' := hC.decl'
  helpers := hC.helpers
  base := hC.base
  ind := hC.ind

namespace ProgCtxT

variable {P : Program} {B : Env} {syms : String → Option Nat} (hC : ProgCtxT P B syms)
include hC

theorem names : (legalProg P).funcs.map (·.name) = P.funcs.map (·.name) := by
  simp only [legalProg_funcs, List.map_map]
  exact List.map_congr_left fun f hf => (legalFactsT (hC.ok f hf)).name

theorem facts : ProgFacts P := ⟨hC.nd, hC.free, hC.decl⟩

theorem facts' : ProgFacts (legalProg P) :=
  ⟨by rw [hC.names]; exact hC.nd, fun g hg => by
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
    exact hC.free' f hf, hC.decl'⟩

theorem func? (n : String) : (legalProg P).func? n = (P.func? n).map legalize :=
  _root_.E2E.LegalProgram.find?_legalize n fun f hf => (legalFactsT (hC.ok f hf)).name

theorem func?_some {n : String} {h : Function} (hp : P.func? n = some h) :
    (legalProg P).func? n = some (legalize h) := by
  rw [hC.func? n, hp]; rfl

theorem func?_none {n : String} (hp : P.func? n = none) : (legalProg P).func? n = none := by
  rw [hC.func? n, hp]; rfl

theorem externNames {n : String} (hn : n ∈ P.externNames) : n ∈ (legalProg P).externNames := by
  simp only [Program.externNames, List.mem_flatMap, legalProg_funcs, List.mem_map] at hn ⊢
  obtain ⟨f, hf, hn⟩ := hn
  obtain ⟨hn', heq, -⟩ := (legalFactsT (hC.ok f hf)).names
  refine ⟨legalize f, ⟨f, hf, rfl⟩, ?_⟩
  have hm : n ∈ (legalize f).externs.map (·.2.name) := by
    rw [heq]; exact List.mem_append_left _ (List.mem_map.mpr hn)
  exact List.mem_map.mp hm

theorem someInd {f : Function} (hf : f ∈ P.funcs) (hn : ¬ IndFree f) : SomeInd (legalProg P) :=
  ⟨legalize f, List.mem_map_of_mem hf, (legalFactsT (hC.ok f hf)).ind hn⟩

theorem indSrc (hI : SomeInd (legalProg P)) : IndScope P B syms :=
  indScope_src (hC.ind hI).1 hC.names (fun _ h => hC.externNames h) fun _ h => hC.func?_none h

end ProgCtxT

/-! ## The induction -/

section Induction

variable {P : Program} {B : Env} {syms : String → Option Nat} (hC : ProgCtxT P B syms)
  {M : Nat} (ih : Refines B P syms M)
include hC ih

/-- A callee run of the guarded environment and the target's: related by the induction
hypothesis. -/
theorem prog_callT {n : String} {h2 : Function} (hp : P.func? n = some h2)
    {vals vals' : List Val} {m : Mem}
    (hexp : ExpRel ((groups h2.sig.params).getD []) vals vals') :
    (∀ rv m', guardFun B P (SomeInd (legalProg P)) syms M h2 n vals m = .returned rv m' →
      ∃ rv', ExpRel ((groups h2.sig.returns).getD []) rv rv' ∧
        tgtFun B (legalProg P) n vals' m = .returned rv' m') ∧
    (∀ c, guardFun B P (SomeInd (legalProg P)) syms M h2 n vals m = .trapped c →
      tgtFun B (legalProg P) n vals' m = .trapped c) := by
  obtain ⟨hh2, rfl⟩ := Program.func?_some hp
  have hp' := hC.func?_some hp
  have key : ∀ o, guardFun B P (SomeInd (legalProg P)) syms M h2 h2.name vals m = o →
      (∀ msg, o ≠ .stuck msg) → ∃ fr m1 fr', enterFunc h2 vals m = .ok (fr, m1) ∧
        enterFunc (legalize h2) vals' m = .ok (fr', m1) ∧
        GoodFrom B P (SomeInd (legalProg P)) syms ⟨fr, [], m1⟩ ∧
        Clif.runLoop B P M ⟨fr, [], m1⟩ = o := by
    intro o ho hs
    obtain ⟨hgood, hl⟩ := guardFun_cases ho hs
    unfold linkFun at hl
    cases hi : initState P h2.name vals m with
    | ok s =>
      rw [hi] at hl
      obtain ⟨fr, m1, he, rfl⟩ := (initState_ok_iff hp).mp hi
      obtain ⟨fr', he'⟩ := enterFunc_legalT (hC.ok h2 hh2) he hexp
      exact ⟨fr, m1, fr', he, he', hgood fr m1 he, hl⟩
    | trap c => exact absurd hi (initState_not_trap P h2.name vals m c)
    | stuck msg => rw [hi] at hl; exact absurd hl.symm (hs msg)
  have tgt : ∀ fr' m1 o k, enterFunc (legalize h2) vals' m = .ok (fr', m1) →
      Clif.runLoop B (legalProg P) k ⟨fr', [], m1⟩ = o → o ≠ .outOfFuel →
      tgtFun B (legalProg P) h2.name vals' m = o := by
    intro fr' m1 o k he' hr ho
    unfold tgtFun
    rw [(initState_ok_iff hp').mpr ⟨fr', m1, he', rfl⟩]
    show runLim B (legalProg P) ⟨fr', [], m1⟩ = o
    rw [runLim_eq (by rw [hr]; exact ho), hr]
  refine ⟨fun rv m' ho => ?_, fun c ho => ?_⟩
  · obtain ⟨fr, m1, fr', he, he', hG, hr⟩ := key _ ho (fun _ h => by cases h)
    obtain ⟨rv', hrel, k, hk⟩ := (ih h2 hh2 vals vals' m fr m1 fr' he he' hexp hG).1 rv m' hr
    exact ⟨rv', hrel, tgt fr' m1 _ k he' hk (fun h => by cases h)⟩
  · obtain ⟨fr, m1, fr', he, he', hG, hr⟩ := key _ ho (fun _ h => by cases h)
    obtain ⟨k, hk⟩ := (ih h2 hh2 vals vals' m fr m1 fr' he he' hexp hG).2 c hr
    exact tgt fr' m1 _ k he' hk (fun h => by cases h)

end Induction

section Induction

variable {P : Program} {B : Env} {syms : String → Option Nat} (hC : ProgCtxT P B syms)
  {M : Nat} (ih : Refines B P syms M)
include hC ih

/-- The source's guarded environment and the target's are related at the declaration `n` of a
function of `P` (with its signature, `ProgCtxT.decl`). -/
theorem extRel_progT {n : String} {h2 : Function} (hp : P.func? n = some h2) {sig : Signature}
    (hsig : h2.sig = sig) :
    ExtRelAt (guardEnv B P (SomeInd (legalProg P)) syms M) (tgtEnv B P (legalProg P)) n sig := by
  intro hs he
  rw [guardEnv_some hp] at he
  cases he
  refine ⟨_, tgtEnv_some (hC.func?_some hp), fun gs rg hgs hrg vals vals' m hty hexp => ?_⟩
  have hexp' : ExpRel ((groups h2.sig.params).getD []) vals vals' := by
    rw [hsig, hgs]; exact hexp
  obtain ⟨h1, h2'⟩ := prog_callT hC ih hp hexp'
  refine ⟨fun rv m' ho _ => ?_, fun c ho => h2' c ho⟩
  obtain ⟨rv', hrel, ht⟩ := h1 rv m' ho
  refine ⟨rv', ht, ?_⟩
  rw [hsig, hrg] at hrel
  exact hrel

/-- At a declaration without `i128` (of a function of `P`, with its signature, or of the base
environment), the two environments return the same values. -/
theorem sameAt_linkT {n : String} {sig : Signature} (hd : sig128 sig = false)
    (hdecl : ∀ h2, P.func? n = some h2 → h2.sig = sig) :
    SameAt (guardEnv B P (SomeInd (legalProg P)) syms M) (tgtEnv B P (legalProg P)) n sig := by
  intro hs he
  cases hpn : P.func? n with
  | some h2 =>
    rw [guardEnv_some hpn] at he
    cases he
    have hs2 := hdecl h2 hpn
    have hd2 : sig128 h2.sig = false := by rw [hs2]; exact hd
    refine ⟨_, tgtEnv_some (hC.func?_some hpn), fun vals m hv => ?_⟩
    obtain ⟨gs, hgs, hG⟩ := groups_plain (sig128_params hd2)
    have hexp : ExpRel ((groups h2.sig.params).getD []) vals vals := by
      rw [hgs, Option.getD_some]
      refine expRel_refl_plain hG (sig128_params hd2) ?_
      have := congrArg List.length hv
      rw [hs2]
      simpa [AbiParam.tys] using this
    obtain ⟨h1, h2'⟩ := prog_callT hC ih hpn hexp
    refine ⟨fun rv m' ho _ => ?_, fun c ho => h2' c ho⟩
    obtain ⟨rv', hrel, ht⟩ := h1 rv m' ho
    obtain ⟨rg, hrg, hR⟩ := groups_plain (sig128_returns hd2)
    rw [hrg, Option.getD_some] at hrel
    rw [← expRel_val hR (sig128_returns hd2) hrel]
    exact ht
  | none =>
    rw [guardEnv_none hpn] at he
    exact ⟨hs, by rw [tgtEnv_none (hC.func?_none hpn)]; exact he,
      fun vals m _ => ⟨fun rv m' ho _ => ho, fun c ho => ho⟩⟩

/-- An indirect call with a call-site signature without `i128`: the two environments resolve the
address to the same name and return the same values. -/
theorem callIndRel_linkT {d : Signature} (hd : sig128 d = false) :
    CallIndRel (guardEnv B P (SomeInd (legalProg P)) syms M) (tgtEnv B P (legalProg P)) P.bare
      (legalProg P).bare d := by
  intro mem a vals
  have hnames : ((guardEnv B P (SomeInd (legalProg P)) syms M).names ++ P.bare.externNames) =
      ((tgtEnv B P (legalProg P)).names ++ (legalProg P).bare.externNames) := by
    simp [guardEnv, tgtEnv, linkEnvN_names]
  -- a function of `P` reached with a signature without `i128` has none either
  have hfun : ∀ n h2, P.func? n = some h2 →
      ((guardEnv B P (SomeInd (legalProg P)) syms M).sigOf n).all d.abiMatch = true →
      ((tgtEnv B P (legalProg P)).sigOf n).all d.abiMatch = true ∧ sig128 h2.sig = false ∧
        AbiParam.tys d.params = AbiParam.tys h2.sig.params := by
    intro n h2 hpn hs
    have hs' : d.abiMatch h2.sig = true := by
      simpa [guardEnv, linkEnvN_sigOf, hpn] using hs
    have hm := Signature.abiMatch_eq_true.mp hs'
    have h2p : sig128 h2.sig = false := sig128_of_tys hd hm.1 hm.2.2
    have hl2 : (legalize h2).sig = h2.sig := by
      have := (legalFactsT (hC.ok h2 (Program.func?_some hpn).1)).sig
      rw [Complete.sigExp_plain h2p] at this
      exact (Option.some.inj this).symm
    refine ⟨?_, h2p, hm.1⟩
    simp [tgtEnv, hC.func?_some hpn, hl2, hs']
  have hexpOf : ∀ n h2, P.func? n = some h2 → sig128 h2.sig = false →
      AbiParam.tys d.params = AbiParam.tys h2.sig.params →
      vals.map (·.ty) = AbiParam.tys d.params → ExpRel ((groups h2.sig.params).getD []) vals vals := by
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
      rw [guardEnv_some hpn] at hg
      cases hg
      obtain ⟨hs', h2p, htp⟩ := hfun n h2 hpn hs
      obtain ⟨h1', -⟩ := prog_callT hC ih hpn (hexpOf n h2 hpn h2p htp hv)
      obtain ⟨rv', hrel, ht⟩ := h1' rv m' ho
      obtain ⟨rg, hrg, hR⟩ := groups_plain (sig128_returns h2p)
      rw [hrg, Option.getD_some] at hrel
      rw [expRel_val hR (sig128_returns h2p) hrel] at ht
      exact callExternAt_ok_iff.mpr ⟨n, _, h1, tgtEnv_some (hC.func?_some hpn), hs', hv, rv, m',
        ht, hrt, rfl⟩
    | none =>
      rw [guardEnv_none hpn] at hg
      have hsN : (tgtEnv B P (legalProg P)).sigOf n = none := by
        simp [tgtEnv, hC.func?_none hpn]
      exact callExternAt_ok_iff.mpr ⟨n, g, h1, by rw [tgtEnv_none (hC.func?_none hpn)]; exact hg,
        by rw [hsN]; rfl, hv, rv, m', ho, hrt, rfl⟩
  · intro c hr
    obtain ⟨n, g, h1, hg, hs, hv, ho⟩ := callExternAt_trap_iff.mp hr
    rw [hnames] at h1
    cases hpn : P.func? n with
    | some h2 =>
      rw [guardEnv_some hpn] at hg
      cases hg
      obtain ⟨hs', h2p, htp⟩ := hfun n h2 hpn hs
      obtain ⟨-, h2'⟩ := prog_callT hC ih hpn (hexpOf n h2 hpn h2p htp hv)
      exact callExternAt_trap_iff.mpr ⟨n, _, h1, tgtEnv_some (hC.func?_some hpn), hs', hv,
        h2' c ho⟩
    | none =>
      rw [guardEnv_none hpn] at hg
      have hsN : (tgtEnv B P (legalProg P)).sigOf n = none := by
        simp [tgtEnv, hC.func?_none hpn]
      exact callExternAt_trap_iff.mpr ⟨n, g, h1, by rw [tgtEnv_none (hC.func?_none hpn)]; exact hg,
        by rw [hsN]; rfl, hv, ho⟩

end Induction

/-- **The refinement of one activation at fuel `M + 1`** from entry frames (`EntryRel`, any slot
addresses and memory), the callees related at fuel `M` (`Refines`). -/
theorem root_refinesT {P : Program} {B : Env} {syms : String → Option Nat}
    (hC : ProgCtxT P B syms) {M : Nat} (ih : Refines B P syms M) {h : Function} (hh : h ∈ P.funcs)
    {args args' : List Val} {fr fr' : Frame} {m1 : Mem} (hE : EntryRel h args args' fr fr')
    (hG : GoodFrom B P (SomeInd (legalProg P)) syms ⟨fr, [], m1⟩) :
    (∀ rv m2, Clif.runLoop B P (M + 1) ⟨fr, [], m1⟩ = .returned rv m2 →
      ∃ rv', ExpRel ((groups h.sig.returns).getD []) rv rv' ∧
        ∃ k, Clif.runLoop B (legalProg P) k ⟨fr', [], m1⟩ = .returned rv' m2) ∧
    (∀ c, Clif.runLoop B P (M + 1) ⟨fr, [], m1⟩ = .trapped c →
      ∃ k, Clif.runLoop B (legalProg P) k ⟨fr', [], m1⟩ = .trapped c) := by
  have hF := hC.facts
  have hF' := hC.facts'
  have hfacts := legalFactsT (hC.ok h hh)
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
      UnlinkInd (guardEnv B P (SomeInd (legalProg P)) syms M) P B syms := fun hn =>
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
  have hguard := guard_run (G := SomeInd (legalProg P)) hF M hh hioE
  -- the target's per-function run is a whole-program run
  have hUIt : UInv (legalProg P) (legalize h) syms ⟨fr', [], m1⟩ :=
    ⟨rfl, hE.lframe' (by simp [Program.only]), fun hn => (hG _ (.refl _)).2.2 ⟨_, hhP', hn⟩⟩
  have hioT : ¬ IndFree (legalize h) → UnlinkInd (tgtEnv B P (legalProg P)) (legalProg P) B syms :=
    fun hn => unlinkInd_tgt (hC.ind ⟨_, hhP', hn⟩).1 (hC.ind ⟨_, hhP', hn⟩).2 hC.names
      (fun _ h => hC.externNames h)
  have hwhole := fun n => unlink_run (unlink_tgt (B := B) (P := P) hF') hhP' hioT (n := n) hUIt
  -- the per-activation refinement under the two environments
  have hact : (∀ n rv m2, Clif.runLoop (guardEnv B P (SomeInd (legalProg P)) syms M) P.bare n
        ⟨fr, [], m1⟩ = .returned rv m2 → rv.map (·.ty) = AbiParam.tys h.sig.returns →
        ∃ rv', ExpRel ((groups h.sig.returns).getD []) rv rv' ∧
          ∃ k, Clif.runLoop (tgtEnv B P (legalProg P)) (legalProg P).bare k ⟨fr', [], m1⟩ =
            .returned rv' m2) ∧
      (∀ n c, Clif.runLoop (guardEnv B P (SomeInd (legalProg P)) syms M) P.bare n
        ⟨fr, [], m1⟩ = .trapped c →
        ∃ k, Clif.runLoop (tgtEnv B P (legalProg P)) (legalProg P).bare k ⟨fr', [], m1⟩ =
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
      have hrun := ident_run (E := guardEnv B P (SomeInd (legalProg P)) syms M)
        (E' := tgtEnv B P (legalProg P)) (P := P) (P' := legalProg P) (f := h)
        (fun fn ex hfe => sameAt_linkT hC ih (by
          obtain ⟨fn', hmem⟩ := lookup_mem hfe
          exact hes _ hmem) (fun h2 hpn => hC.decl h hh fn ex hfe h2 hpn))
        (fun i d hd => callIndRel_linkT hC ih (by
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
      have hE2 : EnvOk2 (guardEnv B P (SomeInd (legalProg P)) syms M) (tgtEnv B P (legalProg P))
          ⟨h, legalize h, cert⟩ P.bare (legalProg P).bare :=
        { src := fun _ _ _ => rfl
          tgt := fun _ _ _ => rfl
          helper := fun op => by
            obtain ⟨hf, hB, hsem⟩ := hbase.1 op
            exact ⟨hf, by rw [tgtEnv_none (hC.func?_none (hC.helpers op))]; exact hB, hsem⟩
          ext := fun fn ex hfe => by
            cases hpn : P.func? ex.name with
            | some h2 => exact extRel_progT hC ih hpn (hC.decl h hh fn ex hfe h2 hpn)
            | none =>
              intro hs he
              rw [guardEnv_none hpn] at he
              obtain ⟨h', hb', hrel⟩ := hbase.2.1.at ex.name ex.sig hs he
              exact ⟨h', by rw [tgtEnv_none (hC.func?_none hpn)]; exact hb', hrel⟩
          keep := keep_guard hF hbase.2.2
          ind := fun _ => ⟨rfl, fun sig d hs hd =>
            have hd128 := Complete.indTB_indSite hTB hs hd
            callIndRel2_of_plain hd128 (callIndRel_linkT hC ih hd128)⟩ }
      have hT := noMemTrap_guard hF M hh hioG hUI hG
      have hI : NoIndInternal (guardEnv B P (SomeInd (legalProg P)) syms M) P.bare h
          ⟨fr, [], m1⟩ := fun _ _ => ⟨(fun _ _ _ _ _ _ _ _ _ _ g hg => nomatch hg),
            (fun _ _ _ _ _ _ _ _ g hg => nomatch hg)⟩
      have href := fun n => legalize_refines2W hp hc hE2 hb hb' hE.func h2 h3 h4 h5 hE.func' h2'
        h3' h5' hE.slots hE.exp (hG _ (.refl _)).1 hT hI n
      exact ⟨fun n rv m2 hr _ => (href n).1 rv m2 hr, fun n c hr => (href n).2 c hr⟩
  refine ⟨fun rv m2 hr => ?_, fun c hr => ?_⟩
  · obtain ⟨n, hn⟩ := hlink _ hr (fun _ h => by cases h) (fun h => by cases h)
    have hn'' := (hguard n _ hUI hG).1 rv m2 hn
    have hty : rv.map (·.ty) = AbiParam.tys h.sig.returns := by
      have := runLoop_returned_tys hC.free (M + 1) _ rv m2 hLe hr
      simpa [State.bottom, hE.func] using this
    obtain ⟨rv', hrel, k, hk⟩ := hact.1 n rv m2 hn'' hty
    obtain ⟨k', hk'⟩ := (hwhole k).1 rv' m2 hk
    exact ⟨rv', hrel, k', hk'⟩
  · obtain ⟨n, hn⟩ := hlink _ hr (fun _ h => by cases h) (fun h => by cases h)
    have hn'' := (hguard n _ hUI hG).2 c hn
    obtain ⟨k, hk⟩ := hact.2 n c hn''
    exact (hwhole k).2 c hk

/-- **The callees are related at every fuel** (by induction on the fuel). -/
theorem prog_refinesT {P : Program} {B : Env} {syms : String → Option Nat}
    (hC : ProgCtxT P B syms) : ∀ M, Refines B P syms M := by
  intro M
  induction M with
  | zero =>
    intro h _ vals vals' m fr m1 fr' _ _ _ _
    exact ⟨fun _ _ h => by simp at h, fun _ h => by simp at h⟩
  | succ M ih =>
    intro h hh vals vals' m fr m1 fr' hent hent' hexp hG
    have hfacts := legalFactsT (hC.ok h hh)
    exact root_refinesT hC ih hh (EntryRel.of_enter ⟨hfacts.name, hfacts.slots⟩ hent hent' hexp) hG

/-- **Whole-program refinement of the original program** (S3): on the source domain
(`ProgCtxT`), a whole-program run of a function `h` of `P` from entry frames (`EntryRel`: the
target's on the ABI-split arguments, the same slots) and memory all of whose whole-program
successors are good (`GoodFrom`) that returns within `M` steps is a return of the legalised
program's run with the results split by `h`'s return groups and the same memory; a trap is the
same trap. -/
theorem legalProg_refinesT {P : Program} {B : Env} {syms : String → Option Nat}
    (hC : ProgCtxT P B syms) {h : Function} (hh : h ∈ P.funcs) {args args' : List Val}
    {fr fr' : Frame} {m1 : Mem} (hE : EntryRel h args args' fr fr')
    (hG : GoodFrom B P (SomeInd (legalProg P)) syms ⟨fr, [], m1⟩) (M : Nat) :
    (∀ rv m2, Clif.runLoop B P M ⟨fr, [], m1⟩ = .returned rv m2 →
      ∃ rv', ExpRel ((groups h.sig.returns).getD []) rv rv' ∧
        ∃ k, Clif.runLoop B (legalProg P) k ⟨fr', [], m1⟩ = .returned rv' m2) ∧
    (∀ c, Clif.runLoop B P M ⟨fr, [], m1⟩ = .trapped c →
      ∃ k, Clif.runLoop B (legalProg P) k ⟨fr', [], m1⟩ = .trapped c) := by
  cases M with
  | zero => exact ⟨fun _ _ h => by simp at h, fun _ h => by simp at h⟩
  | succ M => exact root_refinesT hC (prog_refinesT hC M) hh hE hG

end E2E.LegalProgram
