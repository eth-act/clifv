import FV.Opt.Proof.SimpSimX
import FV.Opt.Proof.SimWinU

/-!
# The simplify validator is sound with handler edges (`Opt.simpOk_simU`, S10f #233)

`Opt.simpOk_simX` (`FV/Opt/Proof/SimpSimX.lean`) with the handler edges of `IsSimU`: a
`try_call`/`try_call_indirect` terminator is not a branch, so the simplifier keeps it renamed
(`SRel.atKept`) and its exception table is `et.mapVals cert.subst.step`; the frames resumed at
the handlers enter the same block with the same arguments (`SRel.hcont`, as `SRel.tcont`).
-/

namespace Opt

open Clif

section
variable {f g : Function} {fi : Info} {cert : SimpCert} (hS : SOk f g fi cert)
  {syms : String → Option Nat}
include hS

/-- The handler edges of a kept `try_call`. -/
theorem SRel.hcont {fr fr' : Frame} {bi k k' : Nat} {et : ExnTable}
    (h : SRel f g fi cert syms fr fr' bi k k') (hs : fr.body = []) (ht0 : fr'.body = [])
    (hterm : fr'.term = mapTerm cert.subst.step fr.term)
    (hsucc : ∀ d ∈ et.handlers, d.block ∈ termSuccs fr.term)
    (hvals : ∀ d ∈ et.handlers, ∀ x ∈ d.vals, fr'.regs (cert.subst.step x) = fr.regs x ∧
      x < f.freshValue ∧ cert.subst.step x < g.freshValue)
    (hw : Win fr fr') :
    HCont (SSR f g fi cert syms) fr et fr' (et.mapVals cert.subst.step) := by
  have hf := h.invf.func
  have hg := h.invg.func
  intro e
  refine ⟨fun hn => ?_, fun fr1 hc => ?_⟩
  · rw [catchIn_eq_none] at hn ⊢
    rw [catch?_mapVals, hn]; rfl
  · obtain ⟨d, bc, regs, hd, hbc, hset, rfl⟩ := catchIn_ok hc
    obtain ⟨bc', hbc', hblk, hpw⟩ := tryHandler_pair cert.subst.step
      (b2 := fr'.func.freshValue) hbc
    obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs)
      (xs := (List.range e.payload.length).map (fr'.func.freshValue + ·)) (vs := e.payload)
      (by simp)
    have hd' : (et.mapVals cert.subst.step).catch? e = some (d.mapVals cert.subst.step) := by
      rw [catch?_mapVals, hd]; rfl
    refine ⟨_, catchIn_of hd' hbc' hset', rfl, rfl, bc, bc', rfl, rfl, fun fr1 he1 => ?_⟩
    have he1' : enterBlock { fr with regs } bc = .ok fr1 := by
      rw [← enterBlock_bt { fr with regs } [] (.jump bc)]; exact he1
    have hW := setMany_tryRets (n := e.payload.length) (W := fr.func.freshValue) hset
    have hW' := setMany_tryRets (n := e.payload.length) (W := fr'.func.freshValue) hset'
    have hlo : ∀ v < f.freshValue, regs v = fr.regs v := catch_regs_lo hset (by rw [hf])
    have hlo' : ∀ v < g.freshValue, regs' v = fr'.regs v := catch_regs_lo hset' (by rw [hg])
    have hR := h.toSCore.regs_congr hS hlo hlo'
    obtain ⟨b2, args2, regs2, -, hga2, -, -, -⟩ := enterBlock_ok he1'
    have hdm := catch?_mem hd
    have hga' : Frame.getMany { fr' with regs := regs' } bc'.args = .ok args2 := by
      refine getMany_pw2 (A := { fr with regs }) (hpw.imp fun x y hxy => ?_) hga2
      simp only
      rcases hxy with ⟨v, hv, hx, hy⟩ | ⟨i, hx, hy⟩
      · rw [hx, hy]
        obtain ⟨h1, h2, h3⟩ := hvals d hdm v hv
        rw [hlo' _ h3, hlo _ h2, h1]
      · rw [hx, hy, hW i, hW' i]
        split
        · rfl
        · exact (hw i).symm
    have hsucc' : bc.block ∈ termSuccs fr.term := by
      rw [tryHandler_block hbc]; exact hsucc d hdm
    obtain ⟨fr1', he1'', j, hr1⟩ := hR.enter hS hs ht0 hsucc' he1'
      (by show bc'.block ∈ termSuccs fr'.term; rw [hterm, termSuccs_mapTerm, hblk]; exact hsucc')
      hblk hga2 hga'
    exact ⟨fr1', (enterBlock_bt { fr' with regs := regs' } [] (.jump bc') bc').trans he1'',
      .inl ⟨j, 0, 0, hr1⟩⟩

variable (hF : SimpFacts f fi cert)
include hF

/-- `SSR` with windows and handler edges: the obligations of `IsSimWU`. -/
theorem SSR.isSimWU (hsd : g.sigDecls = f.sigDecls) : IsSimWU syms (SSR f g fi cert syms) where
  toIsSim := SSR.isSim hS hF
  ci := (SSR.isSimW hS hF hsd).ci
  tc := by
    refine ⟨?_, ?_⟩
    · rintro fr fr' m fn args et n base bc ext vals (⟨bi, k, k', h⟩ | ⟨c, -, -, -, htr, -⟩)
        hI hI' hw hm hb ht htc hca
      · obtain ⟨ht0, hterm, hops⟩ := h.atKept hS hb (by rw [ht]; rfl)
        rw [ht] at hterm hops
        have hf := h.invf.func
        have hg := h.invg.func
        obtain ⟨e0, s0, he0, hs0, hc0, rfl, hbc, rfl⟩ := tcArgs_ok.1 htc
        obtain ⟨bc', hbc', -, -⟩ := tryNormal_pair cert.subst.step (et := et)
          (et' := et.mapVals cert.subst.step) rfl (b2 := fr'.func.freshValue) hbc
        have htc' : tcArgs fr' fn (et.mapVals cert.subst.step) =
            .ok (e0.sig.returns.length, fr'.func.freshValue, bc') := by
          refine tcArgs_ok.2 ⟨e0, s0, ?_, ?_, hc0, rfl, hbc', rfl⟩
          · rw [← he0]; simp only [Function.extern?, hg, hf, hS.externs]
          · rw [← hs0, hg, hf, hsd]; rfl
        have hca' : callArgs fr' fn (args.map cert.subst.step) = .ok (ext, vals) :=
          Res.norm_eq_ok (callArgs_rename (by rw [hg, hf, hS.externs])
            (fun x hx => (hops x (by simp [termOperands, hx])).1)) hca
        refine ⟨fr', fn, args.map cert.subst.step, et.mapVals cert.subst.step, _, bc', .refl _ _,
          ht0, hterm, htc', hca', ?_, ?_⟩
        · exact h.tcont hS hb ht0 (by rw [hterm, ht]) (by rw [ht]; exact normal_succ hbc)
            (fun x hx => hops x (normal_vals_sub x hx)) hw hbc hbc'
        · exact h.hcont hS hb ht0 (by rw [hterm, ht]) (fun d hd => by rw [ht]; exact handler_succ hd)
            (fun d hd x hx => hops x (by simp [termOperands, handler_vals hd hx])) hw
      · rw [htr] at ht; cases ht
    · rintro fr fr' m callee args et n base bc d a vals (⟨bi, k, k', h⟩ | ⟨c, -, -, -, htr, -⟩)
        hI hI' hw hm hb ht htc hca
      · obtain ⟨ht0, hterm, hops⟩ := h.atKept hS hb (by rw [ht]; rfl)
        rw [ht] at hterm hops
        have hf := h.invf.func
        have hg := h.invg.func
        obtain ⟨s0, hs0, rfl, hbc, rfl⟩ := ticArgs_ok.1 htc
        obtain ⟨bc', hbc', -, -⟩ := tryNormal_pair cert.subst.step (et := et)
          (et' := et.mapVals cert.subst.step) rfl (b2 := fr'.func.freshValue) hbc
        have htc' : ticArgs fr' (et.mapVals cert.subst.step) =
            .ok (s0.returns.length, fr'.func.freshValue, bc') :=
          ticArgs_ok.2 ⟨s0, by rw [← hs0, hg, hf, hsd]; rfl, rfl, hbc', rfl⟩
        have hca' : ciArgs fr' (et.mapVals cert.subst.step).sig (cert.subst.step callee)
            (args.map cert.subst.step) = .ok (d, a, vals) :=
          ciArgs_rename (by rw [hg, hf, hsd])
            (fun x hx => (hops x (by
              simp only [List.mem_cons] at hx
              rcases hx with rfl | hx
              · simp [termOperands]
              · simp [termOperands, hx])).1) hca
        refine ⟨fr', cert.subst.step callee, args.map cert.subst.step,
          et.mapVals cert.subst.step, _, bc', .refl _ _, ht0, hterm, htc', hca', ?_, ?_⟩
        · exact h.tcont hS hb ht0 (by rw [hterm, ht]) (by rw [ht]; exact normal_succ hbc)
            (fun x hx => hops x (normal_vals_sub' x hx)) hw hbc hbc'
        · exact h.hcont hS hb ht0 (by rw [hterm, ht]) (fun d hd => by rw [ht]; exact handler_succ hd)
            (fun d hd x hx => hops x (by simp [termOperands, handler_vals hd hx])) hw
      · rw [htr] at ht; cases ht

end

/-- **The simplify validator is sound with handler edges** (for outputs keeping the signature
declarations). -/
theorem simpOk_simU {f g : Function} {fi : Info} {cert : SimpCert} (hf : check f = .ok fi)
    (h : simpOk f g fi cert = true) (hF : SimpFacts f fi cert) (hsd : g.sigDecls = f.sigDecls) :
    FunSimU f g := by
  have hS := simpOk_facts hf h
  refine FunSimU.ofWU hS.name hS.sig hS.slots hS.externs fun syms =>
    ⟨_, SSR.isSimWU hS hF hsd, fun b hb => ?_⟩
  have hb0 : f.blocks[0]? = some b := by
    simpa [Function.entry?, List.head?_eq_getElem?] using hb
  obtain ⟨b', lg, hb0', -, -, hpar, -, -, -, -, -, hps, -⟩ := hS.blocks 0 b hb0
  refine ⟨b', by simpa [Function.entry?, List.head?_eq_getElem?] using hb0', hpar,
    fun args regs slots hty hr hsl => .inl ⟨0, 0, 0, ⟨⟨Inv.entry hS.wff hb hty hr hsl, ?_, ?_, rfl⟩,
      fun lg hlg => by simp [outs]⟩⟩⟩
  · rw [← hpar] at hty hr
    exact Inv.entry hS.wfg (by simpa [Function.entry?, List.head?_eq_getElem?] using hb0') hty hr
      (by rw [hsl, hS.slots])
  · intro v hv
    have hd := avail_entry hS.wff hv
    obtain ⟨b1, p, hb1, hp, hpv⟩ := site_param' hS.wff hd
    rw [hb0] at hb1; cases hb1
    have hσv : cert.subst.step v = v := by rw [← hpv]; exact step_of_not_contains (hps p hp).2.2
    have hgs : (wfData g (gInfo fi cert)).dm v = some (0, 0) := by
      rw [← hpv]; exact site_param hS.wfg hb0' (by rw [hpar]; exact hp)
    rw [hσv]
    refine ⟨⟨0, 0, hgs, .inl ⟨rfl, Nat.le_refl _⟩⟩, rfl, ?_⟩
    intro d t hdt
    rw [hd] at hdt; simp only [Option.some.injEq, Prod.mk.injEq] at hdt
    obtain ⟨rfl, -⟩ := hdt
    exact ⟨0, 0, by rw [hσv]; exact hgs, .refl _⟩

end Opt
