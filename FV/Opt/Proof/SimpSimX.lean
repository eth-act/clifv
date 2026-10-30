import FV.Opt.Proof.SimpSim
import FV.Opt.Proof.GvnEditX

/-!
# The simplify validator is sound, `call_indirect` and `try_call` included (`Opt.simpOk_simX`)

`Opt.simpOk_sim` (`FV/Opt/Proof/SimpSim.lean`) with the obligations of `IsSimX`. A well-formed
function has no `call_indirect`; a `try_call`/`try_call_indirect` terminator is not a branch,
so the simplifier keeps it renamed (`termOk` without a change, no extra statements) and the
frames enter the same normal-return successor with the same arguments (`SCore.enter`), the
call's results bound at each side's fresh value with equal windows (`Win`).
-/

namespace Opt

open Clif

section
variable {f g : Function} {fi : Info} {cert : SimpCert} (hS : SOk f g fi cert)
  {syms : String → Option Nat}
include hS

/-- Registers from the fresh values on are not read. -/
theorem SCore.regs_congr {fr fr' : Frame} {bi k k' : Nat} (h : SCore f g fi cert syms fr fr' bi k k')
    {r r' : Regs} (hr : ∀ v < f.freshValue, r v = fr.regs v)
    (hr' : ∀ v < g.freshValue, r' v = fr'.regs v) :
    SCore f g fi cert syms { fr with regs := r } { fr' with regs := r' } bi k k' where
  invf := h.invf.regs_congr hS.wff hr
  invg := h.invg.regs_congr hS.wfg hr'
  agree v hv := by
    obtain ⟨ha, he, hsa⟩ := h.agree v hv
    refine ⟨ha, ?_, hsa⟩
    show r' (cert.subst.step v) = r v
    rw [hr' _ (avail_lt hS.wfg ha), hr _ (avail_lt hS.wff hv)]
    exact he
  slots := h.slots

/-- At a terminator that is not a branch: kept renamed, no extra statements, operands read
alike. -/
theorem SRel.atKept {fr fr' : Frame} {bi k k' : Nat} (h : SRel f g fi cert syms fr fr' bi k k')
    (hs : fr.body = []) (hB : isBranch fr.term = false) :
    fr'.body = [] ∧ fr'.term = mapTerm cert.subst.step fr.term ∧
      ∀ x ∈ termOperands fr.term, fr'.regs (cert.subst.step x) = fr.regs x ∧
        x < f.freshValue ∧ cert.subst.step x < g.freshValue := by
  obtain ⟨b, b', lg, hb, hb', hlg, hterm, ht', hlt, htok, hbody, hkk, hid, hpar⟩ := h.atEnd hS hs
  have hbr : isBranch lg.term = isBranch b.term := by rw [hlt]; cases b.term <;> rfl
  have hch : lg.changed = false := by
    cases hc : lg.changed
    · rfl
    · simp only [SimpCtx.termOk, hc, ite_true, Bool.and_eq_true] at htok
      rw [hbr, ← hterm, hB] at htok; exact absurd htok.1.1 (by simp)
  simp only [SimpCtx.termOk, hch, Bool.false_eq_true, ite_false, Bool.and_eq_true,
    Array.isEmpty_iff, beq_iff_eq] at htok
  obtain ⟨hex, hte⟩ := htok
  refine ⟨by rw [hbody, hex]; rfl, by rw [ht', hte, hlt, mapTerm_step_idem hS.chain, hterm],
    fun x hx => ?_⟩
  rw [hterm] at hx
  have hav := hS.wff.termUses bi b hb x hx
  rw [← hkk] at hav
  obtain ⟨hav', heq, -⟩ := h.agree x hav
  exact ⟨heq, avail_lt hS.wff hav, avail_lt hS.wfg hav'⟩

/-- The post-call frames of a `try_call`. -/
theorem SRel.tcont {fr fr' : Frame} {bi k k' : Nat} {n : Nat} {et : ExnTable} {bc bc' : BlockCall}
    {rtys : List Ty} (h : SRel f g fi cert syms fr fr' bi k k') (hs : fr.body = [])
    (ht0 : fr'.body = []) (hterm : fr'.term = mapTerm cert.subst.step fr.term)
    (hsucc : bc.block ∈ termSuccs fr.term)
    (hvals : ∀ x ∈ et.normal.vals, fr'.regs (cert.subst.step x) = fr.regs x ∧ x < f.freshValue ∧
      cert.subst.step x < g.freshValue)
    (hw : Win fr fr') (hbc : tryNormal et fr.func.freshValue = .ok bc)
    (hbc' : tryNormal (et.mapVals cert.subst.step) fr'.func.freshValue = .ok bc') :
    TCont (SSR f g fi cert syms) fr (tryRets n fr.func.freshValue) bc fr'
      (tryRets n fr'.func.freshValue) bc' rtys := by
  have hf := h.invf.func
  have hg := h.invg.func
  intro vs regs _ hset
  obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs) (xs := tryRets n fr'.func.freshValue)
    (vs := vs) (by have := (setMany_spec hset).1; simp only [tryRets, List.length_map,
      List.length_range] at this ⊢; exact this)
  refine ⟨regs', hset', fun fr1 he1 => ?_⟩
  have hW := setMany_tryRets hset
  have hW' := setMany_tryRets hset'
  have hlo : ∀ v < f.freshValue, regs v = fr.regs v := by
    intro v hv
    refine ((setMany_spec hset).2 v).1 fun hm => ?_
    obtain ⟨j, -, he⟩ := List.mem_map.1 hm
    have he' : fr.func.freshValue + j = v := he
    rw [hf] at he'
    exact no_window' he' hv
  have hlo' : ∀ v < g.freshValue, regs' v = fr'.regs v := by
    intro v hv
    refine ((setMany_spec hset').2 v).1 fun hm => ?_
    obtain ⟨j, -, he⟩ := List.mem_map.1 hm
    have he' : fr'.func.freshValue + j = v := he
    rw [hg] at he'
    exact no_window' he' hv
  have hR := h.toSCore.regs_congr hS hlo hlo'
  obtain ⟨b2, args2, regs2, -, hga2, -, -, -⟩ := enterBlock_ok he1
  obtain ⟨bc2, hbc2, hblk, hpw⟩ := tryNormal_pair cert.subst.step (et := et)
    (et' := et.mapVals cert.subst.step) rfl (b2 := fr'.func.freshValue) hbc
  rw [hbc'] at hbc2; cases hbc2
  have hga' : Frame.getMany { fr' with regs := regs' } bc'.args = .ok args2 := by
    refine getMany_pw2 (A := { fr with regs }) (hpw.imp fun x y hxy => ?_) hga2
    simp only
    rcases hxy with ⟨v, hv, hx, hy⟩ | ⟨i, hx, hy⟩
    · rw [hx, hy]
      obtain ⟨h1, h2, h3⟩ := hvals v hv
      rw [hlo' _ h3, hlo _ h2, h1]
    · rw [hx, hy, hW i, hW' i]
      split
      · rfl
      · exact (hw i).symm
  obtain ⟨fr1', he1', j, hr1⟩ := hR.enter hS hs ht0 hsucc he1
    (by show bc'.block ∈ termSuccs fr'.term; rw [hterm, termSuccs_mapTerm, hblk]; exact hsucc)
    hblk hga2 hga'
  exact ⟨fr1', he1', .inl ⟨j, 0, 0, hr1⟩⟩

variable (hF : SimpFacts f fi cert)
include hF

/-- `SSR` with windows: the obligations of `IsSimW`. -/
theorem SSR.isSimW (hsd : g.sigDecls = f.sigDecls) : IsSimW syms (SSR f g fi cert syms) where
  toIsSim := SSR.isSim hS hF
  ci := by
    rintro fr fr' m st rest sig callee args d a vals (⟨bi, k, k', h⟩ | ⟨c, -, -, -, -, hp, -⟩)
      - - - hm hb hi hca
    · exfalso
      obtain ⟨b, hbi, h1, -, -⟩ := h.invf.block
      rw [h1] at hb
      obtain ⟨hk, -, -⟩ := drop_eq_cons hb
      exact hS.wff.noCI hbi hk sig callee args hi
    · exfalso
      have := hp st (by rw [hb]; simp)
      rw [hi] at this; cases this
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
          ht0, hterm, htc', hca', ?_⟩
        exact h.tcont hS hb ht0 (by rw [hterm, ht]) (by rw [ht]; exact normal_succ hbc)
          (fun x hx => hops x (normal_vals_sub x hx)) hw hbc hbc'
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
          et.mapVals cert.subst.step, _, bc', .refl _ _, ht0, hterm, htc', hca', ?_⟩
        exact h.tcont hS hb ht0 (by rw [hterm, ht]) (by rw [ht]; exact normal_succ hbc)
          (fun x hx => hops x (normal_vals_sub' x hx)) hw hbc hbc'
      · rw [htr] at ht; cases ht

end

/-- **The simplify validator is sound**, `call_indirect` and `try_call` included (for outputs
keeping the signature declarations). -/
theorem simpOk_simX {f g : Function} {fi : Info} {cert : SimpCert} (hf : check f = .ok fi)
    (h : simpOk f g fi cert = true) (hF : SimpFacts f fi cert) (hsd : g.sigDecls = f.sigDecls) :
    FunSimX f g := by
  have hS := simpOk_facts hf h
  refine FunSimX.ofW hS.name hS.sig hS.slots hS.externs fun syms =>
    ⟨_, SSR.isSimW hS hF hsd, fun b hb => ?_⟩
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
