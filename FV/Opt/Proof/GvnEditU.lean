import FV.Opt.Proof.GvnEditX
import FV.Opt.Proof.SimWinU

/-!
# The edit validator is sound with handler edges (`Opt.editOk_simU`, S10f #233)

`Opt.editOk_simX` (`FV/Opt/Proof/GvnEditX.lean`, GVN, DCE and LICM) with the handler edges of
`IsSimU`: a `try_call`/`try_call_indirect` terminator is kept renamed (`mapTerm σ`), so its
exception table is `et.mapVals σ`: the same tags catch the same exceptions (`catch?_mapVals`),
the handler successor is the same block, its arguments the renamed values (read alike, the
values the handler's operands name) or the payload bound at each side's fresh value with equal
windows (`ER.hcont`, as `ER.tcont` for the normal-return successor).
-/

namespace Opt

open Clif

section
variable {σ : ValueId → ValueId} {f g : Function} {Df Dg : WfData} (hE : EditFacts σ f g Df Dg)
  {syms : String → Option Nat}
include hE

/-- The handler edges of a `try_call` and its renaming. -/
theorem ER.hcont {fr fr'' : Frame} {bi k k'' : Nat} {et : ExnTable}
    (h : ERel σ f g Df Dg syms fr fr'' bi k k'') (hs : fr.body = []) (ht0 : fr''.body = [])
    (hsucc : ∀ d ∈ et.handlers, d.block ∈ termSuccs fr.term)
    (hvals : ∀ d ∈ et.handlers, ∀ x ∈ d.vals, fr''.regs (σ x) = fr.regs x ∧ x < f.freshValue ∧
      σ x < g.freshValue)
    (hw : Win fr fr'') :
    HCont (ER σ f g Df Dg syms) fr et fr'' (et.mapVals σ) := by
  have hf := h.invf.func
  have hg := h.invg.func
  intro e
  refine ⟨fun hn => ?_, fun fr1 hc => ?_⟩
  · rw [catchIn_eq_none] at hn ⊢
    rw [catch?_mapVals, hn]; rfl
  · obtain ⟨d, bc, regs, hd, hbc, hset, rfl⟩ := catchIn_ok hc
    obtain ⟨bc', hbc', hblk, hpw⟩ := tryHandler_pair σ (b2 := fr''.func.freshValue) hbc
    obtain ⟨regs', hset'⟩ := setMany_len (r := fr''.regs)
      (xs := (List.range e.payload.length).map (fr''.func.freshValue + ·)) (vs := e.payload)
      (by simp)
    have hd' : (et.mapVals σ).catch? e = some (d.mapVals σ) := by rw [catch?_mapVals, hd]; rfl
    refine ⟨_, catchIn_of hd' hbc' hset', rfl, rfl, bc, bc', rfl, rfl, fun fr1 he1 => ?_⟩
    have he1' : enterBlock { fr with regs } bc = .ok fr1 := by
      rw [← enterBlock_bt { fr with regs } [] (.jump bc)]; exact he1
    have hW := setMany_tryRets (n := e.payload.length) (W := fr.func.freshValue) hset
    have hW' := setMany_tryRets (n := e.payload.length) (W := fr''.func.freshValue) hset'
    have hlo : ∀ v < f.freshValue, regs v = fr.regs v := catch_regs_lo hset (by rw [hf])
    have hlo' : ∀ v < g.freshValue, regs' v = fr''.regs v := catch_regs_lo hset' (by rw [hg])
    have hR := h.regs_congr hE hlo hlo'
    obtain ⟨b2, args2, regs2, -, hga2, -, -, -⟩ := enterBlock_ok he1'
    have hdm := catch?_mem hd
    have hga' : Frame.getMany { fr'' with regs := regs' } bc'.args = .ok args2 := by
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
    obtain ⟨fr1', he1'', hr1⟩ := hR.enterG hE hs ht0 hsucc' hblk hga2 hga' he1'
    exact ⟨fr1', (enterBlock_bt { fr'' with regs := regs' } [] (.jump bc') bc').trans he1'', hr1⟩

/-- `ER` with windows and handler edges: the obligations of `IsSimWU`. -/
theorem ER.isSimWU (hsd : g.sigDecls = f.sigDecls) : IsSimWU syms (ER σ f g Df Dg syms) where
  toIsSim := ER.isSim hE
  ci := (ER.isSimW hE hsd).ci
  tc := by
    refine ⟨?_, ?_⟩
    · rintro fr fr' m fn args et n base bc ext vals ⟨bi, k, k', h⟩ hI hI' hw hm hb ht htc hca
      obtain ⟨fr'', k'', hst, h2, ht0, hterm, hops⟩ := ER.atTerm hE h hm hb
      rw [ht] at hterm hops
      have hf := h.invf.func
      have hg := h2.invg.func
      obtain ⟨e0, s0, he0, hs0, hc0, rfl, hbc, rfl⟩ := tcArgs_ok.1 htc
      obtain ⟨bc', hbc', -, -⟩ := tryNormal_pair σ (et := et) (et' := et.mapVals σ) rfl
        (b2 := fr''.func.freshValue) hbc
      have htc' : tcArgs fr'' fn (et.mapVals σ) =
          .ok (e0.sig.returns.length, fr''.func.freshValue, bc') := by
        refine tcArgs_ok.2 ⟨e0, s0, ?_, ?_, hc0, rfl, hbc', rfl⟩
        · rw [← he0]; simp only [Function.extern?, hg, hf, hE.externs]
        · rw [← hs0, hg, hf, hsd]; rfl
      have hca' : callArgs fr'' fn (args.map σ) = .ok (ext, vals) :=
        Res.norm_eq_ok (callArgs_rename (by rw [hg, hf, hE.externs])
          (fun x hx => (hops x (by simp [termOperands, hx])).1)) hca
      have hw' : Win fr fr'' := by
        obtain ⟨-, hf2, hw2⟩ := LStar.win hI' hst
        intro i; rw [hf2, hw2 i]; exact hw i
      refine ⟨fr'', fn, args.map σ, et.mapVals σ, _, bc', hst, ht0, hterm, htc', hca', ?_, ?_⟩
      · exact ER.tcont hE h2 hb ht0 (by rw [ht]; exact normal_succ hbc)
          (fun x hx => hops x (normal_vals_sub x hx)) hw' hbc hbc'
      · exact ER.hcont hE h2 hb ht0 (fun d hd => by rw [ht]; exact handler_succ hd)
          (fun d hd x hx => hops x (by simp [termOperands, handler_vals hd hx])) hw'
    · rintro fr fr' m callee args et n base bc d a vals ⟨bi, k, k', h⟩ hI hI' hw hm hb ht htc hca
      obtain ⟨fr'', k'', hst, h2, ht0, hterm, hops⟩ := ER.atTerm hE h hm hb
      rw [ht] at hterm hops
      have hf := h.invf.func
      have hg := h2.invg.func
      obtain ⟨s0, hs0, rfl, hbc, rfl⟩ := ticArgs_ok.1 htc
      obtain ⟨bc', hbc', -, -⟩ := tryNormal_pair σ (et := et) (et' := et.mapVals σ) rfl
        (b2 := fr''.func.freshValue) hbc
      have htc' : ticArgs fr'' (et.mapVals σ) =
          .ok (s0.returns.length, fr''.func.freshValue, bc') :=
        ticArgs_ok.2 ⟨s0, by rw [← hs0, hg, hf, hsd]; rfl, rfl, hbc', rfl⟩
      have hca' : ciArgs fr'' (et.mapVals σ).sig (σ callee) (args.map σ) = .ok (d, a, vals) :=
        ciArgs_rename (by rw [hg, hf, hsd])
          (fun x hx => (hops x (by
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · simp [termOperands]
            · simp [termOperands, hx])).1) hca
      have hw' : Win fr fr'' := by
        obtain ⟨-, hf2, hw2⟩ := LStar.win hI' hst
        intro i; rw [hf2, hw2 i]; exact hw i
      refine ⟨fr'', σ callee, args.map σ, et.mapVals σ, _, bc', hst, ht0, hterm, htc', hca', ?_, ?_⟩
      · exact ER.tcont hE h2 hb ht0 (by rw [ht]; exact normal_succ hbc)
          (fun x hx => hops x (normal_vals_sub' x hx)) hw' hbc hbc'
      · exact ER.hcont hE h2 hb ht0 (fun d hd => by rw [ht]; exact handler_succ hd)
          (fun d hd x hx => hops x (by simp [termOperands, handler_vals hd hx])) hw'

end

/-- **The edit validator is sound with handler edges** (for outputs keeping the signature
declarations). -/
theorem editOk_simU {σ : ValueId → ValueId} {f g : Function} {fi gi : Info}
    (hf : check f = .ok fi) (hg : check g = .ok gi) (h : editOk σ f g fi gi = true)
    (hsd : g.sigDecls = f.sigDecls) : FunSimU f g := by
  have hE := editOk_facts hf hg h
  refine FunSimU.ofWU hE.name hE.sig hE.slots hE.externs fun syms =>
    ⟨_, ER.isSimWU hE hsd, fun b hb => ?_⟩
  have hb0 : f.blocks[0]? = some b := by
    simpa [Function.entry?, List.head?_eq_getElem?] using hb
  obtain ⟨b', hb0', hid, hpar, hσp, -, hal⟩ := hE.blocks 0 b hb0
  refine ⟨b', by simpa [Function.entry?, List.head?_eq_getElem?] using hb0', hpar,
    fun args regs slots hty hr hsl => ⟨0, 0, 0, Inv.entry hE.wff hb hty hr hsl, ?_, ?_, ?_, rfl⟩⟩
  · rw [← hpar] at hty hr
    exact Inv.entry hE.wfg (by simpa [Function.entry?, List.head?_eq_getElem?] using hb0') hty hr
      (by rw [hsl, hE.slots])
  · intro v hv hrep
    obtain ⟨b1, p, hb1, hp, hpv⟩ := site_param' hE.wff (avail_entry hE.wff hv)
    rw [hb0] at hb1; cases hb1
    have hσv : σ v = v := by rw [← hpv]; exact hσp p hp
    rw [hσv]
    refine ⟨⟨0, 0, ?_, .inl ⟨rfl, Nat.le_refl _⟩⟩, rfl⟩
    rw [← hpv]; exact site_param hE.wfg hb0' (by rw [hpar]; exact hp)
  · intro b0 b0' h0 h0'
    rw [hb0] at h0; cases h0
    rw [hb0'] at h0'; cases h0'
    simpa using hal

end Opt
