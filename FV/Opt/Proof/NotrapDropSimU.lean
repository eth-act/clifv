import FV.Opt.Proof.NotrapDropSim
import FV.Opt.Proof.SimWinU

/-!
# Dropping unused `notrap` loads with handler edges: `Opt.NotrapDrop.run_simU` (option D, #1017)

`run_simX` (`FV/Opt/Proof/NotrapDropSim.lean`) with the handler edges of `try_call`
(`Opt.FunSimU`, the runs with unwinding): the pass keeps every terminator, so a `try_call`'s
exception table is the same on both sides and catches alike; a handler binds the payload at each
side's fresh value (above `L`, `Facts.lt`), and its successor's arguments are values of the table
(in `L`, `Facts.terms`) or payload values, which agree.
-/

namespace Opt.NotrapDrop

open Clif Opt

/-- The values of a handler successor are values of the table. -/
theorem handler_vals_sub {et : ExnTable} {d : TryDest} (hd : d ∈ et.handlers) {v : ValueId}
    (hv : v ∈ d.vals) : v ∈ et.vals := by
  unfold ExnTable.handlers at hd
  obtain ⟨it, hit, hm⟩ := List.mem_filterMap.1 hd
  unfold ExnTable.vals
  refine List.mem_append_right _ (List.mem_flatMap.2 ⟨it, hit, ?_⟩)
  cases it with
  | tag n d' => simp only [Option.some.injEq] at hm; subst hm; exact hv
  | default d' => simp only [Option.some.injEq] at hm; subst hm; exact hv
  | context c => cases hm

section
variable {f : Function} {L : Std.HashSet ValueId} (hF : Facts f L)
include hF

/-- After a `try_call`'s callee unwinds: the same table catches alike, and the frames resumed at
the handler enter related blocks. -/
theorem NRel.hcont {fr fr' : Frame} (h : NRel f L fr fr') (hw : Win fr fr') {et : ExnTable}
    (hvals : ∀ v ∈ et.vals, L.contains v = true) : HCont (NRel f L) fr et fr' et := by
  intro e
  refine ⟨fun hn => ?_, fun fr1 hc => ?_⟩
  · rw [catchIn_eq_none] at hn ⊢; exact hn
  · obtain ⟨d, bc, regs, hd, hbc, hset, rfl⟩ := catchIn_ok hc
    have hdm := catch?_mem hd
    obtain ⟨bc2, hbc2, hblk, hpw⟩ := tryHandler_pair id (b2 := fr'.func.freshValue) hbc
    rw [mapVals_id] at hbc2
    obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs)
      (xs := (List.range e.payload.length).map (fr'.func.freshValue + ·)) (vs := e.payload)
      (by simp)
    refine ⟨_, catchIn_of hd hbc2 hset', rfl, rfl, bc, bc2, rfl, rfl, fun a1 he1 => ?_⟩
    have he1' : enterBlock { fr with regs } bc = .ok a1 := by
      rw [← enterBlock_bt { fr with regs } [] (.jump bc)]; exact he1
    have hbase : fr.func.freshValue = f.freshValue := by rw [h.func]
    have hbase' : fr'.func.freshValue = (dropWith f L).freshValue := by rw [h.func']
    have hlo : ∀ v, L.contains v = true → regs' v = regs v := by
      intro v hv
      have h1 := hF.lt v hv
      rw [catch_regs_lo hset' hbase' v h1,
        catch_regs_lo hset hbase v (Nat.lt_of_lt_of_le h1 hF.fresh), h.agree v hv]
    have hW := setMany_tryRets (n := e.payload.length) (W := fr.func.freshValue) hset
    have hW' := setMany_tryRets (n := e.payload.length) (W := fr'.func.freshValue) hset'
    have hargs : ({ fr' with regs := regs' } : Frame).getMany bc2.args =
        ({ fr with regs } : Frame).getMany bc.args := by
      cases hg : ({ fr with regs } : Frame).getMany bc.args with
      | ok vs1 =>
        refine getMany_pw2 (hpw.imp fun x y hp => ?_) hg
        rcases hp with ⟨v, hv, hx, hy⟩ | ⟨i, hx, hy⟩
        · rw [hx, hy]; exact hlo v (hvals v (handler_vals_sub hdm hv))
        · rw [hx, hy]
          show regs' (fr'.func.freshValue + i) = regs (fr.func.freshValue + i)
          rw [hW' i, hW i]
          split
          · rfl
          · exact (hw i).symm
      | trap c => exfalso; exact (Frame.getMany_ne_trap _ _ c).1 hg
      | stuck m =>
        exfalso
        simp only [enterBlock, Res.bind_eq_ok] at he1'
        obtain ⟨_, _, args, ha, _⟩ := he1'
        rw [hg] at ha; cases ha
    have hr : NRel f L { fr with regs } { fr' with regs := regs' } :=
      ⟨h.func, h.func', h.slots, h.body, h.term, h.pp, hlo⟩
    obtain ⟨b1, hb1, hr1⟩ := hr.enter hblk hargs he1'
    exact ⟨b1, (enterBlock_bt { fr' with regs := regs' } [] (.jump bc2) bc2).trans hb1, hr1⟩

theorem isSimWU (syms : String → Option Nat) : IsSimWU syms (NRel f L) where
  toIsSim := (isSimW hF syms).toIsSim
  ci := (isSimW hF syms).ci
  tc := {
    call := by
      intro fr fr' m fn args et n base bc ext vals h _ _ hw _ hb ht htc hca
      have hb' : fr'.body = [] := by rw [h.body, hb]; rfl
      have hops := h.termOps hF
      rw [ht] at hops
      have hterm : ∀ v ∈ termOperands (.tryCall fn args et), L.contains v = true := by
        obtain ⟨b, hbm, -, hterm⟩ := h.pp
        rw [ht] at hterm
        intro v hv; exact hF.terms b hbm v (hterm ▸ hv)
      obtain ⟨ext0, sig, he, hs, hc, rfl, hn, rfl⟩ := tcArgs_ok.1 htc
      obtain ⟨bc', hn', hk⟩ := h.tcont hF hw (fun v hv => hterm v (normal_vals_sub v hv))
        (n := ext0.sig.returns.length) hn
      have htc' : tcArgs fr' fn et = .ok (ext0.sig.returns.length, fr'.func.freshValue, bc') :=
        tcArgs_ok.2 ⟨ext0, sig, by rw [Function.extern?, h.externs]; exact he,
          by rw [h.sigDecls]; exact hs, hc, rfl, hn', rfl⟩
      have hca' : callArgs fr' fn args = callArgs fr fn args := by
        simp only [callArgs, Function.extern?, h.externs,
          getMany_congr (xs := args) (fun x hx => hops x (by simp [termOperands, hx]))]
      exact ⟨fr', fn, args, et, _, bc', .refl _ _, hb', (by rw [h.term, ht]), htc',
        (by rw [hca']; exact hca), hk _,
        h.hcont hF hw (fun v hv => hterm v (by simp [termOperands, hv]))⟩
    ind := by
      intro fr fr' m callee args et n base bc d a vals h _ _ hw _ hb ht htc hca
      have hb' : fr'.body = [] := by rw [h.body, hb]; rfl
      have hops := h.termOps hF
      rw [ht] at hops
      have hterm : ∀ v ∈ termOperands (.tryCallIndirect callee args et), L.contains v = true := by
        obtain ⟨b, hbm, -, hterm⟩ := h.pp
        rw [ht] at hterm
        intro v hv; exact hF.terms b hbm v (hterm ▸ hv)
      obtain ⟨sig, hs, rfl, hn, rfl⟩ := ticArgs_ok.1 htc
      obtain ⟨bc', hn', hk⟩ := h.tcont hF hw (fun v hv => hterm v (normal_vals_sub' v hv))
        (n := sig.returns.length) hn
      have htc' : ticArgs fr' et = .ok (sig.returns.length, fr'.func.freshValue, bc') :=
        ticArgs_ok.2 ⟨sig, by rw [h.sigDecls]; exact hs, rfl, hn', rfl⟩
      have hca' : ciArgs fr' et.sig callee args = ciArgs fr et.sig callee args := by
        simp only [ciArgs, h.sigDecls, Frame.get, hops callee (by simp [termOperands]),
          getMany_congr (xs := args) (fun x hx => hops x (by simp [termOperands, hx]))]
      exact ⟨fr', callee, args, et, _, bc', .refl _ _, hb', (by rw [h.term, ht]), htc',
        (by rw [hca']; exact hca), hk _,
        h.hcont hF hw (fun v hv => hterm v (by simp [termOperands, hv]))⟩ }

/-- **The output with the guard's facts simulates the input, handler edges included.** -/
theorem dropWith_simU : FunSimU f (dropWith f L) := by
  refine FunSimU.ofWU rfl rfl rfl rfl fun syms => ⟨NRel f L, isSimWU hF syms, fun b hb => ?_⟩
  refine ⟨fltB L b, by rw [dropWith_entry?, hb]; rfl, rfl, fun args regs slots _ _ _ => ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨b, List.mem_of_mem_head? hb, List.suffix_refl _, rfl⟩,
    fun _ _ => rfl⟩

end

/-- **The pass simulates every function, handler edges included.** -/
theorem run_simU (f : Function) : FunSimU f (run f) := by
  unfold run
  dsimp only
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    exact dropWith_simU (facts_of h.1.2 h.2)
  · exact FunSimU.refl f

end Opt.NotrapDrop
