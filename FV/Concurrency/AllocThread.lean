import FV.Concurrency.PrepThread
import FV.Backend.Proof.RegallocSound

/-!
# Register allocation with interference (T2h, #311, layer 4a)

The register level (`docs/plans/atomics.md` §3e, layer 4) has two parts: the allocated code's
abstract semantics (`Backend.Proof.MStep`: the location store, moves, the instructions under the
same instruction semantics `sem` as VCode) against VCode, and the Arm machine against the
allocated code. This file is the first, **backward and with interference**: the allocation
checker's simulation (`checkAlloc_sound`, `sim_step_at`: every step of the allocated code is a
move or matched by one VCode step on the same world) lifted to the thread semantics, in which
reads return any bytes:

* `MTStep`: a step of the allocated code with its memory events: an instruction item's events are
  its precise footprint `ev` on the world patched with the read events' bytes (uses read from the
  item's locations), a move has none; `MTRun`: runs;
* `alloc_back`: a step from matched configurations (`Match`, the checker's relation, on the same
  world) is a move (no event, the match kept) or matched by a VCode thread step with the same
  events (the uses are equal, `op_sound`);
* **`alloc_refines`**: if `checkAlloc vc rf` accepts, a run of the allocated code from the entry,
  reading any bytes, is realized by a VCode thread run from the entry with the same events up to
  the moves (`PrepThread.Thin`, hence `ThreadRefine.Refines`), returning (trapping) with the same
  values and world when it does.
-/

namespace Concurrency.AllocThread

open Arm ArmFoot ArmThread Backend Backend.Proof VCodeThread ThreadRefine PrepThread

/-- The uses of an instruction item: the values of its use operands' locations. -/
abbrev itemUses (ops : Array Operand) (allocs : Array Loc) (m : Loc → CV) : List CV :=
  ((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)

/-- **One step of the allocated code with its memory events.** -/
inductive MTStep (vc : VCode) (rf : RFunc) (sem : ISem CV ArmState) (keep : Reg → CV → CV)
    (ev : MInst → List CV → ArmState → List Ev) :
    MConf CV ArmState → List Ev → MConf CV ArmState → Prop
  | move {b src dst its m w} :
      MTStep vc rf sem keep ev (.run ⟨b, .move src dst :: its, m, w⟩) []
        (.run ⟨b, its, upd m dst (m src), w⟩)
  | op {b k allocs its m w vb i ops evs c'} :
      vc.blocks[b]? = some vb → vb.insts[k]? = some i → i.operands = .ok ops →
      evs = ev i (itemUses ops allocs m) (patch evs w) →
      IFoot sem i (itemUses ops allocs m) (patch evs w) evs →
      MStep vc sem keep rf (.run ⟨b, .op k allocs :: its, m, patch evs w⟩) c' →
      MTStep vc rf sem keep ev (.run ⟨b, .op k allocs :: its, m, w⟩) evs c'

/-- Runs of the allocated code with their events. -/
inductive MTRun (vc : VCode) (rf : RFunc) (sem : ISem CV ArmState) (keep : Reg → CV → CV)
    (ev : MInst → List CV → ArmState → List Ev) :
    MConf CV ArmState → List (List Ev) → MConf CV ArmState → Prop
  | nil {c} : MTRun vc rf sem keep ev c [] c
  | cons {c c' c'' evs tr} : MTStep vc rf sem keep ev c evs c' → MTRun vc rf sem keep ev c' tr c'' →
      MTRun vc rf sem keep ev c (evs :: tr) c''

section
variable {vc : VCode} {rf : RFunc} {sem : ISem CV ArmState} {keep : Reg → CV → CV}
  {ev : MInst → List CV → ArmState → List Ev} {c : CheckCtx} {ins : Array (Option AState)}
  {r₀ : Reg → CV} {a0 : AState}

/-- **The backward step of register allocation**: from matched configurations, a step of the
allocated code is a move (no event, the match kept) or is matched by a VCode thread step with the
same events. -/
theorem alloc_back (hc : CheckedAt vc rf c ins a0) {ms : MState CV ArmState} {vs : VState CV ArmState}
    {evs : List Ev} {c' : MConf CV ArmState} (hm : MatchRun c ins keep r₀ ms vs)
    (hs : MTStep vc rf sem keep ev (.run ms) evs c') :
    (evs = [] ∧ ∃ ms', c' = .run ms' ∧ MatchRun c ins keep r₀ ms' vs) ∨
      ∃ v', VTStep vc sem ev (.run vs) evs v' ∧ Match c ins keep r₀ c' v' := by
  obtain ⟨b, its, m, w⟩ := ms
  obtain ⟨b', k, ρ, w''⟩ := vs
  cases hs with
  | move =>
    obtain ⟨hb, hw, vb, a, out, hvb, hrun, hinv, hedges⟩ := hm
    obtain ⟨-, hrun'⟩ := runItems_move hrun
    exact .inl ⟨rfl, _, rfl, hb, hw, vb, _, out, hvb, hrun', Inv_move _ _ hinv, hedges⟩
  | @op _ k0 allocs its _ _ vb0 i ops _ _ hvb0 hi hops hevs hfoot hst =>
    obtain ⟨hb, hw, vb, a, out, hvb, hrun, hinv, hedges⟩ := hm
    simp only at hb hw hvb hrun hinv hedges
    subst hb hw
    obtain ⟨-, hk, i', ops', a', hi', hops', hstep, hrun'⟩ := runItems_op hrun
    subst hk
    have hvbV : vc.blocks[b]? = some vb := by rw [← hc.vc_eq]; exact hvb
    rw [hvbV] at hvb0; cases hvb0
    rw [hi] at hi'; cases hi'
    rw [hops] at hops'; cases hops'
    cases hst with
    | @op _ _ _ _ _ _ _ _ _ outs outs' w' ctl m2 _ hvb1 hi1 hops1 hsz hsem hlen hho hclob hnext =>
      rw [hvbV] at hvb1; cases hvb1
      rw [hi] at hi1; cases hi1
      rw [hops] at hops1; cases hops1
      obtain ⟨_, huse, hinv', hret⟩ := op_sound hstep hinv hlen hho hclob
      rw [huse] at hsem hnext
      have hevs' : evs = ev i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) (patch evs w) := by
        rw [← huse]; exact hevs
      have hfoot' : IFoot sem i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) (patch evs w)
          evs := by rw [← huse]; exact hfoot
      have hlen' : outs.length = (ops.toList.filter Operand.isDef).length := by
        rw [hlen, ← pairs_fst hsz.symm, List.length_map]
      refine .inr ?_
      cases hnext with
      | next hk1 =>
        rw [tryForget_of_ne (ctl := .next) (fun _ e => nomatch e)] at hinv'
        exact ⟨_, .mk hvbV hi hops hevs' hfoot' (VStep.step hvbV hi hops hsem hlen' (VNext.next hk1)),
          rfl, rfl, _, _, out, hvb, hrun', hinv', hedges⟩
      | ret hus =>
        rw [tryForget_of_ne (ctl := .ret) (fun _ e => nomatch e)] at hinv'
        exact ⟨_, .mk hvbV hi hops hevs' hfoot' (VStep.step hvbV hi hops hsem hlen' (VNext.ret hus)),
          rfl, rfl, fun r hr => (hinv' _ _ (hret _ hus r hr)).2⟩
      | halt =>
        exact ⟨_, .mk hvbV hi hops hevs' hfoot' (VStep.step hvbV hi hops hsem hlen' VNext.halt), rfl⟩
      | goto hk1 hsucc hitems =>
        have hits : its = [] := by
          cases its with
          | nil => rfl
          | cons it its =>
            cases it with
            | move => exact absurd hk1 (runItems_move hrun').1
            | op => exact absurd hk1 (runItems_op hrun').1
        subst hits
        obtain ⟨_, rfl⟩ := runItems_nil hrun'
        obtain ⟨preds, hcfg⟩ := hc.cfg
        obtain ⟨e, a'', hedge, hins, hle⟩ := hedges _ (succOf_mem hcfg hsucc)
        have hcfg' : c.vc.cfg = .ok (c.succs, preds) := by rw [hc.vc_eq]; exact hcfg
        have hinvF := edgeForget_inv hcfg' hvb hi hk1 hops (by rw [hc.vc_eq]; exact hsucc) hinv'
        obtain ⟨ρ', henv, hinve⟩ := edge_ok hedge hinvF
        rw [hc.vc_eq] at henv
        obtain ⟨items', hitems', hmr⟩ := enter_block_at keep hc (w := w') (edgeEnv_lt henv) hins hle
          hinve
        rw [hitems] at hitems'
        cases hitems'
        exact ⟨_, .mk hvbV hi hops hevs' hfoot'
          (VStep.step hvbV hi hops hsem hlen' (VNext.goto hk1 hsucc henv)), hmr⟩

/-- Runs: a run of the allocated code from matched configurations is realized by a VCode thread
run with the same events up to the moves, ending in matched configurations. -/
theorem alloc_run (hc : CheckedAt vc rf c ins a0) {cm cmE : MConf CV ArmState}
    {trT : List (List Ev)} (hr : MTRun vc rf sem keep ev cm trT cmE) :
    ∀ {v}, Match c ins keep r₀ cm v → ∃ trS vE, VTRun vc sem ev v trS vE ∧
      Match c ins keep r₀ cmE vE ∧ Thin trS trT := by
  induction hr with
  | nil => intro v hm; exact ⟨[], v, .nil, hm, .nil⟩
  | @cons cm1 cm2 _ evs _ hs _ ih =>
    intro v hm
    cases cm1 with
    | ret => cases hs
    | halt => cases hs
    | run ms =>
      cases v with
      | ret => exact hm.elim
      | halt => exact hm.elim
      | run vs =>
        rcases alloc_back hc hm hs with ⟨rfl, ms', rfl, hm'⟩ | ⟨v', hv, hm'⟩
        · obtain ⟨trS, vE, hrS, hmE, hth⟩ := ih (v := .run vs) hm'
          exact ⟨trS, vE, hrS, hmE, .tgt hth⟩
        · obtain ⟨trS, vE, hrS, hmE, hth⟩ := ih hm'
          exact ⟨_, vE, .cons hv hrS, hmE, .both hth⟩

end

/-- **Register allocation with interference, as traces, with progress** (T2j): `alloc_thin`, and
when the VCode run's last configuration has a step, so has the allocated code's
(`sim_progress_at`). -/
theorem alloc_thinP {vc : VCode} {rf : RFunc} {sem : ISem CV ArmState} {keep : Reg → CV → CV}
    {ev : MInst → List CV → ArmState → List Ev} (h : checkAlloc vc rf = .ok ())
    (m₀ : Loc → CV) (ρ₀ : Nat → CV) (w₀ : ArmState)
    {trT : List (List Ev)} {cT : MConf CV ArmState}
    (hrun : MTRun vc rf sem keep ev (MConf.init rf m₀ w₀) trT cT) :
    ∃ trS cS, VTRun vc sem ev (VConf.init ρ₀ w₀) trS cS ∧ Thin trS trT ∧
      (∀ vals m w, cT = .ret vals m w → cS = .ret vals w) ∧ (∀ w, cT = .halt w → cS = .halt w) ∧
      (∀ cS', VStep vc sem cS cS' → ∃ cT', MStep vc sem keep rf cT cT') := by
  obtain ⟨c, ins, hc⟩ := checked_of_checkAlloc h
  obtain ⟨a0, hat, hle⟩ := hc.at
  have hinv0 : Inv keep a0 m₀ ρ₀ (fun r => m₀ (.reg r)) := Inv_mono hle Inv_entryState
  have hinit : Match c ins keep (fun r => m₀ (.reg r)) (MConf.init rf m₀ w₀) (VConf.init ρ₀ w₀) := by
    obtain ⟨a, out, ha, hrb, hedges⟩ :=
      verifyBlock_ok (hat.blocks 0 (Nat.pos_of_ne_zero hat.nonempty))
    rw [hat.entry] at ha
    cases ha
    obtain ⟨vb, items, hvb, hitems, hrb'⟩ := runBlock_ok hrb
    rw [hat.rf_eq] at hitems
    have : rf.blocks[0]! = items := by simp [getElem!_def, hitems]
    simp only [MConf.init, VConf.init, this]
    exact ⟨rfl, rfl, vb, a0, out, hvb, hrb', hinv0, hedges⟩
  obtain ⟨trS, cS, hrS, hmE, hth⟩ := alloc_run hat hrun hinit
  refine ⟨trS, cS, hrS, hth, fun vals m w hT => ?_, fun w hT => ?_, fun cS' hv => ?_⟩
  · subst hT
    cases cS with
    | ret vals' w' => obtain ⟨rfl, rfl, -⟩ := hmE; rfl
    | _ => exact hmE.elim
  · subst hT
    cases cS with
    | halt w' => cases hmE; rfl
    | _ => exact hmE.elim
  · cases cT with
    | run ms =>
      cases cS with
      | run vs => exact sim_progress_at sem keep hat hmE hv
      | _ => exact hmE.elim
    | ret => cases cS <;> first | exact hmE.elim | cases hv
    | halt => cases cS <;> first | exact hmE.elim | cases hv

/-- **Register allocation with interference, as traces**: if `checkAlloc vc rf` accepts, a run of
the allocated code from the entry (store `m₀`, world `w₀`), reading any bytes, is realized by a
VCode thread run from the entry (vreg file `ρ₀`) with the same events up to the moves (`Thin`),
which returns (traps) with the same values and world when the allocated code does. -/
theorem alloc_thin {vc : VCode} {rf : RFunc} {sem : ISem CV ArmState} {keep : Reg → CV → CV}
    {ev : MInst → List CV → ArmState → List Ev} (h : checkAlloc vc rf = .ok ())
    (m₀ : Loc → CV) (ρ₀ : Nat → CV) (w₀ : ArmState)
    {trT : List (List Ev)} {cT : MConf CV ArmState}
    (hrun : MTRun vc rf sem keep ev (MConf.init rf m₀ w₀) trT cT) :
    ∃ trS cS, VTRun vc sem ev (VConf.init ρ₀ w₀) trS cS ∧ Thin trS trT ∧
      (∀ vals m w, cT = .ret vals m w → cS = .ret vals w) ∧ (∀ w, cT = .halt w → cS = .halt w) := by
  obtain ⟨trS, cS, hrS, hth, hret, hhalt, -⟩ := alloc_thinP h m₀ ρ₀ w₀ hrun
  exact ⟨trS, cS, hrS, hth, hret, hhalt⟩

/-- **Register allocation with interference**: if `checkAlloc vc rf` accepts, a run of the
allocated code from the entry (store `m₀`, world `w₀`), reading any bytes, is realized by a VCode
thread run from the entry (vreg file `ρ₀`) with the same events up to the moves (`Refines` with
equal events, no private location, the atomic updates the two-event steps), which returns
(traps) with the same values and world when the allocated code does. -/
theorem alloc_refines {vc : VCode} {rf : RFunc} {sem : ISem CV ArmState} {keep : Reg → CV → CV}
    {ev : MInst → List CV → ArmState → List Ev} (h : checkAlloc vc rf = .ok ())
    (hlen : ∀ i u w, (ev i u w).length ≤ 2) (m₀ : Loc → CV) (ρ₀ : Nat → CV) (w₀ : ArmState)
    {trT : List (List Ev)} {cT : MConf CV ArmState}
    (hrun : MTRun vc rf sem keep ev (MConf.init rf m₀ w₀) trT cT) :
    ∃ trS cS ψ, VTRun vc sem ev (VConf.init ρ₀ w₀) trS cS ∧
      Refines (· = ·) (fun _ => False) (StepPair (conv trT)) (conv trS) (conv trT) ψ ∧
      (∀ vals m w, cT = .ret vals m w → cS = .ret vals w) ∧ (∀ w, cT = .halt w → cS = .halt w) := by
  obtain ⟨trS, cS, hrS, hth, hret, hhalt⟩ := alloc_thin h m₀ ρ₀ w₀ hrun
  have hlenS := vtrun_len hlen hrS
  obtain ⟨ψ, href⟩ := refines_of_thin (hth.map ProgE2E.convEv) (by
    intro j hj
    simp only [List.getElem_map, List.length_map]
    exact hlenS j (by simpa using hj))
  exact ⟨trS, cS, ψ, hrS, href, hret, hhalt⟩

end Concurrency.AllocThread
