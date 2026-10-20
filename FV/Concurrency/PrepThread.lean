import FV.Concurrency.VCodeEvents
import FV.Concurrency.ThreadRefine
import FV.Backend.Proof.PrepareSound
import FV.E2E.RegLevelDriverSem
import FV.E2E.RegLevelCorrect

/-!
# `prepare` with interference (T2h, #311, layer 3)

`prepare` (unreachable-block removal, critical-edge splitting, reordering) keeps every live block
with the same instructions (the last one possibly retargeted) and inserts edge blocks holding one
`jump`; `prepCheck` validates it (`Backend.Proof.Driver.prep_sound`: a forward simulation of
whole runs). This file gives the event-level statement of `docs/plans/atomics.md` §3e, layer 3,
**backward and with interference**: every run of the prepared VCode's thread semantics
(`VCodeThread.VTStep`, reads returning any bytes) is realized by a run of the original VCode
reading the same bytes:

* `VTRun`: runs of the VCode thread semantics, a list of steps' events;
* `Thin trS trT`: the traces are equal up to steps without events (`refines_of_thin`: then
  `trS` refines `trT` (`ThreadRefine.Refines`) with equal events, no private location, the
  atomic updates the two-event steps);
* `prep_back`: from matched configurations (`PMatch`: same block contents, vreg file and world;
  a branch into an edge block pends until the edge block's `jump`), every step of the prepared
  code is matched by a step of the original with the same events, or has no event;
* **`prep_refines`**: a run of the prepared code from the entry is realized by a run of the
  original from the entry (`Thin`, hence `Refines`) that returns or traps when it does, for an
  instruction semantics with the driver's facts (`DriverSemG`) and events that do not change
  under retargeting and are empty at branches; `prep_refines_csem`: the instance for `csem` and
  its precise footprint `cEvs`.
-/

namespace Concurrency.PrepThread

open Arm ArmFoot ArmThread Backend Backend.Proof Backend.Proof.Driver VCodeThread ThreadRefine

/-! ## Runs of the VCode thread semantics -/

/-- **Runs of the VCode thread semantics**: the steps' events in program order. -/
inductive VTRun (vc : VCode) (sem : ISem CV ArmState) (ev : MInst → List CV → ArmState → List Ev) :
    VConf CV ArmState → List (List Ev) → VConf CV ArmState → Prop
  | nil {c} : VTRun vc sem ev c [] c
  | cons {c c' c'' evs tr} : VTStep vc sem ev c evs c' → VTRun vc sem ev c' tr c'' →
      VTRun vc sem ev c (evs :: tr) c''

/-! ## Traces equal up to steps without events -/

/-- `trS` and `trT` are equal up to steps without events. -/
inductive Thin {α : Type} : List (List α) → List (List α) → Prop
  | nil : Thin [] []
  | both {e trS trT} : Thin trS trT → Thin (e :: trS) (e :: trT)
  | tgt {trS trT} : Thin trS trT → Thin trS ([] :: trT)

theorem Thin.map {α β : Type} (f : α → β) {trS trT : List (List α)} (h : Thin trS trT) :
    Thin (trS.map (·.map f)) (trT.map (·.map f)) := by
  induction h with
  | nil => exact .nil
  | both _ ih => exact .both ih
  | tgt _ ih => exact .tgt ih

/-- The index map of `Thin`: source step `j` is target step `idx j`, order-preserving on the steps
with events, onto the target steps with events. -/
def ThinIdx {α : Type} (trS trT : List (List α)) (idx : Nat → Nat) : Prop :=
  (∀ j (h : j < trS.length), trS[j] ≠ [] → ∃ h' : idx j < trT.length, trT[idx j] = trS[j]) ∧
  (∀ j j' (h : j < trS.length) (h' : j' < trS.length), trS[j] ≠ [] → trS[j'] ≠ [] → j < j' →
    idx j < idx j') ∧
  (∀ J (h : J < trT.length), trT[J] ≠ [] → ∃ j, ∃ h' : j < trS.length, idx j = J ∧ trS[j] ≠ [])

theorem thinIdx_of_thin {α : Type} {trS trT : List (List α)} (h : Thin trS trT) :
    ∃ idx, ThinIdx trS trT idx := by
  induction h with
  | nil =>
    exact ⟨id, fun j h => absurd h (Nat.not_lt_zero _), fun j _ h => absurd h (Nat.not_lt_zero _),
      fun J h => absurd h (Nat.not_lt_zero _)⟩
  | @both e trS trT _ ih =>
    obtain ⟨idx, h1, h2, h3⟩ := ih
    refine ⟨fun j => if j = 0 then 0 else idx (j - 1) + 1, ?_, ?_, ?_⟩
    · intro j hj hne
      rcases j with _ | j
      · exact ⟨by simp, rfl⟩
      · simp only [List.length_cons, List.getElem_cons_succ] at hj hne ⊢
        obtain ⟨hl, he⟩ := h1 j (by omega) hne
        simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel,
          List.getElem_cons_succ]
        exact ⟨by omega, he⟩
    · intro j j' hj hj' hne hne' hlt
      rcases j with _ | j <;> rcases j' with _ | j'
      · omega
      · simp
      · omega
      · simp only [List.length_cons, List.getElem_cons_succ] at hj hj' hne hne'
        simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
        have := h2 j j' (by omega) (by omega) hne hne' (by omega)
        omega
    · intro J hJ hne
      rcases J with _ | J
      · exact ⟨0, by simp, rfl, by simpa using hne⟩
      · simp only [List.length_cons, List.getElem_cons_succ] at hJ hne
        obtain ⟨j, hj, hidx, hne'⟩ := h3 J (by omega) hne
        exact ⟨j + 1, by simp; omega, by simp [hidx], by simpa using hne'⟩
  | @tgt trS trT _ ih =>
    obtain ⟨idx, h1, h2, h3⟩ := ih
    refine ⟨fun j => idx j + 1, ?_, ?_, ?_⟩
    · intro j hj hne
      obtain ⟨hl, he⟩ := h1 j hj hne
      exact ⟨by simp; omega, by simpa using he⟩
    · intro j j' hj hj' hne hne' hlt
      exact Nat.succ_lt_succ (h2 j j' hj hj' hne hne' hlt)
    · intro J hJ hne
      rcases J with _ | J
      · simp at hne
      · simp only [List.length_cons, List.getElem_cons_succ] at hJ hne
        obtain ⟨j, hj, hidx, hne'⟩ := h3 J (by omega) hne
        exact ⟨j, hj, by simp [hidx], hne'⟩

theorem evAt_some {α : Type} {tr : List (List α)} {p : Nat × Nat} {x : α}
    (h : evAt tr p = some x) : ∃ (hj : p.1 < tr.length) (hk : p.2 < tr[p.1].length),
      tr[p.1][p.2] = x := by
  obtain ⟨j, k⟩ := p
  unfold evAt at h
  by_cases hj : j < tr.length
  · rw [List.getElem?_eq_getElem hj] at h
    simp only [Option.bind_some] at h
    by_cases hk : k < tr[j].length
    · rw [List.getElem?_eq_getElem hk] at h
      exact ⟨hj, hk, Option.some.inj h⟩
    · rw [List.getElem?_eq_none (by omega)] at h; cases h
  · rw [List.getElem?_eq_none (by simp at hj ⊢; omega)] at h; simp at h

theorem evAt_of {α : Type} {tr : List (List α)} {j k : Nat} (hj : j < tr.length)
    (hk : k < tr[j].length) : evAt tr (j, k) = some tr[j][k] := by
  simp [evAt, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hk]

theorem ne_nil_of_lt {α : Type} {l : List α} {k : Nat} (h : k < l.length) : l ≠ [] := by
  rintro rfl; simp at h

variable {K V : Type}

/-- **Traces equal up to steps without events refine each other** (equal events, no private
location, the atomic updates the two-event steps). -/
theorem refines_of_thin {trS trT : List (List (Prog.Ev K V))} (h : Thin trS trT)
    (hlen : ∀ j (h : j < trS.length), trS[j].length ≤ 2) :
    ∃ ψ, Refines (· = ·) (fun _ => False) (StepPair trT) trS trT ψ := by
  obtain ⟨idx, h1, h2, h3⟩ := thinIdx_of_thin h
  have img : ∀ p x, evAt trS p = some x → evAt trT (idx p.1, p.2) = some x := by
    intro p x hx
    obtain ⟨hj, hk, rfl⟩ := evAt_some hx
    obtain ⟨hl, he⟩ := h1 p.1 hj (ne_nil_of_lt hk)
    have hk' : p.2 < trT[idx p.1].length := by rw [he]; exact hk
    rw [evAt_of hl hk']
    simp only [he]
  refine ⟨fun p => (idx p.1, p.2), ?_⟩
  exact
    { ev := fun p x hx => ⟨x, img p x hx, rfl, rfl, rfl, rfl, rfl⟩
      mono := fun p q hp hq hl => by
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hp
        obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hq
        obtain ⟨hj, hk, -⟩ := evAt_some hx
        obtain ⟨hj', hk', -⟩ := evAt_some hy
        rcases hl with hl | ⟨he, hl⟩
        · exact .inl (h2 _ _ hj hj' (ne_nil_of_lt hk) (ne_nil_of_lt hk') hl)
        · exact .inr ⟨by simp only [he], hl⟩
      shared := fun _ _ _ h => h
      priv := fun p y hy _ hn => by
        obtain ⟨hj, hk, -⟩ := evAt_some hy
        obtain ⟨j, hj', hidx, hne⟩ := h3 p.1 hj (ne_nil_of_lt hk)
        obtain ⟨hl, he⟩ := h1 j hj' hne
        exfalso
        refine hn (j, p.2) ?_ (by simp only [hidx])
        have hk2 : p.2 < trS[j].length := by rw [← he]; simp only [hidx]; exact hk
        rw [evAt_of hj' hk2]; rfl
      len := hlen
      pair := fun j hj h2' => by
        have hne : trS[j] ≠ [] := by intro e; rw [e] at h2'; simp at h2'
        obtain ⟨hl, he⟩ := h1 j hj hne
        exact ⟨idx j, rfl, rfl, hl, by rw [he]; exact h2'⟩
      pair_inv := fun p q hp hq hpr => by
        obtain ⟨J, e1, e2, hJ, hJ2⟩ := hpr
        simp only [Prod.mk.injEq] at e1 e2
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hp
        obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hq
        obtain ⟨hj, hk, -⟩ := evAt_some hx
        obtain ⟨hj', hk', -⟩ := evAt_some hy
        have hpq : p.1 = q.1 := by
          refine Classical.byContradiction fun hne => ?_
          rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
          · have := h2 _ _ hj hj' (ne_nil_of_lt hk) (ne_nil_of_lt hk') hlt; omega
          · have := h2 _ _ hj' hj (ne_nil_of_lt hk') (ne_nil_of_lt hk) hlt; omega
        obtain ⟨a, b⟩ := p
        obtain ⟨c, d⟩ := q
        simp only at hpq e1 e2
        subst hpq
        exact ⟨a, by rw [e1.2], by rw [e2.2]⟩ }

/-! ## The backward step -/

section
variable {vc vcp : VCode} {sem : ISem CV ArmState} {ev : MInst → List CV → ArmState → List Ev}
  {L : Nat → Prop} {ss' : Array (Array Nat)}

/-- The uses of an instruction with operands `ops` in vreg file `ρ`. -/
abbrev usesOf (ops : Array Operand) (ρ : Nat → CV) : List CV :=
  (ops.toList.filter Operand.isUse).map (ρ ·.vreg)

/-- The vreg file after the defs `outs`. -/
abbrev defsOf (ops : Array Operand) (ρ : Nat → CV) (outs : List CV) : Nat → CV :=
  writeV (writeV ρ (((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isEarly)))
    (((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isLate))

variable (vc vcp sem ev L ss') in
/-- **The match of an original and a prepared configuration**: the counterpart block (same
instruction index, vreg file and world); or the original at a branch whose target is reached
through an edge block, the prepared code in that edge block (`pend`); or the same outcome. -/
inductive PMatch : VConf CV ArmState → VConf CV ArmState → Prop
  | blk {b b' k ρ w} : L b → sigmaOf vc vcp b = some b' →
      PMatch (.run ⟨b, k, ρ, w⟩) (.run ⟨b', k, ρ, w⟩)
  | pend {b b' k ρ w vb i ops outs w2 j s s' t eb l} : L b → sigmaOf vc vcp b = some b' →
      vc.blocks[b]? = some vb → vb.insts[k]? = some i → i.operands = .ok ops →
      sem i (usesOf ops ρ) w = some (outs, w2, .goto j) →
      outs.length = (ops.toList.filter Operand.isDef).length → k + 1 = vb.insts.size →
      succOf vc b j = some s → L s → sigmaOf vc vcp s = some s' → vb.branchArgs = #[] →
      vcp.blocks[t]? = some eb → eb.insts = #[.jump l] → eb.params = #[] → eb.branchArgs = #[] →
      ss'[t]? = some #[s'] → IFoot sem i (usesOf ops ρ) w [] → ev i (usesOf ops ρ) w = [] →
      PMatch (.run ⟨b, k, ρ, w⟩) (.run ⟨t, 0, defsOf ops ρ outs, w2⟩)
  | ret {vals w} : PMatch (.ret vals w) (.ret vals w)
  | halt {w} : PMatch (.halt w) (.halt w)

theorem patch_nil (w : ArmState) : patch [] w = w := rfl

theorem sameInst_facts' {W : Type} {sem : ISem CV W} (hds : DriverSemG sem) {i i' : MInst}
    (h : SameInst i i') : i'.operands = i.operands ∧ sem i' = sem i ∧
      ∀ us, i' = .rets us → i = .rets us := by
  rcases h with rfl | h
  · exact ⟨rfl, rfl, fun _ e => e⟩
  · obtain ⟨h1, -, -, h4⟩ := setTargets_facts h
    exact ⟨h1, hds.retarget i _ i' h, fun us e => absurd e (h4 us)⟩

/-- `keptOk` keeps the number of successors. -/
theorem keptOk_succ_size {ss : Array (Array Nat)} {b b' : Nat} (h : keptOk vc vcp ss ss' b b' = true)
    {sb sb' : Array Nat} (hsb : ss[b]? = some sb) (hsb' : ss'[b']? = some sb') :
    sb'.size = sb.size := by
  unfold keptOk at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨-, hsucc⟩ := h
    rw [hsb, hsb'] at hsucc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hsucc
    exact hsucc.1
  · cases h

/-- What the backward step needs of the check. -/
structure PrepFacts (vc vcp : VCode) (L : Nat → Prop) (ss ss' : Array (Array Nat)) : Prop where
  cfg : ∀ b j, succOf vc b j = ss[b]?.bind (·[j]?)
  cfg' : ∀ b j, succOf vcp b j = ss'[b]?.bind (·[j]?)
  live : ∀ (b : Nat) (sb : Array Nat) (j s : Nat), L b → ss[b]? = some sb → sb[j]? = some s → L s
  kept : ∀ b b', L b → sigmaOf vc vcp b = some b' → Kept vc vcp ss ss' b b'
  size : ∀ b b', L b → sigmaOf vc vcp b = some b' → ∀ sb sb', ss[b]? = some sb →
    ss'[b']? = some sb' → sb'.size = sb.size

theorem edgeEnv_params {V : Type} {v : VCode} {b s : Nat} {vb sb : VBlock}
    (hb : v.blocks[b]? = some vb) (hs : v.blocks[s]? = some sb) (hba : vb.branchArgs = #[])
    {ρ ρ' : Nat → V} (h : edgeEnv v b s ρ = some ρ') : sb.params = #[] ∧ ρ' = ρ := by
  have hsp : sb.params = #[] := by
    cases hps : sb.params.size with
    | zero => exact Array.eq_empty_of_size_eq_zero hps
    | succ n => simp [edgeEnv, hb, hs, hba, hps] at h
  refine ⟨hsp, ?_⟩
  rw [edgeEnv_nil hb hs hba hsp] at h
  exact (Option.some.inj h).symm

/-- **The backward step of `prepare`**: a step of the prepared code from a matched configuration
has no event and keeps the match, or is matched by a step of the original with the same events. -/
theorem prep_back {ss : Array (Array Nat)} (H : PrepFacts vc vcp L ss ss') (hds : DriverSemG sem)
    (hev : ∀ i ls i', i.setTargets ls = some i' → ev i' = ev i)
    (hgoto : ∀ i u w outs w2 j, sem i u w = some (outs, w2, .goto j) → ev i u w = [])
    {src tgt tgt' : VConf CV ArmState} {evs : List Ev}
    (hm : PMatch vc vcp sem ev L ss' src tgt) (hs : VTStep vcp sem ev tgt evs tgt') :
    (evs = [] ∧ PMatch vc vcp sem ev L ss' src tgt') ∨
      ∃ src', VTStep vc sem ev src evs src' ∧ PMatch vc vcp sem ev L ss' src' tgt' := by
  cases hm with
  | ret => cases hs
  | halt => cases hs
  | @blk b b' k ρ w hLb hσ =>
    obtain ⟨vb, vb', hvb, hvb', hpar, hba, hsz, hins, sb, sb', hsb, hsb', hsucc⟩ :=
      (H.kept b b' hLb hσ).blocks
    cases hs with
    | @mk _ _ _ _ vb0' i' ops _ _ hvb0 hi' hops hevs hfoot hst =>
      rw [hvb'] at hvb0; cases hvb0
      have hk : k < vb.insts.size := by
        rw [← hsz]; exact (Array.getElem?_eq_some_iff.mp hi').1
      obtain ⟨i, hi⟩ : ∃ i, vb.insts[k]? = some i := ⟨_, Array.getElem?_eq_getElem hk⟩
      obtain ⟨i'', hi'', hsame⟩ := hins k i hi
      rw [hi'] at hi''; cases hi''
      obtain ⟨hops', hsem', hrets⟩ := sameInst_facts' hds hsame
      have hev' : ev i' = ev i := by
        rcases hsame with e | hst'
        · rw [e]
        · exact hev _ _ _ hst'
      have hopsS : i.operands = .ok ops := by rw [← hops']; exact hops
      cases hst with
      | step hvb1 hi1 hops1 hsem hlen hnext =>
        rename_i vb1 i1 ops1 outs w' ctl
        rw [hvb'] at hvb1; cases hvb1
        rw [hi'] at hi1; cases hi1
        rw [hops] at hops1; cases hops1
        have hsemS : sem i (usesOf ops ρ) (patch evs w) = some (outs, w', ctl) := by
          rw [← hsem']; exact hsem
        have hevS : evs = ev i (usesOf ops ρ) (patch evs w) := by rw [← hev']; exact hevs
        have hfootS : IFoot sem i (usesOf ops ρ) (patch evs w) evs := by
          unfold IFoot at hfoot ⊢; rw [← hsem']; exact hfoot
        cases hnext with
        | next hlt =>
          refine .inr ⟨_, .mk hvb hi hopsS hevS hfootS
            (.step hvb hi hopsS hsemS hlen (.next (by rw [← hsz]; exact hlt))), .blk hLb hσ⟩
        | ret hr =>
          subst hr
          refine .inr ⟨_, .mk hvb hi hopsS hevS hfootS
            (.step hvb hi hopsS hsemS hlen (.ret (hrets _ rfl))), .ret⟩
        | halt =>
          refine .inr ⟨_, .mk hvb hi hopsS hevS hfootS
            (.step hvb hi hopsS hsemS hlen .halt), .halt⟩
        | @goto j t ρ' hlast hsuccT hedgeT =>
          have hnil : evs = [] := by rw [hevS]; exact hgoto _ _ _ _ _ _ hsemS
          subst hnil
          rw [patch_nil] at hsemS hfootS hevS
          rw [H.cfg' b' j, hsb'] at hsuccT
          simp only [Option.bind_some] at hsuccT
          have hjlt : j < sb.size := by
            rw [← H.size b b' hLb hσ sb sb' hsb hsb']
            exact (Array.getElem?_eq_some_iff.mp hsuccT).1
          obtain ⟨s, hs⟩ : ∃ s, sb[j]? = some s := ⟨_, Array.getElem?_eq_getElem hjlt⟩
          have hLs := H.live b sb j s hLb hsb hs
          obtain ⟨s', t0, hs', ht0, hroute⟩ := hsucc j s hs
          rw [hsuccT] at ht0; cases ht0
          obtain ⟨vs, vs', hvs, hvs', hpars, -, -, -, -⟩ := (H.kept s s' hLs hs').blocks
          have hsuccS : succOf vc b j = some s := by rw [H.cfg b j, hsb]; simpa using hs
          rcases hroute with rfl | ⟨hbnil, eb, l, heb, hebi, hebp, hebb, hts⟩
          · -- direct
            have heq : ∀ ρx : Nat → CV, edgeEnv vcp b' t ρx = edgeEnv vc b s ρx := by
              intro ρx
              simp [edgeEnv, hvb, hvb', hvs, hvs', hpars, hba]
            refine .inr ⟨_, .mk hvb hi hopsS hevS hfootS
              (.step hvb hi hopsS hsemS hlen (.goto (by rw [← hsz]; exact hlast) hsuccS
                ((heq _).symm.trans hedgeT))), .blk hLs hs'⟩
          · -- through the edge block: pending
            obtain ⟨-, rfl⟩ := edgeEnv_params hvb' heb (by rw [hba]; exact hbnil) hedgeT
            exact .inl ⟨rfl, .pend hLb hσ hvb hi hopsS hsemS hlen (by rw [← hsz]; exact hlast)
              hsuccS hLs hs' hbnil heb hebi hebp hebb hts hfootS hevS.symm⟩
  | @pend b b' k ρ w vb i ops outs w2 j s s' t eb l hLb hσ hvb hi hops hsem hlen hlast hsucc
      hLs hs' hbnil heb hebi hebp hebb hts hfoot hevn =>
    cases hs with
    | @mk _ _ _ _ eb0 i0 ops0 _ _ heb0 hi0 hops0 hevs hfoot0 hst =>
      rw [heb] at heb0; cases heb0
      rw [hebi] at hi0
      have hi0' : i0 = .jump l := by simpa using hi0.symm
      subst hi0'
      have hops0' : ops0 = #[] := by
        have : (MInst.jump l).operands = .ok #[] := rfl
        rw [this] at hops0; cases hops0; rfl
      subst hops0'
      have hjump : ∀ w', sem (.jump l) (usesOf #[] (defsOf ops ρ outs)) w' =
          some ([], w', .goto 0) := fun w' => hds.jump l w'
      have hnil : evs = [] := by rw [hevs]; exact hgoto _ _ _ _ _ _ (hjump _)
      subst hnil
      cases hst with
      | step hvb1 hi1 hops1 hsem1 hlen1 hnext =>
        rename_i vb1 i1 ops1 outs1 w' ctl
        rw [heb] at hvb1; cases hvb1
        rw [hebi] at hi1
        have hi1' : i1 = .jump l := by simpa using hi1.symm
        subst hi1'
        have hops1' : ops1 = #[] := by
          have : (MInst.jump l).operands = .ok #[] := rfl
          rw [this] at hops1; cases hops1; rfl
        subst hops1'
        rw [hjump] at hsem1
        simp only [Option.some.injEq, Prod.mk.injEq] at hsem1
        obtain ⟨rfl, rfl, rfl⟩ := hsem1
        cases hnext with
        | @goto j0 s0 ρ' _ hsucc0 hedge0 =>
          rw [H.cfg' t 0, hts] at hsucc0
          simp only [Option.bind_some] at hsucc0
          have hs0 : s0 = s' := by simpa using hsucc0.symm
          subst hs0
          obtain ⟨vs, vs', hvs, hvs', hpars, -, -, -, -⟩ := (H.kept s s0 hLs hs').blocks
          obtain ⟨hsp', hρ'⟩ := edgeEnv_params heb hvs' hebb hedge0
          have hsp : vs.params = #[] := by rw [← hpars]; exact hsp'
          simp only [writeV, List.filter_nil, List.zip_nil_left, List.foldl_nil] at hρ'
          subst hρ'
          refine .inr ⟨_, .mk hvb hi hops hevn.symm hfoot
            (.step hvb hi hops hsem hlen (.goto hlast hsucc (edgeEnv_nil hvb hvs hbnil hsp _))),
            .blk hLs hs'⟩

/-- Runs: a run of the prepared code from a matched configuration is realized by a run of the
original with the same events up to steps without events, ending in a matched configuration. -/
theorem prep_run {ss : Array (Array Nat)} (H : PrepFacts vc vcp L ss ss') (hds : DriverSemG sem)
    (hev : ∀ i ls i', i.setTargets ls = some i' → ev i' = ev i)
    (hgoto : ∀ i u w outs w2 j, sem i u w = some (outs, w2, .goto j) → ev i u w = [])
    {tgt tgtE : VConf CV ArmState} {trT : List (List Ev)} (hr : VTRun vcp sem ev tgt trT tgtE) :
    ∀ {src}, PMatch vc vcp sem ev L ss' src tgt → ∃ trS srcE, VTRun vc sem ev src trS srcE ∧
      PMatch vc vcp sem ev L ss' srcE tgtE ∧ Thin trS trT := by
  induction hr with
  | nil => intro src hm; exact ⟨[], src, .nil, hm, .nil⟩
  | cons hs _ ih =>
    intro src hm
    rcases prep_back H hds hev hgoto hm hs with ⟨rfl, hm'⟩ | ⟨src', hs', hm'⟩
    · obtain ⟨trS, srcE, hrS, hmE, hth⟩ := ih hm'
      exact ⟨trS, srcE, hrS, hmE, .tgt hth⟩
    · obtain ⟨trS, srcE, hrS, hmE, hth⟩ := ih hm'
      exact ⟨_, srcE, .cons hs' hrS, hmE, .both hth⟩

end

/-- The step lengths of a run are bounded when the events are. -/
theorem vtrun_len {vc : VCode} {sem : ISem CV ArmState} {ev : MInst → List CV → ArmState → List Ev}
    (hlen : ∀ i u w, (ev i u w).length ≤ 2) {c c' : VConf CV ArmState} {tr : List (List Ev)}
    (h : VTRun vc sem ev c tr c') : ∀ j (hj : j < tr.length), tr[j].length ≤ 2 := by
  induction h with
  | nil => intro j hj; exact absurd hj (Nat.not_lt_zero _)
  | cons hs _ ih =>
    intro j hj
    rcases j with _ | j
    · cases hs with
      | mk _ _ _ hevs _ _ => simp only [List.getElem_cons_zero]; rw [hevs]; exact hlen _ _ _
    · exact ih j (by simpa using hj)

/-- The events of a VCode thread trace as program events. -/
def conv (tr : List (List Ev)) : List (List (Prog.Ev AKind ClifThread.BVal)) :=
  tr.map (·.map ProgE2E.convEv)

/-- **`prepare` with interference**: a run of the prepared code `vcp` from the entry, reading any
bytes, is realized by a run of the original `vc` from the entry with the same events up to steps
without events (`Refines` with equal events, no private location, the atomic updates the two-event
steps), which returns (traps) with the same values and world when the prepared run does. -/
theorem prep_refines {vc vcp : VCode} {sem : ISem CV ArmState}
    {ev : MInst → List CV → ArmState → List Ev} (hds : DriverSemG sem)
    (hcheck : prepCheck vc vcp = true)
    (hev : ∀ i ls i', i.setTargets ls = some i' → ev i' = ev i)
    (hgoto : ∀ i u w outs w2 j, sem i u w = some (outs, w2, .goto j) → ev i u w = [])
    (hlen : ∀ i u w, (ev i u w).length ≤ 2) {ρ₀ : Nat → CV} {w₀ : ArmState}
    {trT : List (List Ev)} {cT : VConf CV ArmState}
    (hrun : VTRun vcp sem ev (.run ⟨0, 0, ρ₀, w₀⟩) trT cT) :
    ∃ trS cS ψ, VTRun vc sem ev (.run ⟨0, 0, ρ₀, w₀⟩) trS cS ∧
      Refines (· = ·) (fun _ => False) (StepPair (conv trT)) (conv trS) (conv trT) ψ ∧
      (∀ vals w, cT = .ret vals w → cS = .ret vals w) ∧ (∀ w, cT = .halt w → cS = .halt w) := by
  unfold prepCheck at hcheck
  split at hcheck
  · rename_i ss ps ss' ps' hcfg hcfg'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
    obtain ⟨⟨⟨h0, hl0⟩, hall⟩, -⟩ := hcheck
    let L : Nat → Prop := fun b => b < vc.blocks.size ∧ liveOf ss b = true
    have hchk : ∀ b, L b → ∃ b', sigmaOf vc vcp b = some b' ∧ keptOk vc vcp ss ss' b b' = true ∧
        (ss[b]?.getD #[]).all (fun s => decide (s < vc.blocks.size) && liveOf ss s) = true := by
      intro b ⟨hlt, hlb⟩
      have := all_range hall hlt
      rw [hlb] at this
      simp only [Bool.not_true, Bool.false_or] at this
      split at this
      · cases this
      · rename_i b' hσ
        simp only [Bool.and_eq_true] at this
        exact ⟨b', hσ, this.1, this.2⟩
    have hkept : ∀ b b', L b → sigmaOf vc vcp b = some b' → keptOk vc vcp ss ss' b b' = true := by
      intro b b' hLb hσ
      obtain ⟨b'', hσ', hk, -⟩ := hchk b hLb
      rw [hσ] at hσ'; cases hσ'
      exact hk
    have H : PrepFacts vc vcp L ss ss' :=
      { cfg := succOf_cfg hcfg
        cfg' := succOf_cfg hcfg'
        live := by
          intro b sb j s hLb hsb hs
          obtain ⟨-, -, -, hall'⟩ := hchk b hLb
          rw [hsb, Option.getD_some] at hall'
          have := (Array.all_eq_true_iff_forall_mem.mp hall') s (Array.mem_of_getElem? hs)
          simpa only [Bool.and_eq_true, decide_eq_true_eq] using this
        kept := fun b b' hLb hσ => keptOk_sound (hkept b b' hLb hσ)
        size := fun b b' hLb hσ sb sb' hsb hsb' =>
          keptOk_succ_size (hkept b b' hLb hσ) hsb hsb' }
    have hL0 : L 0 := by
      refine ⟨?_, hl0⟩
      unfold sigmaOf at h0
      split at h0
      · rename_i vb hvb; exact (Array.getElem?_eq_some_iff.mp hvb).1
      · cases h0
    obtain ⟨trS, cS, hrS, hmE, hth⟩ := prep_run H hds hev hgoto hrun (.blk hL0 h0)
    have hlenS := vtrun_len hlen hrS
    obtain ⟨ψ, href⟩ := refines_of_thin (hth.map ProgE2E.convEv) (by
      intro j hj
      simp only [List.getElem_map, List.length_map]
      exact hlenS j (by simpa using hj))
    refine ⟨trS, cS, ψ, hrS, href, fun vals w h => ?_, fun w h => ?_⟩
    · subst h; cases hmE; rfl
    · subst h; cases hmE; rfl
  · cases hcheck

/-! ## The instance: `csem` and its precise footprint -/

theorem cEvs_setTargets (F : BitVec 64 → Prop) (ctx : FnCtx) {i i' : MInst} {ls : List Label}
    (h : i.setTargets ls = some i') : cEvs F ctx i' = cEvs F ctx i := by
  unfold MInst.setTargets at h
  funext u w
  split at h <;> (try split at h) <;> (try cases h) <;> rfl

theorem loopSem_next {F : BitVec 64 → Prop} {ty : CTy} {a : CV} {body : List Line}
    {regs : List Reg} {uses : List CV} {defs : List Reg} {w : ArmState}
    {r : List CV × ArmState × Ctl} (h : loopSem F ty a body regs uses defs w = some r) :
    r.2.2 = .next := by
  unfold loopSem at h
  split at h
  · split at h
    · split at h
      · cases h; rfl
      · cases h
    · cases h
  · cases h

theorem csem_goto {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst} {u : List CV}
    {w : ArmState} {outs : List CV} {w2 : ArmState} {j : Nat}
    (h : csem F ctx X i u w = some (outs, w2, .goto j)) : cEvs F ctx i u w = [] := by
  unfold cEvs
  by_cases hc : i.isCtl = true
  · simp only [hc, ite_true]
    split
    · exfalso
      simp only [csem] at h
      repeat' split at h
      all_goals first
        | (cases h; done)
        | exact absurd (loopSem_next h) (by simp)
        | simp at h
    · exfalso
      simp only [csem] at h
      repeat' split at h
      all_goals first
        | (cases h; done)
        | exact absurd (loopSem_next h) (by simp)
        | simp at h
    · rfl
  · exact absurd (csem_ctl (by simpa using hc) h) (by simp)

theorem cEvs_len (F : BitVec 64 → Prop) (ctx : FnCtx) (i : MInst) (u : List CV) (w : ArmState) :
    (cEvs F ctx i u w).length ≤ 2 := by
  have h := (VCodeEvents.cEvs_kinds F ctx i u w).length_le
  rw [List.length_map] at h
  refine Nat.le_trans h ?_
  cases i <;> simp [Code.akinds]

/-- **`prepare` with interference, for `csem`** (`prep_refines` with the precise footprint
`cEvs`). -/
theorem prep_refines_csem {vc vcp : VCode} {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    (hcheck : prepCheck vc vcp = true) {ρ₀ : Nat → CV} {w₀ : ArmState}
    {trT : List (List Ev)} {cT : VConf CV ArmState}
    (hrun : VTRun vcp (csem F ctx X) (cEvs F ctx) (.run ⟨0, 0, ρ₀, w₀⟩) trT cT) :
    ∃ trS cS ψ, VTRun vc (csem F ctx X) (cEvs F ctx) (.run ⟨0, 0, ρ₀, w₀⟩) trS cS ∧
      Refines (· = ·) (fun _ => False) (StepPair (conv trT)) (conv trS) (conv trT) ψ ∧
      (∀ vals w, cT = .ret vals w → cS = .ret vals w) ∧ (∀ w, cT = .halt w → cS = .halt w) :=
  prep_refines (driverSem_csem F ctx X).toDriverSemG hcheck
    (fun _ _ _ h => cEvs_setTargets F ctx h) (fun _ _ _ _ _ _ h => csem_goto h)
    (cEvs_len F ctx) hrun

end Concurrency.PrepThread
