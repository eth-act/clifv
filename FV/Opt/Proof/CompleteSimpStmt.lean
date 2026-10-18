import FV.Opt.Proof.CompleteSimpSkel

/-!
# Completeness of simplify: one pure statement

`pure_ok`: the pure path of `Opt.stepStmt` (`pureInsert`, `pureBest`, `pureEmit`, `pureAlts`) on a
statement `v = inst` whose operands are placeable and available: the statement is kept (`v` becomes
available here and placeable) or replaced by a placeable `w` of `v`'s type, available after the
nodes `materialize` emitted; the state facts are kept with `v` no longer bad when kept.
-/

namespace Opt

open Clif

section Pure

variable {f : Function} {V : Nat → Option Block} {B : ValueId → Prop}

/-- Fewer bad values: the values leaving `B` are defined in the view where they are available
and are not new nodes. -/
theorem MInv.weakenB {st : SState} {B' : ValueId → Prop} (h : MInv f V B st)
    (hB : ∀ y, B' y → B y)
    (hav : ∀ y d, st.avail.get? y = some d → B y → ¬ B' y → ∃ t, DefAt V y d t)
    (hnb : ∀ y n, st.defs.get? y = some n → st.avail.contains y = false → B y → ¬ B' y →
      maxValue f < y) : MInv f V B' st := by
  refine ⟨h.fn, h.maxLt, h.knownLt, h.typesFresh, h.defsTy, h.altsKnown, fun y d hy hb => ?_,
    h.defAvail, fun y n hy ha hb => ?_, fun y hy => h.badLe y (hB y hy), h.uniq⟩
  · by_cases hB0 : B y
    · exact hav y d hy hB0 hb
    · exact h.availDef y d hy hB0
  · by_cases hB0 : B y
    · exact hnb y n hy ha hB0 hb
    · exact h.newBig y n hy ha hB0

theorem RInv.weakenB {X : ValueId → Prop} {XN : Inst → Prop} {st : SState} {B' : ValueId → Prop}
    (h : RInv f V B X XN st) (hB : ∀ y, B' y → B y)
    (hav : ∀ y d, st.avail.get? y = some d → B y → ¬ B' y → ∃ t, DefAt V y d t)
    (hnb : ∀ y n, st.defs.get? y = some n → st.avail.contains y = false → B y → ¬ B' y →
      maxValue f < y) : RInv f V B' X XN st := by
  have hg : ∀ y, Good st B y → Good st B' y :=
    Good.mono (fun _ h => h) (fun y hy hb => hy.not_bad (hB y hb)) (fun _ _ h => .inl h)
      (fun _ _ h => .inl h)
  exact ⟨h.m.weakenB hB hav hnb, h.noPartial, fun n w hw => by
    obtain ⟨e1, e2, e3⟩ := h.memo n w hw
    exact ⟨e1.imp (hg w) id, e2, e3⟩, h.alts⟩

/-- Exceptional hash-consing entries whose values became placeable. -/
theorem RInv.dropX {X : ValueId → Prop} {XN : Inst → Prop} {st : SState}
    (h : RInv f V B X XN st) (hx : ∀ n w, st.memo.get? n = some w → X w → XN n → Good st B w) :
    RInv f V B (fun _ => False) (fun _ => False) st := by
  refine ⟨h.m, h.noPartial, fun n w hw => ?_, h.alts⟩
  obtain ⟨e1, e2, e3⟩ := h.memo n w hw
  rcases e1 with e1 | ⟨e1, e1'⟩
  · exact ⟨.inl e1, e2, e3⟩
  · exact ⟨.inl (hx n w hw e1 e1'), e2, e3⟩

/-- Recording the e-class of a value. -/
theorem RInv.altsInsert {X : ValueId → Prop} {XN : Inst → Prop} {st : SState} {x : ValueId}
    {ms : List ValueId} (h : RInv f V B X XN st) (hx : st.known x = true)
    (hms : ∀ m ∈ ms, st.known m = true ∧ st.types.get? m = st.types.get? x ∧
      ∀ n, st.defs.get? m = some n → ∀ y ∈ operands n, Good st B y) :
    RInv f V B X XN ({ st with alts := st.alts.insert x ms } : SState) ∧
      ∀ y, Good st B y → Good ({ st with alts := st.alts.insert x ms } : SState) B y := by
  have hg : ∀ y, Good st B y → Good ({ st with alts := st.alts.insert x ms } : SState) B y := by
    refine Good.mono (fun _ h => h) (fun _ h => h.not_bad) (fun _ _ h => .inl h) (fun y ms' hy => ?_)
    simp only [hm_get?_insert] at hy
    split at hy
    · cases hy; exact .inr fun m hm n hn z hz => (hms m hm).2.2 n hn z hz
    · exact .inl hy
  have hm : MInv f V B ({ st with alts := st.alts.insert x ms } : SState) := by
    refine ⟨h.m.fn, h.m.maxLt, h.m.knownLt, h.m.typesFresh, h.m.defsTy, fun y ms' hy => ?_,
      h.m.availDef, h.m.defAvail, h.m.newBig, h.m.badLe, h.m.uniq⟩
    simp only [hm_get?_insert] at hy
    split at hy
    · rename_i he; subst he; exact hx
    · exact h.m.altsKnown y ms' hy
  refine ⟨⟨hm, h.noPartial, fun n w hw => ?_, fun y ms' hy m hm => ?_⟩, hg⟩
  · obtain ⟨e1, e2, e3⟩ := h.memo n w hw
    exact ⟨e1.imp (hg w) id, e2, e3⟩
  · simp only [hm_get?_insert] at hy
    split at hy
    · rename_i he; subst he; cases hy; exact ⟨(hms m hm).1, (hms m hm).2.1⟩
    · exact h.alts y ms' hy m hm

theorem RInv.anyX {X : ValueId → Prop} {XN : Inst → Prop} {st : SState}
    (h : RInv f V B (fun _ => False) (fun _ => False) st) : RInv f V B X XN st :=
  ⟨h.m, h.noPartial, fun n w hw => by
    obtain ⟨e1, e2, e3⟩ := h.memo n w hw
    exact ⟨.inl (e1.resolve_right (fun h => h.1)), e2, e3⟩, h.alts⟩

/-- `pureInsert`: `v = inst` becomes a node (its value stays bad). -/
theorem pureInsert_ok {st : SState} {v : ValueId} {inst : Inst}
    (hI : RInv f V B (fun _ => False) (fun _ => False) st) (hpure : isPure inst = true)
    (hpt : pureTyped (fun y => st.types.get? y) f inst = true)
    (hty : st.types.get? v = SState.nodeTy inst) (hops : ∀ y ∈ operands inst, Good st B y)
    (hvk : st.known v = false) (hvn : v < st.next) (hvB : B v) :
    RInv f V B (fun _ => False) (fun _ => False) (pureInsert st v inst) ∧
      CInv B (pureInsert st v inst) ∧
      (∀ y, Good st B y → Good (pureInsert st v inst) B y) ∧
      (pureInsert st v inst).defs.get? v = some inst ∧
      (∀ y, y ≠ v → (pureInsert st v inst).defs.get? y = st.defs.get? y) ∧
      (pureInsert st v inst).avail = st.avail ∧ (pureInsert st v inst).alts = st.alts ∧
      (pureInsert st v inst).types = st.types ∧ (pureInsert st v inst).memo = st.memo ∧
      (pureInsert st v inst).next = st.next := by
  have hdefs : ∀ y, (pureInsert st v inst).defs.get? y = if v = y then some inst else st.defs.get? y :=
    fun y => hm_get?_insert' _ _ _ _
  have hne : ∀ y, st.known y = true → v ≠ y := by
    intro y hy he; subst he; rw [hvk] at hy; cases hy
  have kgrow : ∀ y, st.known y = true → (pureInsert st v inst).known y = true := by
    intro y hy
    rcases known_iff.1 hy with h1 | h1
    · obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 h1
      exact known_iff.2 (.inl (by rw [hdefs, if_neg (hne y hy), hm]; rfl))
    · exact known_iff.2 (.inr h1)
  have hgood : ∀ y, Good st B y → Good (pureInsert st v inst) B y := by
    refine Good.mono kgrow (fun y hy => hy.not_bad) (fun y m hm => ?_) (fun _ _ h => .inl h)
    rw [hdefs] at hm; split at hm
    · cases hm; exact .inr hops
    · exact .inl hm
  refine ⟨⟨⟨hI.m.fn, hI.m.maxLt, fun y hy => ?_, hI.m.typesFresh, fun y m hm => ?_, fun y ms hms =>
      kgrow y (hI.m.altsKnown y ms hms), hI.m.availDef, hI.m.defAvail, fun y m hm ha hb => ?_,
      hI.m.badLe, hI.m.uniq⟩, hI.noPartial, fun n w hw => ?_, fun y ms hms m hm => ?_⟩,
    fun k ms hk => by simp [pureInsert] at hk, hgood, by rw [hdefs, if_pos rfl],
    fun y hy => by rw [hdefs, if_neg (Ne.symm hy)], rfl, rfl, rfl, rfl, rfl⟩
  · rcases known_iff.1 hy with h1 | h1
    · simp only [hdefs] at h1; split at h1
      · rename_i he; subst he; exact hvn
      · exact hI.m.knownLt y (known_iff.2 (.inl h1))
    · exact hI.m.knownLt y (known_iff.2 (.inr h1))
  · rw [hdefs] at hm; split at hm
    · rename_i he; subst he; cases hm; exact ⟨hpure, hpt, hty⟩
    · exact hI.m.defsTy y m hm
  · rw [hdefs] at hm; split at hm
    · rename_i he; subst he; exact absurd hvB hb
    · exact hI.m.newBig y m hm ha hb
  · obtain ⟨e1, e2, e3⟩ := hI.memo n w hw
    exact ⟨e1.imp (hgood w) id, kgrow w e2, e3⟩
  · obtain ⟨e1, e2⟩ := hI.alts y ms hms m hm
    exact ⟨kgrow m e1, e2⟩

theorem memoHit_some {st : SState} {bi : Nat} {inst : Inst} {w : ValueId}
    (h : memoHit st bi inst = some w) : st.memo.get? inst = some w := by
  unfold memoHit at h
  split at h
  · split at h
    · cases h
    · rename_i w' hw _; cases h; exact hw
  · cases h

/-- `pureBest`: the best value of `v`'s class is `v` or a placeable value of its type, and the
hash-consing table maps `inst` to it. -/
theorem pureBest_ok {rules : SimplifyFn} (hR : SimpRulesOk rules) (allowed : Inst → Bool)
    (bi : Nat) {st0 : SState} {v : ValueId} {inst : Inst}
    (hI : RInv f V B (fun _ => False) (fun _ => False) st0) (hC : CInv B st0)
    (hvk : st0.known v = true) (hvd : st0.defs.get? v = some inst)
    (hops : ∀ y ∈ operands inst, Good st0 B y) (halts : st0.alts.get? v = none)
    (hty : st0.types.get? v = SState.nodeTy inst)
    (hnode : NodeIn (fun y => st0.types.get? y) f (Good st0 B) (st0.types.get? v) inst) :
    RInv f V B (· = v) (· = inst) (pureBest rules allowed bi st0 v inst).2 ∧
      CInv B (pureBest rules allowed bi st0 v inst).2 ∧
      RStep B st0 (pureBest rules allowed bi st0 v inst).2 ∧
      (pureBest rules allowed bi st0 v inst).2.memo.get? inst =
        some (pureBest rules allowed bi st0 v inst).1 ∧
      ((pureBest rules allowed bi st0 v inst).1 = v ∨
        (Good (pureBest rules allowed bi st0 v inst).2 B (pureBest rules allowed bi st0 v inst).1 ∧
          (pureBest rules allowed bi st0 v inst).2.types.get? (pureBest rules allowed bi st0 v inst).1 =
            st0.types.get? v)) := by
  unfold pureBest
  cases hmh : memoHit st0 bi inst with
  | some w =>
    simp only
    have hw := memoHit_some hmh
    obtain ⟨e1, -, e3⟩ := hI.memo inst w hw
    exact ⟨hI.anyX, hC, RStep.refl st0, hw,
      .inr ⟨e1.resolve_right (fun h => h.1), by rw [e3, hty]⟩⟩
  | none =>
    simp only
    have hI0 : RInv f V B (· = v) (· = inst) ({ st0 with memo := st0.memo.insert inst v } : SState) :=
      (hI.anyX).memoInsert (.inr ⟨rfl, rfl⟩) hvk hty
    have hS0 : RStep B st0 ({ st0 with memo := st0.memo.insert inst v } : SState) :=
      RStep.of_fields rfl rfl rfl rfl rfl rfl rfl rfl
    have hen : ∀ n ∈ SState.enodes ({ st0 with memo := st0.memo.insert inst v } : SState) v,
        NodeIn (fun y => st0.types.get? y) f (Good st0 B) (st0.types.get? v) n := by
      intro n hn
      simp only [SState.enodes, halts, hvd, Option.toList_some, Option.getD_none,
        List.filterMap_nil, List.append_nil, List.mem_singleton] at hn
      subst hn; exact hnode
    obtain ⟨hI1, hS1, hC1, hb1⟩ := opt_spec (X := (· = v)) (XN := (· = inst)) hR allowed rewriteLimit
      _ v hI0 hvk (.inr rfl) (fun n hn y hy => by
        change st0.defs.get? v = some n at hn
        rw [hvd] at hn; cases hn; exact hops y hy)
      hen
    generalize optimizeAt rules allowed rewriteLimit
      ({ st0 with memo := st0.memo.insert inst v } : SState) v = r at hI1 hS1 hC1 hb1
    obtain ⟨b, st1⟩ := r
    simp only at hI1 hS1 hC1 hb1 ⊢
    have hbk : st1.known b = true ∧ st1.types.get? b = SState.nodeTy inst := by
      rcases hb1 with rfl | hb
      · exact ⟨hS1.known hvk, by rw [hS1.typesKnown _ hvk]; exact hty⟩
      · exact ⟨hb.1.known, by rw [hb.2]; exact hty⟩
    refine ⟨hI1.memoInsert (hb1.imp (fun h => ⟨h, rfl⟩) (fun h => h.1) |>.symm) hbk.1 hbk.2,
      (hC1 (hC.congr rfl rfl rfl rfl rfl)).congr rfl rfl rfl rfl rfl,
      hS0.trans (hS1.trans (RStep.of_fields rfl rfl rfl rfl rfl rfl rfl rfl)),
      by simp, hb1⟩

/-- The pure path of `stepStmt` (after its sanity check). -/
def pureStep (rules : SimplifyFn) (allowed : Inst → Bool) (cfg : Cfg) (bi : Nat) (st : SState)
    (subst : Subst) (s : Stmt) (inst : Inst) (v : ValueId) : SState × Subst × StmtLog :=
  let st := pureInsert st v inst
  let (best, st1) := pureBest rules allowed bi st v inst
  let (st', subst', lg) := pureEmit cfg allowed bi st1 subst s inst v best
  (pureAlts st1 st' v best lg, subst', lg)

/-- What the pure path guarantees (module doc). -/
structure PureOk (f : Function) (idom : Array (Option Nat)) (allowed : Inst → Bool) (bi : Nat)
    (B B' : ValueId → Prop) (V : Nat → Option Block) (b : Block) (st stF : SState)
    (subst subst' : Subst) (s : Stmt) (inst : Inst) (v : ValueId) (lg : StmtLog) : Prop where
  inv : RInv f (emitV V bi lg.out.toList) B' (fun _ => False) (fun _ => False) stF
  good : ∀ y, Good st B y → Good stF B' y
  known : ∀ y, st.known y = true → stF.known y = true
  types : ∀ y t, st.types.get? y = some t → stF.types.get? y = some t
  avail : ∀ y d, st.avail.get? y = some d → stF.avail.get? y = some d
  availNew : ∀ y d, stF.avail.get? y = some d →
    st.avail.get? y = some d ∨ (d = bi ∧ ∃ t ∈ lg.out.toList, y ∈ t.results)
  defsKeep : ∀ y n, st.defs.get? y = some n → st.avail.contains y = true →
    stF.defs.get? y = some n
  kind : (lg = .keep { s with inst } ∧ subst' = subst ∧ stF.avail.get? v = some bi ∧
      Good stF B' v ∧ stF.defs.get? v = some inst) ∨
    (∃ w, lg = .repl { s with inst } w lg.out ∧ subst' = subst.insert v w ∧
      (∀ j t, lg.out.toList[j]? = some t →
        NewOk idom (emitV V bi lg.out.toList) bi (b.body.length + j) allowed B' stF t) ∧
      Good stF B' w ∧ AvailAt idom (emitV V bi lg.out.toList) bi (b.body.length + lg.out.size) w ∧
      stF.types.get? w = stF.types.get? v ∧ stF.avail.contains v = false)

/-- The kept statement `v = inst` (`s.results = [v]`) becomes available at the end of block `bi`
and `v` placeable. -/
theorem keepAvail_ok {X : ValueId → Prop} {XN : Inst → Prop} {st1 : SState} {v : ValueId}
    {inst : Inst} {s : Stmt} {b : Block} {B' : ValueId → Prop}
    (hI1 : RInv f V B X XN st1) (hb : V bi = some b) (hres : s.results = [v])
    (hvd : st1.defs.get? v = some inst) (hvops : ∀ y ∈ operands inst, Good st1 B y)
    (hvav : st1.avail.get? v = none) (halts : st1.alts.get? v = none)
    (hB'1 : ∀ y, B' y → B y) (hB'2 : ∀ y, y ≠ v → B y → B' y) (hnB' : ¬ B' v) :
    MInv f (emitV V bi [{ s with inst }]) B' ({ st1 with avail := st1.avail.insert v bi } : SState) ∧
      (∀ y, Good st1 B y → Good ({ st1 with avail := st1.avail.insert v bi } : SState) B' y) ∧
      Good ({ st1 with avail := st1.avail.insert v bi } : SState) B' v ∧
      (∀ y, st1.known y = true → ({ st1 with avail := st1.avail.insert v bi } : SState).known y = true) := by
  have hvk : st1.known v = true := known_iff.2 (.inl (by rw [hvd]; rfl))
  have havail : ∀ y, ({ st1 with avail := st1.avail.insert v bi } : SState).avail.get? y =
      if v = y then some bi else st1.avail.get? y := fun y => hm_get?_insert' _ _ _ _
  have kgrow : ∀ y, st1.known y = true →
      ({ st1 with avail := st1.avail.insert v bi } : SState).known y = true := by
    intro y hy
    rcases known_iff.1 hy with h1 | h1
    · exact known_iff.2 (.inl h1)
    · exact known_iff.2 (.inr (by simp only [hm_contains_insert, h1, Bool.or_true]))
  have hgood : ∀ y, Good st1 B y → Good ({ st1 with avail := st1.avail.insert v bi } : SState) B' y :=
    Good.mono kgrow (fun y hy hb => hy.not_bad (hB'1 y hb)) (fun _ _ h => .inl h)
      (fun _ _ h => .inl h)
  have hnotV : ∀ d t, ¬ DefAt V v d t := by
    intro d t hd; have := hI1.m.defAvail v d t hd; rw [hvav] at this; cases this
  have hdefR : DefAt (emitV V bi [{ s with inst }]) v bi (b.body.length + 1) :=
    ⟨{ b with body := b.body ++ [{ s with inst }] }, by simp [emitV, hb],
     .inr ⟨b.body.length, { s with inst }, rfl, by simp, by simp [hres]⟩⟩
  have hdefV : ∀ y d t, DefAt (emitV V bi [{ s with inst }]) y d t →
      DefAt V y d t ∨ (y = v ∧ d = bi ∧ t = b.body.length + 1) := by
    intro y d t h
    rcases h.of_emit with h | ⟨b0, hb0, rfl, j, s0, rfl, hs0, hy⟩
    · exact .inl h
    · rw [hb] at hb0; cases hb0
      rcases j with _ | j
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hs0
        subst hs0; simp only [hres, List.mem_singleton] at hy
        exact .inr ⟨hy, rfl, rfl⟩
      · simp at hs0
  refine ⟨⟨hI1.m.fn, hI1.m.maxLt, fun y hy => ?_, hI1.m.typesFresh, hI1.m.defsTy,
    fun y ms hms => kgrow y (hI1.m.altsKnown y ms hms), fun y d hy hby => ?_, fun y d t hy => ?_,
    fun y m hm ha hby => ?_, fun y hy => hI1.m.badLe y (hB'1 y hy), fun y d t d' t' h1 h2 => ?_⟩,
    hgood, ?_, kgrow⟩
  · rcases known_iff.1 hy with h1 | h1
    · exact hI1.m.knownLt y (known_iff.2 (.inl h1))
    · simp only [hm_contains_insert, Bool.or_eq_true, beq_iff_eq] at h1
      rcases h1 with rfl | h1
      · exact hI1.m.knownLt _ hvk
      · exact hI1.m.knownLt y (known_iff.2 (.inr h1))
  · rw [havail] at hy; split at hy
    · rename_i he; subst he; cases hy; exact ⟨_, hdefR⟩
    · rename_i he
      obtain ⟨t, ht⟩ := hI1.m.availDef y d hy (fun h => hby (hB'2 y (Ne.symm he) h))
      exact ⟨t, ht.emit bi _⟩
  · rcases hdefV y d t hy with h | ⟨rfl, rfl, rfl⟩
    · have := hI1.m.defAvail y d t h
      rw [havail]; split
      · rename_i he; subst he; rw [hvav] at this; cases this
      · exact this
    · rw [havail, if_pos rfl]
  · have hyv : y ≠ v := by
      rintro rfl
      simp at ha
    have ha' : st1.avail.contains y = false := by
      simpa [hm_contains_insert, Ne.symm hyv] using ha
    exact hI1.m.newBig y m hm ha' (fun h => hby (hB'2 y hyv h))
  · rcases hdefV y d t h1 with h1 | ⟨hy1, hd1, ht1⟩
    · rcases hdefV y d' t' h2 with h2 | ⟨hy2, hd2, ht2⟩
      · exact hI1.m.uniq _ _ _ _ _ h1 h2
      · rw [hy2] at h1; exact absurd h1 (hnotV _ _)
    · rcases hdefV y d' t' h2 with h2 | ⟨hy2, hd2, ht2⟩
      · rw [hy1] at h2; exact absurd h2 (hnotV _ _)
      · exact ⟨hd1.trans hd2.symm, ht1.trans ht2.symm⟩
  · refine Good.mk hnB' (kgrow v hvk) (fun n hn y hy => ?_) (fun ms hms => ?_)
    · change st1.defs.get? v = some n at hn
      rw [hvd] at hn; cases hn; exact hgood y (hvops y hy)
    · change st1.alts.get? v = some ms at hms
      rw [halts] at hms; cases hms

/-- `pureEmit` and `pureAlts` after `pureBest` (`best` and the state `st1`). -/
theorem emitAlts_ok {st st1 : SState} {subst : Subst} {s : Stmt} {inst : Inst} {v best : ValueId}
    {b : Block} (cfg : Cfg) (allowed : Inst → Bool)
    (hb : V bi = some b) (hres : s.results = [v])
    (hI1 : RInv f V B (· = v) (· = inst) st1) (hC1 : CInv B st1)
    (hmem1 : st1.memo.get? inst = some best)
    (hbest : best = v ∨ (Good st1 B best ∧ st1.types.get? best = st1.types.get? v))
    (hvB : B v) (hvk1 : st1.known v = true) (hd1v : st1.defs.get? v = some inst)
    (hops1 : ∀ y ∈ operands inst, Good st1 B y) (hav1 : st1.avail.get? v = none)
    (hal1 : st1.alts.get? v = none)
    (hgst1 : ∀ y, Good st B y → Good st1 B y) (hkst1 : ∀ y, st.known y = true → st1.known y = true)
    (htst1 : ∀ y t, st.types.get? y = some t → st1.types.get? y = some t)
    (havst1 : st1.avail = st.avail)
    (hdst1 : ∀ y n, st.defs.get? y = some n → st.avail.contains y = true → st1.defs.get? y = some n) :
    ((pureEmit cfg allowed bi st1 subst s inst v best).2.2 = .keep { s with inst } ∧
      PureOk f cfg.idom allowed bi B (fun y => B y ∧ y ≠ v) V b st
        (pureAlts st1 (pureEmit cfg allowed bi st1 subst s inst v best).1 v best
          (pureEmit cfg allowed bi st1 subst s inst v best).2.2) subst
        (pureEmit cfg allowed bi st1 subst s inst v best).2.1 s inst v
        (pureEmit cfg allowed bi st1 subst s inst v best).2.2) ∨
    ((∃ w o, (pureEmit cfg allowed bi st1 subst s inst v best).2.2 = .repl { s with inst } w o) ∧
      PureOk f cfg.idom allowed bi B B V b st
        (pureAlts st1 (pureEmit cfg allowed bi st1 subst s inst v best).1 v best
          (pureEmit cfg allowed bi st1 subst s inst v best).2.2) subst
        (pureEmit cfg allowed bi st1 subst s inst v best).2.1 s inst v
        (pureEmit cfg allowed bi st1 subst s inst v best).2.2) := by
  sorry

/-- **The pure path** (module doc): kept (`v` leaves the bad values) or replaced. -/
theorem pure_ok {rules : SimplifyFn} (hR : SimpRulesOk rules) (allowed : Inst → Bool) (cfg : Cfg)
    (bi : Nat) {st : SState} {subst : Subst} {s : Stmt} {inst : Inst} {v : ValueId} {b : Block}
    (hI : RInv f V B (fun _ => False) (fun _ => False) st) (hb : V bi = some b)
    (hres : s.results = [v]) (hpure : isPure inst = true)
    (hpt : pureTyped (fun y => st.types.get? y) f inst = true)
    (hty : st.types.get? v = SState.nodeTy inst) (hops : ∀ y ∈ operands inst, Good st B y)
    (hvk : st.known v = false) (hvn : v < st.next) (hvB : B v) :
    ((pureStep rules allowed cfg bi st subst s inst v).2.2 = .keep { s with inst } ∧
      PureOk f cfg.idom allowed bi B (fun y => B y ∧ y ≠ v) V b st
        (pureStep rules allowed cfg bi st subst s inst v).1 subst
        (pureStep rules allowed cfg bi st subst s inst v).2.1 s inst v
        (pureStep rules allowed cfg bi st subst s inst v).2.2) ∨
    ((∃ w o, (pureStep rules allowed cfg bi st subst s inst v).2.2 = .repl { s with inst } w o) ∧
      PureOk f cfg.idom allowed bi B B V b st
        (pureStep rules allowed cfg bi st subst s inst v).1 subst
        (pureStep rules allowed cfg bi st subst s inst v).2.1 s inst v
        (pureStep rules allowed cfg bi st subst s inst v).2.2) := by
  obtain ⟨hI0, hC0, hg0, hd0v, hd0, ha0, hal0, ht0, hm0, hn0⟩ :=
    pureInsert_ok hI hpure hpt hty hops hvk hvn hvB
  have hvav : st.avail.get? v = none := by
    cases h : st.avail.get? v with
    | none => rfl
    | some d =>
      have : st.known v = true := known_iff.2 (.inr ((hm_contains_iff _ _).2 (by rw [h]; rfl)))
      rw [hvk] at this; cases this
  have hvalts : st.alts.get? v = none := by
    cases h : st.alts.get? v with
    | none => rfl
    | some ms => have := hI.m.altsKnown v ms h; rw [hvk] at this; cases this
  have hk0 : (pureInsert st v inst).known v = true := known_iff.2 (.inl (by rw [hd0v]; rfl))
  have hops0 : ∀ y ∈ operands inst, Good (pureInsert st v inst) B y := fun y hy => hg0 y (hops y hy)
  obtain ⟨hI1, hC1, hS1, hmem1, hbest⟩ := pureBest_ok (V := V) hR allowed bi hI0 hC0 hk0 hd0v hops0
    (by rw [hal0]; exact hvalts) (by rw [ht0]; exact hty)
    ⟨hpure, by rw [ht0]; exact hpt, by rw [ht0]; exact hty.symm, hops0⟩
  have hkst1 : ∀ y, st.known y = true →
      (pureBest rules allowed bi (pureInsert st v inst) v inst).2.known y = true := by
    intro y hy
    refine hS1.known ?_
    rcases known_iff.1 hy with h1 | h1
    · obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 h1
      have hyv : y ≠ v := by rintro rfl; rw [hvk] at hy; cases hy
      exact known_iff.2 (.inl (by rw [hd0 y hyv, hm]; rfl))
    · exact known_iff.2 (.inr (by rw [ha0]; exact h1))
  have hbt : (pureBest rules allowed bi (pureInsert st v inst) v inst).1 = v ∨
      (Good (pureBest rules allowed bi (pureInsert st v inst) v inst).2 B
        (pureBest rules allowed bi (pureInsert st v inst) v inst).1 ∧
       (pureBest rules allowed bi (pureInsert st v inst) v inst).2.types.get?
        (pureBest rules allowed bi (pureInsert st v inst) v inst).1 =
       (pureBest rules allowed bi (pureInsert st v inst) v inst).2.types.get? v) :=
    hbest.imp id (fun h => ⟨h.1, by rw [h.2, hS1.typesKnown v hk0]⟩)
  have hav1 : (pureBest rules allowed bi (pureInsert st v inst) v inst).2.avail.get? v = none := by
    rw [hS1.avail, ha0]; exact hvav
  have hal1 : (pureBest rules allowed bi (pureInsert st v inst) v inst).2.alts.get? v = none := by
    rw [hS1.alts, hal0]; exact hvalts
  have havst : (pureBest rules allowed bi (pureInsert st v inst) v inst).2.avail = st.avail := by
    rw [hS1.avail, ha0]
  exact emitAlts_ok cfg allowed hb hres hI1 hC1 hmem1 hbt hvB (hS1.known hk0) (hS1.defs v inst hd0v)
    (fun y hy => hS1.good y (hops0 y hy)) hav1 hal1 (fun y h => hS1.good y (hg0 y h)) hkst1
    (fun y t hy => hS1.types y t (by rw [ht0]; exact hy)) havst
    (fun y n hy hya => by
      have hyv : y ≠ v := by
        rintro rfl
        rw [← Bool.not_eq_false] at hya
        exact hya (by rw [← Bool.not_eq_true, hm_contains_iff, hvav]; simp)
      exact hS1.defs y n (by rw [hd0 y hyv]; exact hy))

end Pure

end Opt
