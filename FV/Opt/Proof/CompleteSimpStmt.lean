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
  have hg : ∀ y, Placed st B y → Placed st B' y :=
    Placed.mono (fun _ h => h) (fun y hy hb => hy.not_bad (hB y hb)) (fun _ _ h => .inl h)
      (fun _ _ h => .inl h)
  exact ⟨h.m.weakenB hB hav hnb, h.noPartial, fun n w hw => by
    obtain ⟨e1, e2, e3⟩ := h.memo n w hw
    exact ⟨e1.imp (hg w) id, e2, e3⟩, h.alts⟩

/-- Exceptional hash-consing entries whose values became placeable. -/
theorem RInv.dropX {X : ValueId → Prop} {XN : Inst → Prop} {st : SState}
    (h : RInv f V B X XN st) (hx : ∀ n w, st.memo.get? n = some w → X w → XN n → Placed st B w) :
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
      ∀ n, st.defs.get? m = some n → ∀ y ∈ operands n, Placed st B y) :
    RInv f V B X XN ({ st with alts := st.alts.insert x ms } : SState) ∧
      ∀ y, Placed st B y → Placed ({ st with alts := st.alts.insert x ms } : SState) B y := by
  have hg : ∀ y, Placed st B y → Placed ({ st with alts := st.alts.insert x ms } : SState) B y := by
    refine Placed.mono (fun _ h => h) (fun _ h => h.not_bad) (fun _ _ h => .inl h) (fun y ms' hy => ?_)
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
    (hty : st.types.get? v = SState.nodeTy inst) (hops : ∀ y ∈ operands inst, Placed st B y)
    (hvk : st.known v = false) (hvn : v < st.next) (hvB : B v) :
    RInv f V B (fun _ => False) (fun _ => False) (pureInsert st v inst) ∧
      CInv B (pureInsert st v inst) ∧
      (∀ y, Placed st B y → Placed (pureInsert st v inst) B y) ∧
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
      exact known_iff.2 (.inl (by rw [hdefs, ite_eq_right (hne y hy), hm]; rfl))
    · exact known_iff.2 (.inr h1)
  have hgood : ∀ y, Placed st B y → Placed (pureInsert st v inst) B y := by
    refine Placed.mono kgrow (fun y hy => hy.not_bad) (fun y m hm => ?_) (fun _ _ h => .inl h)
    rw [hdefs] at hm; split at hm
    · cases hm; exact .inr hops
    · exact .inl hm
  refine ⟨⟨⟨hI.m.fn, hI.m.maxLt, fun y hy => ?_, hI.m.typesFresh, fun y m hm => ?_, fun y ms hms =>
      kgrow y (hI.m.altsKnown y ms hms), hI.m.availDef, hI.m.defAvail, fun y m hm ha hb => ?_,
      hI.m.badLe, hI.m.uniq⟩, hI.noPartial, fun n w hw => ?_, fun y ms hms m hm => ?_⟩,
    fun k ms hk => by simp [pureInsert] at hk, hgood, by rw [hdefs, ite_eq_left rfl],
    fun y hy => by rw [hdefs, ite_eq_right (Ne.symm hy)], rfl, rfl, rfl, rfl, rfl⟩
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
    (hops : ∀ y ∈ operands inst, Placed st0 B y) (halts : st0.alts.get? v = none)
    (hty : st0.types.get? v = SState.nodeTy inst)
    (hnode : NodeIn (fun y => st0.types.get? y) f (Placed st0 B) (st0.types.get? v) inst) :
    RInv f V B (· = v) (· = inst) (pureBest rules allowed bi st0 v inst).2 ∧
      CInv B (pureBest rules allowed bi st0 v inst).2 ∧
      RStep B st0 (pureBest rules allowed bi st0 v inst).2 ∧
      (pureBest rules allowed bi st0 v inst).2.memo.get? inst =
        some (pureBest rules allowed bi st0 v inst).1 ∧
      ((pureBest rules allowed bi st0 v inst).1 = v ∨
        (Placed (pureBest rules allowed bi st0 v inst).2 B (pureBest rules allowed bi st0 v inst).1 ∧
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
        NodeIn (fun y => st0.types.get? y) f (Placed st0 B) (st0.types.get? v) n := by
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
  good : ∀ y, Placed st B y → Placed stF B' y
  known : ∀ y, st.known y = true → stF.known y = true
  types : ∀ y t, st.types.get? y = some t → stF.types.get? y = some t
  avail : ∀ y d, st.avail.get? y = some d → stF.avail.get? y = some d
  availNew : ∀ y d, stF.avail.get? y = some d →
    st.avail.get? y = some d ∨ (d = bi ∧ ∃ t ∈ lg.out.toList, y ∈ t.results)
  defsKeep : ∀ y n, st.defs.get? y = some n → st.avail.contains y = true →
    stF.defs.get? y = some n
  kind : (lg = .keep { s with inst } ∧ subst' = subst ∧ stF.avail.get? v = some bi ∧
      Placed stF B' v ∧ stF.defs.get? v = some inst) ∨
    (∃ w, lg = .repl { s with inst } w lg.out ∧ subst' = subst.insert v w ∧
      (∀ j t, lg.out.toList[j]? = some t →
        NewOk idom (emitV V bi lg.out.toList) bi (b.body.length + j) allowed B' stF t) ∧
      Placed stF B' w ∧ AvailAt idom (emitV V bi lg.out.toList) bi (b.body.length + lg.out.size) w ∧
      stF.types.get? w = stF.types.get? v ∧ stF.avail.contains v = false)
  fresh : ∀ y n, stF.defs.get? y = some n → st.defs.get? y = some n ∨ maxValue f < y ∨ y = v
  alts : ∀ x ms, stF.alts.get? x = some ms → st.alts.get? x = some ms ∨ ¬ B' x

/-- The kept statement `v = inst` (`s.results = [v]`) becomes available at the end of block `bi`
and `v` placeable. -/
theorem keepAvail_ok {X : ValueId → Prop} {XN : Inst → Prop} {st1 : SState} {v : ValueId}
    {inst : Inst} {s : Stmt} {b : Block} {B' : ValueId → Prop}
    (hI1 : RInv f V B X XN st1) (hb : V bi = some b) (hres : s.results = [v])
    (hvd : st1.defs.get? v = some inst) (hvops : ∀ y ∈ operands inst, Placed st1 B y)
    (hvav : st1.avail.get? v = none) (halts : st1.alts.get? v = none)
    (hB'1 : ∀ y, B' y → B y) (hB'2 : ∀ y, y ≠ v → B y → B' y) (hnB' : ¬ B' v) :
    MInv f (emitV V bi [{ s with inst }]) B' ({ st1 with avail := st1.avail.insert v bi } : SState) ∧
      (∀ y, Placed st1 B y → Placed ({ st1 with avail := st1.avail.insert v bi } : SState) B' y) ∧
      Placed ({ st1 with avail := st1.avail.insert v bi } : SState) B' v ∧
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
  have hgood : ∀ y, Placed st1 B y → Placed ({ st1 with avail := st1.avail.insert v bi } : SState) B' y :=
    Placed.mono kgrow (fun y hy hb => hy.not_bad (hB'1 y hb)) (fun _ _ h => .inl h)
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
    · rw [havail, ite_eq_left rfl]
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
  · refine Placed.mk hnB' (kgrow v hvk) (fun n hn y hy => ?_) (fun ms hms => ?_)
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
    (hbest : best = v ∨ (Placed st1 B best ∧ st1.types.get? best = st1.types.get? v))
    (hvB : B v) (hvk1 : st1.known v = true) (hd1v : st1.defs.get? v = some inst)
    (hops1 : ∀ y ∈ operands inst, Placed st1 B y) (hav1 : st1.avail.get? v = none)
    (hal1 : st1.alts.get? v = none)
    (hgst1 : ∀ y, Placed st B y → Placed st1 B y) (hkst1 : ∀ y, st.known y = true → st1.known y = true)
    (htst1 : ∀ y t, st.types.get? y = some t → st1.types.get? y = some t)
    (havst1 : st1.avail = st.avail)
    (hdst1 : ∀ y n, st.defs.get? y = some n → st.avail.contains y = true → st1.defs.get? y = some n)
    (hfr1 : ∀ y n, st1.defs.get? y = some n → st.defs.get? y = some n ∨ maxValue f < y ∨ y = v)
    (halst1 : st1.alts = st.alts) :
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
  have hvav : st.avail.get? v = none := by rw [← havst1]; exact hav1
  -- the members of `best`'s class
  have hmem : ∀ ms, st1.classes.get? best = some ms → ∀ m ∈ ms, st1.known m = true ∧
      st1.types.get? m = st1.types.get? v ∧
      ∀ n, st1.defs.get? m = some n → ∀ y ∈ operands n, Placed st1 B y := by
    intro ms hms m hm
    obtain ⟨-, h1⟩ := hC1 best ms hms
    obtain ⟨e1, e2, e3⟩ := h1 m hm
    refine ⟨e1, ?_, e3⟩
    rw [e2]; rcases hbest with rfl | h
    · rfl
    · exact h.2
  have keep_case : (pureEmit cfg allowed bi st1 subst s inst v best =
      (({ st1 with avail := st1.avail.insert v bi } : SState), subst, StmtLog.keep { s with inst })) →
      ((pureEmit cfg allowed bi st1 subst s inst v best).2.2 = .keep { s with inst } ∧
      PureOk f cfg.idom allowed bi B (fun y => B y ∧ y ≠ v) V b st
        (pureAlts st1 (pureEmit cfg allowed bi st1 subst s inst v best).1 v best
          (pureEmit cfg allowed bi st1 subst s inst v best).2.2) subst
        (pureEmit cfg allowed bi st1 subst s inst v best).2.1 s inst v
        (pureEmit cfg allowed bi st1 subst s inst v best).2.2) := by
    intro he
    rw [he]
    refine ⟨rfl, ?_⟩
    obtain ⟨hMK, hgK, hgvK, hkK⟩ := keepAvail_ok (s := s) (B' := fun y => B y ∧ y ≠ v) hI1 hb hres
      hd1v hops1 hav1 hal1 (fun y h => h.1) (fun y hy h => ⟨h, hy⟩) (fun h => h.2 rfl)
    let stK : SState := { st1 with avail := st1.avail.insert v bi }
    have hIK : RInv f (emitV V bi [{ s with inst }]) (fun y => B y ∧ y ≠ v) (fun _ => False)
        (fun _ => False) stK := by
      refine ⟨hMK, hI1.noPartial, fun n w hw => ?_, fun x ms hx m hm => ?_⟩
      · obtain ⟨e1, e2, e3⟩ := hI1.memo n w hw
        refine ⟨.inl ?_, hkK w e2, e3⟩
        rcases e1 with e1 | ⟨rfl, -⟩
        · exact hgK w e1
        · exact hgvK
      · obtain ⟨e1, e2⟩ := hI1.alts x ms hx m hm
        exact ⟨hkK m e1, e2⟩
    have havK : ∀ y, stK.avail.get? y = if v = y then some bi else st1.avail.get? y :=
      fun y => hm_get?_insert' _ _ _ _
    -- the class of `best` becomes visible from `v`
    have hfin : ∃ stF, pureAlts st1 stK v best (.keep { s with inst }) = stF ∧
        RInv f (emitV V bi [{ s with inst }]) (fun y => B y ∧ y ≠ v) (fun _ => False)
          (fun _ => False) stF ∧
        (∀ y, Placed stK (fun y => B y ∧ y ≠ v) y → Placed stF (fun y => B y ∧ y ≠ v) y) ∧
        stF.avail = stK.avail ∧ stF.defs = stK.defs ∧ stF.types = stK.types ∧
        (∀ y, stK.known y = true → stF.known y = true) ∧
        (∀ x ms, stF.alts.get? x = some ms → stK.alts.get? x = some ms ∨ x = v) := by
      unfold pureAlts
      simp only [StmtLog.rep, beq_self_eq_true, Bool.true_or, ite_true]
      split
      · rename_i hne
        cases hcl : st1.classes.get? best with
        | none =>
          rw [Std.HashMap.get?_eq_getElem?] at hcl
          simp [hcl] at hne
        | some ms =>
          have := hmem ms hcl
          rw [Std.HashMap.get?_eq_getElem?] at hcl
          simp only [Option.getD_some]
          obtain ⟨h1, h2⟩ := hIK.altsInsert (x := v) (ms := ms) (hkK v hvk1) (fun m hm =>
            ⟨hkK m (this m hm).1, (this m hm).2.1,
             fun n hn y hy => hgK y ((this m hm).2.2 n hn y hy)⟩)
          refine ⟨_, rfl, h1, h2, rfl, rfl, rfl, fun y h => h, fun x ms' hx => ?_⟩
          simp only [hm_get?_insert'] at hx
          split at hx
          · rename_i he; exact .inr he.symm
          · exact .inl hx
      · exact ⟨_, rfl, hIK, fun _ h => h, rfl, rfl, rfl, fun _ h => h, fun _ _ h => .inl h⟩
    obtain ⟨stF, hF, hIF, hgF, haF, hdF, htF, hkF, halF⟩ := hfin
    rw [hF]
    refine ⟨hIF, fun y h => hgF y (hgK y (hgst1 y h)), fun y h => hkF y (hkK y (hkst1 y h)),
      fun y t h => by rw [htF]; exact htst1 y t h, fun y d h => ?_, fun y d h => ?_,
      fun y n h ha => by rw [hdF]; exact hdst1 y n h ha,
      .inl ⟨rfl, rfl, by rw [haF, havK, ite_eq_left rfl], hgF v hgvK, by rw [hdF]; exact hd1v⟩,
      fun y n h => by rw [hdF] at h; exact hfr1 y n h, fun x ms h => ?_⟩
    rotate_right
    · rcases halF x ms h with h | rfl
      · exact .inl (by rw [← halst1]; exact h)
      · exact .inr (fun hb => hb.2 rfl)
    · rw [haF, havK]; split
      · rename_i he; subst he; rw [hvav] at h; cases h
      · rw [havst1]; exact h
    · rw [haF, havK] at h; split at h
      · rename_i he; subst he; cases h
        exact .inr ⟨rfl, { s with inst }, by simp [StmtLog.out], by simp [hres]⟩
      · rw [havst1] at h; exact .inl h
  by_cases hbv : best = v
  · left; apply keep_case; unfold pureEmit; simp [hbv]
  have hgb := hbest.resolve_left hbv
  cases hm : materialize cfg allowed bi (st1.defs.size + 1) (st1, #[]) best with
  | none => left; apply keep_case; unfold pureEmit; simp [hbv, hm]
  | some r =>
    obtain ⟨w, st2, emitted⟩ := r
    right
    obtain ⟨stR, he, hRd, hRa, hRv, hRt, hRn, hRf, hRm, hRp⟩ : ∃ stR : SState,
        pureEmit cfg allowed bi st1 subst s inst v best =
          (stR, subst.insert v w, StmtLog.repl { s with inst } w emitted) ∧
        stR.defs = st2.defs ∧ stR.alts = st2.alts ∧ stR.avail = st2.avail ∧ stR.types = st2.types ∧
        stR.next = st2.next ∧ stR.fn = st2.fn ∧ stR.memo = st2.memo ∧
        stR.partialVals = st2.partialVals :=
      ⟨{ st2 with stats :=
          { st2.stats with rewritten := st2.stats.rewritten + 1, emitted := st2.stats.emitted + emitted.size } },
        by unfold pureEmit; simp [hbv, hm], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rw [he]
    obtain ⟨new, hout, hrun, hgw, hhw, htw⟩ := mat_spec _ _ _ _ _ _ _ _ b hI1.m hb hgb.1 hm
    simp only [List.nil_append] at hout
    have hI2 : RInv f (emitV V bi new) B (fun _ => False) (fun _ => False) stR := by
      refine ((hI1.of_mrun hrun).congr hRd hRa hRv hRt hRn hRf hRm hRp).dropX ?_
      intro n w' hw' hx hn
      rw [hx, hn] at hw'
      have hm2 : st2.memo = st1.memo := by
        obtain ⟨_, _, _, _, _, h⟩ := hrun.step.shape; rw [h]
      rw [hRm, hm2, hmem1] at hw'; cases hw'; exact absurd rfl hbv
    have hgR : ∀ y, Placed st1 B y → Placed stR B y := fun y h => Placed.congr hRd hRa hRv (hrun.good y h)
    have hkR : ∀ y, st1.known y = true → stR.known y = true := by
      intro y hy; have := hrun.step.known y hy
      simpa [SState.known, hRd, hRv] using this
    have hwk : stR.known w = true := (Placed.congr hRd hRa hRv hgw).known
    have hwv : w ≠ v := by rintro rfl; exact hgw.not_bad hvB
    have htwR : stR.types.get? w = stR.types.get? v := by
      rw [hRt, htw, hrun.step.typesKnown v hvk1]; exact hgb.2
    have hfin : ∃ stF, pureAlts st1 stR v best (.repl { s with inst } w emitted) = stF ∧
        RInv f (emitV V bi new) B (fun _ => False) (fun _ => False) stF ∧
        (∀ y, Placed stR B y → Placed stF B y) ∧
        stF.avail = stR.avail ∧ stF.defs = stR.defs ∧ stF.types = stR.types ∧
        (∀ y, stR.known y = true → stF.known y = true) ∧
        (∀ x ms, stF.alts.get? x = some ms → stR.alts.get? x = some ms ∨ x = w) := by
      by_cases hc : (w == v || st1.made.contains best) = true
      · by_cases hne : (!((st1.classes.get? best).getD []).isEmpty) = true
        · cases hcl : st1.classes.get? best with
          | none => rw [hcl] at hne; simp at hne
          | some ms =>
            have := hmem ms hcl
            obtain ⟨h1, h2⟩ := hI2.altsInsert (x := w) (ms := ms) hwk (fun m hm' =>
              ⟨hkR m (this m hm').1, by
                rw [htwR, hRt, hrun.step.typesKnown m (this m hm').1,
                  hrun.step.typesKnown v hvk1]; exact (this m hm').2.1,
               fun n hn y hy => by
                rw [hRd] at hn
                rcases hrun.nodes m n hn with hn0 | hn0
                · exact hgR y ((this m hm').2.2 n hn0 y hy)
                · exact Placed.congr hRd hRa hRv (hn0 y hy)⟩)
            refine ⟨_, ?_, h1, h2, rfl, rfl, rfl, fun y h => h, fun x ms' hx => by
              simp only [hm_get?_insert'] at hx
              split at hx
              · rename_i he; exact .inr he.symm
              · exact .inl hx⟩
            rw [hcl] at hne
            have hms : ms ≠ [] := by simpa using hne
            have hcl' : st1.classes[best]? = some ms := by rw [← Std.HashMap.get?_eq_getElem?]; exact hcl
            simp [pureAlts, StmtLog.rep, hc, hcl', hms]
        · refine ⟨_, ?_, hI2, fun _ h => h, rfl, rfl, rfl, fun _ h => h, fun _ _ h => .inl h⟩
          have hE : (st1.classes[best]?).getD [] = [] := by
            rw [← Std.HashMap.get?_eq_getElem?]; simpa using hne
          simp [pureAlts, StmtLog.rep, hc, hE]
      · refine ⟨_, ?_, hI2, fun _ h => h, rfl, rfl, rfl, fun _ h => h, fun _ _ h => .inl h⟩
        simp only [Bool.not_eq_true] at hc
        simp [pureAlts, StmtLog.rep, hc]
    obtain ⟨stF, hF, hIF, hgF, haF, hdF, htF, hkF, halF⟩ := hfin
    rw [hF]
    refine ⟨⟨w, emitted, rfl⟩, ?_⟩
    dsimp only
    have hout2 : (StmtLog.repl { s with inst } w emitted).out.toList = new := hout
    have hsz : (StmtLog.repl { s with inst } w emitted).out.size = new.length := by
      rw [← hout2, Array.length_toList]
    refine ⟨by rw [hout2]; exact hIF, fun y h => hgF y (hgR y (hgst1 y h)),
      fun y h => hkF y (hkR y (hkst1 y h)),
      fun y t h => by rw [htF, hRt]; exact hrun.step.types y t (htst1 y t h),
      fun y d h => by rw [haF, hRv]; exact hrun.step.avail y d (by rw [havst1]; exact h),
      fun y d h => ?_, fun y n h ha => ?_, .inr ⟨w, rfl, rfl, fun j t hj => ?_, hgF w (Placed.congr hRd hRa hRv hgw), ?_,
        by rw [htF]; exact htwR, ?_⟩, fun y n h => ?_, fun x ms h => ?_⟩
    rotate_right 2
    · rw [hdF, hRd] at h
      rcases hrun.step.fresh y n h with h | h
      · exact hfr1 y n h
      · exact .inr (.inl (by rw [← hI1.m.fn]; exact h))
    · rcases halF x ms h with h | rfl
      · refine .inl ?_
        rw [hRa] at h
        obtain ⟨_, _, _, _, _, e⟩ := hrun.step.shape
        rw [e] at h; rw [← halst1]; exact h
      · exact .inr (Placed.congr hRd hRa hRv hgw).not_bad
    · rw [haF, hRv] at h
      rcases hrun.step.availNew y d h with h | ⟨rfl, t, ht, hy⟩
      · rw [havst1] at h; exact .inl h
      · exact .inr ⟨rfl, t, by rw [hout2]; exact ht, hy⟩
    · rw [hdF, hRd]
      refine hrun.step.defsKeep y n (hdst1 y n h ha) ?_
      rw [havst1]; exact ha
    · rw [hout2] at hj ⊢
      have := hrun.stmts b hb j t hj
      exact (this.mono' (more := []) (fun y n hy _ => by rw [hdF, hRd]; exact hy)
        (fun y d hy => by rw [haF, hRv]; exact hy)
        (fun y hy => hgF y (Placed.congr hRd hRa hRv hy))) |> fun h => by simpa [emitV_nil] using h
    · rw [hout2, hsz]
      have := hhw.at_end (b := { b with body := b.body ++ new }) (by simp [emitV, hb])
      simpa using this
    · rw [haF, hRv]
      cases hc : st2.avail.contains v with
      | false => rfl
      | true =>
        obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 ((hm_contains_iff _ _).1 hc)
        rcases hrun.step.availNew v d hd with h | ⟨-, t, ht, hy⟩
        · rw [hav1] at h; cases h
        · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 ht
          obtain ⟨r, n', rfl, -, -, hrb, -⟩ := hrun.stmts b hb j t hj
          simp only [List.mem_singleton] at hy
          subst hy; exact absurd hvB hrb

/-- **The pure path** (module doc): kept (`v` leaves the bad values) or replaced. -/
theorem pure_ok {rules : SimplifyFn} (hR : SimpRulesOk rules) (allowed : Inst → Bool) (cfg : Cfg)
    (bi : Nat) {st : SState} {subst : Subst} {s : Stmt} {inst : Inst} {v : ValueId} {b : Block}
    (hI : RInv f V B (fun _ => False) (fun _ => False) st) (hb : V bi = some b)
    (hres : s.results = [v]) (hpure : isPure inst = true)
    (hpt : pureTyped (fun y => st.types.get? y) f inst = true)
    (hty : st.types.get? v = SState.nodeTy inst) (hops : ∀ y ∈ operands inst, Placed st B y)
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
  have hops0 : ∀ y ∈ operands inst, Placed (pureInsert st v inst) B y := fun y hy => hg0 y (hops y hy)
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
      (Placed (pureBest rules allowed bi (pureInsert st v inst) v inst).2 B
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
    (fun y n hy => by
      rcases hS1.fresh y n hy with h | h
      · by_cases hyv : y = v
        · exact .inr (.inr hyv)
        · rw [hd0 y hyv] at h; exact .inl h
      · exact .inr (.inl (by rw [← hI.m.fn]; exact h)))
    (hS1.alts.trans hal0)

end Pure

end Opt
