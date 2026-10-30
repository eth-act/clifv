import FV.Opt.Proof.CompleteSimpRules
import FV.Opt.Proof.CompleteGuards

/-!
# Completeness of simplify: the facts recorded along the pass

The pass visits the blocks of `f` in reverse postorder and their statements in order. At a point
of the run (the block records `logs` so far, the current block `bi`, its first `j` statements
processed with records `lgs`), the *output view* is the processed blocks (`blockOf`) and the
current block's statements so far; a source value is *done* when its definition is in a processed
block or before statement `j` of `bi`; the *bad* values are the source values not done yet and the
renamed values (`Bad`).

This module states the facts kept along the run and that they only improve as the run proceeds
(`Prog`, the `*.mono` lemmas):

* `OutStmt`: an output statement's operands are available and placeable (so never renamed), its
  results typed, its node recorded, and it is a renamed source instruction or an allowed node;
* `TermOut`: an output terminator likewise, branching only where the source terminator branched,
  with arguments of the source's types;
* `SLogFact`/`StmtsFact`/`TermLogFact`: the Prop form of `Opt.SimpCtx.stmtOk`/`stmtsOk`/`termOk`
  with placeability for "not renamed" and view availability for `availB`.
-/

namespace Opt

open Clif

section Defs

variable (f : Function)

/-- The output block of a processed block `d` with record `lg`. -/
def blockOf (d : Nat) (lg : BlockLog) : Option Block :=
  (f.blocks[d]?).map fun b =>
    { b with body := ((lg.stmts.toArray.flatMap (·.out)) ++ lg.extra).toList, term := lg.term' }

/-- The processed blocks, and the current block `bi` without statements. -/
def V0 (logs : Array (Option BlockLog)) (bi : Nat) : Nat → Option Block := fun d =>
  match logs[d]? with
  | some (some lg) => blockOf f d lg
  | _ => if d = bi then (f.blocks[d]?).map fun b => { b with body := [] } else none

/-- The output statements of records. -/
def outsOf (lgs : List StmtLog) : List Stmt := lgs.flatMap fun lg => lg.out.toList

/-- A source value defined in a processed block or before statement `j` of block `bi`. -/
def Done (logs : Array (Option BlockLog)) (bi j : Nat) (y : ValueId) : Prop :=
  ∃ d t, (defMap f).get? y = some (d, t) ∧ ((∃ lg, logs[d]? = some (some lg)) ∨ (d = bi ∧ t ≤ j))

/-- The bad values: source values not done yet, and renamed values. -/
def Bad (logs : Array (Option BlockLog)) (bi j : Nat) (S : Subst) (y : ValueId) : Prop :=
  (y ≤ maxValue f ∧ ¬ Done f logs bi j y) ∨ S.contains y = true

end Defs

section Facts

variable (f : Function) (info : Info) (allowed skelOk : Inst → Bool) (idom : Array (Option Nat))

/-- A new instruction: the renaming of an allowed node or skeleton instruction. -/
def NewInst (i : Inst) : Prop :=
  ∃ n σ, (allowed n = true ∨ skelOk n = true) ∧ i = mapOperands σ n ∧ notCall n = true ∧
    isCallInd n = false

/-- An output statement at index `k` of block `d` (module doc). -/
structure OutStmt (V : Nat → Option Block) (B : ValueId → Prop) (st : SState) (d k : Nat)
    (t : Stmt) : Prop where
  uses : ∀ y ∈ operands t.inst, AvailAt idom V d k y ∧ Placed st B y
  results : ∃ ts, t.inst.resultTypes (sigOf f) (fun _ => none) = some ts ∧
    ts.length = t.results.length ∧ ∀ (n : Nat) r, t.results[n]? = some r → st.types.get? r = ts[n]?
  pure : isPure t.inst = true → pureTyped (fun y => st.types.get? y) f t.inst = true
  node : ∀ x, t.results = [x] → isPure t.inst = true → st.defs.get? x = some t.inst
  leaf : skeletonStmt t = true → ∀ r ∈ t.results,
    st.defs.get? r = none ∧ (initAvail f).contains r = true
  nodup : t.results.Nodup
  guard : (∃ b0, f.blocks[d]? = some b0 ∧ ∃ s0 ∈ b0.body, ∃ τ, t.inst = mapOperands τ s0.inst) ∨
    NewInst allowed skelOk t.inst

/-- The output terminator `t` of block `d` (source block `b0`), after `blen` statements. -/
structure TermOut (V : Nat → Option Block) (B : ValueId → Prop) (st : SState) (d blen : Nat)
    (b0 : Block) (t : Terminator) : Prop where
  uses : ∀ y ∈ termOperands t, AvailAt idom V d blen y ∧ Placed st B y
  succs : ∀ id ∈ termSuccs t, id ∈ termSuccs b0.term
  calls : ∀ bc ∈ termCalls t, ∃ bc0 ∈ termCalls b0.term, bc.block = bc0.block ∧
    bc.args.map (fun x => st.types.get? x) = bc0.args.map (fun x => info.types.get? x)
  brt : brTableOk st.types t
  guard : (∃ τ, t = mapTerm τ b0.term) ∨ (isBranch b0.term = true ∧ isBranch t = true)

/-- The record of a skeleton statement (`SimpCtx.stmtOk`, `.skel` case). -/
def SkelLog (V : Nat → Option Block) (B : ValueId → Prop) (st : SState) (S : Subst) (d k' : Nat)
    (s s' : Stmt) (out : Array Stmt) : SkelOut → Prop
  | .keep => out = #[s'] ∧ ∀ r ∈ s.results, Placed st B r
  | .remove => notCall s.inst = true ∧ notSym s.inst = true ∧ s.results = [] ∧
      ∀ t ∈ out.toList, insOk t = true
  | .removeWithVal v' => notCall s.inst = true ∧ notSym s.inst = true ∧
      (∀ t ∈ out.toList, insOk t = true) ∧ AvailAt idom V d (k' + out.size) v' ∧
      ∃ r, s.results = [r] ∧ S.get? r = some v'
  | .replace i => notCall s.inst = true ∧ notSym s.inst = true ∧ (∀ r ∈ s.results, Placed st B r) ∧
      (∀ y ∈ operands i, Placed st B y) ∧ out.size ≥ 1 ∧
      (∀ t ∈ (out.extract 0 (out.size - 1)).toList, insOk t = true) ∧
      out[out.size - 1]? = some { results := s.results, inst := i } ∧ notCall i = true ∧
      notSym i = true
  | .two a c => notCall s.inst = true ∧ notSym s.inst = true ∧
      (∀ y ∈ operands a ++ operands c, Placed st B y) ∧ s.results = [] ∧ out.size ≥ 2 ∧
      (∀ t ∈ (out.extract 0 (out.size - 2)).toList, insOk t = true) ∧
      out[out.size - 2]? = some { inst := a } ∧ out[out.size - 1]? = some { inst := c } ∧
      notCall a = true ∧ notCall c = true ∧ notSym a = true ∧ notSym c = true

/-- The record of a statement (`SimpCtx.stmtOk`), its source operands done (renamed or not bad). -/
def SLogFact (V : Nat → Option Block) (B : ValueId → Prop) (st : SState) (S : Subst) (d : Nat)
    (s : Stmt) (k' : Nat) (lg : StmtLog) : Prop :=
  (∀ y ∈ operands s.inst, S.contains y = true ∨ ¬ B y) ∧
  match lg with
  | .keep s' => s' = renStmt S.step s ∧ ∀ r ∈ s.results, Placed st B r
  | .repl s' w out => s' = renStmt S.step s ∧ isPure s.inst = true ∧
      (∀ t ∈ out.toList, insOk t = true) ∧ (∃ v, s.results = [v] ∧ S.get? v = some w) ∧
      AvailAt idom V d (k' + out.size) w
  | .skel s' o out => s' = renStmt S.step s ∧ skeletonStmt s = true ∧
      SkelLog idom V B st S d k' s s' out o

/-- The records of a block's statements (`SimpCtx.stmtsOk`). -/
def StmtsFact (V : Nat → Option Block) (B : ValueId → Prop) (st : SState) (S : Subst) (d : Nat) :
    List Stmt → List StmtLog → Nat → Prop
  | [], [], _ => True
  | s :: ss, lg :: lgs, k' => SLogFact idom V B st S d s k' lg ∧ StmtsFact V B st S d ss lgs (k' + lg.out.size)
  | _, _, _ => False

/-- The record of a terminator (`SimpCtx.termOk`, and `lg.term`). -/
def TermLogFact (B : ValueId → Prop) (st : SState) (S : Subst) (b0 : Block) (lg : BlockLog) : Prop :=
  (∀ y ∈ termOperands b0.term, S.contains y = true ∨ ¬ B y) ∧ lg.term = mapTerm S.step b0.term ∧
  if lg.changed then isBranch lg.term = true ∧ (∀ y ∈ termOperands lg.term', Placed st B y) ∧
    ∀ t ∈ lg.extra.toList, insOk t = true ∨ (trapOk t = true ∧ ∀ y ∈ operands t.inst, Placed st B y)
  else lg.extra = #[] ∧ lg.term' = lg.term

end Facts

/-! ## Progress -/

/-- The view `V'` extends `V`: same blocks, longer bodies. -/
def VExt (V V' : Nat → Option Block) : Prop :=
  ∀ d b, V d = some b → ∃ b', V' d = some b' ∧ b'.params = b.params ∧ b'.id = b.id ∧
    ∃ rest, b'.body = b.body ++ rest

theorem VExt.refl (V : Nat → Option Block) : VExt V V :=
  fun _ b h => ⟨b, h, rfl, rfl, [], by simp⟩

theorem VExt.trans {V1 V2 V3 : Nat → Option Block} (h1 : VExt V1 V2) (h2 : VExt V2 V3) :
    VExt V1 V3 := by
  intro d b hb
  obtain ⟨b2, hb2, hp2, hi2, r2, hr2⟩ := h1 d b hb
  obtain ⟨b3, hb3, hp3, hi3, r3, hr3⟩ := h2 d b2 hb2
  exact ⟨b3, hb3, hp3.trans hp2, hi3.trans hi2, r2 ++ r3, by rw [hr3, hr2, List.append_assoc]⟩

theorem VExt.emit (V : Nat → Option Block) (bi : Nat) (new : List Stmt) : VExt V (emitV V bi new) := by
  intro d b hb
  by_cases hd : d = bi
  · subst hd; exact ⟨{ b with body := b.body ++ new }, by simp [emitV, hb], rfl, rfl, new, rfl⟩
  · exact ⟨b, by simp [emitV, hd, hb], rfl, rfl, [], by simp⟩

theorem DefAt.ext {V V' : Nat → Option Block} (h : VExt V V') {x : ValueId} {d t : Nat}
    (hx : DefAt V x d t) : DefAt V' x d t := by
  obtain ⟨b, hb, hx⟩ := hx
  obtain ⟨b', hb', hp, -, rest, hr⟩ := h d b hb
  refine ⟨b', hb', ?_⟩
  rcases hx with ⟨rfl, p, hp', rfl⟩ | ⟨j, s, rfl, hs, hx⟩
  · exact .inl ⟨rfl, p, by rw [hp]; exact hp', rfl⟩
  · refine .inr ⟨j, s, rfl, ?_, hx⟩
    rw [hr, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hs).1]; exact hs

theorem AvailAt.ext {idom : Array (Option Nat)} {V V' : Nat → Option Block} (h : VExt V V')
    {i k : Nat} {x : ValueId} (hx : AvailAt idom V i k x) : AvailAt idom V' i k x := by
  obtain ⟨d, t, hd, h'⟩ := hx
  exact ⟨d, t, hd.ext h, h'⟩

/-- How the run moves on (module doc). -/
structure Prog (V V' : Nat → Option Block) (B B' : ValueId → Prop) (st st' : SState)
    (S S' : Subst) : Prop where
  vext : VExt V V'
  good : ∀ y, Placed st B y → Placed st' B' y
  bad : ∀ y, B' y → B y
  types : ∀ y t, st.types.get? y = some t → st'.types.get? y = some t
  defsAv : ∀ x n, st.defs.get? x = some n → st.avail.contains x = true → st'.defs.get? x = some n
  defsLeaf : ∀ x, st.defs.get? x = none → st.known x = true → st'.defs.get? x = none
  subst : ∀ y w, S.get? y = some w → S'.get? y = some w
  newKeys : ∀ y, S'.contains y = true → S.contains y = true ∨ B y

theorem Prog.refl (V : Nat → Option Block) (B : ValueId → Prop) (st : SState) (S : Subst) :
    Prog V V B B st st S S :=
  ⟨VExt.refl V, fun _ h => h, fun _ h => h, fun _ _ h => h, fun _ _ h _ => h, fun _ h _ => h,
   fun _ _ h => h, fun _ h => .inl h⟩

theorem Prog.trans {V1 V2 V3 : Nat → Option Block} {B1 B2 B3 : ValueId → Prop}
    {st1 st2 st3 : SState} {S1 S2 S3 : Subst} (h1 : Prog V1 V2 B1 B2 st1 st2 S1 S2)
    (h2 : Prog V2 V3 B2 B3 st2 st3 S2 S3) (hk : ∀ x, st1.known x = true → st2.known x = true)
    (ha : ∀ x, st1.avail.contains x = true → st2.avail.contains x = true) :
    Prog V1 V3 B1 B3 st1 st3 S1 S3 :=
  ⟨h1.vext.trans h2.vext, fun y h => h2.good y (h1.good y h), fun y h => h1.bad y (h2.bad y h),
   fun y t h => h2.types y t (h1.types y t h),
   fun x n h hx => h2.defsAv x n (h1.defsAv x n h hx) (ha x hx),
   fun x h hx => h2.defsLeaf x (h1.defsLeaf x h hx) (hk x hx),
   fun y w h => h2.subst y w (h1.subst y w h),
   fun y h => by
     rcases h2.newKeys y h with h | h
     · rcases h1.newKeys y h with h | h
       · exact .inl h
       · exact .inr h
     · exact .inr (h1.bad y h)⟩

theorem Prog.step_eq {V V' : Nat → Option Block} {B B' : ValueId → Prop} {st st' : SState}
    {S S' : Subst} (h : Prog V V' B B' st st' S S') (hkB : ∀ y, S.contains y = true → B y)
    {y : ValueId} (hy : S.contains y = true ∨ ¬ B y) : S'.step y = S.step y := by
  unfold Subst.step
  rcases hy with hy | hy
  · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 ((hm_contains_iff _ _).1 hy)
    rw [hw, h.subst y w hw]
  · have h1 : S.get? y = none := by
      cases hc : S.get? y with
      | none => rfl
      | some w => exact absurd (hkB y ((hm_contains_iff _ _).2 (by rw [hc]; rfl))) hy
    have h2 : S'.get? y = none := by
      cases hc : S'.get? y with
      | none => rfl
      | some w =>
        rcases h.newKeys y ((hm_contains_iff _ _).2 (by rw [hc]; rfl)) with h3 | h3
        · rw [← Bool.not_eq_false, ← Bool.not_eq_true, hm_contains_iff, h1] at h3; simp at h3
        · exact absurd h3 hy
    rw [h1, h2]

theorem Prog.renStmt_eq {V V' : Nat → Option Block} {B B' : ValueId → Prop} {st st' : SState}
    {S S' : Subst} (h : Prog V V' B B' st st' S S') (hkB : ∀ y, S.contains y = true → B y)
    {s : Stmt} (hy : ∀ y ∈ operands s.inst, S.contains y = true ∨ ¬ B y) :
    renStmt S'.step s = renStmt S.step s := by
  simp only [renStmt]
  rw [mapOperands_congr (fun y hy' => h.step_eq hkB (hy y hy'))]

section Mono

variable {f : Function} {info : Info} {allowed skelOk : Inst → Bool} {idom : Array (Option Nat)}
  {V V' : Nat → Option Block} {B B' : ValueId → Prop} {st st' : SState} {S S' : Subst}

theorem OutStmt.mono {d k : Nat} {t : Stmt} (h : OutStmt f allowed skelOk idom V B st d k t)
    (hp : Prog V V' B B' st st' S S')
    (hav : ∀ x d t, DefAt V x d t → st.avail.get? x = some d)
    (hV : ∃ b, V d = some b ∧ b.body[k]? = some t) :
    OutStmt f allowed skelOk idom V' B' st' d k t := by
  obtain ⟨b, hb, hk⟩ := hV
  have hres : ∀ r ∈ t.results, st.avail.get? r = some d :=
    fun r hr => hav r d (k + 1) ⟨b, hb, .inr ⟨k, t, rfl, hk, hr⟩⟩
  obtain ⟨h1, ⟨ts, h2a, h2b, h2c⟩, h3, h4, h5, h6, h7⟩ := h
  refine ⟨fun y hy => ⟨(h1 y hy).1.ext hp.vext, hp.good y (h1 y hy).2⟩,
    ⟨ts, h2a, h2b, fun n r hr => ?_⟩, fun hpu => ?_, fun x hx hpu => ?_, fun hs r hr => ?_, h6, h7⟩
  · have := h2c n r hr
    have hrm : r ∈ t.results := List.mem_of_getElem? hr
    cases hts : ts[n]? with
    | none =>
      exfalso
      have := (List.getElem?_eq_some_iff.1 hr).1
      have : n < ts.length := by omega
      rw [List.getElem?_eq_getElem this] at hts; cases hts
    | some u => rw [hts] at this; exact hp.types r u this
  · exact pureTyped_grow hpu (h3 hpu) hp.types
  · have hxm : x ∈ t.results := by rw [hx]; simp
    exact hp.defsAv x _ (h4 x hx hpu) ((hm_contains_iff _ _).2 (by rw [hres x hxm]; rfl))
  · obtain ⟨e1, e2⟩ := h5 hs r hr
    exact ⟨hp.defsLeaf r e1 (known_iff.2 (.inr ((hm_contains_iff _ _).2 (by rw [hres r hr]; rfl)))), e2⟩

theorem TermOut.mono {d blen : Nat} {b0 : Block} {t : Terminator}
    (h : TermOut info idom V B st d blen b0 t) (hp : Prog V V' B B' st st' S S')
    (hknown : ∀ bc ∈ termCalls t, ∀ y ∈ bc.args, ∃ u, st.types.get? y = some u)
    (hbr : ∀ x d tb, t = .brTable x d tb → ∃ u, st.types.get? x = some u) :
    TermOut info idom V' B' st' d blen b0 t := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨fun y hy => ⟨(h1 y hy).1.ext hp.vext, hp.good y (h1 y hy).2⟩, h2,
    fun bc hbc => ?_, ?_, h5⟩
  · obtain ⟨bc0, hbc0, hbl, ha⟩ := h3 bc hbc
    refine ⟨bc0, hbc0, hbl, ?_⟩
    rw [← ha]
    refine List.map_congr_left (fun y hy => ?_)
    obtain ⟨u, hu⟩ := hknown bc hbc y hy
    rw [hu, hp.types y u hu]
  · cases t <;> simp only [brTableOk] at h4 ⊢
    exact hp.types _ _ h4


theorem SkelLog.mono {d k' : Nat} {s s' : Stmt} {out : Array Stmt} {o : SkelOut}
    (h : SkelLog idom V B st S d k' s s' out o) (hp : Prog V V' B B' st st' S S') :
    SkelLog idom V' B' st' S' d k' s s' out o := by
  cases o with
  | keep => exact ⟨h.1, fun r hr => hp.good r (h.2 r hr)⟩
  | remove => exact h
  | removeWithVal v =>
    obtain ⟨e1, e2, e3, e4, r, e5, e6⟩ := h
    exact ⟨e1, e2, e3, e4.ext hp.vext, r, e5, hp.subst r v e6⟩
  | replace i =>
    obtain ⟨e1, e2, e3, e4, e5⟩ := h
    exact ⟨e1, e2, fun r hr => hp.good r (e3 r hr), fun y hy => hp.good y (e4 y hy), e5⟩
  | two a c =>
    obtain ⟨e1, e2, e3, e4⟩ := h
    exact ⟨e1, e2, fun y hy => hp.good y (e3 y hy), e4⟩

theorem SLogFact.mono {d k' : Nat} {s : Stmt} {lg : StmtLog}
    (h : SLogFact idom V B st S d s k' lg) (hp : Prog V V' B B' st st' S S')
    (hkB : ∀ y, S.contains y = true → B y) : SLogFact idom V' B' st' S' d s k' lg := by
  obtain ⟨h0, h⟩ := h
  have hren := hp.renStmt_eq hkB h0
  refine ⟨fun y hy => ?_, ?_⟩
  · rcases h0 y hy with h1 | h1
    · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 ((hm_contains_iff _ _).1 h1)
      exact .inl ((hm_contains_iff _ _).2 (by rw [hp.subst y w hw]; rfl))
    · exact .inr (fun hb => h1 (hp.bad y hb))
  cases lg with
  | keep s' => exact ⟨by rw [hren]; exact h.1, fun r hr => hp.good r (h.2 r hr)⟩
  | repl s' w out =>
    obtain ⟨e1, e2, e3, ⟨v, e4, e5⟩, e6⟩ := h
    exact ⟨by rw [hren]; exact e1, e2, e3, ⟨v, e4, hp.subst v w e5⟩, e6.ext hp.vext⟩
  | skel s' o out =>
    obtain ⟨e1, e2, e3⟩ := h
    exact ⟨by rw [hren]; exact e1, e2, e3.mono hp⟩

theorem StmtsFact.mono {d : Nat} (hp : Prog V V' B B' st st' S S')
    (hkB : ∀ y, S.contains y = true → B y) :
    ∀ (ss : List Stmt) (lgs : List StmtLog) (k' : Nat), StmtsFact idom V B st S d ss lgs k' →
      StmtsFact idom V' B' st' S' d ss lgs k'
  | [], [], _, _ => trivial
  | s :: ss, lg :: lgs, k', ⟨h1, h2⟩ => ⟨h1.mono hp hkB, StmtsFact.mono hp hkB ss lgs _ h2⟩
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim

theorem TermLogFact.mono {b0 : Block} {lg : BlockLog} (h : TermLogFact B st S b0 lg)
    (hp : Prog V V' B B' st st' S S') (hkB : ∀ y, S.contains y = true → B y) :
    TermLogFact B' st' S' b0 lg := by
  obtain ⟨h0, h1, h2⟩ := h
  have hterm : mapTerm S'.step b0.term = mapTerm S.step b0.term :=
    mapTerm_congr (fun y hy => hp.step_eq hkB (h0 y hy))
  refine ⟨fun y hy => ?_, by rw [hterm]; exact h1, ?_⟩
  · rcases h0 y hy with e | e
    · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 ((hm_contains_iff _ _).1 e)
      exact .inl ((hm_contains_iff _ _).2 (by rw [hp.subst y w hw]; rfl))
    · exact .inr (fun hb => e (hp.bad y hb))
  split
  · rename_i hc
    rw [ite_eq_left hc] at h2
    obtain ⟨e1, e2, e3⟩ := h2
    refine ⟨e1, fun y hy => hp.good y (e2 y hy), fun t ht => ?_⟩
    rcases e3 t ht with e | ⟨e, e'⟩
    · exact .inl e
    · exact .inr ⟨e, fun y hy => hp.good y (e' y hy)⟩
  · rename_i hc
    rw [ite_eq_right hc] at h2
    exact h2

end Mono

/-! ## The leaves -/

/-- The leaves of `f` with their blocks (`initAvail`'s insertions). -/
def leafList (f : Function) : List (ValueId × Nat) :=
  f.blocks.zipIdx.flatMap fun x => x.1.params.map (fun p => (p.1, x.2)) ++
    (x.1.body.filter skeletonStmt).flatMap fun s => s.results.map (·, x.2)

theorem params_fold (ps : List (ValueId × Ty)) (bi : Nat) (m : Std.HashMap ValueId Nat) :
    ps.foldl (fun av (x : ValueId × Ty) => match x with | (p, _) => av.insert p bi) m =
      (ps.map fun p => (p.1, bi)).foldl (fun m (x : ValueId × Nat) => m.insert x.1 x.2) m := by
  induction ps generalizing m with
  | nil => rfl
  | cons p ps ih => exact ih _

theorem body_fold (body : List Stmt) (bi : Nat) (m : Std.HashMap ValueId Nat) :
    body.foldl (fun av s =>
      if (!(isPure s.inst && s.results.length == 1)) = true then
        s.results.foldl (fun av r => av.insert r bi) av
      else av) m =
      ((body.filter skeletonStmt).flatMap fun s => s.results.map (·, bi)).foldl
        (fun m (x : ValueId × Nat) => m.insert x.1 x.2) m := by
  induction body generalizing m with
  | nil => rfl
  | cons s ss ih =>
    rw [List.foldl_cons, List.filter_cons]
    by_cases hs : skeletonStmt s = true
    · have hs' : (!(isPure s.inst && s.results.length == 1)) = true := hs
      rw [ite_eq_left hs', ite_eq_left hs, List.flatMap_cons, List.foldl_append, List.foldl_map, ih]
    · have hs' : ¬ (!(isPure s.inst && s.results.length == 1)) = true := hs
      rw [ite_eq_right hs', ite_eq_right hs, ih]

theorem initAvail_eq (f : Function) :
    initAvail f = (leafList f).foldl (fun m x => m.insert x.1 x.2) {} := by
  unfold initAvail leafList
  rw [List.foldl_flatMap]
  congr 1
  funext av x
  obtain ⟨b, bi⟩ := x
  simp only [List.foldl_append]
  rw [params_fold, body_fold]

theorem foldl_insert_get2 {l : List (ValueId × Nat)} :
    ∀ (m : Std.HashMap ValueId Nat) v d,
      (l.foldl (fun m (x : ValueId × Nat) => m.insert x.1 x.2) m).get? v = some d →
      m.get? v = some d ∨ (v, d) ∈ l := by
  induction l with
  | nil => intro m v d h; exact .inl h
  | cons x l ih =>
    intro m v d h0
    rw [List.foldl_cons] at h0
    rcases ih _ v d h0 with h1 | h1
    · rw [hm_get?_insert] at h1
      split at h1
      · rename_i he
        simp only [Option.some.injEq] at h1
        subst he; subst h1; exact .inr (by simp)
      · exact .inl h1
    · exact .inr (List.mem_cons_of_mem _ h1)

theorem sublist_flatMap {α β : Type} {l : List α} {g h : α → List β}
    (hs : ∀ a ∈ l, (g a).Sublist (h a)) : (l.flatMap g).Sublist (l.flatMap h) := by
  induction l with
  | nil => exact List.Sublist.refl _
  | cons a l ih =>
    simp only [List.flatMap_cons]
    exact (hs a (by simp)).append (ih fun a ha => hs a (List.mem_cons_of_mem _ ha))

theorem filter_flatMap_sublist (l : List Stmt) :
    ((l.filter skeletonStmt).flatMap (·.results)).Sublist (l.flatMap (·.results)) := by
  induction l with
  | nil => exact List.Sublist.refl _
  | cons s ss ih =>
    rw [List.filter_cons]
    split
    · simp only [List.flatMap_cons]; exact ih.append_left _
    · simp only [List.flatMap_cons]; exact ih.trans (List.sublist_append_right _ _)

theorem leafList_nodup {f : Function} (hu : UniqueDefs f) : ((leafList f).map (·.1)).Nodup := by
  refine List.Sublist.nodup ?_ hu
  have e1 : (leafList f).map (·.1) = f.blocks.zipIdx.flatMap fun x =>
      x.1.params.map (·.1) ++ (x.1.body.filter skeletonStmt).flatMap (·.results) := by
    simp [leafList, List.map_flatMap, List.map_append, Function.comp_def, List.flatMap_map]
  have e2 : (defSites f).map (·.1) = f.blocks.zipIdx.flatMap fun x =>
      x.1.params.map (·.1) ++ x.1.body.flatMap (·.results) := by
    simp only [defSites, List.map_flatMap, List.map_append, List.map_map]
    congr 1; funext x
    have := sites_body_fst x.2 x.1.body 0
    simp only [List.map_flatMap, List.map_map] at this
    simp only [Function.comp_def] at this ⊢
    rw [this]
  rw [e1, e2]
  exact sublist_flatMap fun x _ => (List.Sublist.refl _).append (filter_flatMap_sublist _)

/-- **The leaves**: `initAvail` maps each block parameter and skeleton result to its block. -/
theorem initAvail_get {f : Function} (hu : UniqueDefs f) (x : ValueId) (d : Nat) :
    (initAvail f).get? x = some d ↔ (x, d) ∈ leafList f := by
  rw [initAvail_eq]
  constructor
  · intro h
    rcases foldl_insert_get2 _ x d h with h | h
    · simp at h
    · exact h
  · intro h
    have := foldl_insert_get_nodup _ (leafList_nodup hu) (x, d) h {}
    rw [Std.HashMap.get?_eq_getElem?]; exact this

theorem mem_leafList {f : Function} {x : ValueId} {d : Nat} :
    (x, d) ∈ leafList f ↔ ∃ b, f.blocks[d]? = some b ∧
      ((∃ p ∈ b.params, p.1 = x) ∨ ∃ s ∈ b.body, skeletonStmt s = true ∧ x ∈ s.results) := by
  simp only [leafList, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_filter,
    Prod.mk.injEq, List.mem_zipIdx_iff_getElem?]
  constructor
  · rintro ⟨⟨b, i⟩, hb, ⟨p, hp, rfl, rfl⟩ | ⟨s, ⟨hs, hsk⟩, r, hr, rfl, rfl⟩⟩
    · exact ⟨b, hb, .inl ⟨p, hp, rfl⟩⟩
    · exact ⟨b, hb, .inr ⟨s, hs, hsk, hr⟩⟩
  · rintro ⟨b, hb, ⟨p, hp, rfl⟩ | ⟨s, hs, hsk, hr⟩⟩
    · exact ⟨(b, d), hb, .inl ⟨p, hp, rfl, rfl⟩⟩
    · exact ⟨(b, d), hb, .inr ⟨s, ⟨hs, hsk⟩, x, hr, rfl, rfl⟩⟩

/-! ## The invariant of the run -/

/-- The output view at a point of block `bi` with records `lgs`. -/
def CurV (f : Function) (logs : Array (Option BlockLog)) (bi : Nat) (lgs : List StmtLog) :
    Nat → Option Block :=
  emitV (V0 f logs bi) bi (outsOf lgs)

/-- **The invariant of the run** at statement `j` of block `bi` (module doc). -/
structure SimpInv (f : Function) (info : Info) (allowed skelOk : Inst → Bool)
    (logs : Array (Option BlockLog)) (bi j : Nat) (lgs : List StmtLog) (st : SState) (S : Subst) :
    Prop where
  rinv : RInv f (CurV f logs bi lgs) (Bad f logs bi j S) (fun _ => False) (fun _ => False) st
  srcTy : ∀ y t, info.types.get? y = some t → st.types.get? y = some t
  leafAv : ∀ y d, (initAvail f).get? y = some d → st.avail.get? y = some d
  availSrc : ∀ y d, st.avail.get? y = some d → y ≤ maxValue f →
    (initAvail f).get? y = some d ∨ ∃ t, (defMap f).get? y = some (d, t) ∧ Done f logs bi j y
  defsSrc : ∀ y n, st.defs.get? y = some n → y ≤ maxValue f → Done f logs bi j y
  defsLeaf : ∀ y, (initAvail f).contains y = true → st.defs.get? y = none
  doneAv : ∀ y, Done f logs bi j y → S.contains y = false →
    Placed st (Bad f logs bi j S) y ∧ ∃ d t, (defMap f).get? y = some (d, t) ∧ st.avail.get? y = some d
  substOk : ∀ y w, S.get? y = some w → Done f logs bi j y ∧ Placed st (Bad f logs bi j S) w ∧
    (∃ d' t', DefAt (CurV f logs bi lgs) w d' t' ∧ ∃ d t, (defMap f).get? y = some (d, t) ∧
      (d' = d ∨ Anc info.cfg.idom d' d)) ∧ st.types.get? w = st.types.get? y
  outs : ∀ d b, CurV f logs bi lgs d = some b →
    (∃ b0, f.blocks[d]? = some b0 ∧ b.params = b0.params ∧ b.id = b0.id) ∧
    ∀ k t, b.body[k]? = some t →
      OutStmt f allowed skelOk info.cfg.idom (CurV f logs bi lgs) (Bad f logs bi j S) st d k t
  done : ∀ d lg, logs[d]? = some (some lg) → ∃ b0 bo, f.blocks[d]? = some b0 ∧
    blockOf f d lg = some bo ∧
    StmtsFact info.cfg.idom (CurV f logs bi lgs) (Bad f logs bi j S) st S d b0.body lg.stmts 0 ∧
    TermLogFact (Bad f logs bi j S) st S b0 lg ∧
    TermOut info info.cfg.idom (CurV f logs bi lgs) (Bad f logs bi j S) st d bo.body.length b0 lg.term'
  cur : ∃ b0, f.blocks[bi]? = some b0 ∧ j ≤ b0.body.length ∧
    StmtsFact info.cfg.idom (CurV f logs bi lgs) (Bad f logs bi j S) st S bi (b0.body.take j) lgs 0
  size : logs.size = f.blocks.length
  notbi : logs[bi]? = some none
  preds : ∀ d, d ≠ bi → Anc info.cfg.idom d bi → ∃ lg, logs[d]? = some (some lg)

section Inv

variable {f : Function} {info : Info} {allowed skelOk : Inst → Bool}
  {logs : Array (Option BlockLog)} {bi j : Nat} {lgs : List StmtLog} {st : SState} {S : Subst}

theorem SimpInv.keyBad (h : SimpInv f info allowed skelOk logs bi j lgs st S) :
    ∀ y, S.contains y = true → Bad f logs bi j S y := fun _ hy => .inr hy

theorem SimpInv.chainFree (h : SimpInv f info allowed skelOk logs bi j lgs st S) : ChainFree S := by
  intro k w hk
  obtain ⟨-, hw, -⟩ := h.substOk k w hk
  cases hc : S[w]? with
  | none => rfl
  | some u =>
    exact absurd (.inr ((hm_contains_iff _ _).2 (by rw [Std.HashMap.get?_eq_getElem?, hc]; rfl)))
      hw.not_bad

theorem SimpInv.find_eq (h : SimpInv f info allowed skelOk logs bi j lgs st S) (x : ValueId) :
    S.find x = S.step x := by
  rw [find_chainFree h.chainFree]; rfl

/-- The type of a defined value. -/
theorem Checked.typed {hc : Checked f info} {y : ValueId} {s : Nat × Nat}
    (h : (defMap f).get? y = some s) : ∃ t, info.types.get? y = some t := by
  have hs := hc.wf.sitesRev y s h
  obtain ⟨i, b, hb, ⟨p, hp, rfl, -⟩ | ⟨k, st, hst, hy, -⟩⟩ := mem_defSites.1 hs
  · exact ⟨p.2, hc.wf.params i b hb p hp⟩
  · obtain ⟨ts, -, hlen, hts⟩ := hc.wf.results i b hb k st hst
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 hy
    have := hts n y hn
    have hnl : n < ts.length := by have := (List.getElem?_eq_some_iff.1 hn).1; omega
    rw [List.getElem?_eq_getElem hnl] at this
    exact ⟨_, this⟩

/-- A use available (in `f`) at statement `j` of block `bi` reads a done value whose renaming
is placeable and available at the end of the current block, of the same type. -/
theorem SimpInv.renOp (hc : Checked f info) (h : SimpInv f info allowed skelOk logs bi j lgs st S)
    {y : ValueId} (hy : ∃ d t, (defMap f).get? y = some (d, t) ∧
      ((d = bi ∧ t ≤ j) ∨ (d ≠ bi ∧ Anc info.cfg.idom d bi))) :
    Done f logs bi j y ∧ (S.contains y = true ∨ ¬ Bad f logs bi j S y) ∧
      Placed st (Bad f logs bi j S) (S.step y) ∧
      AvailHere info.cfg.idom (CurV f logs bi lgs) bi (S.step y) ∧
      st.types.get? (S.step y) = info.types.get? y := by
  obtain ⟨d, t, hd, hpos⟩ := hy
  have hdone : Done f logs bi j y := by
    refine ⟨d, t, hd, ?_⟩
    rcases hpos with ⟨rfl, ht⟩ | ⟨hne, hanc⟩
    · exact .inr ⟨rfl, ht⟩
    · exact .inl (h.preds d hne hanc)
  obtain ⟨ty, hty⟩ := Checked.typed (hc := hc) hd
  have hty' := h.srcTy y ty hty
  cases hS : S.get? y with
  | some w =>
    obtain ⟨-, hw, ⟨d', t', hd', d0, t0, hd0, hrel⟩, htw⟩ := h.substOk y w hS
    rw [hd] at hd0; cases hd0
    have hstep : S.step y = w := by rw [Std.HashMap.get?_eq_getElem?] at hS; simp [Subst.step, hS]
    refine ⟨hdone, .inl ((hm_contains_iff _ _).2 (by rw [hS]; rfl)), by rw [hstep]; exact hw,
      ⟨d', t', by rw [hstep]; exact hd', ?_⟩, by rw [hstep, htw, hty', hty]⟩
    rcases hpos with ⟨rfl, -⟩ | ⟨hne, hanc⟩
    · rcases hrel with rfl | hrel
      · exact .inl rfl
      · exact .inr hrel
    · rcases hrel with rfl | hrel
      · exact .inr hanc
      · exact .inr (hrel.trans hanc)
  | none =>
    have hk : S.contains y = false := by
      cases hc' : S.contains y with
      | false => rfl
      | true => rw [hm_contains_iff, hS] at hc'; cases hc'
    obtain ⟨hp, d1, t1, hd1, hav⟩ := h.doneAv y hdone hk
    rw [hd] at hd1; cases hd1
    have hstep : S.step y = y := by rw [Std.HashMap.get?_eq_getElem?] at hS; simp [Subst.step, hS]
    obtain ⟨t2, ht2⟩ := h.rinv.m.availDef y d hav hp.not_bad
    refine ⟨hdone, .inr hp.not_bad, by rw [hstep]; exact hp, ⟨d, t2, by rw [hstep]; exact ht2, ?_⟩,
      by rw [hstep, hty', hty]⟩
    rcases hpos with ⟨rfl, -⟩ | ⟨-, hanc⟩
    · exact .inl rfl
    · exact .inr hanc

end Inv

end Opt
