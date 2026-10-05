import FV.Backend.Proof.LowerFix
import FV.Backend.Proof.LowerLoop
import FV.Backend.Proof.IselFlow
import FV.Backend.Proof.TryRegs

/-!
# Completeness of `lowerCheck`: facts for the certificate

The facts `certOk_complete` (`LowerCert.lean`) builds on:

* list facts (sublists of `flatMap`s, the positions of a `Nodup` `flatMap`, strict `countP`);
* SSA facts: a value of `f` is defined at most once (`res_unique`, `par_not_res`), a statement
  result's definition is its statement (`defInst_res`, `inst_at`);
* the fresh-vreg ranges of the recorded lowering are increasing in layout order (`BlockOrd`,
  `lowBlocks_ord`);
* the recorded aliases (`mem_aliasOf`, `aliasOf_keys`);
* the must-availability `availIn` without renaming: closed under the results of a statement
  (`availIn_sib`), and the values a statement's lowering may return (`Prov`) are available
  before it (`prov_avail`), as are those of an available value's definition (`prov_closed`);
  for a value available at a block entry and not redefined there, they are too (`prov_entry`).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-! ## Lists -/

/-- An element's image is a sublist of the `flatMap`. -/
theorem sublist_flatMap_of_mem {α β : Type} {g : α → List β} :
    ∀ {l : List α} {a : α}, a ∈ l → (g a).Sublist (l.flatMap g)
  | b :: l, a, h => by
    rw [List.flatMap_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact List.sublist_append_left _ _
    · exact (sublist_flatMap_of_mem h).trans (List.sublist_append_right _ _)

/-- `flatMap` is monotone for the sublist order. -/
theorem flatMap_sublist_flatMap {α β : Type} {g h : α → List β} (hg : ∀ a, (g a).Sublist (h a)) :
    ∀ l : List α, (l.flatMap g).Sublist (l.flatMap h)
  | [] => List.Sublist.slnil
  | a :: l => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact (hg a).append (flatMap_sublist_flatMap hg l)

/-- In a `Nodup` `flatMap`, an element lies in the image of one position only. -/
theorem flatMap_nodup_idx {α β : Type} {g : α → List β} :
    ∀ {l : List α} {i j : Nat} {a b : α} {x : β}, (l.flatMap g).Nodup → l[i]? = some a →
      l[j]? = some b → x ∈ g a → x ∈ g b → i = j
  | [], _, _, _, _, _, _, h, _, _, _ => by simp at h
  | c :: l, i, j, a, b, x, hn, ha, hb, hxa, hxb => by
    rw [List.flatMap_cons, List.nodup_append] at hn
    obtain ⟨-, hn2, hdis⟩ := hn
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at ha hb
        subst ha
        exact absurd rfl (hdis x hxa x (List.mem_flatMap.mpr ⟨b, List.mem_of_getElem? hb, hxb⟩))
    | succ i =>
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at ha hb
        subst hb
        exact absurd rfl (hdis x hxb x (List.mem_flatMap.mpr ⟨a, List.mem_of_getElem? ha, hxa⟩))
      | succ j =>
        simp only [List.getElem?_cons_succ] at ha hb
        rw [flatMap_nodup_idx hn2 ha hb hxa hxb]

/-- The first components of a `filterMap` over a `zip` keeping first components. -/
theorem zip_filterMap_fst {β γ : Type} (g : Nat → β → Option (Nat × γ))
    (hg : ∀ a b p, g a b = some p → p.1 = a) :
    ∀ (l1 : List Nat) (l2 : List β),
      (((l1.zip l2).filterMap fun p => g p.1 p.2).map (·.1)).Sublist l1
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l1, b :: l2 => by
    rw [List.zip_cons_cons, List.filterMap_cons]
    cases h : g a b with
    | none => exact (zip_filterMap_fst g hg l1 l2).cons a
    | some p =>
      rw [List.map_cons, hg a b p h]
      exact (zip_filterMap_fst g hg l1 l2).cons_cons a

/-- The first components of a `flatMap` over a `zip`. -/
theorem zip_flatMap_fst {α β γ δ : Type} (g : α → β → List (δ × γ)) (h : α → List δ)
    (hg : ∀ a b, ((g a b).map (·.1)).Sublist (h a)) :
    ∀ (l1 : List α) (l2 : List β),
      (((l1.zip l2).flatMap fun p => g p.1 p.2).map (·.1)).Sublist (l1.flatMap h)
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l1, b :: l2 => by
    rw [List.zip_cons_cons, List.flatMap_cons, List.flatMap_cons, List.map_append]
    exact (hg a b).append (zip_flatMap_fst g h hg l1 l2)

/-- A pointwise smaller predicate, strictly smaller at an element, counts strictly less. -/
theorem certCountP_lt {α : Type} {p q : α → Bool} :
    ∀ {l : List α} {a : α}, (∀ x ∈ l, p x = true → q x = true) → a ∈ l → q a = true →
      p a = false → l.countP p < l.countP q
  | [], _, _, h, _, _ => by simp at h
  | b :: l, a, hpq, ha, hqa, hpa => by
    rw [List.countP_cons, List.countP_cons]
    have hl : ∀ x ∈ l, p x = true → q x = true := fun x hx => hpq x (List.mem_cons_of_mem b hx)
    rcases List.mem_cons.mp ha with rfl | ha
    · have := List.countP_mono_left hl
      simp [hqa, hpa]; omega
    · have := certCountP_lt hl ha hqa hpa
      have hb := hpq b List.mem_cons_self
      by_cases hp : p b = true
      · simp [hp, hb hp]; omega
      · by_cases hq : q b = true
        · simp [hp, hq]; omega
        · simp [hp, hq]; omega

/-! ## SSA -/

section
variable {f : Clif.Function}

/-- The parameters of an existing block. -/
theorem parsOf_of {bi : Nat} {B : Clif.Block} (hB : f.blocks[bi]? = some B) :
    parsOf f bi = B.params.map (·.1) := by simp [parsOf, hB]

/-- The results of an existing block. -/
theorem defsOf_of {bi : Nat} {B : Clif.Block} (hB : f.blocks[bi]? = some B) :
    defsOf f bi = B.body.flatMap (·.results) := by simp [defsOf, hB]

/-- A result of a block is a result of one of its statements. -/
theorem mem_defs {B : Clif.Block} {x : Nat} :
    x ∈ B.body.flatMap (·.results) ↔ ∃ (j : Nat) (stm : Clif.Stmt), B.body[j]? = some stm ∧ x ∈ stm.results := by
  constructor
  · intro h
    obtain ⟨stm, hs, hx⟩ := List.mem_flatMap.mp h
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hs
    exact ⟨j, stm, hj, hx⟩
  · rintro ⟨j, stm, hj, hx⟩
    exact List.mem_flatMap.mpr ⟨stm, List.mem_of_getElem? hj, hx⟩

/-- `defsOf` membership by statement. -/
theorem mem_defsOf {bi x : Nat} :
    x ∈ defsOf f bi ↔ ∃ (B : Clif.Block) (j : Nat) (stm : Clif.Stmt), f.blocks[bi]? = some B ∧ B.body[j]? = some stm ∧
      x ∈ stm.results := by
  unfold defsOf
  cases hB : f.blocks[bi]? with
  | none => simp
  | some B =>
    simp only [mem_defs]
    constructor
    · rintro ⟨j, stm, h1, h2⟩; exact ⟨B, j, stm, rfl, h1, h2⟩
    · rintro ⟨B', j, stm, h, h1, h2⟩; cases h; exact ⟨j, stm, h1, h2⟩

/-- A parameter is a value of `f`. -/
theorem mem_valueDefs_par {bi : Nat} {B : Clif.Block} (hB : f.blocks[bi]? = some B) {x : Nat}
    (hx : x ∈ B.params.map (·.1)) : x ∈ valueDefs f :=
  List.mem_flatMap.mpr ⟨B, List.mem_of_getElem? hB, List.mem_append_left _ hx⟩

/-- A statement result is a value of `f`. -/
theorem mem_valueDefs_res {bi j : Nat} {B : Clif.Block} {stm : Clif.Stmt}
    (hB : f.blocks[bi]? = some B) (hs : B.body[j]? = some stm) {x : Nat} (hx : x ∈ stm.results) :
    x ∈ valueDefs f :=
  List.mem_flatMap.mpr ⟨B, List.mem_of_getElem? hB,
    List.mem_append_right _ (mem_defs.mpr ⟨j, stm, hs, hx⟩)⟩

variable (hssa : (valueDefs f).Nodup)
include hssa

/-- With SSA, a block's parameters and results are distinct. -/
theorem block_nodup {bi : Nat} {B : Clif.Block} (hB : f.blocks[bi]? = some B) :
    (B.params.map (·.1) ++ B.body.flatMap (·.results)).Nodup :=
  hssa.sublist (sublist_flatMap_of_mem
    (g := fun B : Clif.Block => B.params.map (·.1) ++ B.body.flatMap (·.results))
    (List.mem_of_getElem? hB))

/-- With SSA, a statement's results are distinct. -/
theorem stmt_nodup {bi j : Nat} {B : Clif.Block} {stm : Clif.Stmt} (hB : f.blocks[bi]? = some B)
    (hs : B.body[j]? = some stm) : stm.results.Nodup :=
  (List.nodup_append.mp (block_nodup hssa hB)).2.1.sublist
    (sublist_flatMap_of_mem (List.mem_of_getElem? hs))

/-- A result is defined by one statement. -/
theorem res_unique {bi j bi' j' : Nat} {B B' : Clif.Block} {stm stm' : Clif.Stmt} {x : Nat}
    (hB : f.blocks[bi]? = some B) (hs : B.body[j]? = some stm) (hx : x ∈ stm.results)
    (hB' : f.blocks[bi']? = some B') (hs' : B'.body[j']? = some stm') (hx' : x ∈ stm'.results) :
    bi = bi' ∧ j = j' := by
  have e : bi = bi' := flatMap_nodup_idx hssa hB hB'
    (List.mem_append_right _ (mem_defs.mpr ⟨j, stm, hs, hx⟩))
    (List.mem_append_right _ (mem_defs.mpr ⟨j', stm', hs', hx'⟩))
  subst e
  rw [hB] at hB'; cases hB'
  exact ⟨rfl, flatMap_nodup_idx (List.nodup_append.mp (block_nodup hssa hB)).2.1 hs hs' hx hx'⟩

/-- A parameter is no result. -/
theorem par_not_res {bi bi' j' : Nat} {B B' : Clif.Block} {stm : Clif.Stmt} {x : Nat}
    (hB : f.blocks[bi]? = some B) (hx : x ∈ B.params.map (·.1))
    (hB' : f.blocks[bi']? = some B') (hs : B'.body[j']? = some stm) (hx' : x ∈ stm.results) :
    False := by
  have e : bi = bi' := flatMap_nodup_idx hssa hB hB' (List.mem_append_left _ hx)
    (List.mem_append_right _ (mem_defs.mpr ⟨j', stm, hs, hx'⟩))
  subst e
  rw [hB] at hB'; cases hB'
  exact (List.nodup_append.mp (block_nodup hssa hB)).2.2 x hx x (mem_defs.mpr ⟨j', stm, hs, hx'⟩) rfl

/-- A parameter of block `bi` is not in `defsOf` of any block. -/
theorem par_not_defs {bi tl : Nat} {B : Clif.Block} {x : Nat} (hB : f.blocks[bi]? = some B)
    (hx : x ∈ B.params.map (·.1)) : x ∉ defsOf f tl := by
  intro h
  obtain ⟨T, k, stm, hT, hs, hx'⟩ := mem_defsOf.mp h
  exact par_not_res hssa hB hx hT hs hx'

/-- A result is no parameter of any block. -/
theorem res_not_pars {bi j tl : Nat} {B : Clif.Block} {stm : Clif.Stmt} {x : Nat}
    (hB : f.blocks[bi]? = some B) (hs : B.body[j]? = some stm) (hx : x ∈ stm.results) :
    x ∉ parsOf f tl := by
  unfold parsOf
  split
  · rename_i T hT; exact fun hp => par_not_res hssa hT hp hB hs hx
  · simp

end

/-! ## The context -/

section
variable {f : Clif.Function} {ctx : Ctx} {st0 : LState} (hF : CtxFacts f ctx st0)
  (hssa : (valueDefs f).Nodup)
include hF hssa

/-- A result's definition is its statement's instruction. -/
theorem defInst_res {bi j : Nat} {B : Clif.Block} {stm : Clif.Stmt} {x : Nat}
    (hB : f.blocks[bi]? = some B) (hs : B.body[j]? = some stm) (hx : x ∈ stm.results) :
    ctx.defInst? x = some (blockStart f bi + j) :=
  (hF.defs hssa x _).mpr ⟨bi, B, j, stm, hB, hs, hx, rfl⟩

/-- The instruction defining a value is its statement's. -/
theorem inst_at {x d : Nat} {info : IInfo} (hd : ctx.defInst? x = some d)
    (hi : ctx.insts[d]? = some info) :
    ∃ bi B j stm, f.blocks[bi]? = some B ∧ B.body[j]? = some stm ∧ x ∈ stm.results ∧
      d = blockStart f bi + j ∧ info.clif = some stm.inst ∧ info.results = stm.results := by
  obtain ⟨bi, B, j, stm, hB, hs, hx, rfl⟩ := (hF.defs hssa x d).mp hd
  obtain ⟨info', hi', hc, hr⟩ := hF.stmt bi B j stm hB hs
  rw [hi] at hi'; cases hi'
  exact ⟨bi, B, j, stm, hB, hs, hx, rfl, hc, hr⟩

/-- A parameter has no definition. -/
theorem defInst_par {bi : Nat} {B : Clif.Block} {x : Nat} (hB : f.blocks[bi]? = some B)
    (hx : x ∈ B.params.map (·.1)) : ctx.defInst? x = none := by
  cases hd : ctx.defInst? x with
  | none => rfl
  | some d =>
    obtain ⟨bi', B', j, stm, hB', hs, hx', -⟩ := (hF.defs hssa x d).mp hd
    exact (par_not_res hssa hB hx hB' hs hx').elim

/-- The definition operands of a result are its statement's operands. -/
theorem defArgs_res {bi j : Nat} {B : Clif.Block} {stm : Clif.Stmt} {x : Nat}
    (hB : f.blocks[bi]? = some B) (hs : B.body[j]? = some stm) (hx : x ∈ stm.results) :
    defArgs ctx x = instArgs stm.inst := by
  obtain ⟨info, hi, hc, -⟩ := hF.stmt bi B j stm hB hs
  exact defArgs_eq (defInst_res hF hssa hB hs hx) hi hc

end

/-- The values of `f` are below the first temporary. -/
theorem lt_of_valueDefs {f : Clif.Function} {ctx : Ctx} {st0 : LState} (hF : CtxFacts f ctx st0)
    {x : Nat} (hx : x ∈ valueDefs f) : x < st0.nextVreg := (hF.vals x hx).1

/-! ## The fresh-vreg ranges of the recorded lowering -/

/-- The fresh-vreg ranges of a block's lowering (statements, then the terminator) are increasing
and start at or above `v`. -/
structure BlockOrd (v : Nat) (L : BLow) : Prop where
  stmt : ∀ (j : Nat) (sl : SLow), L.sl[j]? = some sl → v ≤ sl.st.nextVreg ∧ sl.st.nextVreg ≤ sl.st'.nextVreg ∧
    sl.st'.nextVreg ≤ L.tst.nextVreg ∧
    ∀ (j' : Nat) (sl' : SLow), j < j' → L.sl[j']? = some sl' → sl.st'.nextVreg ≤ sl'.st.nextVreg
  term : v ≤ L.tst.nextVreg ∧ L.tst.nextVreg ≤ L.tst'.nextVreg

/-- `BlockOrd` for a smaller lower bound. -/
theorem BlockOrd.mono {v v' : Nat} {L : BLow} (h : BlockOrd v L) (hv : v' ≤ v) : BlockOrd v' L :=
  ⟨fun j sl hs => let ⟨a, b, c, d⟩ := h.stmt j sl hs; ⟨by omega, b, c, d⟩,
    ⟨by have := h.term.1; omega, h.term.2⟩⟩

/-- The statement loop's ranges are increasing, between its start and end states. -/
theorem lowStmts_ord {call : StmtCall}
    (hmono : ∀ ii s r, call ii s = .ok r → s.nextVreg ≤ r.2.1.nextVreg) :
    ∀ {ss : List Clif.Stmt} {ii : Nat} {st : LState} {sls : List SLow} {stE : LState},
      lowStmts call ii ss st = some (sls, stE) → st.nextVreg ≤ stE.nextVreg ∧
      ∀ (j : Nat) (sl : SLow), sls[j]? = some sl → st.nextVreg ≤ sl.st.nextVreg ∧
        sl.st.nextVreg ≤ sl.st'.nextVreg ∧ sl.st'.nextVreg ≤ stE.nextVreg ∧
        ∀ (j' : Nat) (sl' : SLow), j < j' → sls[j']? = some sl' → sl.st'.nextVreg ≤ sl'.st.nextVreg := by
  intro ss
  induction ss with
  | nil =>
    intro ii st sls stE h
    simp only [lowStmts, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Nat.le_refl _, fun j sl h => by simp at h⟩
  | cons s ss ih =>
    intro ii st sls stE h
    simp only [lowStmts] at h
    cases hrun : call ii { st with emitted := #[] } with
    | error e => rw [hrun] at h; cases h
    | ok q =>
      obtain ⟨out, st', tr'⟩ := q
      have hm := hmono _ _ _ hrun
      simp only at hm
      rw [hrun] at h
      cases hout : regsOf out with
      | none => simp only [hout] at h; cases h
      | some rss =>
        cases hrec : lowStmts call (ii + 1) ss { st' with emitted := #[] } with
        | none => simp only [hout, hrec, Option.map_none] at h; cases h
        | some q =>
          obtain ⟨sls', stE'⟩ := q
          simp only [hout, hrec, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨h0, hj⟩ := ih hrec
          simp only at h0 hj
          refine ⟨by omega, fun j sl hsl => ?_⟩
          cases j with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hsl
            subst hsl
            refine ⟨Nat.le_refl _, hm, h0, fun j' sl' hj' hsl' => ?_⟩
            obtain ⟨j', rfl⟩ : ∃ k, j' = k + 1 := ⟨j' - 1, by omega⟩
            simp only [List.getElem?_cons_succ] at hsl'
            exact (hj j' sl' hsl').1
          | succ j =>
            simp only [List.getElem?_cons_succ] at hsl
            obtain ⟨a, b, c, d⟩ := hj j sl hsl
            refine ⟨by omega, b, c, fun j' sl' hj' hsl' => ?_⟩
            obtain ⟨j', rfl⟩ : ∃ k, j' = k + 1 := ⟨j' - 1, by omega⟩
            simp only [List.getElem?_cons_succ] at hsl'
            exact d j' sl' (by omega) hsl'

/-- A `try_call` terminator has its exception table. -/
theorem isTry_with {t : Clif.Terminator} (h : t.isTry = true) : ∃ et, IsTryWith t et := by
  cases t with
  | tryCall fn args et => exact ⟨et, .inl ⟨fn, args, rfl⟩⟩
  | tryCallIndirect c args et => exact ⟨et, .inr ⟨c, args, rfl⟩⟩
  | _ => simp [Clif.Terminator.isTry] at h

/-- A terminator's lowering only allocates. -/
theorem cert_lowTerm_mono {f : Clif.Function} {tcall : TermCallF} {ycall : TryCallF}
    (htm : ∀ ti data t targets s r, tcall ti data t targets s = .ok r → s.nextVreg ≤ r.2.1.nextVreg)
    (hym : ∀ ti data trs targets s r, ycall ti data trs targets s = .ok r →
      s.nextVreg ≤ r.2.1.nextVreg)
    {ti : Nat} {t : Clif.Terminator} {tst : LState} {nl : Nat} {data : V} {targets : List Label}
    {tl : Option TryLow} {tst' : LState} {nl' : Nat}
    (h : lowTerm f tcall ycall ti t tst nl = some (data, targets, tl, tst', nl')) :
    tst.nextVreg ≤ tst'.nextVreg := by
  obtain ⟨h1, h2⟩ := lowTerm_spec h
  cases hti : t.isTry with
  | false =>
    obtain ⟨-, -, out, tr, hc⟩ := h1 hti
    exact htm _ _ _ _ _ _ hc
  | true =>
    obtain ⟨et, het⟩ := isTry_with hti
    obtain ⟨T, -, -, he, -, hr, -, out, tr, hy⟩ := h2 et het
    obtain ⟨-, -, h3, -⟩ := tryRegsOf_spec (exnTableOpnd_cc he) hr
    have := hym _ _ _ _ _ _ hy
    simp only at this
    omega

/-- The ranges of the recorded lowering: increasing within a block, above the start state, and
the ranges of a later block above the end of an earlier block's terminator. -/
theorem lowBlocks_ord {f : Clif.Function} {call : StmtCall} {tcall : TermCallF} {ycall : TryCallF}
    (hmono : ∀ ii s r, call ii s = .ok r → s.nextVreg ≤ r.2.1.nextVreg)
    (htm : ∀ ti data t targets s r, tcall ti data t targets s = .ok r → s.nextVreg ≤ r.2.1.nextVreg)
    (hym : ∀ ti data trs targets s r, ycall ti data trs targets s = .ok r →
      s.nextVreg ≤ r.2.1.nextVreg) :
    ∀ {Bs : List Clif.Block} {start : Nat} {st : LState} {nl : Nat} {bl : List BLow},
      lowBlocks f call tcall ycall start Bs st nl = some bl →
      (∀ (bi : Nat) (L : BLow), bl[bi]? = some L → BlockOrd st.nextVreg L) ∧
      ∀ (bi bi' : Nat) (L L' : BLow), bi < bi' → bl[bi]? = some L → bl[bi']? = some L' →
        BlockOrd L.tst'.nextVreg L' := by
  intro Bs
  induction Bs with
  | nil =>
    intro start st nl bl h
    simp only [lowBlocks, Option.some.injEq] at h
    subst h
    exact ⟨fun bi L h => by simp at h, fun bi bi' L L' _ h => by simp at h⟩
  | cons B Bs ih =>
    intro start st nl bl h
    simp only [lowBlocks] at h
    cases hstm : lowStmts call start B.body st with
    | none => rw [hstm] at h; cases h
    | some q =>
      obtain ⟨sls, stE⟩ := q
      rw [hstm] at h
      simp only at h
      cases hterm : lowTerm f tcall ycall (start + B.body.length) B.term
          { stE with emitted := #[] } nl with
      | none => rw [hterm] at h; cases h
      | some q =>
        obtain ⟨data, targets, tl, tst', nl'⟩ := q
        rw [hterm] at h
        simp only at h
        cases hrec : lowBlocks f call tcall ycall (start + B.body.length + 1) Bs
            { tst' with emitted := #[] } nl' with
        | none => rw [hrec] at h; cases h
        | some bl' =>
          rw [hrec] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          obtain ⟨hA, hP⟩ := ih hrec
          obtain ⟨hs0, hs⟩ := lowStmts_ord hmono hstm
          have ht := cert_lowTerm_mono htm hym hterm
          simp only at ht hA
          have hhead : BlockOrd st.nextVreg
              ⟨start, sls, data, targets, { stE with emitted := #[] }, tst', tl⟩ :=
            ⟨fun j sl hsl => hs j sl hsl, ⟨hs0, ht⟩⟩
          refine ⟨fun bi L hL => ?_, fun bi bi' L L' hlt hL hL' => ?_⟩
          · cases bi with
            | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hL
              subst hL; exact hhead
            | succ bi =>
              simp only [List.getElem?_cons_succ] at hL
              exact (hA bi L hL).mono (by omega)
          · obtain ⟨b', rfl⟩ : ∃ k, bi' = k + 1 := ⟨bi' - 1, by omega⟩
            simp only [List.getElem?_cons_succ] at hL'
            cases bi with
            | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hL
              subst hL; exact hA b' L' hL'
            | succ bi =>
              simp only [List.getElem?_cons_succ] at hL
              exact hP bi b' L L' (by omega) hL hL'

/-- The driver's calls only allocate (`runTerm_mono`). -/
theorem driver_ord {f : Clif.Function} {ctx : Ctx} {st0 : LState} {bl : List BLow}
    (hl : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
      f.blocks.length = some bl) :
    (∀ (bi : Nat) (L : BLow), bl[bi]? = some L → BlockOrd st0.nextVreg L) ∧
      ∀ (bi bi' : Nat) (L L' : BLow), bi < bi' → bl[bi]? = some L → bl[bi']? = some L' →
        BlockOrd L.tst'.nextVreg L' :=
  lowBlocks_ord (fun _ _ r h => by obtain ⟨o, s', tr⟩ := r; exact (runTerm_mono h).1)
    (fun _ _ _ _ _ r h => by obtain ⟨o, s', tr⟩ := r; exact (runTerm_mono h).1)
    (fun _ _ _ _ _ r h => by obtain ⟨o, s', tr⟩ := r; exact (runTerm_mono h).1) hl

/-! ## The recorded aliases -/

/-- Where an alias comes from: result `p.1` of a statement whose lowering returned `vreg p.2`. -/
theorem mem_aliasOf {f : Clif.Function} {bl : List BLow} {p : Nat × Nat} (h : p ∈ aliasOf f bl) :
    ∃ (bi : Nat) (B : Clif.Block) (L : BLow) (j : Nat) (stm : Clif.Stmt) (sl : SLow),
      f.blocks[bi]? = some B ∧ bl[bi]? = some L ∧ B.body[j]? = some stm ∧
      L.sl[j]? = some sl ∧ p.1 ∈ stm.results ∧ ∃ rs c, rs ∈ sl.rss ∧ rs = [.vreg p.2 c] := by
  unfold aliasOf at h
  obtain ⟨⟨B, L⟩, hBL, hp⟩ := List.mem_flatMap.mp h
  obtain ⟨bi, hbi⟩ := List.mem_iff_getElem?.mp hBL
  obtain ⟨hB, hL⟩ := List.getElem?_zip_eq_some.mp hbi
  obtain ⟨⟨stm, sl⟩, hss, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hss
  obtain ⟨hs, hsl⟩ := List.getElem?_zip_eq_some.mp hj
  obtain ⟨⟨r, rs⟩, hrr, hg⟩ := List.mem_filterMap.mp hp
  obtain ⟨hr, hrs⟩ := List.of_mem_zip hrr
  refine ⟨bi, B, L, j, stm, sl, hB, hL, hs, hsl, ?_⟩
  match rs, hg with
  | [.vreg out c], hg =>
    simp only [Option.some.injEq] at hg
    subst hg
    exact ⟨hr, _, c, hrs, rfl⟩

/-- The aliases' keys are statement results, in layout order. -/
theorem aliasOf_keys (f : Clif.Function) (bl : List BLow) :
    ((aliasOf f bl).map (·.1)).Sublist (valueDefs f) := by
  have h1 : ((aliasOf f bl).map (·.1)).Sublist
      (f.blocks.flatMap fun B => B.body.flatMap (·.results)) := by
    unfold aliasOf
    refine zip_flatMap_fst (fun (B : Clif.Block) (L : BLow) => (B.body.zip L.sl).flatMap
      fun (p : Clif.Stmt × SLow) => (p.1.results.zip p.2.rss).filterMap fun (q : Nat × List Reg) =>
        match q.2 with
        | [.vreg out _] => some (q.1, out)
        | _ => none) _ (fun B L => ?_) f.blocks bl
    refine zip_flatMap_fst (fun (stm : Clif.Stmt) (sl : SLow) =>
      (stm.results.zip sl.rss).filterMap fun (q : Nat × List Reg) =>
        match q.2 with
        | [.vreg out _] => some (q.1, out)
        | _ => none) _ (fun stm sl => ?_) B.body L.sl
    refine zip_filterMap_fst (fun (r : Nat) (rs : List Reg) => match rs with
        | [.vreg out _] => some (r, out)
        | _ => none) (fun a b p h => ?_) stm.results sl.rss
    match b, h with
    | [.vreg out _], h => simp only [Option.some.injEq] at h; subst h; rfl
  exact h1.trans (flatMap_sublist_flatMap (fun B => List.sublist_append_right _ _) f.blocks)

/-! ## Available values -/

/-- Membership in `availOf` for a block that exists. -/
theorem mem_av {f : Clif.Function} {In : Array (List Clif.ValueId)} {bi : Nat} {B : Clif.Block}
    (hB : f.blocks[bi]? = some B) {j x : Nat} :
    x ∈ availOf f In bi j ↔
      (x ∈ B.params.map (·.1) ∨ x ∈ In.getD bi [] ∨
        ∃ (k : Nat) (s : Clif.Stmt), k < j ∧ B.body[k]? = some s ∧ x ∈ s.results) ∧
      ¬ ∃ (k : Nat) (s : Clif.Stmt), j ≤ k ∧ B.body[k]? = some s ∧ x ∈ s.results := by
  rw [mem_availOf]
  simp only [List.mem_append, defsBefore, defsFrom, mem_flatMap_take, mem_flatMap_drop, or_assoc]
  exact ⟨fun ⟨B', hB', h⟩ => by rw [hB] at hB'; cases hB'; exact h, fun h => ⟨B, hB, h⟩⟩

/-- Availability grows along the block. -/
theorem availOf_mono {f : Clif.Function} {In : Array (List Clif.ValueId)} {bi j j' x : Nat}
    (hjj : j ≤ j') (h : x ∈ availOf f In bi j) : x ∈ availOf f In bi j' := by
  obtain ⟨B, hB, -⟩ := mem_availOf.mp h
  obtain ⟨hm, hn⟩ := (mem_av hB).mp h
  refine (mem_av hB).mpr ⟨?_, fun ⟨k, s, hk, hs, hx⟩ => hn ⟨k, s, by omega, hs, hx⟩⟩
  rcases hm with h | h | ⟨k, s, hk, hs, hx⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨k, s, by omega, hs, hx⟩)

/-- The available values are values of `f` if the entry values are. -/
theorem avail_vals {f : Clif.Function} {In : Array (List Clif.ValueId)}
    (hIn : ∀ tl x, x ∈ In.getD tl [] → x ∈ valueDefs f) {bi j x : Nat}
    (h : x ∈ availOf f In bi j) : x ∈ valueDefs f := by
  obtain ⟨B, hB, -⟩ := mem_availOf.mp h
  rcases ((mem_av hB).mp h).1 with h | h | ⟨k, s, -, hs, hx⟩
  · exact mem_valueDefs_par hB h
  · exact hIn bi x h
  · exact mem_valueDefs_res hB hs hx

/-- `Prov` is closed under the definitions of its values. -/
theorem prov_trans {ctx : Ctx} {d e n y : Nat} (hn : Prov ctx d n) (he : ctx.defInst? n = some e)
    (h : Prov ctx e y) : Prov ctx d y := by
  induction h with
  | arg hi hc hy => exact .dep hn he hi hc (.inl hy)
  | dep _ he' hi hc hy ih => exact .dep ih he' hi hc hy

section
variable {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
  (hd : Dominated f) (hb : buildCtx f = .ok (ctx, ranges, st0))
include hd hb

/-- `availIn` is closed under the results of a statement. -/
theorem availIn_sib {tl bi j : Nat} {B : Clif.Block} {stm : Clif.Stmt} {x y : Nat}
    (hB : f.blocks[bi]? = some B) (hs : B.body[j]? = some stm) (hx : x ∈ stm.results)
    (hy : y ∈ stm.results) (hxG : x ∈ (availIn f ctx).getD tl []) :
    y ∈ (availIn f ctx).getD tl [] := by
  have hF := ctxFacts_of hb
  have hssa := hd.ssa
  have hG : FixOk f ctx id (fun tl x => x ∈ (availIn f ctx).getD tl []) := inFix_fixOk
  let D : Nat → Nat → Prop := fun tl y => y ∈ (availIn f ctx).getD tl [] ∨
    ∃ (bi : Nat) (B : Clif.Block) (j : Nat) (stm : Clif.Stmt) (x : Nat), f.blocks[bi]? = some B ∧
      B.body[j]? = some stm ∧ x ∈ stm.results ∧ y ∈ stm.results ∧ x ∈ (availIn f ctx).getD tl []
  have hD : FixOk f ctx id D := by
    refine ⟨?_, ?_, ?_⟩
    · rintro tl y (h | ⟨bi, B, j, stm, x, hB, hs, hx, hy, hxG⟩)
      · exact hG.cand tl y h
      · obtain ⟨h1, h2, -, -, -, -⟩ := hG.cand tl x hxG
        have hyv := mem_valueDefs_res hB hs hy
        have hnp := res_not_pars (tl := tl) hssa hB hs hy
        exact ⟨h1, h2, by rw [← hF.size.1]; exact lt_of_valueDefs hF hyv, hyv, hnp, hnp⟩
    · rintro tl y (h | ⟨bi, B, j, stm, x, hB, hs, hx, hy, hxG⟩) p hp
      · rcases hG.out tl y h p hp with h | h | h
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr (.inl h))
      · rcases hG.out tl x hxG p hp with h | h | h
        · exact absurd h (res_not_pars hssa hB hs hx)
        · obtain ⟨P, k, s, hP, hs', hx'⟩ := mem_defsOf.mp h
          obtain ⟨e1, e2⟩ := res_unique hssa hP hs' hx' hB hs hx
          subst e1 e2
          exact .inr (.inl (mem_defsOf.mpr ⟨_, _, _, hB, hs, hy⟩))
        · exact .inr (.inr (.inr ⟨bi, B, j, stm, x, hB, hs, hx, hy, h⟩))
    · rintro tl y (h | ⟨bi, B, j, stm, x, hB, hs, hx, hy, hxG⟩) z hz
      · obtain ⟨h1, h2⟩ := hG.clo tl y h z hz
        exact ⟨h1.imp_right .inl, h2⟩
      · rw [defArgs_res hF hssa hB hs hy, ← defArgs_res hF hssa hB hs hx] at hz
        obtain ⟨h1, h2⟩ := hG.clo tl x hxG z hz
        exact ⟨h1.imp_right .inl, h2⟩
  exact inFix_greatest hD (.inr ⟨bi, B, j, stm, x, hB, hs, hx, hy, hxG⟩)

/-- One step of `Prov` from an available value stays available. -/
theorem avail_step {bi j n d y : Nat} {info : IInfo} {c : Clif.Inst}
    (hn : n ∈ availOf f (availIn f ctx) bi j) (hd' : ctx.defInst? n = some d)
    (hi : ctx.insts[d]? = some info) (hc : info.clif = some c)
    (hy : y ∈ instArgs c ∨ y ∈ info.results) : y ∈ availOf f (availIn f ctx) bi j := by
  have hF := ctxFacts_of hb
  have hssa := hd.ssa
  obtain ⟨bi', B', j', stm', hB', hs', hn', rfl, hc', hr'⟩ := inst_at hF hssa hd' hi
  rw [hc] at hc'; cases hc'
  obtain ⟨B, hB, -⟩ := mem_availOf.mp hn
  obtain ⟨hm, hnf⟩ := (mem_av hB).mp hn
  by_cases hbb : bi' = bi
  · subst hbb
    rw [hB] at hB'; cases hB'
    have hj : j' < j := by
      apply Nat.lt_of_not_le; intro hle; exact hnf ⟨j', stm', hle, hs', hn'⟩
    rcases hy with hy | hy
    · exact availOf_mono (Nat.le_of_lt hj) ((hd.uses ctx ranges st0 hb _ _ hB).1 j' stm' hs' y hy)
    · rw [hr'] at hy
      refine (mem_av hB).mpr ⟨.inr (.inr ⟨j', stm', hj, hs', hy⟩), ?_⟩
      rintro ⟨k, s, hk, hs, hyk⟩
      have := (res_unique hssa hB hs hyk hB hs' hy).2
      omega
  · have hnG : n ∈ (availIn f ctx).getD bi [] := by
      rcases hm with h | h | ⟨k, s, -, hs, hk⟩
      · exact (par_not_res hssa hB h hB' hs' hn').elim
      · exact h
      · exact absurd (res_unique hssa hB hs hk hB' hs' hn').1.symm hbb
    rcases hy with hy | hy
    · obtain ⟨h1, h2⟩ := (inFix_fixOk (gn := id)).clo bi n hnG y
        (by rw [defArgs_res hF hssa hB' hs' hn']; exact hy)
      refine (mem_av hB).mpr ⟨?_, fun ⟨k, s, _, hs, hk⟩ => h2 (mem_defsOf.mpr ⟨B, k, s, hB, hs, hk⟩)⟩
      rcases h1 with h | h
      · exact .inl (by rwa [parsOf_of hB] at h)
      · exact .inr (.inl h)
    · rw [hr'] at hy
      refine (mem_av hB).mpr ⟨.inr (.inl (availIn_sib hd hb hB' hs' hn' hy hnG)), ?_⟩
      rintro ⟨k, s, -, hs, hk⟩
      exact hbb (res_unique hssa hB' hs' hy hB hs hk).1

/-- **The values a statement's lowering may return are available before it.** -/
theorem prov_avail {bi j : Nat} {B : Clif.Block} {stm : Clif.Stmt} (hB : f.blocks[bi]? = some B)
    (hs : B.body[j]? = some stm) {y : Nat} (h : Prov ctx (blockStart f bi + j) y) :
    y ∈ availOf f (availIn f ctx) bi j := by
  have hF := ctxFacts_of hb
  induction h with
  | arg hi hc hy =>
    obtain ⟨info', hi', hc', -⟩ := hF.stmt bi B j stm hB hs
    rw [hi] at hi'; cases hi'
    rw [hc] at hc'; cases hc'
    exact (hd.uses ctx ranges st0 hb bi B hB).1 j stm hs _ hy
  | dep _ hd' hi hc hy ih => exact avail_step hd hb ih hd' hi hc hy

/-- The values the lowering of an available value's definition may return are available. -/
theorem prov_closed {bi j n d y : Nat} (hn : n ∈ availOf f (availIn f ctx) bi j)
    (hd' : ctx.defInst? n = some d) (h : Prov ctx d y) : y ∈ availOf f (availIn f ctx) bi j := by
  induction h with
  | arg hi hc hy => exact avail_step hd hb hn hd' hi hc (.inl hy)
  | dep _ hd'' hi hc hy ih => exact avail_step hd hb ih hd'' hi hc hy

/-- One step of `Prov` from a value available at a block entry and not redefined there. -/
theorem cert_entry_step {tl n d y : Nat} {info : IInfo} {c : Clif.Inst}
    (hn : n ∈ (availIn f ctx).getD tl []) (hnd : n ∉ defsOf f tl) (hd' : ctx.defInst? n = some d)
    (hi : ctx.insts[d]? = some info) (hc : info.clif = some c)
    (hy : y ∈ instArgs c ∨ y ∈ info.results) :
    y ∈ (availIn f ctx).getD tl [] ∧ y ∉ defsOf f tl := by
  have hF := ctxFacts_of hb
  have hssa := hd.ssa
  obtain ⟨bi', B', j', stm', hB', hs', hn', rfl, -, hr'⟩ := inst_at hF hssa hd' hi
  rcases hy with hy | hy
  · have hya : y ∈ defArgs ctx n := by rw [defArgs_eq hd' hi hc]; exact hy
    obtain ⟨h1, h2⟩ := (inFix_fixOk (gn := id)).clo tl n hn y hya
    have h3 := hd.paramFree ctx ranges st0 hb tl n hn hnd y hya
    exact ⟨h1.resolve_left h3, h2⟩
  · rw [hr'] at hy
    refine ⟨availIn_sib hd hb hB' hs' hn' hy hn, fun h => hnd ?_⟩
    obtain ⟨T, k, s, hT, hs, hk⟩ := mem_defsOf.mp h
    obtain ⟨e1, -⟩ := res_unique hssa hT hs hk hB' hs' hy
    subst e1
    exact mem_defsOf.mpr ⟨B', j', stm', hB', hs', hn'⟩

/-- The values the lowering of an entry value's definition may return are entry values (and not
redefined in the block). -/
theorem prov_entry {tl n d y : Nat} (hn : n ∈ (availIn f ctx).getD tl []) (hnd : n ∉ defsOf f tl)
    (hd' : ctx.defInst? n = some d) (h : Prov ctx d y) :
    y ∈ (availIn f ctx).getD tl [] ∧ y ∉ defsOf f tl := by
  induction h with
  | arg hi hc hy => exact cert_entry_step hd hb hn hnd hd' hi hc (.inl hy)
  | dep _ hd'' hi hc hy ih => exact cert_entry_step hd hb ih.1 ih.2 hd'' hi hc hy

end

end Backend.Proof.Driver
