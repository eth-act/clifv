import FV.Backend.Proof.LowerLoopRun

/-!
# `lowerFunction`'s block loop, simulated

The invariant of the loop over the blocks (`LInv`): after `k` blocks, the loop state holds the
renaming-free blocks `rawBlock`, the edge blocks `edgeBlocks` and the aliases `aliasArr` of the
recorded lowering of the first `k` blocks, whose end state and next edge label are the loop's
(`blockStep`).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof Backend.Proof.Prep

/-! ## The entry block's argument setup -/

theorem entryLoop {ctx : Ctx} (hreg : ∀ x r, ctx.valueReg? x = some r → r = .vreg x .int) (R : Reg → Reg)
    (hR : R = id) :
    ∀ (l : List (((Clif.ValueId × Clif.Ty) × ArgLoc) × Nat)) (c : Array MInst) (p : Array (Reg × Reg))
      (c' : Array MInst) (p' : Array (Reg × Reg)), forIn l (c, p) (entryBody ctx) = .ok (c', p') →
      c'.toList = c.toList ++ l.filterMap (entryLoadOf R) ∧ p'.toList = p.toList ++ l.filterMap (entryRegOf R)
  | [], c, p, c', p', h => by
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | q :: l, c, p, c', p', h => by
    subst hR
    rw [List.forIn_cons] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    rename_i st hst
    obtain ⟨⟨⟨v, ty⟩, loc⟩, bytes⟩ := q
    unfold entryBody at hst
    simp only at hst
    split at hst
    · rename_i r hr
      have := hreg v r hr
      subst this
      cases loc with
      | reg pr =>
        simp only [pure, Except.pure, Except.ok.injEq] at hst
        subst hst
        obtain ⟨h1, h2⟩ := entryLoop hreg id rfl l _ _ c' p' h
        refine ⟨by rw [h1]; simp [List.filterMap_cons, entryLoadOf], by rw [h2]; simp [entryRegOf]⟩
      | stack off =>
        simp only [pure, Except.pure, Except.ok.injEq] at hst
        subst hst
        obtain ⟨h1, h2⟩ := entryLoop hreg id rfl l _ _ c' p' h
        refine ⟨by rw [h1]; simp [entryLoadOf], by rw [h2]; simp [List.filterMap_cons, entryRegOf]⟩
    · cases hst

/-! ## Lists -/

theorem segs_eq {α β γ : Type} (g : α × β → List γ) :
    ∀ (ss : List α) (sls : List β), sls.length = ss.length →
      ((List.range ss.length).map fun j => match ss[j]?, sls[j]? with
        | some a, some b => g (a, b)
        | _, _ => []).flatten = (ss.zip sls).flatMap g
  | [], [], _ => rfl
  | a :: ss, b :: sls, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rw [List.length_cons, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.flatten_cons, List.getElem?_cons_zero,
      List.zip_cons_cons, List.flatMap_cons]
    congr 1
    rw [← segs_eq g ss sls h]
    congr 2

theorem zip_snoc {α β : Type} {l : List α} {m : List β} {x : β} {a : α} (hm : l[m.length]? = some a) :
    l.zip (m ++ [x]) = l.zip m ++ [(a, x)] := by
  induction m generalizing l with
  | nil =>
    cases l with
    | nil => simp at hm
    | cons a' l => simp at hm; subst hm; simp
  | cons b m ih =>
    cases l with
    | nil => simp at hm
    | cons a' l =>
      simp only [List.length_cons, List.getElem?_cons_succ] at hm
      simp [ih hm]

/-! ## One block -/

theorem bodyPart_ok {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (sp : CtxSpec f ctx ranges st0) {k : Nat} {B : Clif.Block} (hB : f.blocks[k]? = some B)
    {d : DState} {code : Array MInst} {d' : DState} (he : d.st.emitted = #[])
    (h : bodyPart f ctx B k (blockStart f k) (blockStart f k + B.body.length + 1) d code = .ok (.yield d')) :
    ∃ s data, SInv ctx (blockStart f k) B.body d code B.body.length s ∧ DataOk f B.term data ∧
      termPart f ctx B k (blockStart f k + B.body.length + 1) s.2 s.1 data = .ok (.yield d') := by
  unfold bodyPart at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i s hs
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hs
  simp only [Std.Legacy.Range.size, Nat.add_sub_cancel_left, Nat.add_one_sub_one, Nat.div_one] at hs
  have hS := stmtLoop sp hB he hs
  refine ⟨s, ?_⟩
  split at h
  · rename_i fn args et ht
    split at h
    · cases h
    rename_i data hd
    exact ⟨data, hS, by simp only [DataOk, ht]; rw [← ht]; exact hd, h⟩
  · rename_i c args et ht
    split at h
    · cases h
    rename_i data hd
    exact ⟨data, hS, by simp only [DataOk, ht]; rw [← ht]; exact hd, h⟩
  · rename_i hn1 hn2
    split at h
    · cases h
    rename_i data hd
    refine ⟨data, hS, ?_, h⟩
    unfold DataOk
    split
    · rename_i fn args et ht; exact absurd ht (hn1 fn args et)
    · rename_i c args et ht; exact absurd ht (hn2 c args et)
    · exact hd

/-! ## The block loop's invariant -/

/-- What `lowerFunction` checks of the first `k` blocks, lowered as `blk`. -/
structure PF (f : Clif.Function) (ctx : Ctx) (st0 : LState) (k : Nat) (blk : List BLow) : Prop where
  results : ∀ (bi : Nat) (B : Clif.Block) (L : BLow), f.blocks[bi]? = some B → blk[bi]? = some L →
    ResOk B.body L.sl
  args : ∀ (bi : Nat) (B : Clif.Block), bi < k → f.blocks[bi]? = some B → ArgsOk f ctx (dests B.term)
  tryArgs : ∀ (bi : Nat) (B : Clif.Block) (L : BLow) (et : Clif.ExnTable), f.blocks[bi]? = some B →
    blk[bi]? = some L → IsTryWith B.term et →
    ∃ T : TryLow, L.tl = some T ∧ ∀ (i : Nat) (td : Clif.TryDest), et.dests[i]? = some td →
      TryDestOk f ctx et.handlers.length T.regs.1.length T.regs.2.length i td
  tryLast : ∀ (bi : Nat) (L : BLow) (T : TryLow), blk[bi]? = some L → L.tl = some T →
    ∃ c, L.tst'.emitted.back? = some (.call c)
  entry : 0 < k → ∃ locs n, sigArgLocs f.sig = .ok (locs, n)
  sret : ∀ (bi : Nat) (B : Clif.Block), bi < k → f.blocks[bi]? = some B → ∀ vs, B.term = .ret vs →
    sretRet f = [] → sigRets f.sig = f.sig.returns
  slLen : ∀ (bi : Nat) (B : Clif.Block) (L : BLow), f.blocks[bi]? = some B → blk[bi]? = some L →
    L.sl.length = B.body.length

/-- The invariant of the block loop after `k` blocks, lowered as `blk`. -/
structure LI (f : Clif.Function) (ctx : Ctx) (st0 : LState) (k : Nat) (d : DState) (blk : List BLow) :
    Prop where
  len : blk.length = k
  low : lowB f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 (f.blocks.take k) st0 f.blocks.length =
    some (blk, d.st, d.nextLabel)
  blocks : d.blocks.toList = (f.blocks.zip blk).zipIdx.map fun p => rawBlock f blk p.2 p.1.1
  edges : d.edges.toList = (f.blocks.zip blk).flatMap fun p => edgeBlocks f p.1 p.2
  alias : d.alias = aliasArr (aliasOf f blk)
  em : d.st.emitted = #[]
  pf : PF f ctx st0 k blk

theorem rawBlock_snoc {f : Clif.Function} {blk : List BLow} {L : BLow} {i : Nat} (hi : i < blk.length)
    (B : Clif.Block) : rawBlock f (blk ++ [L]) i B = rawBlock f blk i B := by
  have hs : seg f id (blk ++ [L]) i = seg f id blk i := by
    funext j; simp only [seg, List.getElem?_append_left hi]
  simp only [rawBlock, hs, tseg, List.getElem?_append_left hi]

theorem rawBlock_last {f : Clif.Function} {bl : List BLow} {k : Nat} {B : Clif.Block} {L : BLow}
    (hB : f.blocks[k]? = some B) (hL : bl[k]? = some L) (hlen : L.sl.length = B.body.length) :
    rawBlock f bl k B = mkVB k ((pre f id k ++ (B.body.zip L.sl).flatMap segOf ++ tsegOf L.tl L.tst').toArray)
      (paramsOf k B) (jumpArgsOf B) := by
  simp only [rawBlock, mkVB, paramsOf, jumpArgsOf, tseg, hL, tsegOf, map_mapRegs_id]
  congr 3
  have := segs_eq (fun q : Clif.Stmt × SLow => (segOf q).map (MInst.mapRegs id)) B.body L.sl hlen
  simp only [map_mapRegs_id] at this
  rw [← this]
  congr 1
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [seg, hB, hL, segOf, map_mapRegs_id]
  rcases B.body[j]? with _ | stm <;> rcases L.sl[j]? with _ | sl <;> rfl

theorem aliasArr_append (a b : List (Nat × Nat)) : aliasArr (a ++ b) = b.foldl aliasStep (aliasArr a) := by
  simp [aliasArr, List.foldl_append]

theorem bsl_take (Bs : List Clif.Block) (k : Nat) (hk : k ≤ Bs.length) :
    bsl (Bs.take k) (Bs.take k).length = bsl Bs k := by
  simp only [bsl, List.length_take, Nat.min_eq_left hk, List.take_take, Nat.min_self]

theorem blockStep {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (sp : CtxSpec f ctx ranges st0) {paramBytes : List Nat} (hpb : sigParamBytes f.sig = .ok paramBytes)
    {k : Nat} {B : Clif.Block} (hB : f.blocks[k]? = some B) {d d' : DState} {blk : List BLow}
    (hI : LI f ctx st0 k d blk) (h : blockBody f ctx ranges paramBytes (B, k) d = .ok (.yield d')) :
    ∃ L, LI f ctx st0 (k + 1) d' (blk ++ [L]) := by
  have hreg := sp.regEq
  have hk : k < f.blocks.length := (List.getElem?_eq_some_iff.mp hB).1
  -- the argument setup
  obtain ⟨code0, hc0, hbp, hent⟩ : ∃ code0 : Array MInst, code0.toList = pre f id k ∧
      bodyPart f ctx B k (blockStart f k) (blockStart f k + B.body.length + 1) d code0 = .ok (.yield d') ∧
      (k = 0 → ∃ locs n, sigArgLocs f.sig = .ok (locs, n)) := by
    unfold blockBody at h
    simp only at h
    rw [getElem!_of (sp.ranges k B hB)] at h
    simp only at h
    split at h
    · rename_i hk0
      have hk0' : k = 0 := by simpa using hk0
      subst hk0'
      simp only [bind, Except.bind] at h
      split at h
      · cases h
      rename_i q hloc
      obtain ⟨locs, nn⟩ := q
      simp only at h
      split at h
      · cases h
      rename_i q hq
      obtain ⟨c, pr⟩ := q
      obtain ⟨h1, h2⟩ := entryLoop hreg id rfl _ #[] #[] c pr hq
      refine ⟨_, ?_, h, fun _ => ⟨locs, nn, hloc⟩⟩
      have hlocs : locsOf f.sig = locs := by simp [locsOf, hloc]
      simp only [pre, hB, entryRegs, entryLoads, entryParams, hlocs, hpb]
      simp [h1, h2]
    · rename_i hk0
      have hk0' : k ≠ 0 := by simpa using hk0
      refine ⟨#[], ?_, h, fun h' => absurd h' hk0'⟩
      obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0'
      simp [pre]
  obtain ⟨s, data, hS, hdata, hT⟩ := bodyPart_ok sp hB hI.em hbp
  obtain ⟨sls, hl, hbl, hed, hnl, hal, hcode, hem, hres⟩ := hS
  rw [List.take_length] at hl hal hcode hres
  have hsls := lowStmts_len hl
  obtain ⟨hsret, targets, tl, tst', nl', TO⟩ := termPart_ok sp hem hdata hT
  let L : BLow := ⟨blockStart f k, sls, data, targets, s.1.st, tst', tl⟩
  have hLk : (blk ++ [L])[k]? = some L := by
    rw [List.getElem?_append_right (by rw [hI.len]; exact Nat.le_refl k), hI.len]; simp
  have hzip : f.blocks.zip (blk ++ [L]) = f.blocks.zip blk ++ [(B, L)] :=
    zip_snoc (by rw [hI.len]; exact hB)
  have hzl : (f.blocks.zip blk).length = k := by
    simp [List.length_zip, hI.len]; omega
  refine ⟨L, ⟨by simp [hI.len], ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- the recorded lowering
    rw [List.take_add_one, hB, Option.toList_some, lowB_append, hI.low, Option.bind_some,
      bsl_take _ _ (Nat.le_of_lt hk)]
    simp only [lowB_cons, Nat.zero_add]
    rw [← blockStart_eq, hl]
    simp only [st_eta hem]
    have hlow := TO.low
    rw [show blockStart f k + B.body.length + 1 - 1 = blockStart f k + B.body.length by omega, hnl] at hlow
    rw [hlow]
    simp only [lowB, Option.map_some, TO.st, TO.nl]
    rfl
  · -- the blocks
    rw [TO.blocks, Array.toList_push, hbl, hI.blocks, hzip, List.zipIdx_append, List.map_append, hzl]
    simp only [List.zipIdx_cons, List.zipIdx_nil, Nat.zero_add, List.map_cons, List.map_nil]
    congr 1
    · apply List.map_congr_left
      intro p hp
      have hlt := (List.mem_zipIdx hp).2.1
      rw [hzl] at hlt
      rw [rawBlock_snoc (by rw [hI.len]; omega)]
    · rw [rawBlock_last hB hLk (by rw [hsls])]
      simp only [mkVB]
      dsimp only [L]
      have hc : s.2 ++ (tsegOf tl tst').toArray =
          (pre f id k ++ List.flatMap segOf (B.body.zip sls) ++ tsegOf tl tst').toArray := by
        apply Array.ext'; simp [hcode, hc0]
      rw [hc]
  · -- the edges
    rw [TO.edges L rfl rfl, hed, hI.edges, hzip, List.flatMap_append]
    simp
  · -- the aliases
    rw [TO.alias, hal, hI.alias, aliasOf_eq, aliasOf_eq, hzip, List.flatMap_append, aliasArr_append]
    simp
    rfl
  · rw [TO.st]
  · -- the facts
    have old : ∀ {bi L'}, (blk ++ [L])[bi]? = some L' → bi < k → blk[bi]? = some L' := by
      intro bi L' h hb
      rwa [List.getElem?_append_left (by rw [hI.len]; exact hb)] at h
    have new : ∀ {bi L'}, (blk ++ [L])[bi]? = some L' → ¬ bi < k → bi = k ∧ L' = L := by
      intro bi L' h hb
      have hlt := (List.getElem?_eq_some_iff.mp h).1
      simp only [List.length_append, hI.len, List.length_singleton] at hlt
      have : bi = k := by omega
      subst this
      rw [hLk] at h; exact ⟨rfl, (Option.some.inj h).symm⟩
    refine ⟨fun bi B' L' hB' hL' => ?_, fun bi B' hb hB' => ?_, fun bi B' L' et hB' hL' het => ?_,
      fun bi L' T hL' hT => ?_, fun _ => ?_, fun bi B' hb hB' => ?_, fun bi B' L' hB' hL' => ?_⟩
    · by_cases hb : bi < k
      · exact hI.pf.results bi B' L' hB' (old hL' hb)
      · obtain ⟨hbk, hLL⟩ := new hL' hb
        rw [hbk, hB] at hB'; cases hB'; rw [hLL]; exact hres
    · by_cases hb' : bi < k
      · exact hI.pf.args bi B' hb' hB'
      · have : bi = k := by omega
        subst this; rw [hB] at hB'; cases hB'; exact TO.args
    · by_cases hb : bi < k
      · exact hI.pf.tryArgs bi B' L' et hB' (old hL' hb) het
      · obtain ⟨hbk, hLL⟩ := new hL' hb
        rw [hbk, hB] at hB'; cases hB'; rw [hLL]; exact TO.tryArgs et het
    · by_cases hb : bi < k
      · exact hI.pf.tryLast bi L' T (old hL' hb) hT
      · obtain ⟨hbk, hLL⟩ := new hL' hb
        rw [hLL] at hT ⊢; exact TO.tryLast T hT
    · rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · exact hent hk0
      · exact hI.pf.entry hk0
    · by_cases hb' : bi < k
      · exact hI.pf.sret bi B' hb' hB'
      · have : bi = k := by omega
        subst this; rw [hB] at hB'; cases hB'; exact hsret
    · by_cases hb : bi < k
      · exact hI.pf.slLen bi B' L' hB' (old hL' hb)
      · obtain ⟨hbk, hLL⟩ := new hL' hb
        rw [hbk, hB] at hB'; cases hB'; rw [hLL]; exact hsls

/-! ## The loop bodies only yield -/

/-- `r` is a `yield`. -/
def IsYield {β : Type} : ForInStep β → Prop
  | .yield _ => True
  | .done _ => False

theorem paramsPart_yield {ctx : Ctx} {b : Clif.Block} {bi : Nat} {code : Array MInst} {d : DState}
    {st : LState} {n : List Isle.RuleId} {jumpArgs : Array Reg} {emitted : Array MInst}
    {r : ForInStep DState} (h : paramsPart ctx b bi code d st n jumpArgs emitted = .ok r) : IsYield r := by
  unfold paramsPart at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; trivial
  · simp only [bind, Except.bind] at h
    split at h
    · cases h
    · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; trivial

theorem finishBlock_yield {ctx : Ctx} {b : Clif.Block} {bi ti : Nat} {code : Array MInst} {d : DState}
    {ctx' : Ctx} {targets : Array Label} {jumpArgs : Array Reg} {tryInfo : Option TryInfo}
    {r : ForInStep DState} (h : finishBlock ctx b bi ti code d ctx' targets jumpArgs tryInfo = .ok r) :
    IsYield r := by
  unfold finishBlock at h
  rw [termArgsOf_eq] at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i res _
  obtain ⟨out, st, n⟩ := res
  simp only at h
  split at h
  · cases h
  cases tryInfo with
  | none => exact paramsPart_yield h
  | some t =>
    simp only at h
    split at h
    · exact paramsPart_yield h
    · cases h

theorem tryTerm_yield {f : Clif.Function} {ctx : Ctx} {b : Clif.Block} {bi ti : Nat} {code : Array MInst}
    {d : DState} {ctx' : Ctx} {et : Clif.ExnTable} {r : ForInStep DState}
    (h : tryTerm f ctx b bi ti code d ctx' et = .ok r) : IsYield r := by
  unfold tryTerm at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i q _
  obtain ⟨sig, items⟩ := q
  simp only at h
  split at h
  · split at h
    · cases h
    split at h
    · cases h
    rename_i s _
    obtain ⟨d1, tg⟩ := s
    simp only at h
    split at h
    · exact finishBlock_yield h
    · cases h
  · cases h

theorem termPart_yield {f : Clif.Function} {ctx : Ctx} {b : Clif.Block} {bi stop : Nat}
    {code : Array MInst} {d : DState} {data : V} {r : ForInStep DState}
    (h : termPart f ctx b bi stop code d data = .ok r) : IsYield r := by
  unfold termPart at h
  by_cases hs : sretBad f b.term = true
  · simp only [hs, ↓reduceIte] at h; cases h
  simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
  generalize b.term = t at h
  cases t with
  | jump bc =>
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    split at h
    · cases h
    exact finishBlock_yield h
  | tryCall fn args et => exact tryTerm_yield h
  | tryCallIndirect c args et => exact tryTerm_yield h
  | _ =>
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    exact finishBlock_yield h

theorem blockBody_yield {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {paramBytes : List Nat} {x : Clif.Block × Nat} {d : DState} {r : ForInStep DState}
    (h : blockBody f ctx ranges paramBytes x d = .ok r) : IsYield r := by
  have hb : ∀ {b bi start stop code}, bodyPart f ctx b bi start stop d code = .ok r → IsYield r := by
    intro b bi start stop code h
    unfold bodyPart at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    split at h <;> (split at h; · cases h) <;> exact termPart_yield h
  obtain ⟨b, bi⟩ := x
  unfold blockBody at h
  simp only at h
  split at h
  · simp only [bind, Except.bind] at h
    split at h
    · cases h
    rename_i q _
    obtain ⟨locs, nn⟩ := q
    simp only at h
    split at h
    · cases h
    exact hb h
  · exact hb h

/-! ## The whole loop -/

theorem lowB_out (f : Clif.Function) (call : StmtCall) (tcall : TermCallF) (ycall : TryCallF) :
    ∀ (Bs : List Clif.Block) (start : Nat) (st : LState) (nl : Nat) (bl : List BLow) (st' : LState)
      (nl' : Nat), lowB f call tcall ycall start Bs st nl = some (bl, st', nl') →
      st'.outgoing = (bl.getLast?.map (·.tst'.outgoing)).getD st.outgoing
  | [], start, st, nl, bl, st', nl', h => by
    simp only [lowB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  | B :: Bs, start, st, nl, bl, st', nl', h => by
    rw [lowB_cons] at h
    split at h
    · cases h
    rename_i sls stE _
    split at h
    · rename_i data targets tl tst' nl1 _
      cases hr : lowB f call tcall ycall (start + B.body.length + 1) Bs { tst' with emitted := #[] } nl1 with
      | none => rw [hr] at h; cases h
      | some r =>
        rw [hr] at h
        obtain ⟨bl1, st1, nl2⟩ := r
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have := lowB_out f call tcall ycall Bs _ _ _ bl1 _ _ hr
        rw [this]
        cases bl1 with
        | nil => rfl
        | cons a l => simp [List.getLast?_cons]
    · cases h

/-- **The loop, run**: `lowerFunction`'s final loop state satisfies the invariant after all
blocks. -/
theorem loop_run {f : Clif.Function} {vc : VCode} (h : lowerFunction f = .ok vc) :
    ∃ ctx ranges st0 paramBytes d bl, buildCtx f = .ok (ctx, ranges, st0) ∧
      sigParamBytes f.sig = .ok paramBytes ∧ LI f ctx st0 f.blocks.length d bl ∧
      vc = finishVC f d (slotLayout f.slots).2 := by
  rw [lowerFunction_eq] at h
  unfold lowerFunction' at h
  split at h
  · cases h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i paramBytes hpb
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i q hb
  obtain ⟨ctx, ranges, st0⟩ := q
  simp only at h
  split at h
  · cases h
  rename_i d hd
  simp only [pure, Except.pure, Except.ok.injEq] at h
  have sp := ctxSpec_of hb
  have hP := forIn_inv (blockBody f ctx ranges paramBytes) f.blocks.zipIdx
    (fun k d => ∃ bl, LI f ctx st0 k d bl) ?_ ?_ _ d ?_ hd
  · obtain ⟨bl, hI⟩ := hP
    simp only [List.length_zipIdx] at hI
    refine ⟨ctx, ranges, st0, paramBytes, d, bl, hb, hpb, hI, ?_⟩
    rw [← h]
  · intro k x d d' hx hP hs
    obtain ⟨bl, hI⟩ := hP
    rw [List.getElem?_zipIdx] at hx
    cases hB : f.blocks[k]? with
    | none => rw [hB] at hx; cases hx
    | some B =>
      rw [hB] at hx
      simp only [Option.map_some, Option.some.injEq, Nat.zero_add] at hx
      subst hx
      obtain ⟨L, hL⟩ := blockStep sp hpb hB hI hs
      exact ⟨_, hL⟩
  · intro x b b' hb'
    have := blockBody_yield hb'
    exact this
  · refine ⟨[], ⟨rfl, ?_, by simp, by simp, by simp [aliasOf, aliasArr], ?_, ?_⟩⟩
    · simp [lowB]
    · rw [sp.st0]
    · refine ⟨fun bi B L _ h => by simp at h, fun bi B h => absurd h (Nat.not_lt_zero _),
        fun bi B L et _ h => by simp at h, fun bi L T h => by simp at h, fun h => absurd h (Nat.lt_irrefl 0),
        fun bi B h => absurd h (Nat.not_lt_zero _), fun bi B L _ h => by simp at h⟩

end Backend.Proof.Driver
