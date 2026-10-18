import FV.Backend.Proof.LowerLoopRunT
import FV.Backend.Proof.LowerLoopSim

/-!
# `lowerFunction`'s block loop, simulated, typed (S11e5 Stage C, slice 3)

`LowerLoopSim.lean` over the typed model: the loop invariant `LIT` holds the typed raw blocks
`rawBlockT` (entry `Args`/`stackArgLoad`s `preT`, typed result copies `segT`, parameters and jump
arguments of their classes) and the typed edge blocks `edgeBlocksT`. `loop_runT` needs no premise
on `f`: `buildCtx` gives every value the vreg of its type's class, which is what the typed model
says (`loop_run` takes `Compile.functionE` because its model is integer).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof Backend.Proof.Prep

/-! ## The entry block's argument setup -/

theorem entryLoopT {ctx : Ctx} (hreg : ∀ x r, ctx.valueReg? x = some r → r = vregOf ctx x)
    (R : Reg → Reg) (hR : R = id) :
    ∀ (l : List (((Clif.ValueId × Clif.Ty) × ArgLoc) × Nat)) (c : Array MInst) (p : Array (Reg × Reg))
      (c' : Array MInst) (p' : Array (Reg × Reg)), forIn l (c, p) (entryBody ctx) = .ok (c', p') →
      c'.toList = c.toList ++ l.filterMap (entryLoadOfT ctx R) ∧
        p'.toList = p.toList ++ l.filterMap (entryRegOfT ctx R)
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
        obtain ⟨h1, h2⟩ := entryLoopT hreg id rfl l _ _ c' p' h
        refine ⟨by rw [h1]; simp [List.filterMap_cons, entryLoadOfT],
          by rw [h2]; simp [entryRegOfT]⟩
      | stack off =>
        simp only [pure, Except.pure, Except.ok.injEq] at hst
        subst hst
        obtain ⟨h1, h2⟩ := entryLoopT hreg id rfl l _ _ c' p' h
        refine ⟨by rw [h1]; simp [entryLoadOfT],
          by rw [h2]; simp [List.filterMap_cons, entryRegOfT]⟩
    · cases hst

/-! ## One block -/

/-- Block `bi` (`B`, lowered as `L`) before alias resolution, typed: the entry's typed argument
setup, the statements' segments with typed result copies, the terminator's segment; parameters
and jump arguments of their classes. -/
def rawBlockT (f : Clif.Function) (ctx : Ctx) (bl : List BLow) (bi : Nat) (B : Clif.Block) : VBlock :=
  { label := bi
    insts := (preT f ctx id bi ++ ((List.range B.body.length).map (segT f ctx id bl bi)).flatten ++
      tseg id bl bi).toArray
    params := if bi = 0 then #[] else (B.params.map fun p => vregOf ctx p.1).toArray
    branchArgs := match B.term with
      | .jump bc => (bc.args.map fun a => vregOf ctx a).toArray
      | _ => #[] }

theorem bodyPart_okT {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (sp : CtxSpec f ctx ranges st0) {k : Nat} {B : Clif.Block} (hB : f.blocks[k]? = some B)
    {d : DState} {code : Array MInst} {d' : DState} (he : d.st.emitted = #[])
    (h : bodyPart f ctx B k (blockStart f k) (blockStart f k + B.body.length + 1) d code = .ok (.yield d')) :
    ∃ s data, SInvT ctx (blockStart f k) B.body d code B.body.length s ∧ DataOk f B.term data ∧
      termPart f ctx B k (blockStart f k + B.body.length + 1) s.2 s.1 data = .ok (.yield d') := by
  unfold bodyPart at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i s hs
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hs
  simp only [Std.Legacy.Range.size, Nat.add_sub_cancel_left, Nat.add_one_sub_one, Nat.div_one] at hs
  have hS := stmtLoopT sp hB he hs
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

/-- What `lowerFunction` checks of the first `k` blocks, lowered as `blk` (typed). -/
structure PFT (f : Clif.Function) (ctx : Ctx) (st0 : LState) (k : Nat) (blk : List BLow) : Prop where
  results : ∀ (bi : Nat) (B : Clif.Block) (L : BLow), f.blocks[bi]? = some B → blk[bi]? = some L →
    ResOk B.body L.sl
  args : ∀ (bi : Nat) (B : Clif.Block), bi < k → f.blocks[bi]? = some B → ArgsOkT f ctx (dests B.term)
  tryArgs : ∀ (bi : Nat) (B : Clif.Block) (L : BLow) (et : Clif.ExnTable), f.blocks[bi]? = some B →
    blk[bi]? = some L → IsTryWith B.term et →
    ∃ T : TryLow, L.tl = some T ∧ ∀ (i : Nat) (td : Clif.TryDest), et.dests[i]? = some td →
      TryDestOkT f ctx et.handlers.length T.regs.1.length T.regs.2.length i td
  tryLast : ∀ (bi : Nat) (L : BLow) (T : TryLow), blk[bi]? = some L → L.tl = some T →
    ∃ c, L.tst'.emitted.back? = some (.call c)
  entry : 0 < k → ∃ locs n, sigArgLocs f.sig = .ok (locs, n)
  sret : ∀ (bi : Nat) (B : Clif.Block), bi < k → f.blocks[bi]? = some B → ∀ vs, B.term = .ret vs →
    sretRet f = [] → sigRets f.sig = f.sig.returns
  slLen : ∀ (bi : Nat) (B : Clif.Block) (L : BLow), f.blocks[bi]? = some B → blk[bi]? = some L →
    L.sl.length = B.body.length

/-- The invariant of the block loop after `k` blocks, lowered as `blk` (typed). -/
structure LIT (f : Clif.Function) (ctx : Ctx) (st0 : LState) (k : Nat) (d : DState) (blk : List BLow) :
    Prop where
  len : blk.length = k
  low : lowB f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 (f.blocks.take k) st0 f.blocks.length =
    some (blk, d.st, d.nextLabel)
  blocks : d.blocks.toList = (f.blocks.zip blk).zipIdx.map fun p => rawBlockT f ctx blk p.2 p.1.1
  edges : d.edges.toList = (f.blocks.zip blk).flatMap fun p => edgeBlocksT f ctx p.1 p.2
  alias : d.alias = aliasArr (aliasOf f blk)
  em : d.st.emitted = #[]
  pf : PFT f ctx st0 k blk

theorem rawBlock_snocT {f : Clif.Function} {ctx : Ctx} {blk : List BLow} {L : BLow} {i : Nat}
    (hi : i < blk.length) (B : Clif.Block) : rawBlockT f ctx (blk ++ [L]) i B = rawBlockT f ctx blk i B := by
  have hs : segT f ctx id (blk ++ [L]) i = segT f ctx id blk i := by
    funext j; simp only [segT, List.getElem?_append_left hi]
  simp only [rawBlockT, hs, tseg, List.getElem?_append_left hi]

theorem rawBlock_lastT {f : Clif.Function} {ctx : Ctx} {bl : List BLow} {k : Nat} {B : Clif.Block}
    {L : BLow} (hB : f.blocks[k]? = some B) (hL : bl[k]? = some L) (hlen : L.sl.length = B.body.length) :
    rawBlockT f ctx bl k B = mkVB k ((preT f ctx id k ++ (B.body.zip L.sl).flatMap (segOfT ctx) ++
      tsegOf L.tl L.tst').toArray) (paramsOfT ctx k B) (jumpArgsOfT ctx B) := by
  simp only [rawBlockT, mkVB, paramsOfT, jumpArgsOfT, tseg, hL, tsegOf, map_mapRegs_id]
  congr 3
  have := segs_eq (fun q : Clif.Stmt × SLow => (segOfT ctx q).map (MInst.mapRegs id)) B.body L.sl hlen
  simp only [map_mapRegs_id] at this
  rw [← this]
  congr 1
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [segT, hB, hL, segOfT, map_mapRegs_id]
  rcases B.body[j]? with _ | stm <;> rcases L.sl[j]? with _ | sl <;> rfl

theorem blockStepT {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (sp : CtxSpec f ctx ranges st0) {paramBytes : List Nat}
    (hpb : sigParamBytes f.sig = .ok paramBytes)
    {k : Nat} {B : Clif.Block} (hB : f.blocks[k]? = some B) {d d' : DState} {blk : List BLow}
    (hI : LIT f ctx st0 k d blk) (h : blockBody f ctx ranges paramBytes (B, k) d = .ok (.yield d')) :
    ∃ L, LIT f ctx st0 (k + 1) d' (blk ++ [L]) := by
  have hreg := sp.regEqT
  have hk : k < f.blocks.length := (List.getElem?_eq_some_iff.mp hB).1
  -- the argument setup
  obtain ⟨code0, hc0, hbp, hent⟩ : ∃ code0 : Array MInst, code0.toList = preT f ctx id k ∧
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
      obtain ⟨h1, h2⟩ := entryLoopT hreg id rfl _ #[] #[] c pr hq
      refine ⟨_, ?_, h, fun _ => ⟨locs, nn, hloc⟩⟩
      have hlocs : locsOf f.sig = locs := by simp [locsOf, hloc]
      simp only [preT, hB, entryRegsT, entryLoadsT, entryParams, hlocs, hpb]
      simp [h1, h2]
    · rename_i hk0
      have hk0' : k ≠ 0 := by simpa using hk0
      refine ⟨#[], ?_, h, fun h' => absurd h' hk0'⟩
      obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0'
      simp [preT]
  obtain ⟨s, data, hS, hdata, hT⟩ := bodyPart_okT sp hB hI.em hbp
  obtain ⟨sls, hl, hbl, hed, hnl, hal, hcode, hem, hres⟩ := hS
  rw [List.take_length] at hl hal hcode hres
  have hsls := lowStmts_len hl
  obtain ⟨hsret, targets, tl, tst', nl', TO⟩ := termPart_okT sp hem hdata hT
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
      rw [rawBlock_snocT (by rw [hI.len]; omega)]
    · rw [rawBlock_lastT hB hLk (by rw [hsls])]
      simp only [mkVB]
      dsimp only [L]
      have hc : s.2 ++ (tsegOf tl tst').toArray =
          (preT f ctx id k ++ List.flatMap (segOfT ctx) (B.body.zip sls) ++ tsegOf tl tst').toArray := by
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

/-! ## The whole loop -/

/-- **The loop, run, typed**: `lowerFunction`'s final loop state satisfies the typed invariant
after all blocks, on every input (no scope premise). -/
theorem loop_runT {f : Clif.Function} {vc : VCode} (h : lowerFunction f = .ok vc) :
    ∃ ctx ranges st0 paramBytes d bl, buildCtx f = .ok (ctx, ranges, st0) ∧
      sigParamBytes f.sig = .ok paramBytes ∧ LIT f ctx st0 f.blocks.length d bl ∧
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
    (fun k d => ∃ bl, LIT f ctx st0 k d bl) ?_ ?_ _ d ?_ hd
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
      obtain ⟨L, hL⟩ := blockStepT sp hpb hB hI hs
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
