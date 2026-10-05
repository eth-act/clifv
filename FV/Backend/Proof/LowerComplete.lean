import FV.Backend.Proof.LowerCert
import FV.Backend.Proof.LowerShapeOk
import FV.Backend.Proof.LowerDecide

/-!
# Completeness of the lowering validator (V1)

`lowerCheck_complete`: on input in `Dominated` and `LowerScope` (decidable conditions on the
CLIF function alone: `dominatedB`, `lowerScopeB`), `lowerCheck` accepts every output of
`lowerFunction`. With the soundness direction (`DriverCheckSound.lean`) this makes the lowering
driver correct without the validator as a premise (`E2E.Compiled.of_lower`).

The parts: the shape (`shapeOk_complete`, `LowerShapeOk.lean`), the SSA certificate
(`certOk_complete`, `LowerCert.lean`), and here the remaining conjuncts: `br_table` indices
(`LowerScope`), the `tryCall`/`ElfTlsGetAddr` flags (`IselFlow.lean`: rules never emit a
`tryCall`, only a `tls_value`'s lowering an `ElfTlsGetAddr`), the outgoing area (`call_outgoing`,
`try_outgoing`) and the entry's parameter locations (`sigArgLocs`).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-! ## The entry's parameter locations -/

/-- One step of `argLocs`' fold. -/
def argStep (q : Array ArgLoc × Nat × Nat) (b : Nat) : Array ArgLoc × Nat × Nat :=
  if q.2.1 < 8 then (q.1.push (.reg (.x q.2.1)), q.2.1 + 1, q.2.2)
  else (q.1.push (.stack (alignTo q.2.2 (max b 8))), q.2.1, alignTo q.2.2 (max b 8) + max b 8)

theorem argLocs_eq (bytes : List Nat) :
    (argLocs bytes).1 = (bytes.foldl argStep (#[], 0, 0)).1.toList := rfl

/-- A location in x0..x8 or on the stack. -/
def LocOk (l : ArgLoc) : Prop := ∀ r, l = .reg r → ∃ n, r = .x n ∧ n ≤ 8

theorem argStep_fold : ∀ (bytes : List Nat) (q : Array ArgLoc × Nat × Nat),
    (∀ l ∈ q.1.toList, LocOk l) →
    (bytes.foldl argStep q).1.size = q.1.size + bytes.length ∧
      ∀ l ∈ (bytes.foldl argStep q).1.toList, LocOk l
  | [], q, h => ⟨by simp, h⟩
  | b :: bytes, q, h => by
    have h' : ∀ l ∈ (argStep q b).1.toList, LocOk l := by
      intro l hl
      unfold argStep at hl
      split at hl
      · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hl
        rcases hl with hl | rfl
        · exact h l hl
        · intro r hr; cases hr; exact ⟨_, rfl, by omega⟩
      · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hl
        rcases hl with hl | rfl
        · exact h l hl
        · intro r hr; cases hr
    obtain ⟨h1, h2⟩ := argStep_fold bytes (argStep q b) h'
    refine ⟨?_, h2⟩
    rw [List.foldl_cons, h1]
    unfold argStep
    split <;> simp <;> omega

theorem sretLocStep_fold : ∀ (ps : List Clif.AbiParam) (q : Array ArgLoc × List ArgLoc),
    (∀ l ∈ q.1.toList, LocOk l) → (∀ l ∈ q.2, LocOk l) →
    ∀ l ∈ (ps.foldl sretLocStep q).1.toList, LocOk l
  | [], _, h1, _ => h1
  | p :: ps, q, h1, h2 => by
    rw [List.foldl_cons]
    apply sretLocStep_fold ps
    · intro l hl
      unfold sretLocStep at hl
      split at hl
      · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hl
        rcases hl with hl | rfl
        · exact h1 l hl
        · intro r hr; cases hr; exact ⟨8, rfl, Nat.le_refl _⟩
      · split at hl
        · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hl
          rcases hl with hl | rfl
          · exact h1 l hl
          · exact h2 l (by simp_all)
        · exact h1 l hl
    · intro l hl
      unfold sretLocStep at hl
      split at hl
      · exact h2 l hl
      · split at hl
        · rename_i l0 r0 hq
          exact h2 l (by rw [hq]; exact List.mem_cons_of_mem _ hl)
        · simp at hl

theorem sigArgs_length {s : Clif.Signature} {bytes : List Nat} (h : sigArgs s = .ok bytes) :
    bytes.length = s.params.length := by
  unfold sigArgs at h
  exact (Prep.lmapM_ok h).1

/-- `entryOkB` holds when the parameter locations and byte sizes compute. -/
theorem entryOkB_of {f : Clif.Function} {locs : List ArgLoc} {n : Nat} {bytes : List Nat}
    (hl : sigArgLocs f.sig = .ok (locs, n)) (hb : sigParamBytes f.sig = .ok bytes) :
    entryOkB f = true := by
  have hlocs : locsOf f.sig = locs := by simp [locsOf, hl]
  have key : locs.length = f.sig.params.length ∧ ∀ l ∈ locs, LocOk l := by
    unfold sigArgLocs at hl
    simp only [sigParamBytes] at hb
    rw [hb] at hl
    simp only [bind, Except.bind] at hl
    split at hl
    · split at hl
      · cases hl
      · rename_i hsz
        simp only [pure, Except.pure, Except.ok.injEq] at hl
        obtain ⟨rfl, -⟩ := hl
        refine ⟨by simpa using hsz, fun l hl => ?_⟩
        refine sretLocStep_fold f.sig.params (#[], (argLocs _).1) (by simp) (fun l hl => ?_) l hl
        rw [argLocs_eq] at hl
        exact (argStep_fold _ _ (by simp)).2 l hl
    · simp only [pure, Except.pure, Except.ok.injEq] at hl
      obtain ⟨rfl, -⟩ := hl
      have := argStep_fold bytes (#[], 0, 0) (by simp)
      change (bytes.foldl argStep (#[], 0, 0)).1.toList.length = _ ∧
        ∀ l ∈ (bytes.foldl argStep (#[], 0, 0)).1.toList, LocOk l
      refine ⟨by rw [Array.length_toList, this.1]; simp [sigArgs_length hb], this.2⟩
  simp only [entryOkB, hlocs, key.1, beq_self_eq_true, Bool.true_and, List.all_eq_true,
    Bool.and_eq_true, hb]
  refine ⟨fun l hl => ?_, trivial⟩
  have := key.2 l hl
  match l, this with
  | .stack _, _ => rfl
  | .reg r, h =>
    obtain ⟨n, rfl, hn⟩ := h r rfl
    simpa using hn

/-! ## The VCode's instructions -/

/-- `lowStmts` runs every statement from a state with nothing emitted. -/
theorem lowStmts_emptied {call : StmtCall} :
    ∀ {ss : List Clif.Stmt} {ii : Nat} {st : LState} {sls : List SLow} {stE : LState},
      lowStmts call ii ss st = some (sls, stE) → ∀ sl ∈ sls, sl.st.emitted = #[]
  | [], _, _, _, _, h => by
    simp only [lowStmts, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h; simp
  | _ :: ss, ii, st, sls, stE, h => by
    simp only [lowStmts] at h
    split at h
    · rename_i out st' tr' _
      split at h
      · rename_i rss _
        cases hrec : lowStmts call (ii + 1) ss { st' with emitted := #[] } with
        | none => rw [hrec] at h; cases h
        | some q =>
          rw [hrec] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          intro sl hsl
          rcases List.mem_cons.mp hsl with rfl | hsl
          · rfl
          · exact lowStmts_emptied hrec sl hsl
      · cases h
    · cases h

/-- The blocks of `vcBlocksOf`: a renamed raw block or a renamed edge block. -/
theorem mem_vcBlocksOf {f : Clif.Function} {bl : List BLow} {vb : VBlock}
    (h : vb ∈ (vcBlocksOf f bl).toList) :
    ∃ R, (∃ bi B L, f.blocks[bi]? = some B ∧ bl[bi]? = some L ∧ vb = fixBlock R (rawBlock f bl bi B)) ∨
      (∃ B L e, B ∈ f.blocks ∧ e ∈ edgeBlocks f B L ∧ vb = fixBlock R e) := by
  simp only [vcBlocksOf, List.toList_toArray, List.mem_map, List.mem_append, List.mem_flatMap] at h
  obtain ⟨vb0, h1, rfl⟩ := h
  refine ⟨lowerFunction.resolve (aliasArr (aliasOf f bl)) ((aliasArr (aliasOf f bl)).size + 1), ?_⟩
  rcases h1 with ⟨p, hp, rfl⟩ | ⟨p, hp, he⟩
  · have := List.mem_zipIdx_iff_getElem?.mp hp
    rw [List.getElem?_zip_eq_some] at this
    exact .inl ⟨p.2, p.1.1, p.1.2, this.1, this.2, rfl⟩
  · exact .inr ⟨p.1, p.2, vb0, (List.of_mem_zip hp).1, he, rfl⟩

/-- An edge block is a single `jump`. -/
theorem edgeBlocks_insts {f : Clif.Function} {B : Clif.Block} {L : BLow} {e : VBlock}
    (h : e ∈ edgeBlocks f B L) : ∃ tl, e.insts = #[.jump tl] := by
  unfold edgeBlocks at h
  split at h
  · simp only [List.mem_filterMap, Option.map_eq_some_iff] at h
    obtain ⟨_, -, tl, -, rfl⟩ := h; exact ⟨tl, rfl⟩
  · simp only [List.mem_filterMap, Option.map_eq_some_iff] at h
    obtain ⟨_, -, tl, -, rfl⟩ := h; exact ⟨tl, rfl⟩
  · simp at h
  · simp only [List.mem_filterMap] at h
    obtain ⟨_, -, h⟩ := h
    split at h
    · cases h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨tl, -, rfl⟩ := h; exact ⟨tl, rfl⟩

/-- A property of instructions that every renaming keeps and the driver's own instructions
(`args`, the parameter loads, result `mov`s, `jump`s) have, holds of every instruction of
`vcBlocksOf f bl` if it holds of every statement's and terminator's emitted code. -/
theorem vcBlocks_all (P : MInst → Prop) (hR : ∀ R m, P m → P (m.mapRegs R))
    (hargs : ∀ ds, P (.args ds)) (hload : ∀ op r a fl, P (.load op r a fl))
    (hmov : ∀ s a b, P (.mov s a b)) (hjump : ∀ l, P (.jump l))
    {f : Clif.Function} {bl : List BLow}
    (hs : ∀ (bi : Nat) (B : Clif.Block) (L : BLow) (j : Nat) (stm : Clif.Stmt) (sl : SLow),
      f.blocks[bi]? = some B → bl[bi]? = some L → B.body[j]? = some stm →
      L.sl[j]? = some sl → ∀ m ∈ sl.st'.emitted.toList, P m)
    (ht : ∀ (bi : Nat) (B : Clif.Block) (L : BLow), f.blocks[bi]? = some B → bl[bi]? = some L →
      ∀ m ∈ fixTry L.tl L.tst'.emitted.toList, P m) :
    ∀ vb ∈ (vcBlocksOf f bl).toList, ∀ m ∈ vb.insts.toList, P m := by
  intro vb hvb m hm
  obtain ⟨R, ⟨bi, B, L, hB, hL, rfl⟩ | ⟨B, L, e, -, he, rfl⟩⟩ := mem_vcBlocksOf hvb
  · simp only [fixBlock, rawBlock, Array.toList_map, List.mem_map, List.mem_append,
      List.mem_flatten] at hm
    obtain ⟨m0, hm0, rfl⟩ := hm
    apply hR
    rcases hm0 with (hpre | ⟨sg, hsg, hm0⟩) | htseg
    · unfold pre at hpre
      split at hpre
      · rename_i B0 _
        simp only [List.mem_cons] at hpre
        rcases hpre with rfl | hpre
        · exact hargs _
        · simp only [entryLoads, List.mem_filterMap] at hpre
          obtain ⟨q, -, hq⟩ := hpre
          unfold entryLoadOf at hq
          split at hq
          · cases hq; exact hload _ _ _ _
          · cases hq
      · simp at hpre
    · simp only [List.mem_range] at hsg
      obtain ⟨j, -, rfl⟩ := hsg
      unfold seg at hm0
      rw [hB, hL] at hm0
      simp only at hm0
      split at hm0
      · rename_i stm sl hstm hsl
        simp only [List.mem_map, List.mem_append] at hm0
        obtain ⟨m1, hm1, rfl⟩ := hm0
        apply hR
        rcases hm1 with hm1 | hm1
        · exact hs bi B L j stm sl hB hL hstm hsl m1 hm1
        · simp only [extraOf, List.mem_filterMap] at hm1
          obtain ⟨q, -, hq⟩ := hm1
          split at hq
          · cases hq
          · cases hq; exact hmov _ _ _
          · cases hq
      · simp at hm0
    · unfold tseg at htseg
      rw [hL] at htseg
      simp only [List.mem_map] at htseg
      obtain ⟨m1, hm1, rfl⟩ := htseg
      exact hR _ _ (ht bi B L hB hL m1 hm1)
  · obtain ⟨tl, hi⟩ := edgeBlocks_insts he
    simp only [fixBlock, hi, Array.toList_map, List.mem_map] at hm
    obtain ⟨m0, hm0, rfl⟩ := hm
    simp at hm0
    subst hm0
    exact hR _ _ (hjump tl)

/-! ## The outgoing area along the recorded lowering -/

/-- The driver's calls never lower the outgoing area. -/
def OutMono (call : StmtCall) (tcall : TermCallF) (ycall : TryCallF) : Prop :=
  (∀ ii s out s' tr, call ii s = .ok (out, s', tr) → s.outgoing ≤ s'.outgoing) ∧
  (∀ ti d t ls s out s' tr, tcall ti d t ls s = .ok (out, s', tr) → s.outgoing ≤ s'.outgoing) ∧
  ∀ ti d trs ls s out s' tr, ycall ti d trs ls s = .ok (out, s', tr) → s.outgoing ≤ s'.outgoing

theorem outMono_driver (ctx : Ctx) : OutMono (stmtCall ctx) (termCallF ctx) (tryCallF ctx) :=
  ⟨fun _ _ _ _ _ h => (runTerm_mono h).2.1, fun _ _ _ _ _ _ _ _ h => (runTerm_mono h).2.1,
    fun _ _ _ _ _ _ _ _ h => (runTerm_mono h).2.1⟩

theorem lowStmts_out {call : StmtCall} {tcall : TermCallF} {ycall : TryCallF}
    (hm : OutMono call tcall ycall) :
    ∀ {ss : List Clif.Stmt} {ii : Nat} {st : LState} {sls : List SLow} {stE : LState},
      lowStmts call ii ss st = some (sls, stE) →
      st.outgoing ≤ stE.outgoing ∧ ∀ sl ∈ sls, sl.st'.outgoing ≤ stE.outgoing
  | [], _, _, _, _, h => by
    simp only [lowStmts, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; simp
  | _ :: ss, ii, st, sls, stE, h => by
    simp only [lowStmts] at h
    split at h
    · rename_i out st' tr' hc
      split at h
      · cases hrec : lowStmts call (ii + 1) ss { st' with emitted := #[] } with
        | none => rw [hrec] at h; cases h
        | some q =>
          rw [hrec] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨h1, h2⟩ := lowStmts_out hm hrec
          have h0 := hm.1 _ _ _ _ _ hc
          refine ⟨by simp at h0 h1; omega, fun sl hsl => ?_⟩
          rcases List.mem_cons.mp hsl with rfl | hsl
          · simpa using h1
          · exact h2 sl hsl
      · cases h
    · cases h

theorem foldl_outgoing {α β : Type} (l : List α) (F : β × LState → α → β × LState)
    (hF : ∀ q a, (F q a).2.outgoing = q.2.outgoing) :
    ∀ q, (l.foldl F q).2.outgoing = q.2.outgoing := by
  induction l with
  | nil => intro q; rfl
  | cons a l ih => intro q; rw [List.foldl_cons, ih, hF]

theorem tryRegsOf_outgoing {sig : Clif.Signature} {st st1 : LState} {trs : List Reg × List Reg}
    (h : tryRegsOf sig st = some (trs, st1)) : st1.outgoing = st.outgoing := by
  unfold tryRegsOf at h
  simp only [bind, Option.bind] at h
  split at h
  · cases h
  · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rw [foldl_outgoing _ _ (fun q a => by split <;> rfl)]
    exact foldl_outgoing _ (fun (x : Array Reg × LState) (_ : Reg) =>
      (x.fst.push (x.snd.fresh RegClass.int).fst, (x.snd.fresh RegClass.int).snd)) (fun _ _ => rfl) _

theorem lowTerm_out {f : Clif.Function} {tcall : TermCallF} {ycall : TryCallF} {call : StmtCall}
    (hm : OutMono call tcall ycall) {ti : Nat} {t : Clif.Terminator} {tst : LState} {nl : Nat}
    {data : V} {targets : List Label} {tl : Option TryLow} {tst' : LState} {nl' : Nat}
    (h : lowTerm f tcall ycall ti t tst nl = some (data, targets, tl, tst', nl')) :
    tst.outgoing ≤ tst'.outgoing := by
  obtain ⟨hn, hy⟩ := lowTerm_spec h
  cases ht : t.isTry with
  | false =>
    obtain ⟨-, -, out, tr, hc⟩ := hn ht
    exact hm.2.1 _ _ _ _ _ _ _ _ hc
  | true =>
    obtain ⟨et, het⟩ : ∃ et, IsTryWith t et := by
      cases t <;> simp [Clif.Terminator.isTry] at ht
      · exact ⟨_, .inl ⟨_, _, rfl⟩⟩
      · exact ⟨_, .inr ⟨_, _, rfl⟩⟩
    obtain ⟨T, -, -, -, -, hr, -, out, tr, hc⟩ := hy et het
    have := hm.2.2 _ _ _ _ _ _ _ _ hc
    rw [tryRegsOf_outgoing hr] at this
    simpa using this

theorem getLast?_cons_getD {α β : Type} (g : α → β) (a : α) (l : List α) (d : β) :
    ((a :: l).getLast?.map g).getD d = (l.getLast?.map g).getD (g a) := by
  rw [List.getLast?_cons]
  cases l.getLast? <;> rfl

theorem lowBlocks_out {f : Clif.Function} {call : StmtCall} {tcall : TermCallF} {ycall : TryCallF}
    (hm : OutMono call tcall ycall) :
    ∀ {Bs : List Clif.Block} {start : Nat} {st : LState} {nl : Nat} {bl : List BLow},
      lowBlocks f call tcall ycall start Bs st nl = some bl →
      st.outgoing ≤ (bl.getLast?.map (·.tst'.outgoing)).getD st.outgoing ∧
      ∀ L ∈ bl, (∀ sl ∈ L.sl, sl.st'.outgoing ≤ (bl.getLast?.map (·.tst'.outgoing)).getD st.outgoing) ∧
        L.tst'.outgoing ≤ (bl.getLast?.map (·.tst'.outgoing)).getD st.outgoing
  | [], _, _, _, _, h => by
    simp only [lowBlocks, Option.some.injEq] at h
    subst h; simp
  | B :: Bs, start, st, nl, bl, h => by
    simp only [lowBlocks] at h
    cases hstm : lowStmts call start B.body st with
    | none => rw [hstm] at h; cases h
    | some q =>
      obtain ⟨sls, stE⟩ := q
      rw [hstm] at h
      simp only at h
      cases hterm : lowTerm f tcall ycall (start + B.body.length) B.term { stE with emitted := #[] } nl with
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
          obtain ⟨h1, h2⟩ := lowBlocks_out hm hrec
          obtain ⟨s1, s2⟩ := lowStmts_out hm hstm
          have t1 := lowTerm_out hm hterm
          rw [getLast?_cons_getD]
          simp only at h1 h2 t1 ⊢
          refine ⟨by omega, fun L hL => ?_⟩
          rcases List.mem_cons.mp hL with rfl | hL
          · exact ⟨fun sl hsl => by have := s2 sl hsl; omega, h1⟩
          · exact h2 L hL

/-! ## The flags -/

/-- Every statement of the recorded lowering runs from a state with nothing emitted. -/
theorem lowBlocks_emptied {f : Clif.Function} {call : StmtCall} {tcall : TermCallF}
    {ycall : TryCallF} :
    ∀ {Bs : List Clif.Block} {start : Nat} {st : LState} {nl : Nat} {bl : List BLow},
      lowBlocks f call tcall ycall start Bs st nl = some bl →
      ∀ L ∈ bl, ∀ sl ∈ L.sl, sl.st.emitted = #[]
  | [], _, _, _, _, h => by
    simp only [lowBlocks, Option.some.injEq] at h
    subst h; simp
  | B :: Bs, start, st, nl, bl, h => by
    simp only [lowBlocks] at h
    cases hstm : lowStmts call start B.body st with
    | none => rw [hstm] at h; cases h
    | some q =>
      obtain ⟨sls, stE⟩ := q
      rw [hstm] at h
      simp only at h
      cases hterm : lowTerm f tcall ycall (start + B.body.length) B.term { stE with emitted := #[] } nl with
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
          intro L hL
          rcases List.mem_cons.mp hL with rfl | hL
          · exact lowStmts_emptied hstm
          · exact lowBlocks_emptied hrec L hL

theorem mem_fixTry {T : Option TryLow} {ms : List MInst} {m : MInst} (h : m ∈ fixTry T ms) :
    m ∈ ms ∨ ∃ c ti, m = .tryCall c ti := by
  unfold fixTry at h
  split at h
  · unfold tryFix at h
    split at h
    · simp only [List.mem_append, List.mem_singleton] at h
      rcases h with h | rfl
      · exact .inl (List.dropLast_subset _ h)
      · exact .inr ⟨_, _, rfl⟩
    · exact .inl h
  · exact .inl h

theorem notTry_mapRegs (R : Reg → Reg) (m : MInst) (h : ∀ c ti, m ≠ .tryCall c ti) :
    ∀ c ti, m.mapRegs R ≠ .tryCall c ti := by
  intro c ti he
  cases m <;> simp only [MInst.mapRegs, reduceCtorEq] at he
  exact h _ _ rfl

theorem notTls_mapRegs (R : Reg → Reg) (m : MInst) (h : ∀ s rd tmp, m ≠ .elfTlsGetAddr s rd tmp) :
    ∀ s rd tmp, m.mapRegs R ≠ .elfTlsGetAddr s rd tmp := by
  intro s rd tmp he
  cases m <;> simp only [MInst.mapRegs, reduceCtorEq] at he
  exact h _ _ _ rfl

/-- The emitted code of a run from a state with nothing emitted. -/
theorem emitted_of_run {ctx : Ctx} {term : String} {args : List V} {s : LState} {out : Option V}
    {s' : LState} {tr : List Isle.RuleId} (h : runTerm ctx term args s = .ok (out, s', tr))
    (he : s.emitted = #[]) : ∀ m ∈ s'.emitted.toList, ∀ c ti, m ≠ .tryCall c ti := by
  obtain ⟨-, -, ms, hms, hno⟩ := runTerm_mono h
  rw [hms, he]
  simpa using hno

/-! ## Completeness -/

/-- **Completeness of the lowering validator (V1).** On input satisfying the decidable
conditions `Dominated` and `LowerScope`, `lowerCheck` accepts `lowerFunction`'s output. -/
theorem lowerCheck_complete {f : Clif.Function} {vc : VCode} (hd : Dominated f)
    (hs : LowerScope f) (h : lowerFunction f = .ok vc) : lowerCheck f vc = true := by
  obtain ⟨ctx, ranges, st0, bl, hb, hl, hvb, hout, hlf⟩ := lowerFunction_run h
  obtain ⟨hu, -, hwf⟩ := alias_facts hd hs hb hl
  have hctx : CtxInv f ctx := ctxOk_sound (ctxOk_complete hs hb)
  have hcf := ctxFacts_of hb
  obtain ⟨hlen, hstart⟩ := lowBlocks_start hl
  obtain ⟨-, hspec⟩ := lowBlocks_spec hl
  have hemp := lowBlocks_emptied hl
  obtain ⟨-, hlo⟩ := lowBlocks_out (outMono_driver ctx) hl
  -- the statements' runs
  have hstm : ∀ (bi : Nat) (B : Clif.Block) (L : BLow) (j : Nat) (stm : Clif.Stmt) (sl : SLow),
      f.blocks[bi]? = some B → bl[bi]? = some L →
      B.body[j]? = some stm → L.sl[j]? = some sl →
      (∃ info, ctx.insts[L.start + j]? = some info ∧ info.clif = some stm.inst) ∧
      ∃ tr, runTerm ctx "lower" [.inst (L.start + j)] sl.st =
        .ok (some (.regsVec sl.rss), sl.st', tr) := by
    intro bi B L j stm sl hB hL hj hsl
    obtain ⟨-, hc, -, -⟩ := hspec bi B L hB hL
    obtain ⟨info, hi, hic, -⟩ := hcf.stmt bi B j stm hB hj
    rw [hstart bi L hL]
    exact ⟨⟨info, hi, hic⟩, by rw [← hstart bi L hL]; exact hc j sl hsl⟩
  unfold lowerCheck
  rw [hb]; simp only; rw [hl]
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  refine ⟨⟨⟨⟨shapeOk_complete h hs hd.ssa hb hl hu hwf, certOk_complete hd hs hb hl⟩,
    (hs.ctxFacts ctx ranges st0 hb).1⟩, ?_, ?_⟩, ?_, ?_⟩
  · -- a `tryCall` only for a function with a `try_call`
    by_cases hT : (f.blocks.any fun x => x.term.isTry) = true
    · exact .inl hT
    · right
      have hnt : ∀ B ∈ f.blocks, B.term.isTry = false := by
        intro B hB
        simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at hT
        exact hT B hB
      have hall := vcBlocks_all (fun m => ∀ c ti, m ≠ .tryCall c ti) notTry_mapRegs
        (fun _ _ _ h => nomatch h) (fun _ _ _ _ _ _ h => nomatch h)
        (fun _ _ _ _ _ h => nomatch h) (fun _ _ _ h => nomatch h) (f := f) (bl := bl)
        (fun bi B L j stm sl hB hL hj hsl => by
          obtain ⟨-, tr, hrun⟩ := hstm bi B L j stm sl hB hL hj hsl
          exact emitted_of_run hrun (hemp L (List.mem_of_getElem? hL) sl (List.mem_of_getElem? hsl)))
        (fun bi B L hB hL => by
          obtain ⟨-, -, htst, nl0, nl', hterm⟩ := hspec bi B L hB hL
          obtain ⟨hn, -⟩ := lowTerm_spec hterm
          obtain ⟨htl, -, out, tr, hc⟩ := hn (hnt B (List.mem_of_getElem? hB))
          rw [htl]
          exact emitted_of_run hc htst)
      rw [VCode.hasTryCall, hvb, Bool.eq_false_iff]
      intro hc
      rw [← Array.any_toList, List.any_eq_true] at hc
      obtain ⟨vb, hvb', hi⟩ := hc
      rw [← Array.any_toList, List.any_eq_true] at hi
      obtain ⟨m, hm, hmt⟩ := hi
      have := hall vb hvb' m hm
      cases m <;> simp at hmt
      exact this _ _ rfl
  · -- an `ElfTlsGetAddr` only for a function with a `tls_value`
    by_cases hT : hasTls f = true
    · exact .inl hT
    · right
      have hnt : ∀ B ∈ f.blocks, ∀ st ∈ B.body, ∀ ty gv, st.inst ≠ .tlsValue ty gv := by
        intro B hB st hst ty gv he
        apply hT
        simp only [hasTls, List.any_eq_true]
        exact ⟨B, hB, st, hst, by rw [he]⟩
      have hall := vcBlocks_all (fun m => ∀ s rd tmp, m ≠ .elfTlsGetAddr s rd tmp) notTls_mapRegs
        (fun _ _ _ _ h => nomatch h) (fun _ _ _ _ _ _ _ h => nomatch h)
        (fun _ _ _ _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) (f := f) (bl := bl)
        (fun bi B L j stm sl hB hL hj hsl => by
          obtain ⟨⟨info, hi, hic⟩, tr, hrun⟩ := hstm bi B L j stm sl hB hL hj hsl
          obtain ⟨ms, hms, hno⟩ := stmt_noTls hctx hi hic
            (hnt B (List.mem_of_getElem? hB) stm (List.mem_of_getElem? hj)) hrun
          rw [hms, hemp L (List.mem_of_getElem? hL) sl (List.mem_of_getElem? hsl)]
          simpa using hno)
        (fun bi B L hB hL => by
          obtain ⟨-, -, htst, nl0, nl', hterm⟩ := hspec bi B L hB hL
          obtain ⟨hn, hy⟩ := lowTerm_spec hterm
          have hti : L.start + B.body.length < ctx.insts.size := by
            have := hcf.term bi B hB
            rw [← hstart bi L hL] at this
            exact (Array.getElem?_eq_some_iff.mp this).1
          intro m hm
          rcases mem_fixTry hm with hm | ⟨c, ti, rfl⟩
          · cases ht : B.term.isTry with
            | false =>
              obtain ⟨-, hd, out, tr, hc⟩ := hn ht
              obtain ⟨ms, hms, hno⟩ := termCall_noTls hctx hti hd hc
              rw [hms, htst] at hm
              exact hno m (by simpa using hm)
            | true =>
              obtain ⟨et, het⟩ : ∃ et, IsTryWith B.term et := by
                cases hB' : B.term <;> rw [hB'] at ht <;> simp [Clif.Terminator.isTry] at ht
                · exact ⟨_, .inl ⟨_, _, rfl⟩⟩
                · exact ⟨_, .inr ⟨_, _, rfl⟩⟩
              obtain ⟨T, -, hd, -, -, -, -, out, tr, hc⟩ := hy et het
              obtain ⟨ms, hms, hno⟩ := tryCall_noTls hctx hti hd hc
              rw [hms] at hm
              exact hno m (by simpa using hm)
          · intro s rd tmp h; cases h)
      rw [VCode.hasTls, hvb, Bool.eq_false_iff]
      intro hc
      rw [← Array.any_toList, List.any_eq_true] at hc
      obtain ⟨vb, hvb', hi⟩ := hc
      rw [← Array.any_toList, List.any_eq_true] at hi
      obtain ⟨m, hm, hmt⟩ := hi
      have := hall vb hvb' m hm
      cases m <;> simp at hmt
      exact this _ _ _ rfl
  · -- the outgoing area holds every call's stack arguments
    have hfin : (bl.getLast?.map (·.tst'.outgoing)).getD st0.outgoing = vc.outgoing := by
      rw [hout]; rfl
    have hL : ∀ B ∈ f.blocks, ∃ (bi : Nat) (L : BLow), f.blocks[bi]? = some B ∧ bl[bi]? = some L := by
      intro B hB
      obtain ⟨bi, hbi⟩ := List.mem_iff_getElem?.mp hB
      have : bi < bl.length := by rw [hlen]; exact lt_of_getElem? hbi
      exact ⟨bi, _, hbi, List.getElem?_eq_getElem this⟩
    simp only [callsStackOkB, Bool.and_eq_true, List.all_eq_true]
    refine ⟨fun B hB st hst => ?_, fun B hB => ?_⟩
    · obtain ⟨bi, L, hB', hL'⟩ := hL B hB
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hst
      obtain ⟨hsll, -⟩ := hspec bi B L hB' hL'
      obtain ⟨sl, hsl⟩ : ∃ sl, L.sl[j]? = some sl :=
        ⟨_, List.getElem?_eq_getElem (by rw [hsll]; exact lt_of_getElem? hj)⟩
      obtain ⟨⟨info, hi, hic⟩, tr, hrun⟩ := hstm bi B L j st sl hB' hL' hj hsl
      split
      · rename_i fn args hcall
        split
        · rename_i e he
          rw [hcall] at hic
          have h1 := call_outgoing hctx hi hic he hrun
          have h2 := (hlo L (List.mem_of_getElem? hL')).1 sl (List.mem_of_getElem? hsl)
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨by rw [← hfin]; omega, hs.stackLayout.1 B hB st hst fn args e hcall he⟩
        · rfl
      · rfl
    · obtain ⟨bi, L, hB', hL'⟩ := hL B hB
      split
      · rename_i fn args et ht
        split
        · rename_i e he
          obtain ⟨-, -, -, nl0, nl', hterm⟩ := hspec bi B L hB' hL'
          obtain ⟨-, hy⟩ := lowTerm_spec hterm
          obtain ⟨T, -, hd, -, -, -, -, out, tr, hc⟩ := hy et (.inl ⟨fn, args, ht⟩)
          have hti : L.start + B.body.length < ctx.insts.size := by
            have := hcf.term bi B hB'
            rw [← hstart bi L hL'] at this
            exact (Array.getElem?_eq_some_iff.mp this).1
          rw [ht] at hd
          have h1 := try_outgoing hctx hti hd he hc
          have h2 := (hlo L (List.mem_of_getElem? hL')).2
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨by rw [← hfin]; omega, hs.stackLayout.2 B hB fn args et e ht he⟩
        · rfl
      · rfl
  · -- the entry's parameter locations
    obtain ⟨locs, n, hloc⟩ := hlf.entry hs.nonempty
    obtain ⟨bytes, hby⟩ := hlf.paramBytes
    exact entryOkB_of hloc hby

end Backend.Proof.Driver
