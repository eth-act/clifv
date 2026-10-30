import FV.Backend.Proof.DriverCheckC
import FV.Backend.Proof.InstScopeTF

/-!
# Soundness of the validator with typed `try_call`s (S11e6, #419)

`DriverCheckTy.lean`'s soundness for `lowerCheckTC` (`DriverCheckC.lean`): the recorded lowering
`lowTermC` makes `lowerFunction`'s typed `try_call` calls (`lowTermC_spec`, `lowBlocksC_spec`),
and the shape check gives `LowerShapeTC`, `LowerShapeT` whose `try_call` facts are the typed
helpers' (`tryCallDataC`, `exnTableOpndC`, `tryRegsOfC`): `lowerShapeTC_of_ok`,
`loweringTC_of_check` and the tail facts (`noTryCallTC_of_check`, `noTlsTC_of_check`,
`callsStackTC_of_check`, `tryStackTC_of_check`, `entryOkTC_of_check`, `entryRegsTC_of_check`).
`LowerShapeT`, `lowerCheckT` and their theorems are unchanged. S11f: `LowerShapeTC.scope` is
`InstScopeTF` (the typed scope with the proven float operations; it was `InstScopeT`), so the
shape also describes the validator with the float operations (`DriverCheckTCF.lean`);
`instScopeT_of_lowerCheckTC` keeps the movement scope `lowerCheckTC` checks.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

theorem lowTermC_spec {f : Clif.Function} {tcall : TermCallF} {ycall : TryCallF} {ti : Nat}
    {t : Clif.Terminator} {tst : LState} {nl : Nat} {data : V} {targets : List Label}
    {tl : Option TryLow} {tst' : LState} {nl' : Nat}
    (h : lowTermC f tcall ycall ti t tst nl = some (data, targets, tl, tst', nl')) :
    (t.isTry = false → tl = none ∧ termData (abiTerm f t) = .ok data ∧
      ∃ out tr, tcall ti data t targets tst = .ok (some out, tst', tr)) ∧
    (∀ et, IsTryWith t et → ∃ T, tl = some T ∧ tryCallDataC f t = .ok data ∧
      exnTableOpndC f et = .ok (T.sig, T.items) ∧ tryTargets f et.dests nl = some (targets, nl') ∧
      tryRegsOfC T.sig tst = some (T.regs, T.st1) ∧ tryInfoOf T.sig T.items targets = some T.info ∧
      ∃ out tr, ycall ti data T.regs targets { T.st1 with emitted := #[] } =
        .ok (some out, tst', tr)) := by
  cases t with
  | tryCall fn0 args0 et0 =>
    refine ⟨fun h' => by simp [Clif.Terminator.isTry] at h', fun et ht => ?_⟩
    obtain rfl : et = et0 := by
      rcases ht with ⟨_, _, h'⟩ | ⟨_, _, h'⟩ <;> cases h'; rfl
    simp only [lowTermC] at h
    split at h
    · rename_i data0 sig items targets0 nl0 hd he htt
      split at h
      · rename_i trs st1 hr
        split at h
        · rename_i info hi
          split at h
          · rename_i o tst0 tr0 hy
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
            exact ⟨⟨info, sig, items, trs, st1⟩, rfl, hd, he, htt, hr, hi, o, tr0, hy⟩
          · cases h
        · cases h
      · cases h
    · cases h
  | tryCallIndirect c args0 et0 =>
    refine ⟨fun h' => by simp [Clif.Terminator.isTry] at h', fun et ht => ?_⟩
    obtain rfl : et = et0 := by
      rcases ht with ⟨_, _, h'⟩ | ⟨_, _, h'⟩ <;> cases h'; rfl
    simp only [lowTermC] at h
    split at h
    · rename_i data0 sig items targets0 nl0 hd he htt
      split at h
      · rename_i trs st1 hr
        split at h
        · rename_i info hi
          split at h
          · rename_i o tst0 tr0 hy
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
            exact ⟨⟨info, sig, items, trs, st1⟩, rfl, hd, he, htt, hr, hi, o, tr0, hy⟩
          · cases h
        · cases h
      · cases h
    · cases h
  | _ =>
    refine ⟨fun _ => ?_, fun et ht => by rcases ht with ⟨_, _, h'⟩ | ⟨_, _, h'⟩ <;> cases h'⟩
    simp only [lowTermC] at h
    split at h
    · rename_i data0 targets0 nl0 hd htg
      split at h
      · rename_i o tst0 tr0 hy
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
        exact ⟨rfl, hd, o, tr0, hy⟩
      · cases h
    · cases h

theorem lowBlocksC_spec {f : Clif.Function} {call : StmtCall} {tcall : TermCallF} {ycall : TryCallF} :
    ∀ {Bs : List Clif.Block} {start : Nat} {st : LState} {nl : Nat} {bl : List BLow},
      lowBlocksC f call tcall ycall start Bs st nl = some bl →
      bl.length = Bs.length ∧
      ∀ (bi : Nat) (B : Clif.Block) (L : BLow), Bs[bi]? = some B → bl[bi]? = some L →
        L.sl.length = B.body.length ∧
        (∀ (j : Nat) (sl : SLow), L.sl[j]? = some sl →
          ∃ tr, call (L.start + j) sl.st = .ok (some (.regsVec sl.rss), sl.st', tr)) ∧
        L.tst.emitted = #[] ∧
        ∃ nl0 nl', lowTermC f tcall ycall (L.start + B.body.length) B.term L.tst nl0 =
          some (L.data, L.targets, L.tl, L.tst', nl') := by
  intro Bs
  induction Bs with
  | nil =>
    intro start st nl bl h
    simp only [lowBlocksC, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun bi B L h => by simp at h⟩
  | cons B Bs ih =>
    intro start st nl bl h
    simp only [lowBlocksC] at h
    cases hstm : lowStmts call start B.body st with
    | none => rw [hstm] at h; cases h
    | some q =>
      obtain ⟨sls, stE⟩ := q
      rw [hstm] at h
      simp only at h
      cases hterm : lowTermC f tcall ycall (start + B.body.length) B.term { stE with emitted := #[] } nl with
      | none => rw [hterm] at h; cases h
      | some q =>
        obtain ⟨data, targets, tl, tst', nl'⟩ := q
        rw [hterm] at h
        simp only at h
        cases hrec : lowBlocksC f call tcall ycall (start + B.body.length + 1) Bs
            { tst' with emitted := #[] } nl' with
        | none => rw [hrec] at h; cases h
        | some bl' =>
          rw [hrec] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          obtain ⟨hlen, hbl⟩ := ih hrec
          obtain ⟨hsl, hsj⟩ := lowStmts_spec hstm
          refine ⟨by simp [hlen], fun bi B' L hB hL => ?_⟩
          cases bi with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hB hL
            subst hB hL
            exact ⟨hsl, hsj, rfl, nl, nl', hterm⟩
          | succ bi =>
            simp only [List.getElem?_cons_succ] at hB hL
            exact hbl bi B' L hB hL

section
variable (f : Clif.Function) (vc : VCode) (ctx : Ctx) (st0 : LState) (R : Reg → Reg)
  (gn : Nat → Nat) (bl : List BLow)

/-- **The structure of `lowerFunction f`'s VCode, typed, with typed `try_call`s**
(`LowerShapeT` whose `try_call` facts are `lowerFunction`'s typed helpers: `tryCallDataC`,
`exnTableOpndC`, `tryRegsOfC`). -/
structure LowerShapeTC : Prop where
  hctx : ∃ ranges, buildCtx f = .ok (ctx, ranges, st0)
  ctxInvT : CtxInvT f ctx
  scope : InstScopeTF ctx
  ren : VRenaming R gn
  temps : ∀ n, st0.nextVreg ≤ n → gn n = n
  params : ∀ B ∈ f.blocks, ∀ p ∈ B.params, gn p.1 = p.1
  len : bl.length = f.blocks.length
  size : f.blocks.length ≤ vc.blocks.size
  valsBelow : ∀ x r, ctx.valueReg? x = some r → x < st0.nextVreg
  labels : ∀ l (vb : VBlock), vc.blocks[l]? = some vb → vb.label = l
  fresh : st0.nextVreg ≤ f.freshValue
  tslot : ∀ (bi : Nat) (B : Clif.Block) (L : BLow), f.blocks[bi]? = some B → bl[bi]? = some L →
    ctx.insts[L.start + B.body.length]? = some (⟨.op .unit, [], [], none⟩ : IInfo)
  blk : ∀ bi B L, f.blocks[bi]? = some B → bl[bi]? = some L →
    ∃ vb, vc.blocks[bi]? = some vb ∧
    L.sl.length = B.body.length ∧
    (∀ j stm sl, B.body[j]? = some stm → L.sl[j]? = some sl →
      (∃ info, ctx.insts[L.start + j]? = some info ∧ info.clif = some stm.inst ∧
        info.results = stm.results) ∧
      sl.st.emitted = #[] ∧ st0.nextVreg ≤ sl.st.nextVreg ∧
      (∃ tr, runTerm ctx "lower" [.inst (L.start + j)] sl.st = .ok (some (.regsVec sl.rss), sl.st', tr)) ∧
      (∀ (k : Nat) r out cls, stm.results[k]? = some r → sl.rss[k]? = some [.vreg out cls] →
        gn r = gn out)) ∧
    L.tst.emitted = #[] ∧ st0.nextVreg ≤ L.tst.nextVreg ∧
    (B.term.isTry = false → L.tl = none ∧ termData (abiTerm f B.term) = .ok L.data ∧
      ∃ out tr, runTerm (termCtx ctx (L.start + B.body.length) L.data)
        (termCall B.term (L.start + B.body.length) L.targets).1
        (termCall B.term (L.start + B.body.length) L.targets).2 L.tst = .ok (some out, L.tst', tr)) ∧
    (∀ et, IsTryWith B.term et → ∃ T, L.tl = some T ∧
      tryCallDataC f B.term = .ok L.data ∧ exnTableOpndC f et = .ok (T.sig, T.items) ∧
      tryRegsOfC T.sig L.tst = some (T.regs, T.st1) ∧ tryInfoOf T.sig T.items L.targets = some T.info ∧
      ∃ out tr, runTerm (tryCtx ctx (L.start + B.body.length) L.data T.regs) "lower_branch"
        [.inst (L.start + B.body.length), .labels L.targets] { T.st1 with emitted := #[] } =
        .ok (some out, L.tst', tr)) ∧
    vb.insts.toList = preT f ctx R bi ++ ((List.range B.body.length).map (segT f ctx R bl bi)).flatten ++
      tseg R bl bi ∧
    tseg R bl bi ≠ [] ∧
    vb.params = (if bi = 0 then #[] else (B.params.map fun p => vregOf ctx p.1).toArray) ∧
    vb.branchArgs = (match B.term with
      | .jump bc => (bc.args.map fun a => R (vregOf ctx a)).toArray
      | _ => #[]) ∧
    (match B.term with
      | .jump bc => ∃ tl, blockIdx? f bc.block = some tl ∧ L.targets = [tl]
      | .tryCall _ _ et | .tryCallIndirect _ _ et => L.targets.length = et.dests.length ∧
        ∃ tl tlab T eb, blockIdx? f et.normal.block = some tl ∧ L.targets.getLast? = some tlab ∧
          L.tl = some T ∧ vc.blocks[tlab]? = some eb ∧ eb.insts = #[.jump tl] ∧ eb.params = #[] ∧
          eb.branchArgs = (et.normal.args.map (normArgRegT ctx R T.regs.1)).toArray ∧
          ∀ a ∈ et.normal.args, match a with
            | .val _ => True
            | .ret i => i < T.sig.returns.length
            | .exn _ => False
      | _ => L.targets.length = (dests B.term).length ∧
        ∀ (k : Nat) bc tlab, (dests B.term)[k]? = some bc → L.targets[k]? = some tlab →
          ∃ tl, blockIdx? f bc.block = some tl ∧
            (bc.args = [] → tlab = tl) ∧
            (bc.args ≠ [] → ∃ eb, vc.blocks[tlab]? = some eb ∧ eb.insts = #[.jump tl] ∧
              eb.params = #[] ∧ eb.branchArgs = (bc.args.map fun a => R (vregOf ctx a)).toArray))

end

/-- **Soundness of the typed shape check over the typed `try_call` recording.** -/
theorem lowerShapeTC_of_ok {f : Clif.Function} {vc : VCode} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {st0 : LState} {bl : List BLow} {gn : Nat → Nat}
    (hb : buildCtx f = .ok (ctx, ranges, st0))
    (hl : lowBlocksC f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
      f.blocks.length = some bl)
    (hgn : ∀ n, st0.nextVreg ≤ n → gn n = n) (hs : shapeOkT f vc ctx st0 gn bl = true) :
    LowerShapeTC f vc ctx st0 (renOf gn) gn bl := by
  obtain ⟨-, hlb⟩ := lowBlocksC_spec hl
  simp only [shapeOkT, Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hctx, hsc⟩, hvb⟩, hpar⟩, hlen⟩, hsize⟩, hlab⟩, hblk⟩, hfresh⟩ := hs
  have hblk' : ∀ bi B L, f.blocks[bi]? = some B → bl[bi]? = some L →
      blockOkT f vc ctx st0 (renOf gn) gn bl bi B L = true := by
    intro bi B L hB hL
    have := all_range hblk (lt_of_getElem? hB)
    simpa [hB, hL] using this
  refine ⟨⟨ranges, hb⟩, ctxOkT_sound hctx, (instScopeOk_sound hsc).toTF, renOf_vrenaming gn, hgn, ?_,
    hlen, hsize, ?_, ?_, hfresh, ?_, ?_⟩
  · intro B hB p hp
    have := List.all_eq_true.mp (List.all_eq_true.mp hpar B hB) p hp
    simpa using this
  · intro x r hx
    have : x < ctx.valReg.size := lt_valReg hx
    omega
  · intro l vb hvb
    have := all_range hlab (Array.getElem?_eq_some_iff.mp hvb).1
    simpa [hvb] using this
  · intro bi B L hB hL
    have h := hblk' bi B L hB hL
    unfold blockOkT at h
    split at h
    · cases h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have h' := h.2
      split at h'
      · rename_i info hinfo
        simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff, Option.isNone_iff_eq_none] at h'
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h'
        rw [hinfo]
        cases info
        simp_all
      · cases h'
  · intro bi B L hB hL
    obtain ⟨hsl, hsj, htemp0, nl0, nl', hterm⟩ := hlb bi B L hB hL
    obtain ⟨hnt, hty⟩ := lowTermC_spec hterm
    have h := hblk' bi B L hB hL
    unfold blockOkT at h
    split at h
    · cases h
    · rename_i vb hvb
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hst⟩, htemp⟩, hle⟩, hcode⟩, htne⟩, hpars⟩, hbargs⟩, hsucc⟩, -⟩ := h
      refine ⟨vb, hvb, hsl, ?_, by simpa using htemp, hle, fun hnt' => ?_, fun et ht => ?_,
        hcode, by simpa using htne, hpars, hbargs, succOkT_sound hsucc⟩
      rotate_left
      · obtain ⟨h1, h2, out, tr, h3⟩ := hnt hnt'
        exact ⟨h1, h2, out, tr, h3⟩
      · obtain ⟨T, h1, h2, h3, -, h5, h6, out, tr, h7⟩ := hty et ht
        exact ⟨T, h1, h2, h3, h5, h6, out, tr, h7⟩
      intro j stm sl hj hslj
      have := all_range hst (lt_of_getElem? hj)
      rw [hj, hslj] at this
      obtain ⟨h1, h2, h3, h4⟩ := stmtOk_sound this
      exact ⟨h1, h2, h3, hsj j sl hslj, h4⟩

/-- **Soundness of the validator with typed `try_call`s**: `lowerCheckTC f vc = true` gives the
typed structure of the VCode with typed `try_call` facts, an SSA availability certificate and
the `br_table` index typing. -/
theorem loweringTC_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheckTC f vc = true) :
    ∃ ctx st0 R gn bl A, LowerShapeTC f vc ctx st0 R gn bl ∧ Cert f ctx st0 gn bl A ∧
      ∀ B ∈ f.blocks, BrIdxTyped ctx B.term := by
  unfold lowerCheckTC at h
  split at h
  · cases h
  · rename_i ctx ranges st0 hb
    split at h
    · cases h
    · rename_i bl hl
      simp only [Bool.and_eq_true] at h
      have hS := lowerShapeTC_of_ok (gn := gnAt (gnTable st0.nextVreg (aliasOf f bl))) hb hl
        (fun n hn => gnAt_temp hn) h.1.1.1.1
      exact ⟨ctx, st0, _, _, bl, _, hS, cert_of_ok hS.len h.1.1.1.2, brIdx_of_ok h.1.1.2⟩

/-- The instructions of `buildCtx`'s context are in the typed movement scope when `lowerCheckTC`
accepts (its `instScopeOk`). -/
theorem instScopeT_of_lowerCheckTC {f : Clif.Function} {vc : VCode} (h : lowerCheckTC f vc = true)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (hb : buildCtx f = .ok (ctx, ranges, st0)) : InstScopeT ctx := by
  unfold lowerCheckTC at h
  rw [hb] at h
  simp only at h
  split at h
  · cases h
  · simp only [Bool.and_eq_true] at h
    have hs := h.1.1.1.1
    simp only [shapeOkT, Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hsc⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hs
    exact instScopeOk_sound hsc

/-- The tail of `lowerCheckTC` (its conjuncts after the shape and certificate). -/
theorem lowerCheckTC_tail {f : Clif.Function} {vc : VCode} (h : lowerCheckTC f vc = true) :
    ((f.blocks.any (·.term.isTry) || !vc.hasTryCall) && (hasTls f || !vc.hasTls)) = true ∧
      callsStackOkB f vc.outgoing = true ∧ entryOkBT f = true := by
  unfold lowerCheckTC at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [Bool.and_eq_true] at h
      exact ⟨by simp only [Bool.and_eq_true]; exact h.1.2, h.2.1, h.2.2⟩

/-- A function without `try_call` lowers to VCode without `tryCall` (`lowerCheckTC`). -/
theorem noTryCallTC_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheckTC f vc = true)
    (hf : ∀ B ∈ f.blocks, B.term.isTry = false) : vc.hasTryCall = false := by
  have h1 := (lowerCheckTC_tail h).1
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h1
  rcases h1.1 with h2 | h2
  · obtain ⟨B, hB, hB'⟩ := List.any_eq_true.mp h2
    rw [hf B hB] at hB'; cases hB'
  · exact h2

/-- A function without `tls_value` lowers to VCode without `ElfTlsGetAddr` (`lowerCheckTC`). -/
theorem noTlsTC_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheckTC f vc = true)
    (hf : hasTls f = false) : vc.hasTls = false := by
  have h1 := (lowerCheckTC_tail h).1
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h1
  rcases h1.2 with h2 | h2
  · rw [hf] at h2; cases h2
  · exact h2

/-- The calls of `f` fit the VCode's outgoing area (`lowerCheckTC`). -/
theorem callsStackTC_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheckTC f vc = true) :
    CallsStack f vc.outgoing := by
  have h2 := (lowerCheckTC_tail h).2.1
  simp only [callsStackOkB, Bool.and_eq_true] at h2
  intro B hB st hst fn args e hi he
  have := List.all_eq_true.mp (List.all_eq_true.mp h2.1 B hB) st hst
  rw [hi] at this
  simp only [he, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

/-- The callees of the `try_call`s of `f` fit the VCode's outgoing area (`lowerCheckTC`). -/
theorem tryStackTC_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheckTC f vc = true) :
    TryStack f vc.outgoing := by
  have h2 := (lowerCheckTC_tail h).2.1
  simp only [callsStackOkB, Bool.and_eq_true] at h2
  intro B hB fn args et hi e he
  have := List.all_eq_true.mp h2.2 B hB
  rw [hi] at this
  simp only [he, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

/-- The entry's parameter locations and byte sizes compute (`lowerCheckTC`'s `entryOkBT`). -/
theorem entryOkTC_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheckTC f vc = true) :
    (locsOf f.sig).length = f.sig.params.length ∧ ∃ bytes, sigParamBytes f.sig = .ok bytes := by
  have h2 := (lowerCheckTC_tail h).2.2
  simp only [entryOkBT, Bool.and_eq_true, beq_iff_eq] at h2
  refine ⟨h2.1.1, ?_⟩
  have h3 := h2.2
  split at h3
  · exact ⟨_, ‹_›⟩
  · cases h3

/-- The register-passed parameters of the entry are in x0..x8 or v0..v7 (`lowerCheckTC`). -/
theorem entryRegsTC_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheckTC f vc = true) :
    ∀ l ∈ locsOf f.sig, ∀ r, l = .reg r → (∃ n, r = .x n ∧ n ≤ 8) ∨ (∃ n, r = .v n ∧ n ≤ 7) := by
  have h2 := (lowerCheckTC_tail h).2.2
  simp only [entryOkBT, Bool.and_eq_true, beq_iff_eq] at h2
  intro l hl r hr
  have := List.all_eq_true.mp h2.1.2 l hl
  subst hr
  cases r with
  | x n => exact .inl ⟨n, rfl, by simpa using this⟩
  | v n => exact .inr ⟨n, rfl, by simpa using this⟩
  | _ => cases this

end Backend.Proof.Driver
