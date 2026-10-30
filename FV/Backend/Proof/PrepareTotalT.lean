import FV.Backend.Proof.PrepareTotal
import FV.Backend.Proof.SpillEdgesLowT
import FV.Backend.Proof.IselTermFactsTy
import FV.Backend.Proof.SpillEdgesT
import FV.Backend.Proof.LowerCompleteT

/-!
# `prepare` is total on the typed scope (S11e5 Stage C, slice 8)

`Prep.prepare_ok` (`PrepareTotal.lean`) over the typed movement scope `LowerScopeT`: `prepare`
never fails on `lowerFunction`'s output for `Dominated`, `LowerScopeT` input (`prepare_okT`).

* `trap_shapeRT`, `ret_shapeRT`, `termShapeR_runTermT`: the code of a `return`/`trap` lowering
  over a float-capable context (`CtxInvT`) ends in a terminator (`udf`/`rets`; the symbolic runs
  of `trap_shapeTy`/`ret_shapeTy` with `PrepareTotalIsel`'s stronger conclusion `TermShapeR`);
* `raw_termT`: CLIF block `x`'s typed code ends in a terminator (`raw_term` over `LowT`);
* `prepIn_of_lowerT`: `lowerFunction`'s output meets `PrepIn` (`prepIn_of_lower`, typed);
* `prepare_okT`, `prepare_ok_cfgT`: `prepare` succeeds (with the CFG of its output).

Integer specialization: `prepare_ok_viaT` re-derives `prepare_ok`'s conclusion from its premises.
-/

namespace Backend.Proof.Prep

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-- `LowerTermShapeOkR` over float-capable contexts (`CtxInvT`). -/
def LowerTermShapeOkRT (p : Program) (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxInvT f ctx →
  ∀ (ti : Nat) (t : Clif.Terminator) (data : V), retOrTrap t = true → termData t = .ok data →
  ctx.insts[ti]? = some ⟨data, [], [], none⟩ →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n → ValsBelow ctx st →
    (∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ti]).run (st, tr) = .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ti]).run (st, tr) = .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    TermShapeR st st'

set_option maxHeartbeats 800000 in
/-- **`trap`** (`rule_lower_2237`) ends in `udf`, over float-capable contexts. -/
theorem trap_shapeRT {p : Program} (hp : Data p) : LowerTermShapeOkRT p rule_lower_2237 := by
  intro f ctx _ ti t data hrt hd hi cfg hc m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kU := fun n (hn : 30 ≤ n) s c v s' h => udf_ok hp (ctx := ctx) hc (n := n) (s := s) (c := c)
    (v := v) (s' := s') hn h
  have kS := fun n (hn : 60 ≤ n) i s v s' h => side_effect_inst_ok hp (ctx := ctx) hc (n := n) (i := i)
    (s := s) (v := v) (s' := s') hn h
  cases t with
  | ret xs =>
    rw [termData_ret] at hd; cases hd
    cases hp
    isel_inv [*, rule_lower_2237] at hmatch
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    simp at *
  | trap c =>
    rw [termData_trap] at hd; cases hd
    cases hp
    isel_inv [*, rule_lower_2237] at hmatch heval
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    repeat (isel_inv_simp [] at * <;> isel_destruct <;> subst_vars)
    have h528 := ‹ApplyInternal _ _ _ _ 46 528 _ _ _ _›
    obtain ⟨hs1, rfl⟩ := kU _ (by omega) _ _ _ _ h528
    have h243 := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
    obtain ⟨mi, hmi, hs2, rfl⟩ := kS _ (by omega) _ _ _ _ h243
    simp only at hs1 hs2
    subst hs2
    rw [hs1]
    rw [ofV_udf] at hmi
    cases hmi
    exact ⟨[], .udf c, by simp [LState.emit], rfl⟩
  | _ => simp [retOrTrap] at hrt

set_option maxHeartbeats 800000 in
/-- **`return`** (`rule_lower_2574`) ends in `rets` (values of either class). -/
theorem ret_shapeRT {p : Program} (hp : Data p) : LowerTermShapeOkRT p rule_lower_2574 := by
  intro f ctx _ ti t data hrt hd hi cfg hc m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kR := fun n (hn : 60 ≤ n) xs s v s' h => lower_return_okTy hp (ctx := ctx) hc (n := n)
    (xs := xs) (s := s) (v := v) (s' := s') hn h
  cases t with
  | trap c =>
    rw [termData_trap] at hd; cases hd
    cases hp
    isel_inv [*, rule_lower_2574] at hmatch
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    simp at *
  | ret xs =>
    rw [termData_ret] at hd; cases hd
    cases hp
    ctl_inv [*, rule_lower_2574] at hmatch heval
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    repeat (isel_inv_simp [ext_value_list_slice_iff] at * <;> isel_destruct <;> subst_vars)
    have h294 := ‹ApplyInternal _ _ _ _ 25 294 _ _ _ _›
    obtain ⟨rs, hrs, ps, hps, hs, -⟩ := kR _ (by omega) _ _ _ _ h294
    simp only at hs
    subst hs
    exact ⟨[], .rets (rs.zip ps), by simp [LState.emit], rfl⟩
  | _ => simp [retOrTrap] at hrt

/-- **`lower` on a `return`/`trap`** (float-capable context) appends code ending in a
terminator (`termShapeR_runTerm` over `CtxInvT`). -/
theorem termShapeR_runTermT {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {ti : Nat}
    {t : Clif.Terminator} {data : V} (hrt : retOrTrap t = true) (hd : termData t = .ok data)
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) {st : LState} {out : V} {st' : LState}
    {tr : List RuleId} (hvb : ValsBelow ctx st)
    (h : runTerm ctx "lower" [.inst ti] st = .ok (some out, st', tr)) : TermShapeR st st' := by
  obtain ⟨r, hr, m, n, env', s1, tr2, hm, hn, hfirst, hmatch, heval⟩ := runTerm_lower_rule h
  cases hroot : termRootRule r
  · exact absurd hmatch (Driver.lower_term_nomatch hrt hd hi hr hroot m (st, #[]) env' s1)
  · simp only [termRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
    rcases hroot with e | e
    · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2237 (by rw [e]; rfl)] at hfirst hmatch heval
      exact trap_shapeRT data_program f ctx hctx ti t data hrt hd hi {} rfl m n st #[] env' s1 out
        st' tr2 hm hn hvb hfirst hmatch heval
    · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2574 (by rw [e]; rfl)] at hfirst hmatch heval
      exact ret_shapeRT data_program f ctx hctx ti t data hrt hd hi {} rfl m n st #[] env' s1 out
        st' tr2 hm hn hvb hfirst hmatch heval

/-! ## `lowerFunction`'s VCode, typed -/

section lowT
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {bl : List BLow}
  {RR : Reg → Reg} (H : LowT f vc ctx st0 bl RR)
include H

/-- **CLIF block `x`'s typed code ends in a terminator** (`raw_term` over `LowT`, float scope). -/
theorem raw_termTF (hs : LowerScopeTF f) (hbt : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term) {x : Nat}
    {B : Clif.Block} {L : BLow} (hB : f.blocks[x]? = some B) (hL : bl[x]? = some L) :
    ∃ t, (fixBlock RR (rawBlockT f ctx bl x B)).insts.back? = some t ∧ t.isTerminator = true := by
  obtain ⟨ranges0, hb0⟩ := H.hb
  obtain ⟨t, hb', hjump, hnt, htry⟩ :=
    H.raw_backG (ctxInvT_ofF hs hb0) (fun B' hB' => termIntPos_ofF hs hb0 hB') hbt hB hL
  obtain ⟨-, -, hem, nl0, nl1, hlt⟩ := (lowBlocks_spec H.hbl).2 x B L hB hL
  rcases try_or B.term with ht | ⟨et, het⟩
  · obtain ⟨ranges, hb⟩ := H.hb
    have sp := ctxSpec_of hb
    have hctx : CtxInvT f ctx := ctxInvT_ofF hs hb
    have hst : L.start = blockStart f x := (lowBlocks_start H.hbl).2 x L hL
    have hph := sp.facts.term x B hB
    rw [← hst] at hph
    obtain ⟨htl, hd, out, tr, hrun⟩ := (lowTerm_spec hlt).1 ht
    obtain ⟨hctx', hi'⟩ := termCtx_factsTy hctx hph L.data
    have hval : ValsBelow ctx L.tst := by
      intro y r hy
      have h1 : y < ctx.valReg.size := by
        simp only [Ctx.valueReg?] at hy
        cases hh : ctx.valReg[y]? with
        | none => rw [hh] at hy; cases hy
        | some _ => exact (Array.getElem?_eq_some_iff.mp hh).1
      have h2 := sp.facts.size
      obtain ⟨stE, nlE, hr⟩ := H.low
      have h3 := lowB_mono _ _ _ _ _ _ _ hr x L hL
      omega
    have hvb' : ValsBelow (termCtx ctx (L.start + B.body.length) L.data) L.tst := hval
    have hfix : fixTry L.tl L.tst'.emitted.toList = L.tst'.emitted.toList := by rw [htl]; rfl
    have last : ∀ (ms : List MInst) (i : MInst), L.tst'.emitted = L.tst.emitted ++ (ms ++ [i]).toArray →
        (fixBlock RR (rawBlockT f ctx bl x B)).insts.back? = some (i.mapRegs RR) := by
      intro ms i he
      apply raw_backT_of hL
      rw [hfix, he, hem]
      simp
    -- a branch has as many targets as successors
    have hlen : (∀ bc, B.term ≠ .jump bc) → L.targets.length = (dests B.term).length := by
      intro hj'
      have htg := lowTerm_targets ht hlt
      rw [shape_targetsOf_other hj'] at htg
      exact (edgeTargets_spec htg).1
    unfold termCallF termCall at hrun
    cases hT : B.term with
    | jump bc =>
      obtain ⟨tl, rfl, -⟩ := hjump bc hT
      exact ⟨_, hb', rfl⟩
    | brif c tb eb =>
      refine ⟨t, hb', isTerminator_of_targets ?_⟩
      rw [(hnt ht).1]
      intro h0
      have := hlen (fun bc e => by rw [hT] at e; cases e)
      rw [h0, hT] at this
      simp [dests] at this
    | brTable y d tbl =>
      refine ⟨t, hb', isTerminator_of_targets ?_⟩
      rw [(hnt ht).1]
      intro h0
      have := hlen (fun bc e => by rw [hT] at e; cases e)
      rw [h0, hT] at this
      simp [dests] at this
    | ret xs =>
      rw [hT] at hrun hd
      obtain ⟨ms, i, he, hit⟩ := termShapeR_runTermT (t := .ret (xs ++ sretRet f)) hctx' rfl hd hi'
        hvb' hrun
      exact ⟨_, last _ _ he, by rw [isTerminator_mapRegs]; exact hit⟩
    | trap c =>
      rw [hT] at hrun hd
      obtain ⟨ms, i, he, hit⟩ := termShapeR_runTermT (t := .trap c) hctx' rfl hd hi' hvb' hrun
      exact ⟨_, last _ _ he, by rw [isTerminator_mapRegs]; exact hit⟩
    | returnCall fn args =>
      rw [hT] at hd
      simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
    | tryCall => rw [hT] at ht; cases ht
    | tryCallIndirect => rw [hT] at ht; cases ht
  · obtain ⟨c, ti, rfl, -⟩ := htry et het
    exact ⟨_, hb', rfl⟩

/-- **CLIF block `x`'s typed code ends in a terminator** (`raw_term` over `LowT`). -/
theorem raw_termT (hs : LowerScopeT f) (hbt : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term) {x : Nat}
    {B : Clif.Block} {L : BLow} (hB : f.blocks[x]? = some B) (hL : bl[x]? = some L) :
    ∃ t, (fixBlock RR (rawBlockT f ctx bl x B)).insts.back? = some t ∧ t.isTerminator = true :=
  raw_termTF H hs.toTF hbt hB hL

end lowT

/-- **`lowerFunction`'s VCode meets `PrepIn`** on `LowerScopeTF` input (`prepIn_of_lower` over
the float scope). -/
theorem prepIn_of_lowerTF {f : Clif.Function} {vc : VCode} (hs : LowerScopeTF f)
    (h : lowerFunction f = .ok vc) : PrepIn vc := by
  obtain ⟨ctx, st0, bl, RR, H⟩ := lowT_of hs.externsE h
  obtain ⟨ranges, hb⟩ := H.hb
  have hbt : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term := brIdx_of_ok (hs.ctxFacts ctx ranges st0 hb).1
  have hn : 0 < f.blocks.length := List.length_pos_iff.mpr hs.nonempty
  obtain ⟨B0, hB0⟩ : ∃ B0, f.blocks[0]? = some B0 := ⟨_, List.getElem?_eq_getElem hn⟩
  have dom := prepDomain_ofTF hs h
  -- a block's label is its index
  have tgt : ∀ (l : Nat) (vb : VBlock), vc.blocks[l]? = some vb → l ≠ 0 →
      ∃ k, lab vc.blocks l = some k ∧ k ≠ 0 := by
    intro l vb hvb h0
    obtain ⟨hl, e⟩ := Array.getElem?_eq_some_iff.mp hvb
    refine ⟨l, lab_of dom.labels hl ?_, h0⟩
    rw [e]
    rcases H.cases hvb with ⟨B, L, -, -, -, rfl⟩ | ⟨bi, B, L, e', -, -, -, hel, -, rfl⟩
    · rfl
    · exact hel
  refine ⟨dom, fun vb hvb => ?_, fun b vb hvb => ?_⟩
  · rw [H.raw_at hB0] at hvb
    cases hvb
    rfl
  rcases H.cases hvb with ⟨B, L, -, hB, hL, rfl⟩ | ⟨bi, B, L, e, hB, hL, he, -, -, rfl⟩
  · obtain ⟨t, hb', -, hnt, htry⟩ :=
      H.raw_backG (ctxInvT_ofF hs hb) (fun B' hB' => termIntPos_ofF hs hb hB') hbt hB hL
    obtain ⟨t2, hb2, hterm⟩ := raw_termTF H hs hbt hB hL
    rw [hb'] at hb2
    cases hb2
    refine ⟨t, hb', hterm, fun l hl => ?_⟩
    have hBm := List.mem_of_getElem? hB
    -- an edge block of `B`: labelled from the number of CLIF blocks on
    have viaE : ∀ e ∈ edgeBlocksT f ctx B L, e.label = l → ∃ k, lab vc.blocks l = some k ∧ k ≠ 0 := by
      intro e he hel
      obtain ⟨hge, hat⟩ := H.edge_at hB hL he
      rw [hel] at hge hat
      exact tgt l _ hat (by omega)
    rcases try_or B.term with ht | ⟨et, het⟩
    · rw [(hnt ht).1] at hl
      rcases (H.raw_tgt hB hL).1 ht l hl with ⟨bc, hbc, hidx, -⟩ | ⟨e, he, hel⟩
      · obtain ⟨TB, -, hTBi⟩ := block?_of_idx hidx
        exact tgt l _ (H.raw_at hTBi) fun h0 => hs.noEntryPred B hBm bc.block
          (by rw [succIds_of ht]; exact List.mem_map_of_mem hbc) (h0 ▸ hidx)
      · exact viaE e he hel
    · obtain ⟨c, ti, rfl, htg⟩ := htry et het
      rw [htg] at hl
      obtain ⟨e, he, hel⟩ := ((H.raw_tgt hB hL).2 et het).2 l hl
      exact viaE e he hel
  · obtain ⟨tl, TB, hins, -, hTB, htl0, -⟩ := H.edge_factsG hs.noEntryPred hB hL he
    refine ⟨.jump tl, by simp [fixBlock, hins]; rfl, rfl, fun l hl => ?_⟩
    simp only [MInst.targets, List.mem_singleton] at hl
    subst hl
    exact tgt _ _ (H.raw_at hTB) htl0

/-- **`lowerFunction`'s VCode meets `PrepIn`** on `Dominated`, `LowerScopeT` input
(`prepIn_of_lower` over the typed scope). -/
theorem prepIn_of_lowerT {f : Clif.Function} {vc : VCode} (_hd : Dominated f) (hs : LowerScopeT f)
    (h : lowerFunction f = .ok vc) : PrepIn vc :=
  prepIn_of_lowerTF hs.toTF h

/-- **`prepare` never fails on `lowerFunction`'s output** for input in the float scope
(`LowerScopeTF`). -/
theorem prepare_okTF {f : Clif.Function} {vc : VCode} (hs : LowerScopeTF f)
    (hl : lowerFunction f = .ok vc) : ∃ vcp, prepare vc = .ok vcp :=
  prepare_ok_of (prepIn_of_lowerTF hs hl)

/-- **`prepare` never fails on `lowerFunction`'s output** for input in the typed scope
(`Dominated`, `LowerScopeT`). -/
theorem prepare_okT {f : Clif.Function} {vc : VCode} (hd : Dominated f) (hs : LowerScopeT f)
    (hl : lowerFunction f = .ok vc) : ∃ vcp, prepare vc = .ok vcp :=
  prepare_ok_of (prepIn_of_lowerT hd hs hl)

/-- `prepare_okT`, with the CFG of `prepare`'s output (`cfg3`). -/
theorem prepare_ok_cfgT {f : Clif.Function} {vc : VCode} (hd : Dominated f) (hs : LowerScopeT f)
    (hl : lowerFunction f = .ok vc) : ∃ vcp, prepare vc = .ok vcp ∧ ∃ ss ps, vcp.cfg = .ok (ss, ps) := by
  obtain ⟨vcp, h⟩ := prepare_okT hd hs hl
  refine ⟨vcp, h, ?_⟩
  obtain ⟨ss0, ps0, ss1, ps1, ss2, ps2, next, B, E, hc0, -, hS, hc2, rfl⟩ := prepare_facts h
  exact cfg3 (prepDomain_ofT hd hs hl) (cfg_spec hc0) (cfg_spec hc2) hS

/-- **Integer specialization**: `prepare_ok`'s conclusion from its premises, through the typed
theorem (`LowerScope.toT`). -/
theorem prepare_ok_viaT {f : Clif.Function} {vc : VCode} (hd : dominatedB f = true)
    (hs : lowerScopeB f = true) (hl : lowerFunction f = .ok vc) : ∃ vcp, prepare vc = .ok vcp :=
  prepare_okT (dominated_of hd) (lowerScope_of hs).toT hl

end Backend.Proof.Prep
