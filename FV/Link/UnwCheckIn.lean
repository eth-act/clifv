import FV.Link.UnwTryIn
import FV.Backend.Proof.LowerSimUCheck
import FV.Backend.Proof.UnwTryShape
import FV.Backend.Proof.UnwCallStmt

/-!
# The exceptional-edge validator from the input (S10g, #404)

`unwCheck f vc` (`FV/Backend/Proof/LowerSimUCheck.lean`) decides `UnwShape` on the lowering
`lowerCheck` records. **`unwCheck_complete`**: on input in the lowering scope (`Dominated`,
`LowerScope`) with the `try_call` input conditions `tryTablesB` (every exception table has at
least one item, each a `tag 0`/`tag 1` handler) and **`tryRetsB`** (every `try_call` signature
has at most two ABI returns, so the call defines x0 and x1 only), `unwCheck` accepts
`lowerFunction`'s output. The parts:

* a call statement's code contains a call (`stmtCall_hasCall`, `UnwCallStmt.lean`);
* a `try_call`'s code is call-free code then one call with the `try_call` defs
  (`tryEmS_run`, `UnwTryShape.lean`), so the call is last, its operands compute, its defs are
  late with distinct vregs, its def constraints are x0 and x1 (`tryUOk`), and the payload
  arguments `exnN` are those defs;
* the first handler's label holds `lowerFunction`'s edge block (a `jump` to the handler's
  block with the handler's arguments, `edgeBlocks`), found at its label (`LowerShape.labels`);
* the edge into the handler's block satisfies `Cert`'s edge conditions: `edgeOk_succ`, the edge
  argument of `certBlock_ok` for any successor of the block (not only the normal edge).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- **`edgeOk` for every successor** (`certBlock_ok`'s edge argument, generalised from the
edges the driver simulation enters, `edgeIds`, to every successor, `succIds`, such as a
`try_call`'s handlers). -/
theorem edgeOk_succ {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    {bl : List BLow} (hd : Dominated f) (hsc : LowerScope f)
    (hb : buildCtx f = .ok (ctx, ranges, st0))
    (hl : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
      f.blocks.length = some bl)
    {bi : Nat} {B : Clif.Block} {L : BLow} (hB : f.blocks[bi]? = some B) (hL : bl[bi]? = some L)
    {b : Clif.BlockId} (hbS : b ∈ succIds B.term) :
    blockIdx? f b ≠ some 0 ∧
      edgeOk f ctx (gnOf f st0 bl) f.blocks.toArray bl.toArray (inFix f ctx (gnOf f st0 bl))
        (Avail.of B L (inFix f ctx (gnOf f st0 bl)) bi) B.body.length b = true := by
  have hF := ctxFacts_of hb
  have hssa := hd.ssa
  have hD := defsAt_of hd hb hl hB hL
  have hlen' := (lowBlocks_start hl).1
  have hIn := inFix_fixOk (f := f) (ctx := ctx) (gn := gnOf f st0 bl)
  refine ⟨hsc.noEntryPred B (List.mem_of_getElem? hB) b hbS,
    edgeOk_of hlen' (fun tl TB TL htl hTB hTL => ?_)⟩
  have hDT := defsAt_of hd hb hl hTB hTL
  refine ⟨(List.nodup_append.mp (block_nodup hssa hTB)).1, fun x _ hm => ?_⟩
  have hxa := (mem_avail hTB hDT).mpr hm
  obtain ⟨hm1, hm2⟩ := (mem_av hTB).mp hxa
  have hxd : x ∉ defsOf f tl := fun h => by
    obtain ⟨T, k, s, hT, hs, hk⟩ := mem_defsOf.mp h
    rw [hTB] at hT; cases hT
    exact hm2 ⟨k, s, Nat.zero_le _, hs, hk⟩
  by_cases hxp : x ∈ TB.params.map (·.1)
  · exact ⟨.inl hxp, .inl ⟨hxp, defInst_par hF hssa hTB hxp⟩⟩
  · have hxi : x ∈ (inFix f ctx (gnOf f st0 bl)).getD tl [] := by
      rcases hm1 with h | h | ⟨k, _, hk, _⟩
      · exact absurd h hxp
      · exact h
      · omega
    have hxG := inFix_sub _ hxi
    refine ⟨.inr fun y hy => ?_, .inr ⟨hxp, ?_, ?_⟩⟩
    · rw [← parsOf_of hTB]; exact hd.paramFree ctx ranges st0 hb tl x hxG hxd y hy
    · have hsucc : tl ∈ succIdx f bi := by
        simp only [succIdx, hB]
        exact List.mem_filterMap.mpr ⟨b, hbS, htl⟩
      have hout := hIn.out tl x hxi bi hsucc
      refine (mem_avail hB hD).mp ((mem_av hB).mpr ⟨?_, ?_⟩)
      · rcases hout with h | h | h
        · exact .inl (by rwa [parsOf_of hB] at h)
        · obtain ⟨B', k, s, hB', hs, hk⟩ := mem_defsOf.mp h
          rw [hB] at hB'; cases hB'
          exact .inr (.inr ⟨k, s, lt_of_getElem? hs, hs, hk⟩)
        · exact .inr (.inl h)
      · rintro ⟨k, s, hk, hs, _⟩
        have := lt_of_getElem? hs; omega
    · have := (hIn.cand tl x hxi).2.2.2.2.2
      rwa [parsOf_of hTB] at this

/-- What `tryExnB` checks, as propositions, suffices (the converse of `tryExnB_sound`). -/
theorem tryExnB_of {f : Clif.Function} {vc : VCode} {ctx : Ctx} {gn : Nat → Nat}
    {bla : Array BLow} {In : Array (List Clif.ValueId)} {bi : Nat} {B : Clif.Block} {L : BLow}
    {et : Clif.ExnTable} {T : TryLow} {n : Nat} {d : Clif.TryDest} {rest : List Clif.ExnItem}
    {c : CallInfo} {ops : Array Operand} {h : TryHandler} {tl : Nat} {eb : VBlock}
    (hT : L.tl = some T) (hit : et.items = .tag n d :: rest) (hn : n ≤ 1)
    (hlast : L.tst'.emitted.toList.getLast? = some (.call c))
    (hpre : L.tst'.emitted.toList.dropLast.all notCallB = true) (hok : tryUOk c T.info = true)
    (hops : (MInst.call c).operands = .ok ops) (hh : T.info.handlers.head? = some h)
    (htl : blockIdx? f d.block = some tl) (hdl : defsLateB ops = true)
    (hargs : d.args.all (exnArgOk ops) = true) (htl0 : tl ≠ 0)
    (hedge : edgeOk f ctx gn f.blocks.toArray bla In (Avail.of B L In bi) B.body.length d.block =
      true)
    (heb : vc.blocks[h.label]? = some eb) (hi : eb.insts = #[.jump tl]) (hp : eb.params = #[])
    (hba : eb.branchArgs = (d.args.map (exnArgReg (renOf gn) ops)).toArray) :
    tryExnB f vc ctx gn bla In bi B L et = true := by
  unfold tryExnB
  rw [hT, hit, hlast]
  simp only [hops, hh, htl, heb, hpre, hok, hdl, hargs, hi, hp, hba, hedge, Bool.and_eq_true,
    decide_eq_true_eq, and_true, true_and]
  exact ⟨hn, htl0⟩

end Backend.Proof.Driver

namespace Link.EhCheck.Complete

set_option autoImplicit false

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.UnwShape E2E

/-! ## The input condition -/

/-- **The `try_call` signatures of `f`**: each has at most two ABI returns (the call then
defines exactly x0 and x1, the payload registers, `tryUOk`). -/
def tryRetsB (f : Clif.Function) : Bool :=
  f.blocks.all fun B => match B.term with
    | .tryCall _ _ et | .tryCallIndirect _ _ et => match f.sigDecls.lookup et.sig with
      | some sig => decide ((sigRets sig).length ≤ 2)
      | none => true
    | _ => true

theorem tryRets_of {f : Clif.Function} (h : tryRetsB f = true) {B : Clif.Block}
    (hB : B ∈ f.blocks) {et : Clif.ExnTable} (ht : IsTryWith B.term et) {sig : Clif.Signature}
    (hs : f.sigDecls.lookup et.sig = some sig) : (sigRets sig).length ≤ 2 := by
  have hb := List.all_eq_true.1 h B hB
  have hb' : (match f.sigDecls.lookup et.sig with
      | some sig => decide ((sigRets sig).length ≤ 2)
      | none => true) = true := by
    rcases ht with ⟨fn, args, he⟩ | ⟨c, args, he⟩ <;> rw [he] at hb <;> exact hb
  rw [hs] at hb'
  simpa using hb'

/-! ## Facts of the lowering -/

/-- The callee conventions `exnTableOpnd` admits. -/
theorem exnTableOpnd_conv {f : Clif.Function} {et : Clif.ExnTable} {sig : Clif.Signature}
    {items : List (Option Nat)} (h : exnTableOpnd f et = .ok (sig, items)) :
    sig.callConv = none ∨ sig.callConv = some .systemV := by
  unfold exnTableOpnd at h
  cases hs : f.sigDecls.lookup et.sig with
  | none => simp [hs] at h
  | some sig' =>
    simp only [hs] at h
    split at h
    · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    · rename_i hcc
      simp only [bind, Except.bind, pure, Except.pure] at h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · split at h
        · cases h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          simp only [Bool.not_eq_true, Bool.not_eq_false', Bool.or_eq_true,
            Option.isNone_iff_eq_none, beq_iff_eq] at hcc
          exact hcc

/-- `tryInfoOf`'s `clobberAll` for a convention `exnTableOpnd` admits. -/
theorem tryInfoOf_clob {sig : Clif.Signature} {items : List (Option Nat)} {ls : List Label}
    {info : TryInfo} (h : tryInfoOf sig items ls = some info)
    (hc : sig.callConv = none ∨ sig.callConv = some .systemV) : info.clobberAll = false := by
  unfold tryInfoOf at h
  split at h
  · cases h
  · cases h
    rcases hc with hc | hc <;> simp [hc]

/-- `tryInfoOf`'s first handler. -/
theorem tryInfoOf_head {sig : Clif.Signature} {n : Nat} {items : List (Option Nat)} {l : Label}
    {ls : List Label} {info : TryInfo} (h : tryInfoOf sig (some n :: items) (l :: ls) = some info) :
    ∃ hs, info.handlers = .tag n l :: hs := by
  unfold tryInfoOf at h
  split at h
  · cases h
  · cases h; exact ⟨_, rfl⟩

/-- The operands of a `try_call` rule's call: they compute, and its defs are `callDefOps D`. -/
theorem tryCall_ops {dst : CallDest} {L : List (Nat × Reg)} {D : List (Reg × Nat)}
    (hdst : (∃ nm, dst = .sym nm) ∨ ∃ t, dst = .reg (.vreg t .int)) :
    ∃ ops, (MInst.call ⟨dst, retPairs L, callDefs D⟩).operands = .ok ops ∧
      ops.toList.filter Operand.isDef = callDefOps D := by
  rcases hdst with ⟨nm, rfl⟩ | ⟨t, rfl⟩
  · exact ⟨_, operands_call_sym nm L D, by rw [List.toList_toArray]; exact defs_call L D⟩
  · refine ⟨_, operands_call_reg t L D, ?_⟩
    rw [List.toList_toArray, List.filter_cons_of_neg (by simp [tgtOp, Operand.isDef]),
      defs_call]

/-- The def operands of a `try_call` with at most two returns: `x0 ↦ b`, `x1 ↦ b + 1`. -/
theorem outDefs_two (b n : Nat) (hn : n ≤ 2) :
    outDefs b (max n 2) = [(.x 0, b), (.x 1, b + 1)] := by
  rw [show max n 2 = 2 by omega]
  simp [outDefs, List.range_succ]

/-! ## Completeness -/

set_option maxHeartbeats 1000000 in
/-- **Completeness of the exceptional-edge validator.** On input in the lowering scope
(`Dominated`, `LowerScope`) whose `try_call` tables have `tag 0`/`tag 1` items only
(`tryTablesB`) and whose `try_call` signatures have at most two ABI returns (`tryRetsB`),
`unwCheck` accepts `lowerFunction`'s output. -/
theorem unwCheck_complete {f : Clif.Function} {vc : VCode} (hd : Dominated f) (hs : LowerScope f)
    (ht : tryTablesB f = true) (hr : tryRetsB f = true) (h : lowerFunction f = .ok vc) :
    unwCheck f vc = true := by
  obtain ⟨ctx, ranges, st0, bl, hb, hl, hvb, -, hlf⟩ := lowerFunction_run hs.subsetE h
  obtain ⟨hu, hk, hwf⟩ := alias_facts hd hs hb hl
  have hR := resolve_eq hu hk hwf
  have hctx : CtxInv f ctx := ctxOk_sound (ctxOk_complete hs hb)
  have hcf := ctxFacts_of hb
  obtain ⟨hlen, hspec⟩ := lowBlocks_spec hl
  obtain ⟨-, hstart⟩ := lowBlocks_start hl
  have hS := lowerShape_of_ok (gn := gnOf f st0 bl) hb hl (fun n hn => gnAt_temp hn)
    (shapeOk_complete h hs hd.ssa hb hl hu hwf)
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
  unfold unwCheck
  rw [hb]; simp only; rw [hl]; simp only
  unfold unwOk
  refine List.all_eq_true.mpr fun bi hbi => ?_
  have hbi' := List.mem_range.mp hbi
  obtain ⟨B, hB⟩ : ∃ B, f.blocks[bi]? = some B := ⟨_, List.getElem?_eq_getElem hbi'⟩
  obtain ⟨L, hL⟩ : ∃ L, bl[bi]? = some L := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
  simp only [hB, hL]
  unfold unwBlockB
  simp only [Bool.and_eq_true]
  refine ⟨List.all_eq_true.mpr fun j _ => ?_, ?_⟩
  · -- a call statement's code contains a call
    split
    · rename_i stm sl hs' hsl
      obtain ⟨⟨info, hi, hic⟩, tr, hrun⟩ := hstm bi B L j stm sl hB hL hs' hsl
      have hany : ((∃ fn args, stm.inst = .call fn args) ∨
          ∃ sig callee args, stm.inst = .callIndirect sig callee args) →
          (sl.st'.emitted.toList.any fun m => !notCallB m) = true := fun hc => by
        obtain ⟨ci, hci⟩ := stmtCall_hasCall hctx hi hic hc hrun
        exact List.any_eq_true.mpr ⟨_, hci, rfl⟩
      unfold stmtCallB
      cases hI : stm.inst <;> simp only
      · exact hany (.inl ⟨_, _, hI⟩)
      · exact hany (.inr ⟨_, _, _, hI⟩)
    · rfl
  · -- the exceptional edge of a `try_call`
    rcases try_or B.term with hnt | ⟨et, het⟩
    · cases hT : B.term <;> simp [hT, Clif.Terminator.isTry] at hnt ⊢
    have hte : tryExnB f vc ctx (gnOf f st0 bl) bl.toArray (inFix f ctx (gnOf f st0 bl)) bi B L
        et = true := by
      obtain ⟨-, -, -, nl0, nl', hlt⟩ := hspec bi B L hB hL
      have hph := hcf.term bi B hB
      rw [← hstart bi L hL] at hph
      obtain ⟨T, hT, hdat, hexn, htt, htr, hinfo, out, tr, hrun⟩ := (lowTerm_spec hlt).2 et het
      obtain ⟨pre, dst, Lp, hem, hpre, hdst⟩ := tryEmS_run hs hb hph het hdat hexn htr hrun
      -- the table: a first `tag n` item with handler `d`
      obtain ⟨hne, hall⟩ := tryTables_of ht hBmem het
      obtain ⟨it0, rest, hit⟩ := List.exists_cons_of_ne_nil hne
      obtain ⟨n, d, rfl, hn⟩ := hall it0 (by rw [hit]; exact List.mem_cons_self ..)
      obtain ⟨hs', hhd⟩ : ∃ hs', et.handlers = d :: hs' := by
        simp [Clif.ExnTable.handlers, hit]
      have hds : et.dests = d :: (hs' ++ [et.normal]) := by
        simp [Clif.ExnTable.dests, hhd]
      -- the labels and the handler's block
      obtain ⟨htg, -, hidx⟩ := tryTargets_spec htt
      obtain ⟨nl1, hnl⟩ : ∃ ls, L.targets = nl0 :: ls := by
        rw [htg, hds]; exact ⟨_, List.range'_succ ..⟩
      obtain ⟨tl, htl⟩ := Option.isSome_iff_exists.mp (hidx d (by rw [hds]; exact List.mem_cons_self ..))
      have hdS : d.block ∈ succIds B.term := by
        rcases het with ⟨fn, args, he⟩ | ⟨c, args, he⟩ <;> rw [he] <;>
          simp only [succIds, hds, List.map_cons, List.mem_cons, true_or]
      obtain ⟨hnot0, hedge⟩ := edgeOk_succ hd hs hb hl hB hL hdS
      have htl0 : tl ≠ 0 := fun h0 => hnot0 (h0 ▸ htl)
      -- the items and the first handler
      obtain ⟨hilen, hiall⟩ := exnTableOpnd_items hexn hall
      obtain ⟨o, os, hitems⟩ : ∃ o os, T.items = o :: os := by
        cases hT' : T.items with
        | nil => rw [hT', hit] at hilen; simp at hilen
        | cons o os => exact ⟨o, os, rfl⟩
      obtain ⟨n0, rfl, hn0⟩ := hiall o (by rw [hitems]; exact List.mem_cons_self ..)
      rw [hitems, hnl] at hinfo
      obtain ⟨hs0, hhs⟩ := tryInfoOf_head hinfo
      have hhead : T.info.handlers.head? = some (.tag n0 nl0) := by rw [hhs]; rfl
      have hclob := tryInfoOf_clob hinfo (exnTableOpnd_conv hexn)
      -- the call's defs (over the declared returns, #587; the check bounds `sigRets`, which is
      -- at least as long)
      have hn2 : T.sig.returns.length ≤ 2 := by
        have h := tryRets_of hr hBmem het (Backend.exnTableOpnd_sig hexn)
        rcases sigRets_cases T.sig with e | ⟨e0, -⟩
        · rw [← e]; exact h
        · rw [e0]; exact Nat.zero_le _
      have hD2 := outDefs_two L.tst.nextVreg _ hn2
      obtain ⟨ops, hops, hdefs⟩ := tryCall_ops (L := Lp)
        (D := outDefs L.tst.nextVreg (max T.sig.returns.length 2)) hdst
      rw [hD2] at hdefs
      have hdc : defCons (.call ⟨dst, retPairs Lp,
          callDefs (outDefs L.tst.nextVreg (max T.sig.returns.length 2))⟩) =
          [.fixed (.x 0), .fixed (.x 1)] := by
        unfold defCons; rw [hops]; simp only [hdefs]; rfl
      have hpay : ∀ i, i < 2 → payVreg ops i = some (L.tst.nextVreg + i) := by
        intro i hi
        unfold payVreg
        rw [hdefs]
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl
      obtain ⟨-, htrs, -, -⟩ := tryRegsOf_spec (exnTableOpnd_cc hexn) htr
      -- the arguments the handler's edge passes
      obtain ⟨T', hT', hargs⟩ := hlf.tryArgs bi B L et hB hL het
      rw [hT, Option.some.injEq] at hT'
      subst hT'
      have hdargs := (hargs 0 d (by rw [hds]; rfl)).2
      have hnoret : ∀ i, Clif.TryArg.ret i ∉ d.args := fun i hi => by
        have := (hdargs _ hi).1
        rw [hhd] at this
        simp at this
      have hexn' : ∀ i, Clif.TryArg.exn i ∈ d.args → i < 2 := fun i hi => by
        have := (hdargs _ hi).2
        rw [htrs] at this
        simpa using this
      -- the edge block of the first handler, at its label
      obtain ⟨eb0, heb0e⟩ : ∃ eb0 : VBlock, eb0 =
          { label := nl0, insts := #[MInst.jump tl],
            branchArgs := (d.args.map (tryEdgeArg T.regs.1 T.regs.2)).toArray } := ⟨_, rfl⟩
      have heb0 : eb0 ∈ edgeBlocks f B L := by
        rw [shape_edgeBlocks_try het hT]
        refine List.mem_filterMap.mpr ⟨(d, nl0), ?_, by simp [edgeOfTry, htl, heb0e]⟩
        rw [hds, hnl]
        exact List.mem_cons_self ..
      have hmem : fixBlock (renOf (gnOf f st0 bl)) eb0 ∈ vc.blocks.toList := by
        rw [hvb]
        unfold vcBlocksOf
        simp only
        rw [hR]
        exact List.mem_map.mpr ⟨_, List.mem_append_right _ (List.mem_flatMap.mpr
          ⟨(B, L), List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨hB, hL⟩), heb0⟩), rfl⟩
      obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem hmem
      have hgi' : vc.blocks[i]? = some (fixBlock (renOf (gnOf f st0 bl)) eb0) := by
        rw [← Array.getElem?_toList, List.getElem?_eq_getElem hi, hgi]
      have hlab := hS.labels i _ hgi'
      simp only [fixBlock, heb0e] at hlab
      subst hlab heb0e
      refine tryExnB_of hT hit hn ?_ ?_ ?_ hops hhead htl ?_ ?_ htl0 hedge hgi' ?_ rfl ?_
      · rw [hem]; simp
      · rw [hem]
        simp only [Array.empty_append, List.toList_toArray, List.dropLast_concat,
          List.all_eq_true]
        intro m hm
        cases m with
        | call ci => exact absurd rfl (hpre _ hm ci)
        | _ => rfl
      · simp only [tryUOk, payloadRegOk, hdc, hclob, hhs, Bool.not_false, Bool.and_true,
          Bool.and_eq_true, Bool.or_eq_true]
        refine ⟨⟨⟨?_, by decide⟩, .inr (by decide)⟩, .inr (by decide)⟩
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn0 with rfl | rfl <;> rfl
      · simp [defsLateB, hdefs, callDefOps, Operand.isLate]
      · refine List.all_eq_true.mpr fun a ha => ?_
        cases a with
        | val v => rfl
        | ret i => exact absurd ha (hnoret i)
        | exn i =>
          have hi2 := hexn' i ha
          simp only [exnArgOk, hpay i hi2, hi2, decide_true, Option.isSome_some, Bool.and_self]
      · simp [fixBlock, MInst.mapRegs]
      · simp only [fixBlock, List.map_toArray, List.map_map]
        refine congrArg List.toArray (List.map_congr_left fun a ha => ?_)
        cases a with
        | val v => rfl
        | ret i => exact absurd ha (hnoret i)
        | exn i =>
          have hi2 := hexn' i ha
          simp only [Function.comp_apply, tryEdgeArg, exnArgReg, hpay i hi2, htrs]
          rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl
    rcases het with ⟨fn, args, he⟩ | ⟨c, args, he⟩ <;> rw [he] <;> exact hte

end Link.EhCheck.Complete
