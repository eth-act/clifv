import FV.E2E.LinkOwnCalls

/-! # `CallShapeHyp` from the ISLE runs (`CallRunHyp`) and the GOT vregs (`GotRunHyp`)

`callShapeHyp_of`: the call sites of `lowerFunction`'s VCode (`CallShapeHyp`) follow from two
smaller, program-independent hypotheses:

* `CallRunHyp`, the ISLE inversion at the level of one run of the driver (the form of
  `Spill.IselCtlHyp`): `lower` on a `call`/`call_indirect` statement emits only calls of that
  statement (operands `ShapeOf` the registers `callRegs` of its signature; a `blr` of a fresh
  vreg after the run's GOT load of the callee's name), `lower` on any other statement and a
  non-`try_call` terminator emit no call, and a `try_call`'s `lower_branch` emits the call of
  that terminator last and no other call; no run emits a `tryCall`.
* `GotRunHyp`: a fresh vreg that the run of a direct `call`/`try_call` loads from the GOT slot of
  `n` and calls through has GOT symbol `n` (`gotOf`). Not every GOT-loaded vreg has one: a
  `func_addr` of a non-colocated function is a GOT load into a fresh vreg `t` to which the CLIF
  value is renamed (`aliasOf`), so a `call_indirect` of it in another block is a `blr t` with no
  GOT load before it in its block (`gotOf vc t = none`; an indirect site, which needs no GOT
  symbol).

The driver part is proven here: the alias renaming (`VRenaming`; fresh vregs are fixed), the
entry block's `Args`/loads, the `mov`s of `extraOf`, the edge blocks' `jump`s, and `tryFix`
(the last call of a `try_call` run becomes the `tryCall`, whose `rets` are the ABI results of the
exception table's signature, the callee's: `tryCallData`).
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill

/-! ## The hypotheses -/

/-- A call emitted by `lower` on the CLIF statement `inst` (fresh vregs from `N`; `ms`: the
run's emitted instructions). -/
def RunCall (f : Clif.Function) (inst : Clif.Inst) (N : Nat) (ms : List MInst) (c : CallInfo) :
    Prop :=
  (∃ fn args e, inst = .call fn args ∧ f.extern? fn = some e ∧ ShapeOf (callRegs e.sig args) c ∧
    (c.dest = .sym e.name ∨ ∃ t, N ≤ t ∧ c.dest = .reg (.vreg t .int) ∧
      MInst.loadExtNameGot (.vreg t .int) e.name ∈ ms)) ∨
  (∃ sg callee args s, inst = .callIndirect sg callee args ∧ f.sigDecls.lookup sg = some s ∧
    ShapeOf (callRegs s args) c ∧ ∃ t, c.dest = .reg (.vreg t .int))

/-- The call a `try_call`/`try_call_indirect` terminator `t`'s `lower_branch` emits last. -/
def TryRunCall (f : Clif.Function) (t : Clif.Terminator) (N : Nat) (ms : List MInst)
    (c : CallInfo) : Prop :=
  (∃ fn args et e, t = .tryCall fn args et ∧ f.extern? fn = some e ∧
    ShapeOf (callRegs e.sig args) c ∧
    (c.dest = .sym e.name ∨ ∃ t', N ≤ t' ∧ c.dest = .reg (.vreg t' .int) ∧
      MInst.loadExtNameGot (.vreg t' .int) e.name ∈ ms)) ∨
  (∃ callee args et s, t = .tryCallIndirect callee args et ∧ f.sigDecls.lookup et.sig = some s ∧
    ShapeOf (callRegs s args) c ∧ ∃ t', c.dest = .reg (.vreg t' .int))

/-- No `call` among `ms`. -/
def NoCalls (ms : List MInst) : Prop := ∀ c, MInst.call c ∉ ms

/-- No `tryCall` among `ms`. -/
def NoTry (ms : List MInst) : Prop := ∀ c ti, MInst.tryCall c ti ∉ ms

/-- **The ISLE call inversion, per run of the driver** (program-independent; the form of
`Spill.IselCtlHyp`): a statement's `lower` emits only calls of that statement (`RunCall`, none
for a statement that is no call), a non-`try_call` terminator's run no call, a `try_call`'s
`lower_branch` the call of that terminator last (`TryRunCall`) and no other call; no run emits
a `tryCall`. -/
def CallRunHyp : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (st0 : LState),
    Dominated f → LowerScope f → AbiSigsOk f → buildCtx f = .ok (ctx, ranges, st0) →
    (∀ ii info inst s out s' tr, ctx.insts[ii]? = some info → info.clif = some inst →
      (∃ B ∈ f.blocks, ∃ st ∈ B.body, st.inst = inst) → ctx.valDef.size ≤ s.nextVreg →
      runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr) →
      ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧ NoTry ms ∧
        ∀ c, MInst.call c ∈ ms → RunCall f inst ctx.valDef.size ms c) ∧
    (∀ ti t data targets s out s' tr, ti < ctx.insts.size →
      ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → t.isTry = false →
      termData (abiTerm f t) = .ok data → ctx.valDef.size ≤ s.nextVreg →
      termCallF ctx ti data t targets s = .ok (out, s', tr) →
      ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧ NoTry ms ∧ NoCalls ms) ∧
    (∀ ti t et data sig items lo trs st1 targets out s' tr, ti < ctx.insts.size →
      ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → IsTryWith t et →
      (∃ B ∈ f.blocks, B.term = t) →
      tryCallData f t = .ok data → exnTableOpnd f et = .ok (sig, items) →
      ctx.valDef.size ≤ lo.nextVreg → tryRegsOf sig lo = some (trs, st1) →
      tryCallF ctx ti data trs targets { st1 with emitted := #[] } = .ok (out, s', tr) →
      ∃ (ms : List MInst) (c : CallInfo), s'.emitted = (ms ++ [MInst.call c]).toArray ∧
        NoTry ms ∧ NoCalls ms ∧ TryRunCall f t ctx.valDef.size (ms ++ [MInst.call c]) c)

/-- **The GOT vreg of a direct call** (program-independent): in the code `ms` a `call`
statement's `lower` run, or a `try_call` terminator's `lower_branch` run, emits (before
`tryFix`), a fresh vreg `t` that the run loads from the GOT slot of `n` and calls through has the
GOT symbol `n` in `lowerFunction`'s VCode. (Unlike a `func_addr`'s GOT vreg, it is no run's
result, so no alias renames a CLIF value to it, and no instruction outside its run reads or
writes it.) -/
def GotRunHyp : Prop :=
  ∀ (p : Clif.Program) (f : Clif.Function) (vc : VCode), InSubset p f → Dominated f →
    LowerScope f → lowerFunction f = .ok vc →
    ∀ (ctx : Ctx) (ranges : Array (Nat × Nat)) (st0 : LState) (bl : List BLow),
      buildCtx f = .ok (ctx, ranges, st0) →
      lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length =
        some bl →
      ∀ (bi : Nat) (B : Clif.Block) (L : BLow) (ms : List MInst) (c : CallInfo) (t : Nat)
        (n : String), f.blocks[bi]? = some B → bl[bi]? = some L →
        ((∃ (j : Nat) (stm : Clif.Stmt) (sl : SLow) (fn : Clif.FnRef) (args : List Nat),
            B.body[j]? = some stm ∧ L.sl[j]? = some sl ∧
            stm.inst = Clif.Inst.call fn args ∧ sl.st'.emitted.toList = ms) ∨
          (∃ T fn args et, B.term = .tryCall fn args et ∧ L.tl = some T ∧
            L.tst'.emitted.toList = ms)) →
        ctx.valDef.size ≤ t → MInst.loadExtNameGot (.vreg t .int) n ∈ ms →
        MInst.call c ∈ ms → c.dest = .reg (.vreg t .int) → gotOf vc t = some n

/-! ## Renaming -/

/-- The renaming of a call's operands (`MInst.mapRegs` on `call`/`tryCall`). -/
def callMap (R : Reg → Reg) (c : CallInfo) : CallInfo :=
  { c with
    dest := match c.dest with
      | .reg r => .reg (R r)
      | d => d
    uses := c.uses.map fun (v, p) => (R v, p)
    defs := c.defs.map fun (p, v) => (p, R v) }

theorem mapRegs_call_inv {R : Reg → Reg} {m : MInst} {c : CallInfo}
    (h : m.mapRegs R = .call c) : ∃ c0, m = .call c0 ∧ c = callMap R c0 := by
  cases m <;> simp only [MInst.mapRegs, reduceCtorEq] at h
  all_goals first
    | (cases h; exact ⟨_, rfl, rfl⟩)
    | (injection h with h; exact ⟨_, rfl, h.symm⟩)
    | skip

theorem mapRegs_tryCall_inv {R : Reg → Reg} {m : MInst} {c : CallInfo} {ti : TryInfo}
    (h : m.mapRegs R = .tryCall c ti) : ∃ c0, m = .tryCall c0 ti ∧ c = callMap R c0 := by
  cases m <;> simp only [MInst.mapRegs, reduceCtorEq] at h
  all_goals first
    | (cases h; exact ⟨_, rfl, rfl⟩)
    | (injection h with h1 h2; subst h2; exact ⟨_, rfl, h1.symm⟩)
    | skip

theorem shapeOf_map {R : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming R gn) {rs : List Reg}
    {c : CallInfo} (h : ShapeOf rs c) : ShapeOf rs (callMap R c) := by
  obtain ⟨L, D, hu, hd, hL, hD⟩ := h
  refine ⟨L.map fun q => (gn q.1, q.2), D.map fun q => (q.1, gn q.2), ?_, ?_, ?_, ?_⟩
  · simp only [callMap, hu, retPairs, List.map_map]
    exact List.map_congr_left fun q _ => by simp [hg.vreg]
  · simp only [callMap, hd, callDefs, List.map_map]
    exact List.map_congr_left fun q _ => by simp [hg.vreg]
  · simpa [List.map_map, Function.comp_def] using hL
  · simpa [List.map_map, Function.comp_def] using hD

theorem callMap_sym {R : Reg → Reg} {c : CallInfo} {n : String} (h : c.dest = .sym n) :
    (callMap R c).dest = .sym n := by
  simp [callMap, h]

theorem callMap_reg {R : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming R gn) {c : CallInfo}
    {t : Nat} (h : c.dest = .reg (.vreg t .int)) :
    (callMap R c).dest = .reg (.vreg (gn t) .int) := by
  simp [callMap, h, hg.vreg]

/-! ## `try_call` facts -/

theorem tryInfoOf_rets {s : Clif.Signature} {items : List (Option Nat)} {ls : List Label}
    {info : TryInfo} (h : tryInfoOf s items ls = some info) : info.rets = (sigRets s).length := by
  unfold tryInfoOf at h
  split at h
  · cases h
  · cases h; rfl

/-- A direct `try_call`'s exception table signature is its callee's. -/
theorem tryCallData_sig {f : Clif.Function} {fn : Clif.FnRef} {args : List Nat}
    {et : Clif.ExnTable} {data : V} {sig : Clif.Signature} {items : List (Option Nat)}
    {e : Clif.ExtFunc} (h : tryCallData f (.tryCall fn args et) = .ok data)
    (he : exnTableOpnd f et = .ok (sig, items)) (hf : f.extern? fn = some e) : e.sig = sig := by
  simp only [tryCallData, he, hf, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i hne
    simpa using hne

/-! ## The lift -/

/-- **`CallShapeHyp` from the per-run ISLE inversion and the GOT vregs of direct calls.** -/
theorem callShapeHyp_of (hR : CallRunHyp) (hG : GotRunHyp) : CallShapeHyp := by
  intro p f vc hsub hd hs hl b vb k hb
  have ha := abiSigsOk_of_inSubset hsub
  obtain ⟨ctx, ranges, st0, bl, hbc, hlb, hvb, -, -⟩ := lowerFunction_run hl
  obtain ⟨hS, hT, hY⟩ := hR f ctx ranges st0 hd hs ha hbc
  have hgr := hG p f vc hsub hd hs hl ctx ranges st0 bl hbc hlb
  have hcf := ctxFacts_of hbc
  obtain ⟨-, hstart⟩ := lowBlocks_start hlb
  obtain ⟨-, hspec⟩ := lowBlocks_spec hlb
  have hemp := lowBlocks_emptied hlb
  obtain ⟨hord, -⟩ := driver_ord hlb
  have hN : st0.nextVreg = ctx.valDef.size := hcf.size.1
  let al := aliasOf f bl
  let R := lowerFunction.resolve (aliasArr al) ((aliasArr al).size + 1)
  let gn := chaseF (fun n => ((aliasArr al)[n]?).join) ((aliasArr al).size + 1)
  have hg : VRenaming R gn := ⟨resolve_vreg _ _, fun r hr => by
    cases r with
    | vreg n c => exact absurd rfl (hr n c)
    | _ => rfl⟩
  have hkey : ∀ n o, (n, o) ∈ al → n < ctx.valDef.size := by
    intro n o hm
    have := (aliasOf_keys f bl).subset (List.mem_map_of_mem (f := (·.1)) hm)
    exact hN ▸ (hcf.vals n this).1
  have hfix : ∀ n, ctx.valDef.size ≤ n → gn n = n := fun n hn =>
    resolve_fix al (fun o hm => absurd (hkey n o hm) (by omega))
  have hvbm : vb ∈ vc.blocks.toList := Array.mem_toList_iff.mpr (Array.mem_of_getElem? hb)
  suffices H : ∀ i ∈ vb.insts.toList, (∀ c, i = .call c → SiteCall f vc false 0 c) ∧
      (∀ c ti, i = .tryCall c ti → SiteCall f vc true ti.rets c) by
    have hk : ∀ i, vb.insts[k]? = some i → i ∈ vb.insts.toList := fun i h =>
      Array.mem_toList_iff.mpr (Array.mem_of_getElem? h)
    exact ⟨fun c h => (H _ (hk _ h)).1 c rfl, fun c ti h => (H _ (hk _ h)).2 c ti rfl⟩
  intro i hi
  rw [hvb] at hvbm
  rcases mem_vcBlocksOf' hvbm with ⟨bi, B, L, hB, hL, rfl⟩ | ⟨B, L, e, -, he, rfl⟩
  · have hi' : i ∈ ((rawBlock f bl bi B).insts.map (MInst.mapRegs R)).toList := hi
    rw [rawBlock_insts] at hi'
    simp only [List.mem_append, List.mem_flatten, List.mem_map, List.mem_range] at hi'
    rcases hi' with (hpre | ⟨sg, ⟨j, -, rfl⟩, hm⟩) | htseg
    · -- the entry block's `Args` and parameter loads
      unfold pre at hpre
      split at hpre
      · simp only [List.mem_cons] at hpre
        rcases hpre with rfl | hpre
        · exact ⟨fun c h => (by cases h), fun c ti h => (by cases h)⟩
        · simp only [entryLoads, List.mem_filterMap] at hpre
          obtain ⟨q, -, hq⟩ := hpre
          unfold entryLoadOf at hq
          split at hq
          · cases hq; exact ⟨fun c h => (by cases h), fun c ti h => (by cases h)⟩
          · cases hq
      · simp at hpre
    · -- a statement's segment
      unfold seg at hm
      rw [hB, hL] at hm
      simp only at hm
      split at hm
      · rename_i stm sl hstm hsl
        simp only [List.mem_map, List.mem_append] at hm
        obtain ⟨m, hm, rfl⟩ := hm
        rcases hm with hm | hm
        · obtain ⟨info, hinf, hic, -⟩ := hcf.stmt bi B j stm hB hstm
          obtain ⟨-, hc, -, -⟩ := hspec bi B L hB hL
          obtain ⟨tr, hrun⟩ := hc j sl hsl
          rw [hstart bi L hL] at hrun
          have hge : ctx.valDef.size ≤ sl.st.nextVreg := hN ▸ ((hord bi L hL).stmt j sl hsl).1
          have hBm : B ∈ f.blocks := List.mem_of_getElem? hB
          have hsm : stm ∈ B.body := List.mem_of_getElem? hstm
          obtain ⟨ms, hms, hnt, hcall⟩ := hS _ info stm.inst _ _ _ _ hinf hic
            ⟨B, hBm, stm, hsm, rfl⟩ hge hrun
          rw [hemp L (List.mem_of_getElem? hL) sl (List.mem_of_getElem? hsl)] at hms
          rw [hms] at hm
          have hm' : m ∈ ms := by simpa using hm
          refine ⟨fun c h => ?_, fun c ti h => ?_⟩
          · obtain ⟨c0, rfl, rfl⟩ := mapRegs_call_inv h
            rcases hcall c0 hm' with ⟨fn, args, e, hin, hfn, hsh, hdst⟩ |
              ⟨sg', callee, args, s, hin, hsg, hsh, t, hdst⟩
            · refine ⟨args, .inl ⟨e, ⟨fn, hfn, B, hBm, .inl ⟨rfl, stm, hsm, hin⟩⟩,
                shapeOf_map hg hsh, fun h => (by cases h), ?_⟩⟩
              rcases hdst with hdst | ⟨t, ht, hdst, hgl⟩
              · exact .inl (callMap_sym hdst)
              · exact .inr ⟨t, by rw [callMap_reg hg hdst, hfix t ht],
                  hgr bi B L ms c0 t e.name hB hL
                    (.inl ⟨j, stm, sl, fn, args, hstm, hsl, hin, by rw [hms]; simp⟩)
                    ht hgl hm' hdst⟩
            · exact ⟨args, .inr ⟨s, ⟨B, hBm, .inl ⟨rfl, stm, hsm, sg', callee, hin, hsg⟩⟩,
                shapeOf_map hg hsh, fun h => (by cases h), gn t, callMap_reg hg hdst⟩⟩
          · obtain ⟨c0, rfl, -⟩ := mapRegs_tryCall_inv h
            exact absurd hm' (hnt c0 ti)
        · obtain ⟨s, a, b, rfl⟩ := mem_extraOf hm
          exact ⟨fun c h => (by cases h), fun c ti h => (by cases h)⟩
      · simp at hm
    · -- the terminator's segment
      unfold tseg at htseg
      rw [hL] at htseg
      simp only [List.mem_map] at htseg
      obtain ⟨m, hm, rfl⟩ := htseg
      obtain ⟨-, -, htst, nl0, nl', hterm⟩ := hspec bi B L hB hL
      obtain ⟨hn, hy⟩ := lowTerm_spec hterm
      have hph := hcf.term bi B hB
      rw [← hstart bi L hL] at hph
      have hti := (Array.getElem?_eq_some_iff.mp hph).1
      have hge : ctx.valDef.size ≤ L.tst.nextVreg := hN ▸ (hord bi L hL).term.1
      have hBm : B ∈ f.blocks := List.mem_of_getElem? hB
      cases ht : B.term.isTry with
      | false =>
        obtain ⟨htl, hdat, out, tr, hc⟩ := hn ht
        obtain ⟨ms, hms, hnt, hnc⟩ := hT _ _ _ _ _ _ _ _ hti hph ht hdat hge hc
        rw [htst] at hms
        rw [htl] at hm
        simp only [fixTry, hms] at hm
        have hm' : m ∈ ms := by simpa using hm
        refine ⟨fun c h => ?_, fun c ti h => ?_⟩
        · obtain ⟨c0, rfl, -⟩ := mapRegs_call_inv h
          exact absurd hm' (hnc c0)
        · obtain ⟨c0, rfl, -⟩ := mapRegs_tryCall_inv h
          exact absurd hm' (hnt c0 ti)
      | true =>
        obtain ⟨et, het⟩ : ∃ et, IsTryWith B.term et := isTry_with ht
        obtain ⟨T, hT', hdat, hex, -, hreg, hinfo, out, tr, hc⟩ := hy et het
        obtain ⟨ms, c, hms, hnt, hnc, hsite⟩ := hY _ _ _ _ _ _ _ _ _ _ _ _ _ hti hph het
          ⟨B, hBm, rfl⟩ hdat hex hge hreg hc
        rw [hT'] at hm
        simp only [fixTry, tryFix, hms, List.toList_toArray, List.getLast?_concat,
          List.dropLast_concat] at hm
        have hrets := tryInfoOf_rets hinfo
        have hsig := Backend.Proof.Driver.exnTableOpnd_sig hex
        rcases List.mem_append.mp hm with hm | hm
        · refine ⟨fun c' h => ?_, fun c' ti h => ?_⟩
          · obtain ⟨c0, rfl, -⟩ := mapRegs_call_inv h
            exact absurd hm (hnc c0)
          · obtain ⟨c0, rfl, -⟩ := mapRegs_tryCall_inv h
            exact absurd hm (hnt c0 ti)
        · simp only [List.mem_singleton] at hm
          subst hm
          refine ⟨fun c' h => by simp [MInst.mapRegs] at h, fun c' ti h => ?_⟩
          obtain ⟨c0, h0, rfl⟩ := mapRegs_tryCall_inv h
          cases h0
          rcases hsite with ⟨fn, args, et', e, hte, hfn, hsh, hdst⟩ |
            ⟨callee, args, et', s, hte, hsg, hsh, t, hdst⟩
          · have het' : et = et' := by
              rcases het with ⟨_, _, h'⟩ | ⟨_, _, h'⟩ <;> rw [hte] at h' <;> cases h'; rfl
            subst het'
            have hes : e.sig = T.sig := tryCallData_sig (hte ▸ hdat) hex hfn
            refine ⟨args, .inl ⟨e, ⟨fn, hfn, B, hBm, .inr ⟨rfl, et, hte⟩⟩,
              shapeOf_map hg hsh, fun _ => by rw [hrets, hes], ?_⟩⟩
            rcases hdst with hdst | ⟨t, ht', hdst, hgl⟩
            · exact .inl (callMap_sym hdst)
            · exact .inr ⟨t, by rw [callMap_reg hg hdst, hfix t ht'],
                hgr bi B L (ms ++ [MInst.call c]) c t e.name hB hL
                  (.inr ⟨T, fn, args, et, hte, hT', by rw [hms]⟩) ht' hgl (by simp) hdst⟩
          · have het' : et = et' := by
              rcases het with ⟨_, _, h'⟩ | ⟨_, _, h'⟩ <;> rw [hte] at h' <;> cases h'; rfl
            subst het'
            have hs' : s = T.sig := by rw [hsg] at hsig; cases hsig; rfl
            subst hs'
            exact ⟨args, .inr ⟨_, ⟨B, hBm, .inr ⟨rfl, callee, et, hte, hsg⟩⟩,
              shapeOf_map hg hsh, fun _ => hrets, gn t, callMap_reg hg hdst⟩⟩
  · obtain ⟨tl, hie⟩ := edgeBlocks_insts he
    simp only [fixBlock, hie] at hi
    simp at hi
    subst hi
    exact ⟨fun c h => (by cases h), fun c ti h => (by cases h)⟩

end E2E.LinkCheck
