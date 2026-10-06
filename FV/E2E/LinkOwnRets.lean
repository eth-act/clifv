import FV.Backend.Proof.IselTermFacts
import FV.E2E.SpillCtlCheck
import FV.E2E.LinkCheck

/-!
# Own-output facts of `okB`: `sretRets` and `entryRegs`

Two checks of `okB` (`LinkCheck.chks`) are facts about the compiler's own output, proven here
once for every in-scope function:

* `retsB_of_lower`: every `Rets` of `lowerFunction g` carries at least `(sigRets g.sig).length`
  pairs when `g` has an `sret` parameter (check "sretRets"). A `return xs` is lowered as
  `return (xs ++ sretRet g)` (`abiTerm`); rule `rule_lower_2574` (`lower_return`, `gen_return`)
  emits one `Rets` pair per value (`ret_retShape`); `lowerFunction` rejects an `sret` signature
  with returns (`sret_returns_nil`), so `sigRets g.sig` is the single struct pointer, and it
  rejects a `return` without the struct pointer to append (`LoopFacts.sret`), so every such
  `Rets` has at least one pair. The other `Rets`-free code: the entry block's `Args`/loads, the
  `extraOf` moves, edge-block jumps, the `tryCall` of `tryFix`, `trap`'s `udf`
  (`trap_retShape`), and the ISLE runs of statements and branches (`IselNoRetsHyp`).
* `entryB_of_lower`: the entry `Args` of `prepare (lowerFunction g)` reads only registers of
  `regLocs g.sig` (check "entryRegs"): it is `lowerFunction`'s entry `Args`
  (`prep_entry_args`), the pairs `entryRegs` of the register locations of `locsOf g.sig`.

`IselNoRetsHyp` is the one ISLE fact taken as a hypothesis: `lower` on a statement and
`lower_branch` emit no `Rets`. Only the extern constructor `gen_return` emits a `Rets`
(`externCtor_shp`: `MInst.ofV` decodes no `Rets`), `gen_return` is applied only by rule
`rule_prelude_lower_1493` (term `lower_return`), and `lower_return` only by `rule_lower_2574`,
which matches only a `return`'s data; neither term is reachable from the rules of
`lower_branch` nor from the other rules of `lower` (a syntactic closure over `program`'s rules).
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver

/-! ## The ISLE runs and `Rets` -/

/-- The instructions emitted from `s` to `s'` contain no `Rets`. -/
def NoRetsSince (s s' : LState) : Prop :=
  ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧ ∀ m ∈ ms, ∀ us, m ≠ .rets us

/-- **The ISLE inversion for `Rets`**: `lower` on a statement of a function (in `buildCtx`'s
context) and `lower_branch` (in any context: a branch's or a `try_call`'s) emit no `Rets`.
Only `gen_return` emits a `Rets`; it is reachable only through `lower_return` from
`rule_lower_2574`, the `lower` rule of a `return` (whose data no statement has). -/
def IselNoRetsHyp : Prop :=
  (∀ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (st0 : LState),
    buildCtx f = .ok (ctx, ranges, st0) →
    ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst) (s : LState) (out : Option V) (s' : LState)
      (tr : List Isle.RuleId), ctx.insts[ii]? = some info → info.clif = some inst →
      runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr) → NoRetsSince s s') ∧
  (∀ (ctx : Ctx) (ti : Nat) (targets : List Label) (s : LState) (out : Option V) (s' : LState)
    (tr : List Isle.RuleId),
    runTerm ctx "lower_branch" [.inst ti, .labels targets] s = .ok (out, s', tr) →
      NoRetsSince s s')

/-- The instructions emitted from `st` to `st'`: a `Rets` among them only for a `return` `t`,
with one pair per returned value. -/
def RetShape (t : Clif.Terminator) (st st' : LState) : Prop :=
  ∃ ms : List MInst, st'.emitted = st.emitted ++ ms.toArray ∧
    ∀ m ∈ ms, ∀ us, m = .rets us → ∃ xs, t = .ret xs ∧ us.length = xs.length

section Rules

open Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-- `LowerTermShapeOk` with the `Rets` conclusion. -/
def LowerRetShapeOk (p : Program) (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxInv f ctx →
  ∀ (ti : Nat) (t : Clif.Terminator) (data : V), retOrTrap t = true → termData t = .ok data →
  ctx.insts[ti]? = some ⟨data, [], [], none⟩ →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n →
    (∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ti]).run (st, tr) = .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ti]).run (st, tr) = .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    RetShape t st st'

/-- **`trap`** (`rule_lower_2237`): `udf`. -/
theorem trap_retShape {p : Program} (hp : Data p) : LowerRetShapeOk p rule_lower_2237 := by
  intro f ctx hctx ti t data hrt hd hi cfg hc m n st tr env' s1 out st' tr' hm hn _ hmatch heval
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
    rw [ofV_udf] at hmi
    cases hmi
    simp only at hs1 hs2
    subst hs2
    rw [hs1]
    refine ⟨[.udf c], by simp [LState.emit], fun m hm us hus => ?_⟩
    simp only [List.mem_singleton] at hm
    subst hm; cases hus
  | _ => simp [retOrTrap] at hrt

set_option maxHeartbeats 800000 in
/-- **`return`** (`rule_lower_2574`): one `Rets` with one pair per returned value. -/
theorem ret_retShape {p : Program} (hp : Data p) : LowerRetShapeOk p rule_lower_2574 := by
  intro f ctx hctx ti t data hrt hd hi cfg hc m n st tr env' s1 out st' tr' hm hn _ hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kR := fun n (hn : 60 ≤ n) xs s v s' h => lower_return_ok hp (ctx := ctx) hc (n := n)
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
    obtain ⟨rs, ps, hrs, hps, hs, -⟩ := kR _ (by omega) _ _ _ _ h294
    simp only at hs
    subst hs
    have hrs' := mapM_valueReg hctx hrs
    subst hrs'
    obtain ⟨-, rfl⟩ := retRegs_eq hps
    refine ⟨[.rets _], by simp [LState.emit], fun m hm us hus => ?_⟩
    simp only [List.mem_singleton] at hm
    subst hm; cases hus
    exact ⟨_, rfl, by simp⟩
  | _ => simp [retOrTrap] at hrt

/-- **`lower` on a `return`/`trap`**: its `Rets` carry one pair per returned value. -/
theorem retShape_runTerm {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ti : Nat}
    {t : Clif.Terminator} {data : V} (hrt : retOrTrap t = true) (hd : termData t = .ok data)
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) {st : LState} {out : V} {st' : LState}
    {tr : List RuleId} (h : runTerm ctx "lower" [.inst ti] st = .ok (some out, st', tr)) :
    RetShape t st st' := by
  obtain ⟨r, hr, m, n, env', s1, tr2, hm, hn, hfirst, hmatch, heval⟩ := runTerm_lower_rule h
  cases hroot : termRootRule r
  · exact absurd hmatch (termUnmatchable r hr hroot f ctx hctx ti t data hrt hd hi {} m (st, #[])
      env' s1)
  · simp only [termRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
    rcases hroot with e | e
    · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2237 (by rw [e]; rfl)] at hfirst hmatch heval
      exact trap_retShape data_program f ctx hctx ti t data hrt hd hi {} rfl m n st #[] env' s1 out
        st' tr2 hm hn hfirst hmatch heval
    · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2574 (by rw [e]; rfl)] at hfirst hmatch heval
      exact ret_retShape data_program f ctx hctx ti t data hrt hd hi {} rfl m n st #[] env' s1 out
        st' tr2 hm hn hfirst hmatch heval

end Rules

/-! ## The `Rets` of `lowerFunction` -/

/-- A renamed `Rets` is a `Rets` of as many pairs. -/
theorem mapRegs_rets {R : Reg → Reg} {m : MInst} {us : List (Reg × Reg)}
    (h : m.mapRegs R = .rets us) : ∃ us0, m = .rets us0 ∧ us0.length = us.length := by
  cases m <;> simp only [MInst.mapRegs, reduceCtorEq] at h
  case rets us0 =>
    cases h
    exact ⟨us0, rfl, by simp⟩

/-- **The `Rets` of `lowerFunction`'s output** are the lowered `return`s of `f`'s blocks, one pair
per value of `return (xs ++ sretRet f)`. -/
theorem vc_rets (hI : IselNoRetsHyp) {f : Clif.Function} {vc : VCode} (hs : LowerScope f)
    (hl : lowerFunction f = .ok vc) {b : Nat} {vb : VBlock} {k : Nat} {us : List (Reg × Reg)}
    (hb : vc.blocks[b]? = some vb) (hk : vb.insts[k]? = some (.rets us)) :
    ∃ B ∈ f.blocks, ∃ xs, B.term = .ret xs ∧ us.length = (xs ++ sretRet f).length := by
  obtain ⟨ctx, ranges, st0, bl, hbc, hlb, hvb, -, -⟩ := lowerFunction_run hl
  have hctx : CtxInv f ctx := ctxOk_sound (ctxOk_complete hs hbc)
  have hcf := ctxFacts_of hbc
  obtain ⟨-, hstart⟩ := lowBlocks_start hlb
  obtain ⟨-, hspec⟩ := lowBlocks_spec hlb
  have hemp := lowBlocks_emptied hlb
  obtain ⟨hS, hY⟩ := hI
  have hS := hS f ctx ranges st0 hbc
  rw [hvb] at hb
  rcases vcBlocksOf_get hb with ⟨B, L, hB, hL, rfl⟩ | ⟨-, B, L, e, he, rfl⟩
  · have hl' := hk
    rw [fixBlock, ← Array.getElem?_toList, rawBlock_insts] at hl'
    have hm := List.mem_of_getElem? hl'
    simp only [List.mem_append, List.mem_flatten, List.mem_map, List.mem_range] at hm
    rcases hm with (hpre | ⟨sg, ⟨j, -, rfl⟩, hm⟩) | htseg
    · -- the entry block's `Args` and parameter loads
      exfalso
      unfold pre at hpre
      split at hpre
      · simp only [List.mem_cons] at hpre
        rcases hpre with h | h
        · cases h
        · simp only [entryLoads, List.mem_filterMap] at h
          obtain ⟨q, -, hq⟩ := h
          unfold entryLoadOf at hq
          split at hq <;> cases hq
      · simp at hpre
    · -- a statement's segment
      exfalso
      unfold seg at hm
      rw [hB, hL] at hm
      simp only at hm
      split at hm
      · rename_i stm sl hstm hsl
        simp only [List.mem_map, List.mem_append] at hm
        obtain ⟨m, hm, hmr⟩ := hm
        obtain ⟨us0, rfl, -⟩ := mapRegs_rets hmr
        rcases hm with hm | hm
        · obtain ⟨-, hc, -, -⟩ := hspec b B L hB hL
          obtain ⟨info, hinf, hic, -⟩ := hcf.stmt b B j stm hB hstm
          obtain ⟨tr, hrun⟩ := hc j sl hsl
          rw [hstart b L hL] at hrun
          obtain ⟨ms, hms, hno⟩ := hS _ info stm.inst _ _ _ _ hinf hic hrun
          rw [hemp L (List.mem_of_getElem? hL) sl (List.mem_of_getElem? hsl)] at hms
          rw [hms] at hm
          exact hno _ (by simpa using hm) us0 rfl
        · obtain ⟨s, a, c, h⟩ := mem_extraOf hm
          cases h
      · simp at hm
    · -- the terminator's segment
      unfold tseg at htseg
      rw [hL] at htseg
      simp only [List.mem_map] at htseg
      obtain ⟨m, hm, hmr⟩ := htseg
      obtain ⟨us0, rfl, hlen⟩ := mapRegs_rets hmr
      obtain ⟨-, -, htst, nl0, nl', hterm⟩ := hspec b B L hB hL
      obtain ⟨hn, hy⟩ := lowTerm_spec hterm
      have hph := hcf.term b B hB
      rw [← hstart b L hL] at hph
      cases ht : B.term.isTry with
      | false =>
        obtain ⟨htl, hdat, out, tr, hc⟩ := hn ht
        rw [htl] at hm
        simp only [fixTry] at hm
        obtain ⟨hctx', hi'⟩ := termCtx_facts hctx hph L.data
        unfold termCallF at hc
        have hno : ∀ ms : List MInst, L.tst'.emitted = L.tst.emitted ++ ms.toArray →
            (∀ m ∈ ms, ∀ us, m ≠ .rets us) → False := by
          intro ms hms hno
          rw [hms, htst] at hm
          exact hno _ (by simpa using hm) us0 rfl
        have hbr : runTerm (termCtx ctx (L.start + B.body.length) L.data) "lower_branch"
            [.inst (L.start + B.body.length), .labels L.targets] L.tst = .ok (some out, L.tst', tr) →
            False := fun h => by
          obtain ⟨ms, hms, hn'⟩ := hY _ _ _ _ _ _ _ h
          exact hno ms hms hn'
        revert hc hdat
        cases hT : B.term with
        | ret xs =>
          intro hdat hc
          obtain ⟨ms, hms, hr⟩ := retShape_runTerm (t := abiTerm f (.ret xs)) hctx' rfl hdat hi' hc
          rw [hms, htst] at hm
          obtain ⟨xs', hx, hl2⟩ := hr _ (by simpa using hm) us0 rfl
          simp only [abiTerm, Clif.Terminator.ret.injEq] at hx
          subst hx
          exact ⟨B, List.mem_of_getElem? hB, xs, rfl, by omega⟩
        | trap c =>
          intro hdat hc
          obtain ⟨ms, hms, hr⟩ := retShape_runTerm (t := abiTerm f (.trap c)) hctx' rfl hdat hi' hc
          rw [hms, htst] at hm
          obtain ⟨xs', hx, -⟩ := hr _ (by simpa using hm) us0 rfl
          cases hx
        | jump d => intro _ hc; exact (hbr hc).elim
        | brif c a b' => intro _ hc; exact (hbr hc).elim
        | brTable x d tbl => intro _ hc; exact (hbr hc).elim
        | returnCall fn args =>
          intro hdat _
          simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hdat
        | tryCall fn args et => rw [hT] at ht; simp [Clif.Terminator.isTry] at ht
        | tryCallIndirect callee args et => rw [hT] at ht; simp [Clif.Terminator.isTry] at ht
      | true =>
        exfalso
        obtain ⟨et, het⟩ : ∃ et, IsTryWith B.term et := isTry_with ht
        obtain ⟨T, hT', -, -, -, -, -, out, tr, hc⟩ := hy et het
        obtain ⟨ms, hms, hno⟩ := hY _ _ _ _ _ _ _ hc
        rw [hT'] at hm
        simp only [fixTry, tryFix, hms, Array.empty_append, List.toList_toArray] at hm
        split at hm
        · rcases List.mem_append.mp hm with hm | hm
          · exact hno _ (List.dropLast_subset _ hm) us0 rfl
          · simp at hm
        · exact hno _ hm us0 rfl
  · -- an edge block: a single `jump`
    exfalso
    obtain ⟨tl, hie⟩ := edgeBlocks_insts he
    have hm := Array.mem_of_getElem? hk
    simp only [fixBlock, hie] at hm
    simp [MInst.mapRegs] at hm

/-- `lowerFunction` rejects an `sret` signature with return values. -/
theorem sret_returns_nil {f : Clif.Function} {vc : VCode} (hl : lowerFunction f = .ok vc)
    (hs : f.sig.params.any (·.purpose == .sret) = true) : f.sig.returns = [] := by
  rw [lowerFunction_eq] at hl
  unfold lowerFunction' at hl
  cases hr : f.sig.returns with
  | nil => rfl
  | cons r rs =>
    exfalso
    split at hl
    · cases hl
    · cases hb : sigParamBytes f.sig with
      | error e => simp [hb, bind, Except.bind] at hl
      | ok pb =>
        simp only [hb, hs, hr, bind, Except.bind] at hl
        split at hl
        · cases hl
        · simp at *

/-- An `sret` signature without returns returns the struct pointer only. -/
theorem sigRets_length_sret {s : Clif.Signature} (hs : s.params.any (·.purpose == .sret) = true)
    (hr : s.returns = []) : (sigRets s).length = 1 := by
  obtain ⟨p, hp⟩ : ∃ p, s.params.find? (·.purpose == .sret) = some p := by
    cases h : s.params.find? (·.purpose == .sret) with
    | some p => exact ⟨p, rfl⟩
    | none =>
      rw [List.find?_eq_none] at h
      obtain ⟨x, hx, hx'⟩ := List.any_eq_true.mp hs
      exact absurd hx' (h x hx)
  simp [sigRets, hp, hr]

/-- **Check "sretRets" on `lowerFunction`'s output**: every `Rets` of an `sret` function carries
its ABI results. -/
theorem retsB_of_lower (hI : IselNoRetsHyp) {g : Clif.Function} {vc : VCode}
    (hs : lowerScopeB g = true) (hl : lowerFunction g = .ok vc) : allInsts vc (retsB g) = true := by
  have hS := lowerScope_of hs
  obtain ⟨-, -, -, -, -, -, hlf⟩ := lowerFunction_run hl
  unfold allInsts
  rw [Array.all_eq_true_iff_forall_mem]
  intro vb hvb
  rw [Array.all_eq_true_iff_forall_mem]
  intro i hi
  obtain ⟨b, hb⟩ := Array.mem_iff_getElem?.mp hvb
  obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.mp hi
  cases i with
  | rets us =>
    simp only [retsB, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
    cases hsr : g.sig.params.any (·.purpose == .sret) with
    | false => exact .inl rfl
    | true =>
      right
      obtain ⟨B, hB, xs, hT, hlen⟩ := vc_rets hI hS hl hb hk
      have hr := sret_returns_nil hl hsr
      have h1 := sigRets_length_sret hsr hr
      have hne : sretRet g ≠ [] := fun h0 => by
        have := hlf.sret B hB xs hT h0
        rw [hr] at this
        rw [this] at h1
        cases h1
      have : 1 ≤ (sretRet g).length := List.length_pos_iff.mpr hne
      simp only [List.length_append] at hlen
      omega
  | _ => rfl

/-! ## The entry `Args` -/

/-- The `Args` pairs of the entry block are in `regLocs`. -/
theorem entryRegs_regLocs (f : Clif.Function) (R : Reg → Reg) (B : Clif.Block) :
    ∀ q ∈ entryRegs f R B, q.2 ∈ regLocs f.sig := by
  intro q hq
  unfold entryRegs at hq
  obtain ⟨a, ha, hq⟩ := List.mem_filterMap.mp hq
  have hloc : a.1.2 ∈ locsOf f.sig := by
    unfold entryParams at ha
    exact (List.of_mem_zip (List.of_mem_zip ha).1).2
  unfold entryRegOf at hq
  split at hq
  · rename_i p hp
    cases hq
    exact List.mem_filterMap.mpr ⟨_, hloc, by rw [hp]⟩
  · cases hq

/-- `lowerFunction`'s block 0 starts with the `Args` of `entryRegs`. -/
theorem vc_entry {f : Clif.Function} {vc : VCode} (hs : LowerScope f)
    (hl : lowerFunction f = .ok vc) :
    ∃ vb0 ds, vc.blocks[0]? = some vb0 ∧ vb0.insts[0]? = some (.args ds) ∧
      ∀ q ∈ ds, q.2 ∈ regLocs f.sig := by
  have hne := (prepDomain_of_lower hs hl hs.nonempty).nonempty
  obtain ⟨ctx, ranges, st0, bl, hb, hlb, hvb, -, -⟩ := lowerFunction_run hl
  obtain ⟨vb0, hvb0⟩ : ∃ vb0, vc.blocks[0]? = some vb0 := ⟨_, Array.getElem?_eq_getElem hne⟩
  have hvb0' := hvb0
  rw [hvb] at hvb0'
  rcases vcBlocksOf_get hvb0' with ⟨B, L, hB, hL, rfl⟩ | ⟨h0, -⟩
  · refine ⟨_, _, hvb0, ?_, entryRegs_regLocs f _ B⟩
    rw [fixBlock, ← Array.getElem?_toList, rawBlock_insts]
    simp only [pre, hB]
    rfl
  · exact absurd h0 (Nat.lt_irrefl 0)

/-- `prepare` keeps block 0's leading `Args` (`prep_entry`, with the pairs named). -/
theorem prep_entry_args {vc vcp : VCode} (hp : prepare vc = .ok vcp) (hd : Prep.PrepDomain vc)
    {vb0 : VBlock} {ds : List (Reg × Reg)} (hvb0 : vc.blocks[0]? = some vb0)
    (hi0 : vb0.insts[0]? = some (.args ds)) :
    ∃ vb, vcp.blocks[0]? = some vb ∧ vb.insts[0]? = some (.args ds) := by
  obtain ⟨ss0, ps0, ss1, ps1, ss2, ps2, next, B, E, hc0, hc1, hS, hc2, rfl⟩ := Prep.prepare_facts hp
  have cs0 := Prep.cfg_spec hc0
  have cs2 : Prep.CfgSpec (B ++ E) ss2 := Prep.cfg_spec hc2
  obtain ⟨h10, hk0, -, -, -, hR, -, hR0, -, -⟩ := Prep.facts_basic hd cs0 cs2 hS
  obtain ⟨t, -, hback, hterm, -⟩ := cs0.blk 0 vb0 hvb0
  have hsz : 1 < vb0.insts.size := by
    have h0' : 0 < vb0.insts.size := (Array.getElem?_eq_some_iff.mp hi0).1
    refine Nat.lt_of_not_le fun hc => ?_
    have h1 : vb0.insts.size = 1 := by omega
    rw [Array.back?_eq_getElem?, h1] at hback
    rw [hback] at hi0
    cases hi0
    cases hterm
  have h0 : 0 < (rpo ss2).size := (Array.getElem?_eq_some_iff.mp hR0).1
  have e0 : (rpo ss2)[0] = 0 := (Array.getElem?_eq_some_iff.mp hR0).2
  obtain ⟨hj, e⟩ := Prep.v3_get hR h0
  have hB0 : 0 < B.size := by rw [hS.size]; exact h10
  have hV0 : (Prep.keep vc.blocks (reachable ss0))[0] = vb0 := by
    have := hk0
    rw [Array.getElem?_eq_getElem h10, hvb0] at this
    exact Option.some.inj this
  refine ⟨B[0], ?_, ?_⟩
  · rw [e]; simp only [e0, Array.getElem_append_left hB0]
  rcases hS.rw 0 h10 hB0 with h | ⟨t, t', ls, -, -, -, h4, -⟩
  · rw [h, hV0]; exact hi0
  · rw [h4, hV0]
    simp only [Array.getElem?_push, Array.size_pop, Array.getElem?_pop]
    split
    · omega
    · split
      · exact hi0
      · omega

/-- **Check "entryRegs" on the pipeline's output**: the entry `Args` of the prepared VCode reads
only registers of `regLocs g.sig`. -/
theorem entryB_of_lower {g : Clif.Function} {vc vcp : VCode} (hs : lowerScopeB g = true)
    (hl : lowerFunction g = .ok vc) (hp : Backend.prepare vc = .ok vcp) : entryB g vcp = true := by
  have hS := lowerScope_of hs
  obtain ⟨vb0, ds, hvb0, hi0, hds⟩ := vc_entry hS hl
  obtain ⟨vb, hvb, hi⟩ := prep_entry_args hp (prepDomain_of_lower hS hl hS.nonempty) hvb0 hi0
  simp only [entryB, hvb, hi, List.all_eq_true, decide_eq_true_eq]
  exact hds

end E2E.LinkCheck
