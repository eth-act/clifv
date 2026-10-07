import FV.E2E.LinkOwnCallsStmtHyp
import FV.E2E.LinkOwnCallsTryHyp
import FV.E2E.LinkOwnGotRun

/-!
# `GotLocalHyp`: the GOT vreg of a direct call's run

The code of a run that loads a GOT slot into a vreg `t` and calls through `t` is the code of the
GOT `call` rule (1032, `rule_lower_2518`) or the GOT `try_call` rule (1035, `rule_lower_2551`):
the stores of the stack-passed arguments, `loadExtNameGot t name`, then the call through `t`,
whose defs are vregs below `t` (`gotOk_of_emit`). Every other run of a statement emits no call
(the no-call model) or no GOT load (rules 1031, 1033); every other `try_call` run no GOT load
(rules 1034, 1036). A statement's results are vregs below its GOT vreg (`out = outRegs`).
**`gotLocalHyp : GotLocalHyp`.**
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Isle Isle.Interp
  Isle.Aarch64

set_option maxRecDepth 100000

/-- The GOT facts `GotLocalHyp` asks of a run's code `ms`, for the GOT vreg `t` of `n`. -/
def GotOk (ms : List MInst) (t : Nat) (n : String) : Prop :=
  (∀ m ∈ ms, t ∈ vdefs m → m = .loadExtNameGot (.vreg t .int) n) ∧
  (∀ (k : Nat) (ci : CallInfo), (ms[k]? = some (.call ci) ∨ ∃ ti, ms[k]? = some (.tryCall ci ti)) →
    ci.dest = .reg (.vreg t .int) → ∃ k' < k, ms[k']? = some (.loadExtNameGot (.vreg t .int) n))

theorem idx3 {α : Type} (A : List α) (x y : α) (k : Nat) (m : α) (h : (A ++ [x] ++ [y])[k]? = some m) :
    m ∈ A ∨ (k = A.length ∧ m = x) ∨ (k = A.length + 1 ∧ m = y) := by
  rw [List.append_assoc] at h
  by_cases hk : k < A.length
  · left
    rw [List.getElem?_append_left hk] at h
    exact List.mem_of_getElem? h
  · right
    rw [List.getElem?_append_right (by omega)] at h
    obtain ⟨j, rfl⟩ : ∃ j, k = A.length + j := ⟨k - A.length, by omega⟩
    simp only [Nat.add_sub_cancel_left] at h
    rcases j with _ | _ | j
    · left
      simp at h
      exact ⟨rfl, h.symm⟩
    · right
      simp at h
      exact ⟨rfl, h.symm⟩
    · simp at h

/-- **The code of a GOT call**: only the load defines the GOT vreg `T`, and it precedes the call. -/
theorem gotOk_shape (E : List (Nat × Nat × Nat)) (T : Nat) (nm : String) (L : List (Nat × Reg))
    (b K : Nat) (hK : b + K ≤ T) {t : Nat} {n : String}
    (hl : MInst.loadExtNameGot (.vreg t .int) n ∈ E.map argStore ++
      [MInst.loadExtNameGot (.vreg T .int) nm] ++
      [MInst.call ⟨.reg (.vreg T .int), retPairs L, callDefs (outDefs b K)⟩]) :
    t = T ∧ GotOk (E.map argStore ++ [MInst.loadExtNameGot (.vreg T .int) nm] ++
      [MInst.call ⟨.reg (.vreg T .int), retPairs L, callDefs (outDefs b K)⟩]) t n := by
  have htn : t = T ∧ n = nm := by
    simp [argStore] at hl
    exact hl
  obtain ⟨rfl, rfl⟩ := htn
  refine ⟨rfl, fun m hm hv => ?_, fun k ci hk _ => ?_⟩
  · simp only [List.mem_append, List.mem_map, List.mem_singleton] at hm
    rcases hm with (⟨e, -, rfl⟩ | rfl) | rfl
    · rw [vdefs_argStore] at hv
      cases hv
    · rfl
    · rw [vdefs_call_reg] at hv
      simp only [outDefs, List.map_map, List.mem_map, List.mem_range, Function.comp_def] at hv
      obtain ⟨j, hj, he⟩ := hv
      omega
  · have hload : (E.map argStore ++ [MInst.loadExtNameGot (.vreg t .int) n] ++
        [MInst.call ⟨.reg (.vreg t .int), retPairs L, callDefs (outDefs b K)⟩])[(E.map argStore).length]? =
        some (.loadExtNameGot (.vreg t .int) n) := by
      rw [List.append_assoc, List.getElem?_append_right (Nat.le_refl _)]
      simp
    rcases hk with hk | ⟨ti, hk⟩
    · rcases idx3 _ _ _ _ _ hk with hm | ⟨-, hm⟩ | ⟨rfl, -⟩
      · simp [argStore] at hm
      · cases hm
      · exact ⟨_, by omega, hload⟩
    · rcases idx3 _ _ _ _ _ hk with hm | ⟨-, hm⟩ | ⟨-, hm⟩
      · simp [argStore] at hm
      · cases hm
      · cases hm

theorem gotOk_of_emit {s0 s' : LState} (h0 : s0.emitted = #[]) (E : List (Nat × Nat × Nat)) (T : Nat)
    (nm : String) (L : List (Nat × Reg)) (b K : Nat) (hK : b + K ≤ T)
    (he : s'.emitted = s0.emitted ++ (E.map argStore ++ [MInst.loadExtNameGot (.vreg T .int) nm] ++
      [MInst.call ⟨.reg (.vreg T .int), retPairs L, callDefs (outDefs b K)⟩]).toArray)
    {t : Nat} {n : String} (hl : MInst.loadExtNameGot (.vreg t .int) n ∈ s'.emitted.toList) :
    t = T ∧ GotOk s'.emitted.toList t n := by
  have hms : s'.emitted.toList = E.map argStore ++ [MInst.loadExtNameGot (.vreg T .int) nm] ++
      [MInst.call ⟨.reg (.vreg T .int), retPairs L, callDefs (outDefs b K)⟩] := by
    rw [he, h0]
    simp
  rw [hms] at hl ⊢
  exact gotOk_shape E T nm L b K hK hl

theorem calls_of_emit_bl {s0 s' : LState} (h0 : s0.emitted = #[]) (E : List (Nat × Nat × Nat))
    (c : CallInfo) (he : s'.emitted = s0.emitted ++ (E.map argStore ++ [] ++ [MInst.call c]).toArray) :
    (∀ t n, MInst.loadExtNameGot (.vreg t .int) n ∉ s'.emitted.toList) ∧
      ∀ c', MInst.call c' ∈ s'.emitted.toList → c' = c := by
  rw [he, h0]
  refine ⟨fun t n hm => ?_, fun c' hm => ?_⟩
  · simp [argStore] at hm
  · simp [argStore] at hm
    exact hm

theorem lower_len' : (program.rulesOf 686).length ≤ 1000 := by
  rw [data_program.r686]
  decide

/-! ## A statement's run -/

/-- **A statement's `lower` run** (from empty code) that loads `t` from the GOT and calls
through `t`: `GotOk`, and `t` is none of its results. -/
theorem stmt_got {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) (hd : DataC ctx)
    (ha : AbiSigsOk f) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hmem : ∃ B ∈ f.blocks, ∃ st ∈ B.body, st.inst = inst) {s : LState} {out : Option V}
    {s' : LState} {tr : List RuleId} (h0 : s.emitted = #[])
    (h : runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr)) {t : Nat} {n : String}
    {c : CallInfo} (hl : MInst.loadExtNameGot (.vreg t .int) n ∈ s'.emitted.toList)
    (hcall : MInst.call c ∈ s'.emitted.toList) (hdest : c.dest = .reg (.vreg t .int)) :
    GotOk s'.emitted.toList t n ∧
      ∀ rss, out = some (.regsVec rss) → ∀ cl, [Reg.vreg t cl] ∉ rss := by
  obtain ⟨t', tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower] at ht
  cases ht
  have hlen := lower_len'
  rcases internal_cases (cfg := {}) rfl data_program.t686 term_686_kind rfl happ with
    ⟨-, rfl⟩ | ⟨rl, hrl, m, env, s1, tr1, tr2, hmn, hnm, hmatch, heval⟩
  · rw [h0] at hl
    simp at hl
  · have hm1 : 1000 ≤ m := by omega
    cases hx : callExcl.contains rl.id with
    | false =>
      exfalso
      have hok := List.all_eq_true.mp callRootS_ok rl hrl
      rw [hx, Bool.false_or] at hok
      obtain ⟨hTr, hCr⟩ := callRuleOk_of hok
      obtain ⟨-, r1, he1⟩ := (uSoundAt (cfg := {}) (callModel ctx hd) rfl m).mrule _ _ _ _ _ _ _
        hTr hCr (fun v hv => by simp only [List.mem_singleton] at hv; subst hv; rfl) trivial hmatch
      obtain ⟨-, r2, -⟩ := (uSoundAt (cfg := {}) (callModel ctx hd) rfl 999999).expr _ _ _ _ _ _ _
        (ruleTerms_rhs hTr) (ruleTys_rhs hCr) he1 trivial heval
      obtain ⟨ms, hms, hno⟩ := noCall_trans r1 r2
      rw [hms, h0] at hcall
      have := hno _ (by simpa using hcall)
      simp [isCallB] at this
    | true =>
      simp only [callExcl, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
        beq_iff_eq] at hx
      rcases hx with e | e | e
      · exfalso
        obtain rfl := eq_of_mem_of_id lower_ids_nodup hrl mem_lower_2508 (by rw [e]; rfl)
        obtain ⟨o, rfl⟩ := Option.isSome_iff_exists.mp
          (Cov.totality.1 ctx {} _ _ env (s1, tr1) _ (s', tr2) Cov.total_2508 heval)
        obtain ⟨E, nm, L, D, he', -, -⟩ := run_2508_rel (N := 0) data_program hctx ha hi hc rfl hm1
          (by omega) (Nat.zero_le _) hmatch heval
        have hcc := (calls_of_emit_bl h0 E _ he').2 c hcall
        subst hcc
        cases hdest
      · obtain rfl := eq_of_mem_of_id lower_ids_nodup hrl mem_lower_2518 (by rw [e]; rfl)
        obtain ⟨o, rfl⟩ := Option.isSome_iff_exists.mp
          (Cov.totality.1 ctx {} _ _ env (s1, tr1) _ (s', tr2) Cov.total_2518 heval)
        obtain ⟨E, nm, L, k, he', -, -, hout⟩ := run_2518_rel (N := 0) data_program hctx ha hi hc
          rfl hm1 (by omega) (Nat.zero_le _) hmatch heval
        obtain ⟨htT, hok⟩ := gotOk_of_emit h0 E _ nm L s.nextVreg k (Nat.le_refl _) he' hl
        refine ⟨hok, fun rss hrss cl hmem' => ?_⟩
        simp only [Option.some.injEq] at hrss
        rw [hout] at hrss
        cases hrss
        simp only [outRegs, List.mem_map, List.mem_range, List.cons.injEq, and_true] at hmem'
        obtain ⟨j, hj, hjt⟩ := hmem'
        cases hjt
        omega
      · exfalso
        obtain rfl := eq_of_mem_of_id lower_ids_nodup hrl mem_lower_2529 (by rw [e]; rfl)
        obtain ⟨o, rfl⟩ := Option.isSome_iff_exists.mp
          (Cov.totality.1 ctx {} _ _ env (s1, tr1) _ (s', tr2) Cov.total_2529 heval)
        have hsigs : ∀ sig callee args s, inst = .callIndirect sig callee args →
            f.sigDecls.lookup sig = some s → sigAbiOk s = true := fun sig callee args s he hs =>
          (ha.2 s (Cov.mem_indSigs (he ▸ hmem) hs)).2
        obtain ⟨E, x, L, D, he', -, -⟩ := run_2529_rel (N := 0) data_program indData_program hctx
          hi hc hsigs rfl hm1 (by omega) hmatch heval
        exact (calls_of_emit_bl h0 E _ he').1 t n hl

/-! ## A `try_call`'s run -/

/-- **A `try_call`'s `lower_branch` run** that loads `tv` from the GOT and calls through `tv`:
`GotOk`. -/
theorem try_got {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) (ha : AbiSigsOk f) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) {t : Clif.Terminator}
    {et : Clif.ExnTable} {data : V} {sig : Clif.Signature} {items : List (Option Nat)}
    {lo st1 : LState} {trs : List Reg × List Reg} {targets : List Label} {out : V} {s' : LState}
    {tr : List RuleId} (het : IsTryWith t et) (hd : tryCallData f t = .ok data)
    (he : exnTableOpnd f et = .ok (sig, items)) (htr : tryRegsOf sig lo = some (trs, st1))
    (h : tryCallF ctx ti data trs targets { st1 with emitted := #[] } = .ok (some out, s', tr))
    {tv : Nat} {n : String} (hl : MInst.loadExtNameGot (.vreg tv .int) n ∈ s'.emitted.toList) :
    GotOk s'.emitted.toList tv n := by
  have hctx' : CtxInv f (tryCtx ctx ti data trs) := { ctxInv_termCtx hctx hph data with }
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have htr' : tryRegsOf sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := htr
  have hnd : ((program.rulesOf TId.lower_branch).map Rule.id).Nodup := by
    rw [show TId.lower_branch = 687 from rfl, data_program.r687]
    decide +kernel
  have hlen := lower_branch_len
  unfold tryCallF at h
  obtain ⟨t', tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower_branch] at ht
  cases ht
  rcases internal_cases (cfg := {}) rfl data_program.t687 term_687_kind rfl happ with
    ⟨hr, -⟩ | ⟨rl, hrl, m, env, s1, tr1, tr2, hmn, hnm, hmatch, heval⟩
  · cases hr
  · have hm1 : 1000 ≤ m := by omega
    have h0 : ({ st1 with emitted := #[] } : LState).emitted = #[] := rfl
    rcases het with ⟨fn, args, rfl⟩ | ⟨callee, args, rfl⟩
    · cases hroot : tryRootRule rl with
      | false =>
        exact absurd hmatch (tryUnmatchable rl hrl hroot f _ hctx' ti fn args et data targets hd hi
          {} m _ env _)
      | true =>
        simp only [tryRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
        rcases hroot with e | e
        · rw [eq_of_mem_of_rid hnd hrl mem_lower_branch_2542 (by rw [e]; rfl)] at hmatch heval
          obtain ⟨E, cl, he', -, -⟩ := try_bl_rel (N := 0) data_program tryData_program hctx' ha hd
            he hi htr' rfl hm1 (by omega) hmatch heval
          exact absurd hl ((calls_of_emit_bl h0 E _ he').1 tv n)
        · rw [eq_of_mem_of_rid hnd hrl mem_lower_branch_2551 (by rw [e]; rfl)] at hmatch heval
          obtain ⟨E, nm, L, K, he', -, hK⟩ := try_got_rel (N := 0)
            (st := { st1 with emitted := #[] }) data_program tryData_program hctx' ha hd he hi htr'
            rfl hm1 (by omega) (Nat.zero_le _) (Nat.le_refl _) hmatch heval
          exact (gotOk_of_emit h0 E _ nm L _ K hK he' hl).2
    · cases hroot : tryIndRootRule rl with
      | false =>
        exact absurd hmatch (tryIndUnmatchable rl hrl hroot f _ hctx' ti callee args et data
          targets hd hi {} m _ env _)
      | true =>
        simp only [tryIndRootRule, beq_iff_eq] at hroot
        rw [eq_of_mem_of_rid hnd hrl mem_lower_branch_2561 (by rw [hroot]; rfl)] at hmatch heval
        obtain ⟨E, cl, he', -⟩ := try_ind_rel (N := 0) data_program tryData_program
          indData_program tryIndData_program hctx' hd he hi htr' rfl hm1 (by omega) hmatch heval
        exact absurd hl ((calls_of_emit_bl h0 E _ he').1 tv n)

/-! ## `GotLocalHyp` -/

/-- **`GotLocalHyp`.** -/
theorem gotLocalHyp : GotLocalHyp := by
  intro p f vc hsub hd hs hl ctx ranges st0 bl hb hlb bi B L ms c t n hB hL hcase _ hload hcall
    hdest
  have ha := abiSigsOk_of_inSubset hsub
  have hctx : CtxInv f ctx := ctxOk_sound (ctxOk_complete hs hb)
  have hdc := dataC_of_build hb
  have hcf := ctxFacts_of hb
  obtain ⟨-, hstart⟩ := lowBlocks_start hlb
  obtain ⟨-, hspec⟩ := lowBlocks_spec hlb
  have hemp := lowBlocks_emptied hlb
  obtain ⟨hlenB, hc, -, nl0, nl', hterm⟩ := hspec bi B L hB hL
  have hBm : B ∈ f.blocks := List.mem_of_getElem? hB
  have hstmt : ∀ (j : Nat) (sl : SLow), L.sl[j]? = some sl → sl.st'.emitted.toList = ms →
      GotOk ms t n ∧ ∀ cl, [Reg.vreg t cl] ∉ sl.rss := by
    intro j sl hsl hms
    have hj : j < B.body.length := by
      have := (List.getElem?_eq_some_iff.mp hsl).1
      omega
    have hstm : B.body[j]? = some B.body[j] := List.getElem?_eq_getElem hj
    obtain ⟨info, hinf, hic, -⟩ := hcf.stmt bi B j _ hB hstm
    obtain ⟨tr, hrun⟩ := hc j sl hsl
    rw [hstart bi L hL] at hrun
    have h0 := hemp L (List.mem_of_getElem? hL) sl (List.mem_of_getElem? hsl)
    obtain ⟨hg, hr⟩ := stmt_got hctx hdc ha hinf hic
      ⟨B, hBm, B.body[j], List.mem_of_getElem? hstm, rfl⟩ h0 hrun (hms ▸ hload) (hms ▸ hcall) hdest
    exact ⟨hms ▸ hg, hr _ rfl⟩
  rcases hcase with ⟨j, stm, sl, fn, args, hstm, hsl, -, hms⟩ | ⟨T, fn, args, et, hT, hTl, hms⟩
  · obtain ⟨⟨g1, g2⟩, -⟩ := hstmt j sl hsl hms
    exact ⟨g1, g2, fun j' sl' hsl' hms' => (hstmt j' sl' hsl' hms').2⟩
  · obtain ⟨-, hy⟩ := lowTerm_spec hterm
    have het : IsTryWith B.term et := .inl ⟨fn, args, hT⟩
    obtain ⟨T', hT', hdat, hex, -, hreg, -, out, tr, htc⟩ := hy et het
    have hph := hcf.term bi B hB
    rw [← hstart bi L hL] at hph
    have hg := try_got hctx ha hph het hdat hex hreg htc (hms ▸ hload)
    rw [hms] at hg
    exact ⟨hg.1, hg.2, fun j' sl' hsl' hms' => (hstmt j' sl' hsl' hms').2⟩

end E2E.LinkCheck
