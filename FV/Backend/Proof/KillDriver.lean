import FV.Backend.Proof.KillOracle
import FV.Backend.Proof.KillCtor
import FV.Backend.Proof.TryRegs
import FV.Backend.Proof.LowerLoop
import FV.Backend.Proof.DriverCheckSound
import FV.Backend.Proof.IselShpTotal
import FV.Backend.Proof.IselCovModel

/-!
# Killed vregs of the ISLE lowering (V4, `SpillKillFree`): the driver's runs, `KillRunsHyp`

The uniform invariant (`Isle.Interp.UModel`, `KillGen.lean`) instantiated with the killed-vreg
invariant (`KP`/`IsK`/`RsK`, `KillBase.lean`): `kModel` on a term set `T` (no `invalid_reg`, and
`gen_call_rets` only outside a `try_call`'s context) with black-box oracles `O` (`OracleK`,
`KillOracle.lean`). Three instances: `sModel` (`killTabS`, a statement's or a `return`/`trap`'s
`lower`), `bModel` (`killTabB`, `lower_branch`), and `iModel` (the terms of both sets but
`br_table_impl`, with the LL/SC loops as oracles) for `imm`, the sub-run `br_table_impl`'s
oracle obligation asks for.

The driver's calls: a statement's `lower` (`stmt_kill`: `nop`'s rule 587 checked by hand, it
matches only an instruction without results; 636/637 never match), a terminator's run
(`term_kill`), a `try_call`'s `lower_branch` (`try_kill`, whose context has the nonempty
`try_call` vregs). **`killRunsHyp : KillRunsHyp`.**
-/

namespace Backend.Proof.Kill

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Spill Backend.Proof.Driver Isle Isle.Interp
  Isle.Aarch64

/-! ## Rule and run facts -/

set_option maxRecDepth 100000 in
theorem lower_587_noIflets : (program.rulesOf TId.lower).all (fun r =>
    r.id != 587 || r.iflets.isEmpty) = true := by
  rw [show TId.lower = 686 from rfl, data_program.r686]
  decide +kernel

set_option maxRecDepth 100000 in
theorem nop_match_results {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {rl : Rule} (hrl : rl ∈ program.rulesOf TId.lower) (h587 : rl.id = 587) {m : Nat}
    {s0 s1 : LState × Array RuleId} {env : Isle.Interp.Env V}
    (hm : (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 = .ok (some env, s1)) :
    info.results = [] := by
  have hop := List.all_eq_true.mp lower_ops rl hrl
  simp only [h587, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hop
  have hn := pinned_names hctx hi hc hop.1 kind_nullAry kind_nop hm
  rw [variantNames_Nop] at hn
  have hnop := instNames_nop (Option.some.inj hn).symm
  subst hnop
  obtain ⟨tys, hty, -, hlen⟩ := hctx.resTys ii info .nop hi hc
  simp [Clif.Inst.resultTypes] at hty
  subst hty
  exact List.eq_nil_of_length_eq_zero hlen

theorem isK_start {ctx : Ctx} {lo : Nat} {s : LState} (h1 : ctx.valDef.size ≤ lo)
    (h2 : lo ≤ s.nextVreg) : IsK ctx lo s s :=
  ⟨⟨[], by simp⟩, h1, h2, fun m hm => by simp [emittedSince, ← Array.length_toList] at hm⟩

theorem runKill_of {ctx : Ctx} {lo : Nat} {s0 s : LState} (h : IsK ctx lo s0 s) :
    RunKill ctx.valDef.size lo s0 s := by
  obtain ⟨⟨ms, hms⟩, -, -, hm⟩ := h
  rw [emittedSince_eq hms] at hm
  refine ⟨ms, hms, fun m hm' => (hm m hm').1, fun k hk => ?_, fun m hm' u hu => (hm m hm').2.2.1 u hu⟩
  obtain ⟨m, hm', hk⟩ := List.mem_flatMap.mp hk
  exact (hm m hm').2.1 k hk

theorem outKill_of {ctx : Ctx} {lo : Nat} {s0 s : LState} {out : Option V}
    (h : ∀ v, out = some v → KP ctx lo s0 s v) : OutKill ctx.valDef.size lo s0 s out := by
  intro rss hout rs hrs n c hn
  exact (h _ hout).2.1 n c (by simp only [V.regsK, List.mem_flatten]; exact ⟨rs, hrs, hn⟩)

theorem tryDefs_of {ctx : Ctx} {lo : Nat} {s0 s : LState} (h : IsK ctx lo s0 s)
    (he : s0.emitted = #[]) (hne : ctx.tryRegs ≠ ([], [])) :
    ∀ m ∈ s.emitted.toList, ∀ c, m = .call c → ∀ q ∈ c.defs, ∀ n cl, q.2 = .vreg n cl →
      q.2 ∈ ctx.tryRegs.1 ∨ q.2 ∈ ctx.tryRegs.2 := by
  intro m hm
  have : m ∈ emittedSince s0 s := by simp [emittedSince, he, hm]
  exact (h.2.2.2 m this).2.2.2 hne

theorem trs_ne {f : Clif.Function} {et : Clif.ExnTable} {sig : Clif.Signature}
    {items : List (Option Nat)} (he : exnTableOpnd f et = .ok (sig, items)) {lo st1 : LState}
    {trs : List Reg × List Reg} (htr : tryRegsOf sig lo = some (trs, st1)) : trs ≠ ([], []) := by
  obtain ⟨-, rfl, -⟩ := tryRegsOf_spec (exnTableOpnd_cc he) htr
  simp


/-! ## The model -/

theorem noBrT_ok : killTabS.all (fun t => !killTabB.contains t || killOracles.contains t ||
    (program.rulesOf t).all fun rl => !(ruleTerms rl).contains TId.br_table_impl) = true := by
  native_decide

/-- No non-oracle term of both sets applies `br_table_impl`. -/
theorem noBrT : ∀ t ∈ killTabS, t ∈ killTabB → t ∉ killOracles → ∀ rl ∈ program.rulesOf t,
    TId.br_table_impl ∉ ruleTerms rl := by
  intro t hS hB ho rl hrl
  have h := List.all_eq_true.mp noBrT_ok t hS
  have hB' : killTabB.contains t = true := by simpa using hB
  have ho' : killOracles.contains t = false := by simpa using ho
  rw [hB', ho'] at h
  simp only [Bool.not_true, Bool.false_or, List.all_eq_true] at h
  intro hm
  have := h rl hrl
  simp [hm] at this


theorem termIds_ok : (List.range program.terms.size).all
    (fun i => (program.term? i).all (·.id == i)) = true := by
  native_decide

/-- A term of the program has its index as id. -/
theorem termOf_id_eq {t : TermId} {term : Term} (h : termOf program t = .ok term) : term.id = t := by
  have ht := termOf_program_eq h
  have hlt : t < program.terms.size := by
    unfold Program.term? at ht
    exact (Array.getElem?_eq_some_iff.mp ht).1
  have := List.all_eq_true.mp termIds_ok t (List.mem_range.mpr hlt)
  rw [ht] at this
  simpa using this

theorem isKVariant_zero : isKVariant 0 = false := by decide

/-- **The killed-vreg model** of the driver's semantics in context `ctx` (fresh vregs from `lo`,
code from `s0`), on the terms `T` with black-box oracles `O`. -/
def kModel (ctx : Ctx) (lo : Nat) (s0 : LState) (T O : TermId → Prop) (hvr : ValRegK ctx)
    (hd : DataK ctx) (hT : ∀ t, T t → t ∉ Excl ∧ (t = TId.gen_call_rets → ctx.tryRegs = ([], [])))
    (hcl : ∀ t, T t → ¬ O t → ∀ rl ∈ program.rulesOf t,
      (∀ u ∈ ruleTerms rl, T u) ∧ ∀ q ∈ ruleTys rl, killCall q.1 q.2)
    (hor : ∀ t, O t → OracleK ctx lo s0 t) : UModel program (sem ctx) where
  P := KP ctx lo s0
  Is := IsK ctx lo s0
  Rs := RsK
  T := T
  C := killCall
  O := O
  rs_refl := rsK_refl
  rs_trans := fun _ _ _ => rsK_trans
  mono := fun _ _ _ hs _ hr hp => kp_mono hs hr hp
  int := fun _ ty i _ => kp_int ty i
  bool := fun _ b _ => kp_bool b
  prim := fun _ _ _ _ _ h => kp_prim h
  mkd := fun _ _ _ term k _ _ hC ht hk _ hvs => kp_mkData hvs (by
    rcases hk with hk | ⟨-, rfl⟩
    · exact hC term k ht hk
    · rw [isKVariant_zero]; exact fun h => Bool.false_ne_true h.2)
  un := fun _ _ _ _ _ _ _ _ _ _ _ hv hu => kp_unData hv hu
  ext := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hx => kp_extract hd hx
  ctor := fun _ t _ _ _ _ _ _ _ hTt ht _ hIs hvs h => kp_ctor hvr hvs hIs h
    (by rw [termOf_id_eq ht]; exact (hT t hTt).1) (by rw [termOf_id_eq ht]; exact (hT t hTt).2)
  oracle := fun t hO => hor t hO
  closed := hcl

theorem notExcl {t : TermId} (h : t ∈ killTabS ++ killTabB) : t ∉ Excl := by
  have := (killTab_noX t h).2.2.2
  simpa [Excl] using this

/-- The model on `imm`'s terms (both tables, without `br_table_impl`), with the LL/SC loops as
oracles. -/
def iModel (ctx : Ctx) (lo : Nat) (s0 : LState) (hvr : ValRegK ctx) (hd : DataK ctx) :
    UModel program (sem ctx) :=
  kModel ctx lo s0 (fun t => t ∈ killTabS ∧ t ∈ killTabB ∧ t ≠ TId.br_table_impl)
    (fun t => t = TId.atomic_rmw_loop ∨ t = TId.atomic_cas_loop) hvr hd
    (fun t ht => ⟨notExcl (List.mem_append_left _ ht.1),
      fun hg => absurd (hg ▸ ht.2.1) genCallRets_notB⟩)
    (fun t ⟨hS, hB, hbr⟩ hO rl hrl => by
      have ho : t ∉ killOracles := by
        simp only [killOracles, List.mem_cons, List.not_mem_nil, or_false]
        rintro (h | h | h)
        · exact hO (.inl h)
        · exact hO (.inr h)
        · exact hbr h
      obtain ⟨hSt, hSc⟩ := killTabS_closed t hS ho rl hrl
      obtain ⟨hBt, -⟩ := killTabB_closed t hB ho rl hrl
      exact ⟨fun u hu => ⟨hSt u hu, hBt u hu, fun he => noBrT t hS hB ho rl hrl (he ▸ hu)⟩, hSc⟩)
    (fun t hO => by
      rcases hO with rfl | rfl
      · exact oracle_rmw Cov.totality
      · exact oracle_cas Cov.totality)

theorem killCall_imm (ty : TypeId) : killCall ty TId.imm := by
  intro term k ht hk
  rw [show TId.imm = 553 from rfl, program_term_553] at ht
  cases ht
  rw [term_553_kind] at hk
  cases hk

/-- `imm`'s runs keep the invariant (the sub-runs of `br_table_impl`). -/
theorem oracleK_imm {ctx : Ctx} {lo : Nat} {s0 : LState} (hvr : ValRegK ctx) (hd : DataK ctx) :
    OracleK ctx lo s0 TId.imm :=
  fun _ hc n ty vs s tr r s' tr' hvs hIs h =>
    uSound (iModel ctx lo s0 hvr hd) hc n ty TId.imm vs s tr r s' tr'
      ⟨imm_mem.1, imm_mem.2, by decide⟩ (killCall_imm ty) hvs hIs h

/-- The model of a statement's or a terminator's `lower` run (no `try_call` vregs). -/
def sModel (ctx : Ctx) (lo : Nat) (s0 : LState) (hvr : ValRegK ctx) (hd : DataK ctx)
    (htr : ctx.tryRegs = ([], [])) : UModel program (sem ctx) :=
  kModel ctx lo s0 (· ∈ killTabS) (· ∈ killOracles) hvr hd
    (fun _ ht => ⟨notExcl (List.mem_append_left _ ht), fun _ => htr⟩)
    killTabS_closed (oracle_all Cov.totality (oracleK_imm hvr hd))

/-- The model of a `lower_branch` run. -/
def bModel (ctx : Ctx) (lo : Nat) (s0 : LState) (hvr : ValRegK ctx) (hd : DataK ctx) :
    UModel program (sem ctx) :=
  kModel ctx lo s0 (· ∈ killTabB) (· ∈ killOracles) hvr hd
    (fun _ ht => ⟨notExcl (List.mem_append_right _ ht),
      fun hg => absurd (hg ▸ ht) genCallRets_notB⟩)
    killTabB_closed (oracle_all Cov.totality (oracleK_imm hvr hd))

theorem kp_inst {ctx : Ctx} {lo : Nat} {s0 s : LState} (i : Nat) : KP ctx lo s0 s (.inst i) :=
  kp_clean rfl rfl rfl

theorem kp_labels {ctx : Ctx} {lo : Nat} {s0 s : LState} (ls : List Label) :
    KP ctx lo s0 s (.labels ls) :=
  kp_clean rfl rfl rfl

/-! ## The driver's calls -/

set_option maxRecDepth 100000 in
theorem iflets_587 {rl : Rule} (hrl : rl ∈ program.rulesOf TId.lower) (h587 : rl.id = 587) :
    rl.iflets = [] := by
  have := List.all_eq_true.mp lower_587_noIflets rl hrl
  simp only [h587, bne_self_eq_false, Bool.false_or, List.isEmpty_iff] at this
  exact this

/-- **A statement's `lower` run.** -/
theorem stmt_kill {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx)
    (htr : ctx.tryRegs = ([], [])) (hvr : ValRegK ctx) (hd : DataK ctx) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst) {s : LState}
    {out : Option V} {s' : LState} {tr : List RuleId} (hN : ctx.valDef.size ≤ s.nextVreg)
    (h : runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr)) :
    RunKill ctx.valDef.size s.nextVreg s s' ∧
      (info.results ≠ [] → OutKill ctx.valDef.size s.nextVreg s s' out) := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower] at ht
  cases ht
  have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
      ((∀ u ∈ ruleTerms rl, u ∈ killTabS) ∧ ∀ q ∈ ruleTys rl, killCall q.1 q.2) ∨
        (rl ∈ program.rulesOf TId.lower ∧ rl.id = 587) ∨
        ∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠
          .ok (some env, s1) := by
    intro rl hrl
    by_cases h587 : rl.id = 587
    · exact .inr (.inl ⟨hrl, h587⟩)
    by_cases h636 : rl.id = 636 ∨ rl.id = 637
    · exact .inr (.inr (lower_636_637_nomatch hctx hi hc hrl h636))
    · exact .inl (killRootS rl hrl h587 (fun h => h636 (.inl h)) (fun h => h636 (.inr h)))
  obtain ⟨hIs, -, hv⟩ := uRoot (sModel ctx s.nextVreg s hvr hd htr) rfl (fun _ _ => info.results = [])
    (fun rl => rl ∈ program.rulesOf TId.lower ∧ rl.id = 587) data_program.t686 term_686_kind rfl
    hrules
    (fun rl _ ⟨hrl, h587⟩ k m s1 tr1 env s2 tr2 r s3 tr3 _ _ _ _ hIs hm he => by
      obtain ⟨hs, -⟩ := Cov.matchRule_noIfLets (iflets_587 hrl h587) hm
      cases hs
      obtain ⟨rfl, -⟩ := nop_rhs Cov.totality hrl h587 _ rfl _ _ _ _ _ _ _ he
      exact ⟨hIs, rsK_refl _, fun _ _ => nop_match_results hctx hi hc hrl h587 hm⟩)
    (fun v hv => by simp only [List.mem_singleton] at hv; subst hv; exact kp_inst ii)
    (isK_start hN (Nat.le_refl _)) happ
  refine ⟨runKill_of hIs, fun hres => outKill_of fun v hv' => ?_⟩
  rcases hv v hv' with hp | hq
  · exact hp
  · exact absurd hq hres

/-- **A `lower_branch` run** keeps the invariant. -/
theorem branch_kill {ctx : Ctx} (hvr : ValRegK ctx) (hd : DataK ctx) {lo : Nat} {s0 : LState}
    {ti : Nat} {targets : List Label} {s : LState} {out : Option V} {s' : LState} {tr : List RuleId}
    (hIs : IsK ctx lo s0 s)
    (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] s = .ok (out, s', tr)) :
    IsK ctx lo s0 s' := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower_branch] at ht
  cases ht
  exact (uRoot (bModel ctx lo s0 hvr hd) rfl (fun _ _ => False) (fun _ => False)
    data_program.t687 term_687_kind rfl (fun rl hrl => .inl (killRootB rl hrl))
    (fun _ _ h => h.elim)
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact kp_inst ti
      · exact kp_labels targets)
    hIs happ).1

/-- **A terminator's run.** -/
theorem term_kill {f : Clif.Function} {ctx : Ctx} (htr : ctx.tryRegs = ([], [])) (hvr : ValRegK ctx)
    (hd : DataK ctx) {ti : Nat} (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩)
    {t : Clif.Terminator} (hty : t.isTry = false) {data : V}
    (hdat : termData (abiTerm f t) = .ok data) {targets : List Label} {s : LState}
    {out : Option V} {s' : LState} {tr : List RuleId} (hN : ctx.valDef.size ≤ s.nextVreg)
    (h : termCallF ctx ti data t targets s = .ok (out, s', tr)) :
    RunKill ctx.valDef.size s.nextVreg s s' := by
  have hti : ti < ctx.insts.size := (Array.getElem?_eq_some_iff.mp hph).1
  have hslot := termCtx_self hti data
  have hvr' : ValRegK (termCtx ctx ti data) := valRegK_termCtx hvr ti data
  have hd' : DataK (termCtx ctx ti data) := dataK_termCtx hd (termData_kClean hdat) ti
  have hIs0 : IsK (termCtx ctx ti data) s.nextVreg s s := isK_start hN (Nat.le_refl _)
  unfold termCallF at h
  have hbranch : runTerm (termCtx ctx ti data) "lower_branch" [.inst ti, .labels targets] s =
      .ok (out, s', tr) → RunKill ctx.valDef.size s.nextVreg s s' := fun h =>
    runKill_of (branch_kill hvr' hd' hIs0 h)
  have hlower : retOrTrap (abiTerm f t) = true →
      runTerm (termCtx ctx ti data) "lower" [.inst ti] s = .ok (out, s', tr) →
      RunKill ctx.valDef.size s.nextVreg s s' := by
    intro hrt h
    obtain ⟨t', tr', ht, happ⟩ := runTerm_apply h
    rw [program_termByName_lower] at ht
    cases ht
    have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
        ((∀ u ∈ ruleTerms rl, u ∈ killTabS) ∧ ∀ q ∈ ruleTys rl, killCall q.1 q.2) ∨ False ∨
          ∀ m s0 env s1, (matchRule program (sem (termCtx ctx ti data)) {} m rl [.inst ti]).run s0 ≠
            .ok (some env, s1) := by
      intro rl hrl
      cases hroot : termRootRule rl with
      | false => exact .inr (.inr (lower_term_nomatch hrt hdat hslot hrl hroot))
      | true =>
        simp only [termRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
        exact .inl (killRootS rl hrl (by rcases hroot with h | h <;> simp [h])
          (by rcases hroot with h | h <;> simp [h]) (by rcases hroot with h | h <;> simp [h]))
    exact runKill_of (uRoot (sModel (termCtx ctx ti data) s.nextVreg s hvr' hd' htr) rfl
      (fun _ _ => False) (fun _ => False) data_program.t686 term_686_kind rfl hrules
      (fun _ _ h => h.elim)
      (fun v hv => by simp only [List.mem_singleton] at hv; subst hv; exact kp_inst ti)
      hIs0 happ).1
  cases t with
  | ret vs => exact hlower rfl h
  | trap c => exact hlower rfl h
  | jump bc => exact hbranch h
  | brif c a b => exact hbranch h
  | brTable x d tb => exact hbranch h
  | returnCall fn args => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hdat
  | tryCall fn args et => simp [Clif.Terminator.isTry] at hty
  | tryCallIndirect callee args et => simp [Clif.Terminator.isTry] at hty

/-- **A `try_call`'s `lower_branch` run.** -/
theorem try_kill {f : Clif.Function} {ctx : Ctx} (hvr : ValRegK ctx) (hd : DataK ctx) {ti : Nat}
    {t : Clif.Terminator} {et : Clif.ExnTable} {data : V} (hdat : tryCallData f t = .ok data)
    {sig : Clif.Signature} {items : List (Option Nat)} (he : exnTableOpnd f et = .ok (sig, items))
    {lo st1 : LState} {trs : List Reg × List Reg} (hlo : ctx.valDef.size ≤ lo.nextVreg)
    (htr : tryRegsOf sig lo = some (trs, st1)) {targets : List Label} {out : Option V}
    {s' : LState} {tr : List RuleId}
    (h : tryCallF ctx ti data trs targets { st1 with emitted := #[] } = .ok (out, s', tr)) :
    RunKill ctx.valDef.size st1.nextVreg { st1 with emitted := #[] } s' ∧
      ∀ m ∈ s'.emitted.toList, ∀ c, m = .call c → ∀ q ∈ c.defs, ∀ n cl, q.2 = .vreg n cl →
        q.2 ∈ trs.1 ∨ q.2 ∈ trs.2 := by
  have hst := (tryRegsOf_mono htr).1
  unfold tryCallF at h
  have hIs := branch_kill (ctx := tryCtx ctx ti data trs) (valRegK_tryCtx hvr ti data trs)
    (dataK_tryCtx hd (tryCallData_kClean hdat) ti trs) (lo := st1.nextVreg)
    (s0 := { st1 with emitted := #[] }) (s := { st1 with emitted := #[] })
    (isK_start (Nat.le_trans hlo hst) (Nat.le_refl _)) h
  exact ⟨runKill_of (ctx := tryCtx ctx ti data trs) hIs,
    tryDefs_of (ctx := tryCtx ctx ti data trs) hIs rfl (trs_ne he htr)⟩

/-! ## The killed-vreg facts of the ISLE runs -/

/-- **`KillRunsHyp`**: every ISLE run of the driver kills only fresh vregs of the run, reads only
CLIF values' vregs and unkilled vregs of the run, and a `try_call`'s calls define only its result
vregs. -/
theorem killRunsHyp : KillRunsHyp := by
  intro f ctx ranges st0 _ hs _ hb
  have hctx : CtxInv f ctx := ctxOk_sound (ctxOk_complete hs hb)
  have htr := (ctxFacts_of hb).tryRegs
  have hvr := valRegK_of_build hb
  have hd := dataK_of_build hb
  exact ⟨fun ii info inst s out s' tr hi hc hN h => stmt_kill hctx htr hvr hd hi hc hN h,
    fun ti t data targets s out s' tr _ hph hty hdat hN h =>
      term_kill htr hvr hd hph hty hdat hN h,
    fun ti t et data sig items lo trs st1 targets out s' tr _ _ _ _ hdat he hlo htr h =>
      try_kill hvr hd hdat he hlo htr h⟩

end Backend.Proof.Kill
