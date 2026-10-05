import FV.Backend.Proof.LowerSpec
import FV.Backend.Proof.IselFlowGen
import FV.Backend.Proof.IselFlowInst
import FV.Backend.Proof.IselFlowRootF
import FV.Backend.Proof.IselFlowRootT
import FV.Backend.Proof.IselCtlUnmatch

/-!
# Completeness of `lowerCheck`: what the ISLE lowering of one instruction can produce

Facts about every run of the ISLE interpreter in the driver's contexts, decided once over the
exported rule data (no per-program check):

* `runTerm_mono`: the fresh-vreg counter and the outgoing area only grow, and the emitted code
  is only extended, never by a `tryCall` (only `lowerFunction` makes one);
* `stmt_flow`: the result registers a statement's lowering returns are fresh vregs of that call
  or registers of values the instruction reaches through its operands (`Prov`);
* `stmt_noTls`, `term_noTls`: only the lowering of a `tls_value` emits an `ElfTlsGetAddr`.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64

/-- The lowering-state relation of `runTerm_mono`. -/
def StRel (s s' : LState) : Prop :=
  s.nextVreg ≤ s'.nextVreg ∧ s.outgoing ≤ s'.outgoing ∧
    ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧ ∀ m ∈ ms, ∀ c ti, m ≠ .tryCall c ti

theorem stRel_refl (s : LState) : StRel s s := ⟨Nat.le_refl _, Nat.le_refl _, [], by simp, by simp⟩

theorem stRel_trans (a b c : LState) (h1 : StRel a b) (h2 : StRel b c) : StRel a c := by
  obtain ⟨g1, g2, ms, g3, g4⟩ := h1
  obtain ⟨g5, g6, ms', g7, g8⟩ := h2
  refine ⟨Nat.le_trans g1 g5, Nat.le_trans g2 g6, ms ++ ms', by simp [g7, g3], ?_⟩
  intro m hm
  rcases List.mem_append.mp hm with hm | hm
  · exact g4 m hm
  · exact g8 m hm

theorem stRel_ctor (ctx : Ctx) (term : Term) (vs : List V) (s : LState) (v : V) (s' : LState)
    (h : (sem ctx).ctor term vs s = .ok (v, s')) : StRel s s' := by
  have hc := externCtor_ok ctx term vs s v s' h
  obtain ⟨ms, h1, h2⟩ := hc.emit
  exact ⟨hc.vreg, hc.out, ms, h1, fun m hm => (h2 m hm).1⟩

/-- A successful `runTerm` is a run of `applyTerm` of the named term. -/
theorem runTerm_apply {ctx : Ctx} {term : String} {args : List V} {s : LState} {out : Option V}
    {s' : LState} {tr : List RuleId} (h : runTerm ctx term args s = .ok (out, s', tr)) :
    ∃ (t : Isle.Term) (tr' : Array RuleId), program.termByName? term = some t ∧
      (applyTerm program (sem ctx) {} 1000000 t.ret t.id args).run (s, #[]) =
      .ok (out, (s', tr')) := by
  unfold runTerm Interp.run at h
  split at h
  · rename_i r hr
    cases h
    cases ht : program.termByName? term with
    | none => rw [ht] at hr; cases hr
    | some t =>
      rw [ht] at hr
      simp only [bind, Except.bind] at hr
      split at hr
      · cases hr
      · rename_i q hq
        obtain ⟨v, st', tr'⟩ := q
        simp only [pure, Except.pure, Except.ok.injEq] at hr
        subst hr
        exact ⟨t, tr', rfl, hq⟩
  · cases h

/-- Any ISLE run with the driver's semantics: fresh vregs and the outgoing area only grow, the
emitted code is extended, never by a `tryCall`. -/
theorem runTerm_mono {ctx : Ctx} {term : String} {args : List V} {s : LState} {out : Option V}
    {s' : LState} {tr : List Isle.RuleId} (h : runTerm ctx term args s = .ok (out, s', tr)) :
    s.nextVreg ≤ s'.nextVreg ∧ s.outgoing ≤ s'.outgoing ∧
    ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧ ∀ m ∈ ms, ∀ c ti, m ≠ .tryCall c ti := by
  obtain ⟨t, tr', -, h⟩ := runTerm_apply h
  exact (presAt stRel_refl stRel_trans (stRel_ctor ctx) 1000000).apply _ _ _ _ _ _ _ _ h
/-! ## Root rules that cannot match -/

/-- A root rule of `lower` outside the closure never matches a statement (`exclOk`). -/
theorem lower_nonroot_nomatch {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {r : Rule} (hr : r ∈ program.rulesOf TId.lower) (hroot : closureRootIds.contains r.id = false) :
    ∀ m s0 env s1, (matchRule program (sem ctx) {} m r [.inst ii]).run s0 ≠ .ok (some env, s1) := by
  intro m s0 env' s1 hmatch
  have hok := List.all_eq_true.mp exclOk_program r hr
  simp only [exclOk, hroot, Bool.false_or] at hok
  cases m with
  | zero => rw [matchRule.eq_1] at hmatch; cases hmatch
  | succ m =>
    obtain ⟨env0, ha, -⟩ := matchRule_some_inv hmatch
    split at hok
    · rename_i q hargs
      rw [hargs] at ha
      obtain ⟨e1, h1, -⟩ := matchArgs_cons_inv ha
      exact fails_sound hctx q .inst _ _ _ _ hok
        ⟨ii, info, inst, rfl, hi, hc, hctx.data ii info inst hi hc⟩ h1
    · cases hok

/-- The format and opcode terms of a root pattern `(inst_data_value _ (Fmt (Op) …))`. -/
def rootOp (r : Rule) : Option (Nat × Nat) :=
  match r.args with
  | .term 18 209 [_, .term 152 fT (.term 151 oT [] :: _)] :: _ => some (fT, oT)
  | _ => none

set_option maxRecDepth 100000 in
/-- `nop`'s rule (587) pins `NullAry`/`Nop`, the `tls_value` rules (1129, 1130)
`UnaryGlobalValue`/`TlsValue`. -/
theorem lower_ops : (program.rulesOf TId.lower).all (fun r =>
    (r.id != 587 || rootOp r == some (2466, 2348)) &&
    ((r.id != 1129 && r.id != 1130) || rootOp r == some (2478, 2334))) = true := by
  rw [show TId.lower = 686 from rfl, data_program.r686]
  decide +kernel

set_option maxRecDepth 100000 in
theorem kind_nullAry : (match termOf program 2466 with
    | .ok t => t.kind == .enumVariant VIdx.InstructionData.NullAry | .error _ => false) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kind_nop : (match termOf program 2348 with
    | .ok t => t.kind == .enumVariant VIdx.Opcode.Nop | .error _ => false) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kind_ugv : (match termOf program 2478 with
    | .ok t => t.kind == .enumVariant VIdx.InstructionData.UnaryGlobalValue | .error _ => false) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kind_tls : (match termOf program 2334 with
    | .ok t => t.kind == .enumVariant VIdx.Opcode.TlsValue | .error _ => false) = true := by
  decide +kernel

theorem kind_of {t : TermId} {k : Nat}
    (h : (match termOf program t with | .ok t => t.kind == .enumVariant k | .error _ => false) = true) :
    ∃ tf, termOf program t = .ok tf ∧ tf.kind = .enumVariant k := by
  revert h
  cases termOf program t with
  | error e => simp
  | ok tf => intro h; exact ⟨tf, rfl, by simpa using h⟩

/-- A rule pinning format `fT` and opcode `oT` matched only instructions with that data. -/
theorem rootOp_match {ctx : Ctx} {r : Rule} {fT oT : Nat} (hq : rootOp r = some (fT, oT))
    {tf to : Term} {kf o : Nat} (htf : termOf program fT = .ok tf) (hkf : tf.kind = .enumVariant kf)
    (hto : termOf program oT = .ok to) (hko : to.kind = .enumVariant o) {m ii : Nat} {vs : List V}
    {s s1 : LState × Array RuleId} {env : Interp.Env V}
    (h : (matchRule program (sem ctx) {} m r (.inst ii :: vs)).run s = .ok (some env, s1)) :
    ∃ info fs, ctx.insts[ii]? = some info ∧ info.data = .data 152 kf (.data 151 o [] :: fs) := by
  cases m with
  | zero => rw [matchRule.eq_1] at h; cases h
  | succ m =>
    obtain ⟨env0, ha, -⟩ := matchRule_some_inv h
    unfold rootOp at hq
    split at hq
    · rename_i q1 fT' oT' rest qs hargs
      simp only [Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      rw [hargs] at ha
      obtain ⟨e1, h1, -⟩ := matchArgs_cons_inv ha
      obtain ⟨fs, hx, hm⟩ := matchPat_extract_inv data_program.t209 term_209_kind rfl h1
      rw [sem_extract] at hx
      obtain ⟨info, hinfo, rfl⟩ := ext_inst_data_value_inv hx
      obtain ⟨e2, -, hm2⟩ := matchArgs_cons_inv hm
      obtain ⟨e3, hp2, -⟩ := matchArgs_cons_inv hm2
      obtain ⟨fs', hu, hm3⟩ := matchPat_enum_inv htf hkf hp2
      have hd := sem_unData_inv hu
      cases fs' with
      | nil =>
        rw [matchArgs.eq_3] at hm3
        all_goals first | cases hm3 | (intros; simp_all)
      | cons g gs =>
        obtain ⟨e4, hp3, -⟩ := matchArgs_cons_inv hm3
        obtain ⟨fs1, hu1, hm4⟩ := matchPat_enum_inv hto hko hp3
        have hg := sem_unData_inv hu1
        cases fs1 with
        | nil => exact ⟨info, gs, hinfo, by rw [hd, hg]⟩
        | cons _ _ =>
          rw [matchArgs.eq_3] at hm4
          all_goals first | cases hm4 | (intros; simp_all)
    · cases hq

theorem instNames_nop {c : Clif.Inst} (h : (instNames c).2 = "Nop") : c = .nop := by
  cases c <;> simp only [instNames] at h <;>
    first
    | rfl
    | (rename_i op _ _; cases op <;> simp [unaryOpcode] at h)
    | (rename_i op _ _ _; cases op <;> simp [binaryOpcode, divOpcode] at h)
    | (rename_i op _ _ _ _; cases op <;> simp [loadOpcode] at h)
    | (rename_i op _ _ _ _ _; cases op <;> simp [storeOpcode] at h)
    | (rename_i op _ _; cases op <;> simp at h)
    | simp at h

theorem instNames_tls {c : Clif.Inst} (h : (instNames c).2 = "TlsValue") :
    ∃ ty gv, c = .tlsValue ty gv := by
  cases c <;> simp only [instNames] at h <;>
    first
    | exact ⟨_, _, rfl⟩
    | (rename_i op _ _; cases op <;> simp [unaryOpcode] at h)
    | (rename_i op _ _ _; cases op <;> simp [binaryOpcode, divOpcode] at h)
    | (rename_i op _ _ _ _; cases op <;> simp [loadOpcode] at h)
    | (rename_i op _ _ _ _ _; cases op <;> simp [storeOpcode] at h)
    | (rename_i op _ _; cases op <;> simp at h)
    | simp at h

set_option maxRecDepth 20000 in
theorem variantNames_Nop : (variantNames 151)[VIdx.Opcode.Nop]? = some "Nop" := rfl
set_option maxRecDepth 20000 in
theorem variantNames_Tls : (variantNames 151)[VIdx.Opcode.TlsValue]? = some "TlsValue" := rfl

set_option maxRecDepth 100000 in
/-- The opcode of a statement whose rule pinned opcode `o`. -/
theorem pinned_names {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {r : Rule} {fT oT : Nat} (hq : rootOp r = some (fT, oT)) {kf o : Nat}
    (hk : (match termOf program fT with | .ok t => t.kind == .enumVariant kf | .error _ => false) = true)
    (ho : (match termOf program oT with | .ok t => t.kind == .enumVariant o | .error _ => false) = true)
    {m : Nat} {s s1 : LState × Array RuleId} {env : Interp.Env V}
    (h : (matchRule program (sem ctx) {} m r [.inst ii]).run s = .ok (some env, s1)) :
    (variantNames 151)[o]? = some (instNames inst).2 := by
  obtain ⟨tf, htf, hkf⟩ := kind_of hk
  obtain ⟨to, hto, hko⟩ := kind_of ho
  obtain ⟨info', fs, hi', hd⟩ := rootOp_match hq htf hkf hto hko h
  rw [hi] at hi'; cases hi'
  have := hctx.data ii info inst hi hc
  rw [hd] at this
  exact (instData_inv_names this).2

/-- `lower` on a `return`/`trap`: only the terminator rules can match (by format). -/
theorem lower_term_nomatch {ctx : Ctx} {ti : Nat} {t : Clif.Terminator} {data : V}
    (hrt : retOrTrap t = true) (hd : termData t = .ok data)
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) {r : Rule} (hr : r ∈ program.rulesOf TId.lower)
    (hroot : termRootRule r = false) :
    ∀ m s0 env s1, (matchRule program (sem ctx) {} m r [.inst ti]).run s0 ≠ .ok (some env, s1) := by
  intro m s env' s1 hmatch
  have hok := List.all_eq_true.mp lower_fmts r hr
  simp only [lowerFmtOk, hroot, Bool.false_or] at hok
  split at hok
  · rename_i fT hfT
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hok
    obtain ⟨⟨⟨hlo, hhi⟩, h1⟩, h2⟩ := hok
    obtain ⟨info, fs, hinfo, hdat⟩ :=
      ruleFmt_match (vs := []) data_program fmtKinds_program hfT hlo hhi hmatch
    rw [hi] at hinfo
    cases hinfo
    obtain ⟨fs', rfl⟩ := termData_fmt hd
    simp only [V.data.injEq] at hdat
    cases t <;> simp [retOrTrap] at hrt <;> simp [termFmt] at hdat <;>
      first | omega | simp [termData, throw, throwThe, MonadExceptOf.throw] at hd
  · cases hok

theorem mem_regsVec {rss : List (List Reg)} {rs : List Reg} (h : rs ∈ rss) {r : Reg} (hr : r ∈ rs) :
    r ∈ (V.regsVec rss).regsIn := by
  simp only [V.regsIn, List.mem_flatten]; exact ⟨rs, h, hr⟩

theorem noTls_of {s s' : LState} (h : NoTlsSince s s') :
    ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧
      ∀ m ∈ ms, ∀ sym rd tmp, m ≠ .elfTlsGetAddr sym rd tmp := by
  obtain ⟨ms, h1, h2⟩ := h
  exact ⟨ms, h1, fun m hm sym rd tmp he => h2 m hm ⟨sym, rd, tmp, he⟩⟩

/-- The data of the root statement and of defining instructions is safe. -/
theorem stmt_root_safe {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst) :
    ∀ j info', (j = ii ∨ ∃ n, ctx.defInst? n = some j) → ctx.insts[j]? = some info' →
      info'.data.tlsIn = false ∧ info'.data.instsIn = [] := by
  intro j info' hj hinfo
  rcases hj with rfl | ⟨n, hd⟩
  · rw [hi] at hinfo; cases hinfo
    have := instData_ok (hctx.data _ _ _ hi hc)
    exact ⟨this.2.2.1, this.2.1⟩
  · obtain ⟨c, hcc⟩ := Option.isSome_iff_exists.mp (hctx.defClif n j info' hd hinfo)
    have := instData_ok (hctx.data _ _ _ hinfo hcc)
    exact ⟨this.2.2.1, this.2.1⟩

theorem termCtx_self {ctx : Ctx} {ti : Nat} (hti : ti < ctx.insts.size) (data : V) :
    (termCtx ctx ti data).insts[ti]? = some ⟨data, [], [], none⟩ := by
  show (ctx.insts.set! ti _)[ti]? = _
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hti]

/-- The data of a terminator's slot and of defining instructions is safe. -/
theorem term_root_safe {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ti : Nat}
    (hti : ti < ctx.insts.size) {data : V} (hdat : data.tlsIn = false ∧ data.instsIn = [])
    (ctx' : Ctx) (hins : ctx'.insts = (termCtx ctx ti data).insts) (hdef : ctx'.valDef = ctx.valDef) :
    ∀ j info', (j = ti ∨ ∃ n, ctx'.defInst? n = some j) → ctx'.insts[j]? = some info' →
      info'.data.tlsIn = false ∧ info'.data.instsIn = [] := by
  intro j info' hj hinfo
  rw [hins] at hinfo
  by_cases hjt : j = ti
  · subst hjt
    rw [termCtx_self hti] at hinfo; cases hinfo
    exact hdat
  · rw [termCtx_insts_ne hjt] at hinfo
    rcases hj with h | ⟨n, hd⟩
    · exact absurd h hjt
    · have hd' : ctx.defInst? n = some j := by
        unfold Ctx.defInst? at hd ⊢; rw [hdef] at hd; exact hd
      obtain ⟨c, hcc⟩ := Option.isSome_iff_exists.mp (hctx.defClif n j info' hd' hinfo)
      have := instData_ok (hctx.data _ _ _ hinfo hcc)
      exact ⟨this.2.2.1, this.2.1⟩

set_option maxRecDepth 100000 in
/-- **The result registers of a statement's lowering**: each is a fresh vreg of the call or the
register of a value the instruction reaches through its operands. -/
theorem stmt_flow {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx)
    (htr : ctx.tryRegs = ([], [])) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst) {s : LState} {out : V}
    {s' : LState} {tr : List Isle.RuleId} (h : runTerm ctx "lower" [.inst ii] s = .ok (some out, s', tr)) :
    ∀ rss, out = .regsVec rss → info.results ≠ [] → ∀ rs ∈ rss, ∀ o cls, rs = [.vreg o cls] →
      (s.nextVreg ≤ o ∧ o < s'.nextVreg) ∨ Prov ctx ii o := by
  intro rss hout hres rs hrs o cls hrso
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower] at ht
  cases ht
  have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
      aRule program flowTab false [⟨1, true⟩] ⟨1, false⟩ rl = true ∨
        ∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠ .ok (some env, s1) := by
    intro rl hrl
    have hf := List.all_eq_true.mp flowRoot_ok rl hrl
    have hop := List.all_eq_true.mp lower_ops rl hrl
    simp only [flowRootOk, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hf
    rcases hf with (hcr | h587) | ha
    · exact .inr (lower_nonroot_nomatch hctx hi hc hrl hcr)
    · refine .inr fun m s0 env s1 hm => hres ?_
      simp only [h587, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hop
      have hn := pinned_names hctx hi hc hop.1 kind_nullAry kind_nop hm
      rw [variantNames_Nop] at hn
      have hnop := instNames_nop (Option.some.inj hn).symm
      subst hnop
      obtain ⟨tys, hty, -, hlen⟩ := hctx.resTys ii info .nop hi hc
      simp [Clif.Inst.resultTypes] at hty
      subst hty
      exact List.eq_nil_of_length_eq_zero hlen
    · exact .inl ha
  have hins : Holds2 (γF ctx ii s.nextVreg) s [⟨1, true⟩] [.inst ii] :=
    ⟨γF_of_clean fun _ => ⟨fun r hr => by simp [V.regsIn] at hr, fun n hn => by simp [V.valsIn] at hn,
      fun j hj => .inl ⟨by simp, by simpa [V.instsIn] using hj⟩⟩, trivial⟩
  obtain ⟨-, hv⟩ := (soundAt (flowModel hctx hi hc htr (lo := s.nextVreg)) (cfg := {}) rfl
    flowTab_ok 1000000).root T.lower.ret T.lower.id T.lower _ _ [⟨1, true⟩] ⟨1, false⟩ [.inst ii] s #[]
    (some out) s' tr' data_program.t686 term_686_kind hrules hins (Nat.le_refl _) happ
  have hcl := (hv out rfl).2 rfl
  subst hout
  exact hcl.1 (.vreg o cls) (mem_regsVec hrs (by rw [hrso]; exact List.mem_singleton_self _)) o cls rfl

set_option maxRecDepth 100000 in
/-- Only the lowering of a `tls_value` emits an `ElfTlsGetAddr`. -/
theorem stmt_noTls {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hnt : ∀ ty gv, inst ≠ .tlsValue ty gv) {s : LState} {out : Option V} {s' : LState}
    {tr : List Isle.RuleId} (h : runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr)) :
    ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧
      ∀ m ∈ ms, ∀ sym rd tmp, m ≠ .elfTlsGetAddr sym rd tmp := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower] at ht
  cases ht
  have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
      aRule program tlsTab true [⟨2, true⟩] FA.top rl = true ∨
        ∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠ .ok (some env, s1) := by
    intro rl hrl
    have hf := List.all_eq_true.mp tlsRoot_ok rl hrl
    have hop := List.all_eq_true.mp lower_ops rl hrl
    simp only [tlsRootOk, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hf
    rcases hf with ((hcr | h1) | h1) | ha
    · exact .inr (lower_nonroot_nomatch hctx hi hc hrl hcr)
    all_goals try exact .inl ha
    all_goals
      refine .inr fun m s0 env s1 hm => ?_
      simp only [h1, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hop
      have hq : rootOp rl = some (2478, 2334) := by
        rcases hop.2 with h | h
        · simp at h
        · exact h
      have hn := pinned_names hctx hi hc hq kind_ugv kind_tls hm
      rw [variantNames_Tls] at hn
      obtain ⟨ty, gv, rfl⟩ := instNames_tls (Option.some.inj hn).symm
      exact hnt ty gv rfl
  have hins : Holds2 (γT ctx ii) s [⟨2, true⟩] [.inst ii] :=
    ⟨fun _ => ⟨rfl, fun j hj => .inl (by simpa [V.instsIn] using hj)⟩, trivial⟩
  obtain ⟨hIs, -⟩ := (soundAt (tlsModel (stmt_root_safe hctx hi hc) s) (cfg := {}) rfl
    tlsTab_ok 1000000).root T.lower.ret T.lower.id T.lower _ _ [⟨2, true⟩] FA.top [.inst ii] s #[]
    out s' tr' data_program.t686 term_686_kind hrules hins ⟨[], by simp, by simp⟩ happ
  exact noTls_of hIs

set_option maxRecDepth 100000 in
/-- `lower_branch` from a safe terminator slot: nothing emitted is an `ElfTlsGetAddr`. -/
theorem branch_noTls {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ti : Nat}
    (hti : ti < ctx.insts.size) {data : V} (hdat : data.tlsIn = false ∧ data.instsIn = [])
    (ctx' : Ctx) (hins' : ctx'.insts = (termCtx ctx ti data).insts) (hdef : ctx'.valDef = ctx.valDef)
    {targets : List Label} {s : LState} {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : runTerm ctx' "lower_branch" [.inst ti, .labels targets] s = .ok (out, s', tr)) :
    ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧
      ∀ m ∈ ms, ∀ sym rd tmp, m ≠ .elfTlsGetAddr sym rd tmp := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower_branch] at ht
  cases ht
  have hins : Holds2 (γT ctx' ti) s [⟨2, true⟩, ⟨2, true⟩] [.inst ti, .labels targets] :=
    ⟨fun _ => ⟨rfl, fun j hj => .inl (by simpa [V.instsIn] using hj)⟩,
     fun _ => ⟨rfl, fun j hj => by simp [V.instsIn] at hj⟩, trivial⟩
  obtain ⟨hIs, -⟩ := (soundAt (tlsModel (term_root_safe hctx hti hdat ctx' hins' hdef) s)
    (cfg := {}) rfl tlsTab_ok 1000000).root T.lower_branch.ret T.lower_branch.id T.lower_branch _ _
    [⟨2, true⟩, ⟨2, true⟩] FA.top _ s #[] out s' tr' data_program.t687 term_687_kind
    (fun rl hrl => .inl (List.all_eq_true.mp tlsRootBranch_ok rl hrl)) hins ⟨[], by simp, by simp⟩ happ
  exact noTls_of hIs

set_option maxRecDepth 100000 in
/-- A terminator's lowering (`lower` on `return`/`trap`, `lower_branch` on a branch) emits no
`ElfTlsGetAddr`. -/
theorem termCall_noTls {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ti : Nat}
    (hti : ti < ctx.insts.size) {t : Clif.Terminator} {data : V}
    (hd : termData (abiTerm f t) = .ok data) {targets : List Label} {s : LState} {out : Option V}
    {s' : LState} {tr : List Isle.RuleId} (h : termCallF ctx ti data t targets s = .ok (out, s', tr)) :
    ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧
      ∀ m ∈ ms, ∀ sym rd tmp, m ≠ .elfTlsGetAddr sym rd tmp := by
  have hdok := termData_ok hd
  have hdat : data.tlsIn = false ∧ data.instsIn = [] := ⟨hdok.2.2.1, hdok.2.1⟩
  unfold termCallF at h
  have hlower : retOrTrap (abiTerm f t) = true →
      runTerm (termCtx ctx ti data) "lower" [.inst ti] s = .ok (out, s', tr) →
      ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧
        ∀ m ∈ ms, ∀ sym rd tmp, m ≠ .elfTlsGetAddr sym rd tmp := by
    intro hrt h
    obtain ⟨t', tr', ht, happ⟩ := runTerm_apply h
    rw [program_termByName_lower] at ht
    cases ht
    have hslot := termCtx_self hti data
    have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
        aRule program tlsTab true [⟨2, true⟩] FA.top rl = true ∨
          ∀ m s0 env s1, (matchRule program (sem (termCtx ctx ti data)) {} m rl [.inst ti]).run s0 ≠
            .ok (some env, s1) := by
      intro rl hrl
      cases hroot : termRootRule rl with
      | false => exact .inr (lower_term_nomatch hrt hd hslot hrl hroot)
      | true =>
        have hf := List.all_eq_true.mp tlsRoot_ok rl hrl
        simp only [termRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
        simp only [tlsRootOk] at hf
        rcases hroot with h1 | h1 <;> rw [h1] at hf <;>
          exact .inl (by simpa (config := { decide := true }) using hf)
    have hins : Holds2 (γT (termCtx ctx ti data) ti) s [⟨2, true⟩] [.inst ti] :=
      ⟨fun _ => ⟨rfl, fun j hj => .inl (by simpa [V.instsIn] using hj)⟩, trivial⟩
    obtain ⟨hIs, -⟩ := (soundAt (tlsModel (term_root_safe hctx hti hdat (termCtx ctx ti data) rfl rfl) s)
      (cfg := {}) rfl tlsTab_ok 1000000).root T.lower.ret T.lower.id T.lower _ _ [⟨2, true⟩] FA.top
      [.inst ti] s #[] out s' tr' data_program.t686 term_686_kind hrules hins ⟨[], by simp, by simp⟩ happ
    exact noTls_of hIs
  cases t with
  | ret vs => exact hlower rfl h
  | trap c => exact hlower rfl h
  | jump bc => exact branch_noTls hctx hti hdat _ rfl rfl h
  | brif c a b => exact branch_noTls hctx hti hdat _ rfl rfl h
  | brTable x d tb => exact branch_noTls hctx hti hdat _ rfl rfl h
  | returnCall fn args => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
  | tryCall fn args et => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
  | tryCallIndirect callee args et => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd

set_option maxRecDepth 100000 in
/-- A `try_call`'s lowering (`lower_branch`) emits no `ElfTlsGetAddr`. -/
theorem tryCall_noTls {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ti : Nat}
    (hti : ti < ctx.insts.size) {t : Clif.Terminator} {data : V} (hd : tryCallData f t = .ok data)
    {trs : List Reg × List Reg} {targets : List Label} {s : LState} {out : Option V} {s' : LState}
    {tr : List Isle.RuleId} (h : tryCallF ctx ti data trs targets s = .ok (out, s', tr)) :
    ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧
      ∀ m ∈ ms, ∀ sym rd tmp, m ≠ .elfTlsGetAddr sym rd tmp := by
  have hdok := tryCallData_ok hd
  exact branch_noTls hctx hti ⟨hdok.2.2.1, hdok.2.1⟩ (tryCtx ctx ti data trs) rfl rfl h

end Backend.Proof.Driver
