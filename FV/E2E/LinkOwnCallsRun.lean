import FV.E2E.LinkOwnCallsShape
import FV.Backend.Proof.KillDriver

/-!
# The ISLE call inversion per run (`CallRunHyp`): runs that emit no call

The uniform invariant of ISLE runs (`Isle.Interp.UModel`, `KillGen.lean`) with the value
predicate "holds no `MInst.Call`/`MInst.CallInd` data" (`vCIn`) and the run relation "emits no
`call`/`tryCall`" (`NoCallSince`), on the term set `callTab`: the closure under `Isle.ruleTerms`
of the terms applied by the rules of `lower` other than the `call`/`call_indirect` rules
1031–1033 and by the closure-root rules of `lower_branch` (the `try_call` rules 1034–1036 are
not). Decided over the exported rule data: `callTab` is closed and no call site of its rules
builds `Call`/`CallInd` data. A call is emitted only through `emit` of such data
(`Cov.externCtor_shp`, `ofV_call_cIn`), extern constructors build none (`externCtor_c`) and
extractors return none (`externExtract_c`, the CLIF data holds no `MInst` data).

Proven: `stmt_noCalls` (a statement that is no `call`/`call_indirect`: rules 1031–1033 pin the
`Call`/`CallIndirect` formats), `term_noCalls` (a non-`try_call` terminator), and
`callRunHyp_of`: `CallRunHyp` from the two remaining parts, `CallStmtRunHyp` (a
`call`/`call_indirect` statement's run) and `TryRunHyp` (a `try_call`'s run).
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 100000

/-! ## Call data inside values -/

/-- The `MInst` variants of a call. -/
def isCallV (k : Nat) : Bool := k == VIdx.MInst.Call || k == VIdx.MInst.CallInd

mutual
/-- Does the value hold `MInst.Call`/`MInst.CallInd` data? -/
def vCIn : V → Bool
  | .data ty k fs => (ty == tyMInst && isCallV k) || vCInL fs
  | _ => false
/-- `vCIn` of a list. -/
def vCInL : List V → Bool
  | [] => false
  | v :: vs => vCIn v || vCInL vs
end

theorem vCInL_eq_false : ∀ {vs : List V}, vCInL vs = false ↔ ∀ w ∈ vs, vCIn w = false
  | [] => by simp [vCInL]
  | v :: vs => by simp [vCInL, vCInL_eq_false]

/-- A call or a `tryCall`. -/
def isCallB : MInst → Bool
  | .call _ => true
  | .tryCall _ _ => true
  | _ => false

/-- **`MInst.ofV`** builds a call only from `Call`/`CallInd` data. -/
theorem ofV_call_cIn {v : V} {m : MInst} (h : MInst.ofV v = some m) (hm : isCallB m = true) :
    vCIn v = true := by
  unfold MInst.ofV at h
  obtain ⟨⟨k, fs⟩, he, h2⟩ := Flow.bind_some_ex h
  clear h
  rw [Flow.enumOf_eq he]
  have key : isCallV k = true := by
    revert hm
    revert h2
    revert m
    apply _root_.ofV_split _
      (fun k _ (r : Option MInst) => ∀ m, r = some m → isCallB m = true → isCallV k = true)
    all_goals
      intros
      rename_i m hm hc
      try simp only at hm
      repeat' (first | (obtain ⟨_, _, hm⟩ := Flow.bind_some_ex hm) | split at hm)
      all_goals first
        | (cases hm; done)
        | (simp only [pure, Option.some.injEq] at hm
           subst hm
           first
           | (simp [isCallB] at hc; done)
           | rfl)
  simp [vCIn, key]

/-- Instructions without a call or a `tryCall` were emitted from `s` to `s'`. -/
def NoCallSince (s s' : LState) : Prop :=
  ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧ ∀ m ∈ ms, isCallB m = false

theorem noCall_refl (s : LState) : NoCallSince s s := ⟨[], by simp, by simp⟩

theorem noCall_trans {a b c : LState} (h1 : NoCallSince a b) (h2 : NoCallSince b c) :
    NoCallSince a c := by
  obtain ⟨ms, g1, g2⟩ := h1
  obtain ⟨ms', g3, g4⟩ := h2
  refine ⟨ms ++ ms', by simp [g3, g1], fun m hm => ?_⟩
  rcases List.mem_append.mp hm with hm | hm
  · exact g2 m hm
  · exact g4 m hm

/-! ## Extern constructors and extractors -/

/-- A constructor's result holds no call data if its arguments hold none. -/
def CtorCP (args : List V) (r : ExtResult (V × LState)) : Prop :=
  ∀ v st', r = .ok (v, st') → vCInL args = false → vCIn v = false

set_option maxHeartbeats 4000000 in
/-- **Every extern constructor** builds no call data. -/
theorem externCtor_c (ctx : Ctx) (t : Term) (args : List V) (st : LState) :
    CtorCP args (externCtor ctx t args st) := by
  unfold externCtor
  split
  · intro v st' h
    split at h
    · cases h
      intro _
      rfl
    · cases h
  · apply externCtor_split _ (fun _ args r => CtorCP args r)
    all_goals
      intros
      unfold CtorCP
      intro v st' h hargs
      try dsimp only at h
      repeat' (split at h)
      all_goals try (cases h; done)
    all_goals cases h
    all_goals first
      | rfl
      | (simp_all [vCIn, vCInL]; done)
      | (simp_all (config := { decide := true }) [vCIn, vCInL, isCallV]; done)
      | (rename_i heq
         simp only [Option.map_eq_some_iff, Function.comp_apply] at heq
         obtain ⟨_, _, rfl⟩ := heq
         rfl)

/-- An extern constructor emits no call if its arguments hold no call data. -/
theorem ctor_noCall (ctx : Ctx) {term : Term} {vs : List V} {s : LState} {v : V} {s' : LState}
    (hargs : ∀ w ∈ vs, vCIn w = false) (h : (sem ctx).ctor term vs s = .ok (v, s')) :
    NoCallSince s s' := by
  rw [sem_ctor] at h
  obtain ⟨ms, h1, h2⟩ := Cov.externCtor_shp ctx term vs s v s' h
  refine ⟨ms, h1, fun m hm => ?_⟩
  cases hc : isCallB m with
  | false => rfl
  | true =>
    exfalso
    rcases h2 m hm with hn | ⟨-, i, rfl, hi⟩ | ⟨-, rss, ps, rs, -, -, -, rfl⟩
    · cases m <;> simp_all [isCallB, MInst.isCtl]
    · have := ofV_call_cIn hi hc
      rw [hargs i (by simp)] at this
      cases this
    · simp [isCallB] at hc

/-- The data of the context's instructions holds no call data. -/
def DataC (ctx : Ctx) : Prop :=
  ∀ (i : Nat) (info : IInfo), ctx.insts[i]? = some info → vCIn info.data = false

/-- An extractor's outputs hold no call data. -/
def ExtCP (r : ExtResult (List V)) : Prop :=
  ∀ fs, r = .ok fs → ∀ f ∈ fs, vCIn f = false

set_option maxHeartbeats 2000000 in
theorem externExtract_c {ctx : Ctx} (hd : DataC ctx) (t : Term) (v : V) (st : LState) :
    ExtCP (externExtract ctx t v st) := by
  unfold externExtract
  split
  · intro fs h
    split at h
    · cases h
      simp [vCIn]
    · cases h
  · intro fs h; cases h
  · apply externExtract_split _ (fun _ _ r => ExtCP r)
    all_goals
      intros
      unfold ExtCP
      intro fs h
      try dsimp only at h
      repeat' (split at h)
      all_goals try (cases h; done)
    all_goals cases h
    all_goals first
      | (simp (config := { decide := true }) [vCIn]; done)
      | (simp only [List.forall_mem_cons]
         exact ⟨rfl, hd _ _ ‹_›, fun _ h => by cases h⟩)

/-! ## The data of the driver's contexts -/

theorem cIn_mkVariant {ty : TypeId} {name : String} {fs : List V} (hty : ty ≠ tyMInst)
    (h : vCInL fs = false) : vCIn (mkVariant ty name fs) = false := by
  unfold mkVariant
  split
  · simp [vCIn, hty, h]
  · rfl

theorem cInL_nil' : vCInL [] = false := rfl

theorem cInL_cons' {v : V} {vs : List V} (h1 : vCIn v = false) (h2 : vCInL vs = false) :
    vCInL (v :: vs) = false := by simp [vCInL, h1, h2]

theorem cIn_int {i : Int} : vCIn (V.int i) = false := rfl
theorem cIn_value {x : Nat} : vCIn (V.value x) = false := rfl
theorem cIn_values {xs : List Nat} : vCIn (V.values xs) = false := rfl
theorem cIn_op {o : Opnd} : vCIn (V.op o) = false := rfl
theorem cIn_blockCalls {bs : List Nat} : vCIn (V.blockCalls bs) = false := rfl

/-- Build `vCIn = false` of an `instDataV` term. -/
macro "c_data" : tactic => `(tactic| (
  unfold instDataV opcodeV
  repeat' first
    | with_reducible apply cIn_mkVariant (by decide)
    | with_reducible exact cInL_nil'
    | with_reducible apply cInL_cons'
    | with_reducible exact cIn_int
    | with_reducible exact cIn_value
    | with_reducible exact cIn_values
    | with_reducible exact cIn_op
    | with_reducible exact cIn_blockCalls))

set_option maxRecDepth 20000 in
theorem instData_cIn {f : Clif.Function} {c : Clif.Inst} {d : V} (h : instData f c = .ok d) :
    vCIn d = false := by
  cases c <;> simp only [instData] at h
  all_goals (repeat' split at h)
  all_goals first
    | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h)
    | (simp only [pure, Except.pure, Except.ok.injEq] at h
       subst h
       c_data)

theorem termData_cIn {t : Clif.Terminator} {d : V} (h : termData t = .ok d) : vCIn d = false := by
  cases t <;> simp only [termData] at h
  all_goals first
    | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h)
    | (simp only [pure, Except.pure, Except.ok.injEq] at h
       subst h
       c_data)

theorem dataC_of_build {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {st0 : LState} (hb : buildCtx f = .ok (ctx, ranges, st0)) : DataC ctx := by
  have sp := ctxSpec_of hb
  intro i info hi
  rcases sp.insts info (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi)) with
    rfl | ⟨B, hB, s, hs, rfl⟩
  · rfl
  · obtain ⟨d, hd⟩ := ((sp.blockC B hB).2 s hs).1
    have hdo : (infoOf f s).data = d := by
      show dataOf f s = d
      unfold dataOf
      rw [hd]
    rw [hdo]
    exact instData_cIn hd

theorem dataC_termCtx {ctx : Ctx} (h : DataC ctx) {data : V} (hd : vCIn data = false)
    (ti : Nat) : DataC (termCtx ctx ti data) := by
  intro j info hj
  by_cases hji : j = ti
  · subst hji
    by_cases hlt : j < ctx.insts.size
    · have : (termCtx ctx j data).insts[j]? = some ⟨data, [], [], none⟩ := by
        show (ctx.insts.set! j _)[j]? = _
        rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hlt]
      rw [this] at hj
      cases hj
      exact hd
    · have : (termCtx ctx j data).insts = ctx.insts := by
        show ctx.insts.set! j _ = _
        rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds]
        simp [hlt]
      rw [this] at hj
      exact h j info hj
  · rw [termCtx_insts_ne hji] at hj
    exact h j info hj

/-! ## The term set -/

/-- Worklist closure under `Isle.ruleTerms` (`k`: fuel; the closure property is decided
afterwards). -/
def callClose : Nat → List TermId → Std.HashSet TermId → Std.HashSet TermId
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | k + 1, t :: ts, seen =>
    if seen.contains t then callClose k ts seen
    else callClose k ((program.rulesOf t).flatMap ruleTerms ++ ts) (seen.insert t)

/-- The `call`/`call_indirect` rules of `lower`. -/
def callExcl : List RuleId := [1031, 1032, 1033]

/-- The terms the root rules apply: those of `lower` but 1031–1033, and those of the
closure-root rules of `lower_branch`. -/
def callRoots : List TermId :=
  ((program.rulesOf TId.lower).filter fun r => !callExcl.contains r.id).flatMap ruleTerms ++
    ((program.rulesOf TId.lower_branch).filter fun r => closureRoot r).flatMap ruleTerms

/-- **The terms of non-call runs.** -/
def callTab : List TermId := (callClose 10000000 callRoots {}).toList

/-- A call site `(ty, t)` builds no `Call`/`CallInd` data. -/
def callSite (ty : TypeId) (t : TermId) : Prop :=
  ∀ term k, termOf program t = .ok term → term.kind = .enumVariant k →
    ¬(ty = tyMInst ∧ isCallV k = true)

/-- `callSite`, decided. -/
def callSiteB (ty : TypeId) (t : TermId) : Bool :=
  match program.term? t with
  | some term =>
    match term.kind with
    | .enumVariant k => !(ty == tyMInst && isCallV k)
    | _ => true
  | none => true

theorem callSite_of {ty : TypeId} {t : TermId} (h : callSiteB ty t = true) : callSite ty t := by
  intro term k ht hk ⟨hty, hkv⟩
  rw [callSiteB, Kill.termOf_program_eq ht] at h
  simp [hk, hty, hkv] at h

/-- A rule's terms are in `callTab` and its call sites build no call data. -/
def callRuleOkB (rl : Rule) : Bool :=
  (ruleTerms rl).all (callTab.contains ·) && (ruleTys rl).all fun q => callSiteB q.1 q.2

theorem callRuleOk_of {rl : Rule} (h : callRuleOkB rl = true) :
    (∀ u ∈ ruleTerms rl, u ∈ callTab) ∧ ∀ q ∈ ruleTys rl, callSite q.1 q.2 := by
  simp only [callRuleOkB, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨fun u hu => by simpa using h.1 u hu, fun q hq => callSite_of (h.2 q hq)⟩

theorem callTab_closedB : callTab.all (fun t => (program.rulesOf t).all callRuleOkB) = true := by
  native_decide

theorem callRootS_ok :
    (program.rulesOf TId.lower).all (fun rl => callExcl.contains rl.id || callRuleOkB rl) = true := by
  native_decide

theorem callRootB_ok :
    (program.rulesOf TId.lower_branch).all (fun rl => !closureRoot rl || callRuleOkB rl) = true := by
  native_decide

theorem callTab_closed : ∀ t ∈ callTab, ∀ rl ∈ program.rulesOf t,
    (∀ u ∈ ruleTerms rl, u ∈ callTab) ∧ ∀ q ∈ ruleTys rl, callSite q.1 q.2 :=
  fun t ht rl hrl =>
    callRuleOk_of (List.all_eq_true.mp (List.all_eq_true.mp callTab_closedB t ht) rl hrl)

/-! ## The model -/

/-- **The no-call model** of the driver's semantics in a context whose data holds no call
data, on `callTab`. -/
def callModel (ctx : Ctx) (hd : DataC ctx) : UModel program (sem ctx) where
  P := fun _ v => vCIn v = false
  Is := fun _ => True
  Rs := NoCallSince
  T := (· ∈ callTab)
  C := callSite
  O := fun _ => False
  rs_refl := noCall_refl
  rs_trans := fun _ _ _ => noCall_trans
  mono := fun _ _ _ _ _ _ h => h
  int := fun _ _ _ _ => rfl
  bool := fun _ _ _ => rfl
  prim := fun _ ty n c _ h => by
    simp only [sem] at h
    split at h
    · obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp h
      rfl
    · cases h
  mkd := fun _ ty t term k vs _ hC ht hk _ hvs => by
    show vCIn (.data ty k vs) = false
    simp only [vCIn, Bool.or_eq_false_iff, Bool.and_eq_false_iff]
    refine ⟨?_, vCInL_eq_false.mpr hvs⟩
    rcases hk with hk | ⟨-, rfl⟩
    · by_cases h : ty = tyMInst
      · exact .inr (by simpa using fun h' => hC term k ht hk ⟨h, h'⟩)
      · exact .inl (by simpa using h)
    · exact .inr rfl
  un := fun _ ty _ _ v k fs _ _ _ _ hv hu => by
    simp only [sem] at hu
    split at hu
    · split at hu
      · cases hu
        intro f hf
        simp only [vCIn, Bool.or_eq_false_iff] at hv
        exact vCInL_eq_false.mp hv.2 f hf
      · cases hu
    · cases hu
  ext := fun s _ term _ _ _ _ v fs _ _ _ _ _ h => externExtract_c hd term v s fs h
  ctor := fun s _ term _ _ _ vs v s' _ _ _ _ hvs h =>
    ⟨externCtor_c ctx term vs s v s' h (vCInL_eq_false.mpr hvs), trivial, ctor_noCall ctx hvs h⟩
  oracle := fun _ h => h.elim
  closed := fun t ht _ rl hrl => callTab_closed t ht rl hrl

theorem noCalls_of {s s' : LState} (h : NoCallSince s s') :
    ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧ NoTry ms ∧ NoCalls ms := by
  obtain ⟨ms, h1, h2⟩ := h
  refine ⟨ms, h1, fun c ti hm => ?_, fun c hm => ?_⟩
  · have := h2 _ hm
    simp [isCallB] at this
  · have := h2 _ hm
    simp [isCallB] at this

/-! ## The `call` rules match only `call`/`call_indirect` statements -/

theorem callFmt_inst {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {rl : Rule} {fT oT kf : Nat} (hq : rootOp rl = some (fT, oT))
    (hk : (match termOf program fT with | .ok t => t.kind == .enumVariant kf | .error _ => false) = true)
    {o : Nat}
    (ho : (match termOf program oT with | .ok t => t.kind == .enumVariant o | .error _ => false) = true)
    {m : Nat} {s0 s1 : LState × Array RuleId} {env : Isle.Interp.Env V}
    (hm : (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 = .ok (some env, s1)) :
    (variantNames 152)[kf]? = some (instNames inst).1 := by
  obtain ⟨tf, htf, hkf⟩ := kind_of hk
  obtain ⟨to, hto, hko⟩ := kind_of ho
  obtain ⟨info', fs, hi', hd⟩ := rootOp_match hq htf hkf hto hko hm
  rw [hi] at hi'
  cases hi'
  have hdat := hctx.data ii info inst hi hc
  rw [hd] at hdat
  exact (instData_inv_names hdat).1

theorem variantNames_Call : (variantNames 152)[VIdx.InstructionData.Call]? = some "Call" := rfl

theorem variantNames_CallIndirect :
    (variantNames 152)[VIdx.InstructionData.CallIndirect]? = some "CallIndirect" := rfl

/-- **The `call` rules 1031–1033** match only a `call`/`call_indirect` statement. -/
theorem call_nomatch {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hnc : ∀ fn args, inst ≠ .call fn args) (hni : ∀ sg callee args, inst ≠ .callIndirect sg callee args)
    {rl : Rule} (hrl : rl ∈ program.rulesOf TId.lower) (hid : callExcl.contains rl.id = true) :
    ∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠ .ok (some env, s1) := by
  intro m s0 env s1 hm
  simp only [callExcl, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
    beq_iff_eq] at hid
  have hcall : (instNames inst).1 = "Call" → False := fun h => by
    cases inst <;> simp [instNames] at h
    exact hnc _ _ rfl
  have hind : (instNames inst).1 = "CallIndirect" → False := fun h => by
    cases inst <;> simp [instNames] at h
    exact hni _ _ _ rfl
  rcases hid with h | h | h
  · rw [eq_of_mem_of_id lower_ids_nodup hrl mem_lower_2508 (by rw [h]; rfl)] at hm
    have := callFmt_inst hctx hi hc (rl := rule_lower_2508) (fT := 2453) (oT := 2292)
      (kf := VIdx.InstructionData.Call) (o := 8) rfl (by decide +kernel) (by decide +kernel) hm
    rw [variantNames_Call] at this
    exact hcall (Option.some.inj this).symm
  · rw [eq_of_mem_of_id lower_ids_nodup hrl mem_lower_2518 (by rw [h]; rfl)] at hm
    have := callFmt_inst hctx hi hc (rl := rule_lower_2518) (fT := 2453) (oT := 2292)
      (kf := VIdx.InstructionData.Call) (o := 8) rfl (by decide +kernel) (by decide +kernel) hm
    rw [variantNames_Call] at this
    exact hcall (Option.some.inj this).symm
  · rw [eq_of_mem_of_id lower_ids_nodup hrl mem_lower_2529 (by rw [h]; rfl)] at hm
    have := callFmt_inst hctx hi hc (rl := rule_lower_2529) (fT := 2454) (oT := 2293)
      (kf := VIdx.InstructionData.CallIndirect) (o := 9) rfl (by decide +kernel) (by decide +kernel) hm
    rw [variantNames_CallIndirect] at this
    exact hind (Option.some.inj this).symm

/-! ## The driver's runs -/

/-- **A statement that is no call**: its `lower` run emits no call and no `tryCall`. -/
theorem stmt_noCalls {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) (hd : DataC ctx)
    {ii : Nat} {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info)
    (hc : info.clif = some inst) (hnc : ∀ fn args, inst ≠ .call fn args)
    (hni : ∀ sg callee args, inst ≠ .callIndirect sg callee args) {s : LState} {out : Option V}
    {s' : LState} {tr : List RuleId} (h : runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr)) :
    NoCallSince s s' := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower] at ht
  cases ht
  have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
      ((∀ u ∈ ruleTerms rl, (callModel ctx hd).T u) ∧
        ∀ q ∈ ruleTys rl, (callModel ctx hd).C q.1 q.2) ∨
        False ∨ ∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠
          .ok (some env, s1) := by
    intro rl hrl
    cases hx : callExcl.contains rl.id with
    | true => exact .inr (.inr (call_nomatch hctx hi hc hnc hni hrl hx))
    | false =>
      have h := List.all_eq_true.mp callRootS_ok rl hrl
      rw [hx, Bool.false_or] at h
      exact .inl (callRuleOk_of h)
  exact (uRoot (callModel ctx hd) rfl (fun _ _ => False) (fun _ => False) data_program.t686
    term_686_kind rfl hrules (fun _ _ h => h.elim)
    (fun v hv => by simp only [List.mem_singleton] at hv; subst hv; rfl) trivial happ).2.1

/-- **A non-`try_call` terminator's run** emits no call and no `tryCall`. -/
theorem term_noCalls {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) (hd : DataC ctx)
    {ti : Nat} (hti : ti < ctx.insts.size) (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩)
    {t : Clif.Terminator} (hty : t.isTry = false) {data : V}
    (hdat : termData (abiTerm f t) = .ok data) {targets : List Label} {s : LState}
    {out : Option V} {s' : LState} {tr : List RuleId}
    (h : termCallF ctx ti data t targets s = .ok (out, s', tr)) : NoCallSince s s' := by
  have hctx' := ctxInv_termCtx hctx hph data
  have hslot := termCtx_self hti data
  have hd' : DataC (termCtx ctx ti data) := dataC_termCtx hd (termData_cIn hdat) ti
  unfold termCallF at h
  have hbranch : retOrTrap (abiTerm f t) = false →
      runTerm (termCtx ctx ti data) "lower_branch" [.inst ti, .labels targets] s = .ok (out, s', tr) →
      NoCallSince s s' := by
    intro hrt h
    obtain ⟨t', tr', ht, happ⟩ := runTerm_apply h
    rw [program_termByName_lower_branch] at ht
    cases ht
    have hrules : ∀ rl ∈ program.rulesOf T.lower_branch.id,
        ((∀ u ∈ ruleTerms rl, (callModel _ hd').T u) ∧
          ∀ q ∈ ruleTys rl, (callModel _ hd').C q.1 q.2) ∨ False ∨
          ∀ m s0 env s1, (matchRule program (sem (termCtx ctx ti data)) {} m rl
            [.inst ti, .labels targets]).run s0 ≠ .ok (some env, s1) := by
      intro rl hrl
      cases hcr : closureRoot rl with
      | false => exact .inr (.inr fun m s0 env s1 =>
          branchExcludedUnmatchable rl hrl hcr f _ hctx' ti _ data targets hrt hdat hslot {} m s0 env s1)
      | true =>
        have h := List.all_eq_true.mp callRootB_ok rl hrl
        rw [hcr, Bool.not_true, Bool.false_or] at h
        exact .inl (callRuleOk_of h)
    exact (uRoot (callModel _ hd') rfl (fun _ _ => False) (fun _ => False) data_program.t687
      term_687_kind rfl hrules (fun _ _ h => h.elim)
      (fun v hv => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl <;> rfl)
      trivial happ).2.1
  have hlower : retOrTrap (abiTerm f t) = true →
      runTerm (termCtx ctx ti data) "lower" [.inst ti] s = .ok (out, s', tr) →
      NoCallSince s s' := by
    intro hrt h
    obtain ⟨t', tr', ht, happ⟩ := runTerm_apply h
    rw [program_termByName_lower] at ht
    cases ht
    have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
        ((∀ u ∈ ruleTerms rl, (callModel _ hd').T u) ∧
          ∀ q ∈ ruleTys rl, (callModel _ hd').C q.1 q.2) ∨ False ∨
          ∀ m s0 env s1, (matchRule program (sem (termCtx ctx ti data)) {} m rl [.inst ti]).run s0 ≠
            .ok (some env, s1) := by
      intro rl hrl
      cases hroot : termRootRule rl with
      | false => exact .inr (.inr (lower_term_nomatch hrt hdat hslot hrl hroot))
      | true =>
        have h := List.all_eq_true.mp callRootS_ok rl hrl
        simp only [termRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
        have hx : callExcl.contains rl.id = false := by
          rcases hroot with e | e <;> simp [callExcl, e]
        rw [hx, Bool.false_or] at h
        exact .inl (callRuleOk_of h)
    exact (uRoot (callModel _ hd') rfl (fun _ _ => False) (fun _ => False) data_program.t686
      term_686_kind rfl hrules (fun _ _ h => h.elim)
      (fun v hv => by simp only [List.mem_singleton] at hv; subst hv; rfl) trivial happ).2.1
  cases t with
  | ret vs => exact hlower rfl h
  | trap c => exact hlower rfl h
  | jump bc => exact hbranch rfl h
  | brif c a b => exact hbranch rfl h
  | brTable x d tb => exact hbranch rfl h
  | returnCall fn args => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hdat
  | tryCall fn args et => simp [Clif.Terminator.isTry] at hty
  | tryCallIndirect callee args et => simp [Clif.Terminator.isTry] at hty

/-! ## `CallRunHyp` from the call statements' and the `try_call`s' runs -/

/-- **The remaining part of `CallRunHyp` for statements**: a `call`/`call_indirect`
statement's `lower` run emits no `tryCall` and only calls of that statement (`RunCall`). -/
def CallStmtRunHyp : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (st0 : LState),
    Dominated f → LowerScope f → Spill.AbiSigsOk f → buildCtx f = .ok (ctx, ranges, st0) →
    ∀ ii info inst s out s' tr, ctx.insts[ii]? = some info → info.clif = some inst →
      ((∃ fn args, inst = .call fn args) ∨ ∃ sg callee args, inst = .callIndirect sg callee args) →
      (∃ B ∈ f.blocks, ∃ st ∈ B.body, st.inst = inst) → ctx.valDef.size ≤ s.nextVreg →
      runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr) →
      ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧ NoTry ms ∧
        ∀ c, MInst.call c ∈ ms → RunCall f inst ctx.valDef.size ms c

/-- **The `try_call` part of `CallRunHyp`** (its third conjunct): a `try_call`'s
`lower_branch` run that returns a value (the driver's: `lowTerm_spec`; `lower_branch` is
partial, and a run committing to no rule emits nothing) emits the call of that terminator last
(`TryRunCall`) and no other call. -/
def TryRunHyp : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (st0 : LState),
    Dominated f → LowerScope f → Spill.AbiSigsOk f → buildCtx f = .ok (ctx, ranges, st0) →
    ∀ ti t et data sig items lo trs st1 targets (out : V) s' tr, ti < ctx.insts.size →
      ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → IsTryWith t et →
      (∃ B ∈ f.blocks, B.term = t) →
      tryCallData f t = .ok data → exnTableOpnd f et = .ok (sig, items) →
      ctx.valDef.size ≤ lo.nextVreg → tryRegsOf sig lo = some (trs, st1) →
      tryCallF ctx ti data trs targets { st1 with emitted := #[] } = .ok (some out, s', tr) →
      ∃ (ms : List MInst) (c : CallInfo), s'.emitted = (ms ++ [MInst.call c]).toArray ∧
        NoTry ms ∧ NoCalls ms ∧ TryRunCall f t ctx.valDef.size (ms ++ [MInst.call c]) c

/-- **`CallRunHyp`** from its call-statement and `try_call` parts: the other statements and the
non-`try_call` terminators emit no call (`stmt_noCalls`, `term_noCalls`). -/
theorem callRunHyp_of (hC : CallStmtRunHyp) (hT : TryRunHyp) : CallRunHyp := by
  intro f ctx ranges st0 hd hs ha hb
  have hctx : CtxInv f ctx := ctxOk_sound (ctxOk_complete hs hb)
  have hdc := dataC_of_build hb
  refine ⟨fun ii info inst s out s' tr hi hc hmem hN h => ?_,
    fun ti t data targets s out s' tr hti hph hty hdat _ h =>
      noCalls_of (term_noCalls hctx hdc hti hph hty hdat h),
    hT f ctx ranges st0 hd hs ha hb⟩
  by_cases hcall : (∃ fn args, inst = .call fn args) ∨
      ∃ sg callee args, inst = .callIndirect sg callee args
  · exact hC f ctx ranges st0 hd hs ha hb ii info inst s out s' tr hi hc hcall hmem hN h
  · obtain ⟨ms, h1, h2, h3⟩ := noCalls_of (stmt_noCalls hctx hdc hi hc
      (fun fn args e => hcall (.inl ⟨fn, args, e⟩))
      (fun sg callee args e => hcall (.inr ⟨sg, callee, args, e⟩)) h)
    exact ⟨ms, h1, h2, fun c hm => (h3 c hm).elim⟩

end E2E.LinkCheck
