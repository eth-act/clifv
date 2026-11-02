import FV.Backend.Proof.LowerContract
import FV.Backend.Proof.DriverCheckTy
import FV.Backend.Proof.IselExclT
import FV.Backend.Proof.IselTermIntPos
import FV.Compile.StoreTyped
import FV.Backend.Proof.InstScopeTF

/-!
# The typed lowering contracts (S11e5 Stage C, slice 7)

The integer M4 obligations (`LowerRulesCorrect`, `MemRulesCorrect`, `CallRulesCorrect`, …,
`IselContract.lean`) quantify over the contexts of subset-E functions (`CtxInv`: every value an
`i8..i64` in an X register). A function of the typed movement scope (`Compile.functionET`) has a
float-capable context: `CtxInvT` (class-aware vregs, `f32`/`f64` values, integer operands in
integer positions), `InstScopeT` (its instructions in `Compile.instET`), the callees of its
`call` statements with integer signatures (`CallsE`). This file states the obligations over such
contexts (`CtxT`), for the integer
instructions of a mixed context; the float families already proven over `CtxInvT`
(`LowerRulesCorrectT`, `MemRulesCorrectRT`, `LowerRulesCorrectFT`) are reused unchanged.

* `CtxT f ctx`: `CtxInvT f ctx ∧ InstScopeTF ctx ∧ CallsE f ctx` (`CtxInv.toCtxT`; integer
  externs give `CallsE`, `CtxT.ofExterns`). S11e6: until then the third field was
  `f.externs.all sigE`; the proofs only use it for the `call` statements, and a `try_call`'s
  callee may have float parameters and returns (`IselCtlTryF`), so the field is the weaker
  `CallsE` (every family over `CtxT` is stronger). S11f: until then the second field was
  `InstScopeT`; the rule families' proofs never read it, so it is the weaker `InstScopeTF` (the
  S11f float arithmetic, rounding and conversions among the instructions, `Compile.instETF`):
  every family over `CtxT` is stronger. The statements whose truth depends on the instructions
  (`NonEUnmatchableT`, the dispatchers `lowerInstOk_of_rulesT`, `lowerInstOk_runTermT`,
  `instCallsT_of_rules`) take `InstScopeT ctx` explicitly, so their meaning is unchanged; the
  dispatchers over `InstScopeTF` are `LowerContractTF.lean`'s.
* Statements, on the subset-E instructions (`Compile.instE`) of a typed context:
  `LowerRuleOkTX`, `LowerRulesCorrectTI` (the integer `lower` roots: closure roots that are not
  call, indirect-call, memory, float-movement or float-arithmetic roots), `MemRuleOkRTX`,
  `MemRulesCorrectRTI` (the integer memory roots), `CallRuleOkT`/`CallRulesCorrectT`,
  `IndRuleOkT`/`IndRulesCorrectT`; on the other instructions of the typed scope only the float
  roots (and the float arm of `select`) match (`NonEUnmatchableT`).
* Terminators: `LowerTermOkT` is `LowerTermOk` whose `return` puts the returned values in their
  class's ABI return registers (`retRegsT`: x0.. for integers, v0.. for floats, separate
  counters); `LowerTermRuleOkT`/`LowerTermRulesCorrectT`, `TermUnmatchableT`;
  `BranchRuleOkT`/`BranchRulesCorrectT`, `BranchExcludedUnmatchableT` (branches: `LowerTermOk`);
  `TryRuleOkT`/`TryRulesCorrectT`, `TryUnmatchableT`, `TryIndRuleOkT`/`TryIndRulesCorrectT`,
  `TryIndUnmatchableT` (`LowerTryOk`: calls are integer-only in the typed scope).
* The driver's calls for one context: `InstCallsT`, `TermCallsT`, `TryCallsT`, `TryIndCallsT`.

Integer specializations: `CtxInv.toCtxT`, `LowerTermOk.toT` (on an integer context),
`retRegsT_int`.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64 Backend.Proof.Driver

/-! ## Float-capable rule contexts -/

/-- **The context premise of the typed obligations**: a float-capable lowering context
(`CtxInvT`), its instructions in the typed scope with the proven float operations
(`InstScopeTF`; weakened from `InstScopeT` in S11f), and the callees of its `call` statements
with integer signatures (`CallsE`: the statement calls are integer-only; the callee of a
`try_call` terminator is not constrained). -/
structure CtxT (f : Clif.Function) (ctx : Ctx) : Prop where
  inv : CtxInvT f ctx
  scope : InstScopeTF ctx
  calls : CallsE f ctx

/-- A typed context of a function with integer externs (`Compile.functionET`). -/
theorem CtxT.ofExterns {f : Clif.Function} {ctx : Ctx} (hinv : CtxInvT f ctx)
    (hsc : InstScopeT ctx) (hx : f.externs.all (Compile.sigE ·.2.sig) = true) : CtxT f ctx :=
  ⟨hinv, hsc.toTF, callsE_of_externs hx ctx⟩

/-- **Integer specialization**: a subset-E context is a typed one. -/
theorem CtxInv.toCtxT {f : Clif.Function} {ctx : Ctx} (h : CtxInv f ctx)
    (hE : Compile.functionE f = true) : CtxT f ctx := by
  refine CtxT.ofExterns h.toT h.instScopeT ?_
  simp only [Compile.functionE, Bool.and_eq_true] at hE
  exact hE.1.2

/-- The externs of a subset-E function have integer signatures (the fact `CtxInv.toCtxT`'s
`CtxT` carried before S11e6). -/
theorem CtxInv.toCtxT_externsE {f : Clif.Function} (hE : Compile.functionE f = true) :
    f.externs.all (Compile.sigE ·.2.sig) = true := by
  simp only [Compile.functionE, Bool.and_eq_true] at hE
  exact hE.1.2

/-- The externs of a function of the typed scope have integer signatures. -/
theorem functionET_externs {f : Clif.Function} (h : Compile.functionET f = true) :
    f.externs.all (Compile.sigE ·.2.sig) = true := by
  simp only [Compile.functionET, Bool.and_eq_true] at h
  exact h.1.1.1.2

/-! ## Statements -/

/-- A `select` of floats (the float arm of the shared `select` root 971, `LowerRulesCorrectT`). -/
def FloatSelect (i : Clif.Inst) : Prop := ∃ ty c x y, i = .select ty c x y ∧ ty.isFloat = true

/-- **Root rule correctness over typed contexts** (`LowerRuleOk` with `CtxT`), for the
instructions satisfying `P`. -/
def LowerRuleOkTX (P : Clif.Inst → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (p : Program) (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxT f ctx → ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst),
  ctx.insts[ii]? = some info → info.clif = some inst → P inst →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n → ValsBelow ctx st →
    (∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ii]).run (st, tr) = .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ii]).run (st, tr) = .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx inst info.results st rss st' ms

/-- `LowerRuleOkTP` (over `CtxInvT` alone) gives `LowerRuleOkTX` (more premises). -/
theorem LowerRuleOkTP.toTX {P : Clif.Inst → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} {p : Program} {r : Rule} (h : LowerRuleOkTP P isem MR env cp p r) :
    LowerRuleOkTX P isem MR env cp p r :=
  fun f ctx hctx => h f ctx hctx.inv

/-- **The integer `lower` roots over typed contexts** (FloatsC7F): every closure root of
`lower` that is not a call (`callRootRule`), indirect-call (`indRootRule`), memory
(`memRootRule`), float-movement (`floatMoveRootRule`) or float-arithmetic
(`floatArithRootRule`) root is correct on the subset-E instructions (`Compile.instE`) of a
typed context (the shared `select` root 971 thus on integer `select`s; its float arm is
`LowerRulesCorrectT`'s). The other instructions of the typed scope: `NonEUnmatchableT`. -/
def LowerRulesCorrectTI (p : Program) : Prop :=
  ∀ (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program),
    Refines F isem → MRStable F MR →
    ∀ r ∈ p.rulesOf TId.lower, closureRoot r = true → callRootRule r = false →
      indRootRule r = false → memRootRule r = false → floatMoveRootRule r = false →
      floatArithRootRule r = false →
      LowerRuleOkTX (fun i => Compile.instE i = true) isem MR env cp p r

/-- The CLIF verifier's typing of a float `store`: the stored value has a float type. -/
def StoreTyped (ctx : Ctx) (i : Clif.Inst) : Prop :=
  ∀ op ty fl x q off, i = .store op ty fl x q off → ty.isFloat = true →
    ∀ t, ctx.valueType? x = some t → t ∈ fTys

/-- Every instruction of the context is store-typed (`StoreTyped`; from `Compile.storeTypedB`,
`storesTyped_of_buildCtx`). -/
def StoresTyped (ctx : Ctx) : Prop :=
  ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info →
    info.clif = some inst → StoreTyped ctx inst

/-- A subset-E instruction is store-typed (it stores only integer types). -/
theorem storeTyped_of_instE {ctx : Ctx} {i : Clif.Inst} (h : Compile.instE i = true) :
    StoreTyped ctx i := by
  intro op ty fl x q off hi hf
  subst hi
  simp only [Compile.instE, Bool.and_eq_true] at h
  rw [Compile.isFloat_of_tyE h.1] at hf
  cases hf

/-- **Integer specialization**: a subset-E context is store-typed. -/
theorem CtxInv.storesTyped {f : Clif.Function} {ctx : Ctx} (h : CtxInv f ctx) : StoresTyped ctx :=
  fun ii info inst hi hc => storeTyped_of_instE (h.instE ii info inst hi hc)

/-- **Soundness of `Compile.storeTypedB` for `buildCtx`'s context**: a value a float `store`
stores has, in the context, a float type (`CtxSpec.class_of_argClassOk`: every definition of it
is a float). -/
theorem storesTyped_of_buildCtx {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {st0 : LState} (hT : Compile.storeTypedB f = true) (hb : buildCtx f = .ok (ctx, ranges, st0)) :
    StoresTyped ctx := by
  have sp := ctxSpec_of hb
  intro ii info inst hi hc op ty fl x q off hinst hf t ht
  obtain ⟨B, hB, s, hs, -, rfl⟩ := sp.inst_of hi hc
  have hvt : valTyOk ty = true := by cases ty <;> simp_all [valTyOk]
  have hcl := sp.class_of_argClassOk
    (Compile.storeTypedB_sound hT B hB s hs op ty fl x q off hinst hf) hvt t ht
  rcases sp.tyOf x t ht with ⟨B', hB', ⟨v, ty'⟩, hq', -, rfl⟩ |
    ⟨B', hB', s', hs', m, ty', -, hty, rfl⟩
  · have hv' : valTyOk ty' = true := (sp.blockC B' hB').1 _ hq'
    revert hcl hv' hf
    cases ty' <;> cases ty <;> simp [valTyOk, eTy, Clif.Ty.isInt, Clif.Ty.isFloat, CTy.ofClif,
      CTy.valClass, CTy.regClass?, fTys]
  · have hv' : valTyOk ty' = true := ((sp.blockC B' hB').2 s' hs').2.2 ty' (List.mem_of_getElem? hty)
    revert hcl hv' hf
    cases ty' <;> cases ty <;> simp [valTyOk, eTy, Clif.Ty.isInt, Clif.Ty.isFloat, CTy.ofClif,
      CTy.valClass, CTy.regClass?, fTys]

/-- The integer operands of a typed-scope function's terminators are in integer positions of
`buildCtx`'s context (`termIntPos_of` from `Compile.functionET` alone). -/
theorem termIntPos_of_functionET {f : Clif.Function} (hT : Compile.functionET f = true)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (hb : buildCtx f = .ok (ctx, ranges, st0)) {B : Clif.Block} (hB : B ∈ f.blocks) :
    TermIntPos ctx B.term := by
  intro x hx t ht
  refine (ctxSpec_of hb).eCTys_of_not_floatDef ht fun hfd => ?_
  simp only [Compile.functionET, Compile.opsTypedT, Bool.and_eq_true, List.all_eq_true] at hT
  have := (hT.1.2 B hB).2 x hx
  simp [hfd] at this

/-- `abiTerm` changes only `return`s, which have no integer-position operands. -/
theorem termIntPos_abiTerm {ctx : Ctx} {f : Clif.Function} {t : Clif.Terminator}
    (h : TermIntPos ctx t) : TermIntPos ctx (abiTerm f t) := by
  cases t <;> first | exact h | (intro x hx; simp [abiTerm, Compile.termIntOperands] at hx)

/-- **The closure roots of `lower` other than the float ones never match a non-E instruction
of a typed context** (FloatsC7F): on an instruction of the typed scope outside subset E (a float
constant, `load`/`store` of a float, a `select` of floats, a `bitcast`), the first matching
closure root is a float-movement, float-memory or float-arithmetic root, or the `select` root
971 on a float `select`. The integer `store` roots dispatch on the stored value's type, so a
float `store` is assumed store-typed (`StoreTyped`). Stated with the lowering's premise that the
rules before `r` failed, for contexts whose instructions are in the typed movement scope
(`InstScopeT`, explicit since `CtxT.scope` is the weaker `InstScopeTF`: the statement is the one
before S11f). -/
def NonEUnmatchableT (p : Program) : Prop :=
  ∀ r ∈ p.rulesOf TId.lower, closureRoot r = true → floatMoveRootRule r = false →
    floatMemRootRule r = false → floatArithRootRule r = false →
  ∀ (f : Clif.Function) (ctx : Ctx), CtxT f ctx → InstScopeT ctx →
  ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info →
    info.clif = some inst → Compile.instE inst = false → (r.id = 971 → ¬ FloatSelect inst) →
    StoreTyped ctx inst →
  ∀ (cfg : Config) (m : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V)
    (s1 : LState × Array RuleId),
    (∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ii]).run (st, tr) = .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ii]).run (st, tr) ≠ .ok (some env', s1)

/-- `MemRuleOkR` over typed contexts, on the subset-E instructions. -/
def MemRuleOkRTX (Rd : BitVec 64 → Prop) (F : BitVec 64 → Prop) (sb : Nat)
    (syms : String → Option Nat) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (p : Program) (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxT f ctx → MemRelOk F sb syms f MR →
  ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info → info.clif = some inst →
  Compile.instE inst = true →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n → ValsBelow ctx st →
    (∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ii]).run (st, tr) = .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ii]).run (st, tr) = .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOkR Rd isem MR env cp ctx inst info.results st rss st' ms

/-- **The integer memory roots over typed contexts** (FloatsC7F; `MemRulesCorrectR` with
`CtxT`): every memory root that is not a float memory root (`floatMemRootRule`, proven in
`MemRulesCorrectRT`) is correct under `MemRefinesR Rd`, on the subset-E instructions. -/
def MemRulesCorrectRTI (p : Program) : Prop :=
  ∀ (Rd : BitVec 64 → Prop) (F : BitVec 64 → Prop) (sb : Nat) (syms : String → Option Nat)
    (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program),
    Refines F isem → MRStable F MR → MemRefinesR Rd F sb syms isem →
    ∀ r ∈ p.rulesOf TId.lower, memRootRule r = true → floatMemRootRule r = false →
      MemRuleOkRTX Rd F sb syms isem MR env cp p r

/-- `CallRuleOk` over typed contexts, on the subset-E instructions. -/
def CallRuleOkT (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (exts : List Clif.ExtFunc) (outB : Nat) (p : Program) (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxT f ctx → ExternsIn f exts →
  ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info → info.clif = some inst →
  Compile.instE inst = true →
  (∀ fn args e, inst = .call fn args → f.extern? fn = some e → SigStackOk e.sig outB) →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n → ValsBelow ctx st →
    (∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ii]).run (st, tr) = .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ii]).run (st, tr) = .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx inst info.results st rss st' ms

/-- **The call roots over typed contexts** (FloatsC7F; `CallRulesCorrect` with `CtxT`). -/
def CallRulesCorrectT (p : Program) : Prop :=
  ∀ (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (exts : List Clif.ExtFunc) (sb : Nat) (syms : String → Option Nat) (outB : Nat),
    Refines F isem → MRStable F MR → MemRefines F sb syms isem → OutArgsOk F outB MR →
    CallsRefine F env exts MR isem →
    ∀ r ∈ p.rulesOf TId.lower, callRootRule r = true → CallRuleOkT isem MR env cp exts outB p r

/-- `IndRuleOk` over typed contexts, on the subset-E instructions. -/
def IndRuleOkT (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (sigs : List Clif.Signature) (p : Program) (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxT f ctx →
  ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info → info.clif = some inst →
  Compile.instE inst = true → IndSigOk f sigs inst →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n → ValsBelow ctx st →
    (∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ii]).run (st, tr) = .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ii]).run (st, tr) = .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx inst info.results st rss st' ms

/-- **The `call_indirect` root over typed contexts** (FloatsC7F; `IndRulesCorrect` with
`CtxT`). -/
def IndRulesCorrectT (p : Program) : Prop :=
  ∀ (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (sigs : List Clif.Signature),
    Refines F isem → MRStable F MR → IndCallsRefine env sigs MR isem →
    ∀ r ∈ p.rulesOf TId.lower, indRootRule r = true → IndRuleOkT isem MR env cp sigs p r

/-! ## Terminators -/

/-- **The ABI return registers of values of the given classes** (`retRegsC` without its
8-register bound): an integer in the next X register, a float in the next V register, from
`x nx` and `v nv`. -/
def retRegsT : List RegClass → Nat → Nat → List Reg
  | [], _, _ => []
  | .int :: cs, nx, nv => .x nx :: retRegsT cs (nx + 1) nv
  | .float :: cs, nx, nv => .v nv :: retRegsT cs nx (nv + 1)

theorem retRegsT_length : ∀ (cs : List RegClass) (nx nv : Nat), (retRegsT cs nx nv).length = cs.length
  | [], _, _ => rfl
  | .int :: cs, nx, nv => by simp [retRegsT, retRegsT_length cs]
  | .float :: cs, nx, nv => by simp [retRegsT, retRegsT_length cs]

/-- **Integer specialization**: integer values return in x0, x1, …. -/
theorem retRegsT_int : ∀ (n nx nv : Nat),
    retRegsT (List.replicate n .int) nx nv = (List.range' nx n).map Reg.x
  | 0, _, _ => rfl
  | n + 1, nx, nv => by
    simp only [List.replicate_succ, retRegsT, List.range'_succ, List.map_cons, retRegsT_int n]

/-- `retRegsC` (the lowering's return registers, within the register bound) is `retRegsT`. -/
theorem retRegsC_eq : ∀ (cs : List RegClass) (nx nv : Nat) (rs : List Reg),
    retRegsC cs nx nv = some rs → rs = retRegsT cs nx nv
  | [], _, _, rs, h => by simp [retRegsC] at h; subst h; rfl
  | .int :: cs, nx, nv, rs, h => by
    simp only [retRegsC] at h
    split at h
    · obtain ⟨rs', h1, rfl⟩ := Option.map_eq_some_iff.mp h
      simp [retRegsT, retRegsC_eq cs _ _ rs' h1]
    · cases h
  | .float :: cs, nx, nv, rs, h => by
    simp only [retRegsC] at h
    split at h
    · obtain ⟨rs', h1, rfl⟩ := Option.map_eq_some_iff.mp h
      simp [retRegsT, retRegsC_eq cs _ _ rs' h1]
    · cases h

/-- **`lower` on `return`/`trap`, `lower_branch` on a branch, typed** (`LowerTermOk` whose
`return` puts each returned value `x` in the next ABI return register of its context class
`valClassOf ctx x`, `retRegsT`). -/
structure LowerTermOkT {W : Type} (isem : ISem CV W) (MR : MemRelTW W) (ctx : Ctx)
    (t : Clif.Terminator)
    (targets : List Label) (st st' : LState) (ms : List MInst) : Prop where
  mono : st.nextVreg ≤ st'.nextVreg
  defs : ∀ m ∈ ms, ∀ d ∈ vdefs m, st.nextVreg ≤ d ∧ d < st'.nextVreg
  run : ∀ (fr : Clif.Frame) (cm : Clif.Mem) (ρ : Nat → CV) (w : W),
    fr.func = ctx.func → ValsHeld fr ρ → DFGCons ctx fr → MR fr.slots cm w →
    match t with
    | .ret xs => ∀ vals, fr.getMany xs = .ok vals → UsesOk st fr ms ∧
        ∃ k us ops ρ₁ w₁ outs w₂,
          seqRun isem ms ρ w = some (.stop k (.rets us) ops ρ₁ w₁ outs w₂ .ret) ∧
          us.map (·.2) = retRegsT (xs.map (valClassOf ctx)) 0 0 ∧ us.length = vals.length ∧
          AllHold vals (vuses ops ρ₁) ∧ MR fr.slots cm w₂
    | .trap c => UsesOk st fr ms ∧ ∃ k i ops ρ₁ w₁ outs w₂,
        seqRun isem ms ρ w = some (.stop k i ops ρ₁ w₁ outs w₂ .halt) ∧ trapCode? i = some c
    | t => (∀ i, ms.getLast? = some i → i.targets = targets) ∧ ∀ j, branchIdx fr t = .ok j →
        UsesOk st fr ms ∧ ∃ k i ops ρ₁ w₁ outs w₂,
          seqRun isem ms ρ w = some (.stop k i ops ρ₁ w₁ outs w₂ (.goto j)) ∧ k + 1 = ms.length ∧
          MR fr.slots cm w₂

/-- A getMany's results are one per value. -/
theorem getMany_length {fr : Clif.Frame} :
    ∀ {xs : List Clif.ValueId} {vals : List Clif.Val}, fr.getMany xs = .ok vals →
      vals.length = xs.length
  | [], vals, h => by simp only [Clif.Frame.getMany, Clif.Res.ok.injEq] at h; subst h; rfl
  | x :: xs, vals, h => by
    simp only [Clif.Frame.getMany, Clif.Frame.get] at h
    cases hx : fr.regs x with
    | none => rw [hx] at h; simp [Clif.Res.ofOption] at h
    | some v =>
      rw [hx] at h
      simp only [Clif.Res.ofOption_some, Clif.Res.ok_bind] at h
      cases hr : fr.getMany xs with
      | ok vs0 =>
        rw [hr] at h
        simp only [Clif.Res.ok_bind, Clif.Res.pure_eq, Clif.Res.ok.injEq] at h
        subst h
        simp [getMany_length hr]
      | trap => rw [hr] at h; cases h
      | stuck => rw [hr] at h; cases h

/-- A branch's (or trap's) `LowerTermOk` is a `LowerTermOkT`. -/
theorem LowerTermOk.toT_of_not_ret {W : Type} {isem : ISem CV W} {MR : MemRelTW W} {ctx : Ctx}
    {t : Clif.Terminator} {targets : List Label} {st st' : LState} {ms : List MInst}
    (h : LowerTermOk isem MR ctx t targets st st' ms) (ht : ∀ xs, t ≠ .ret xs) :
    LowerTermOkT isem MR ctx t targets st st' ms := by
  refine ⟨h.mono, h.defs, fun fr cm ρ w hf hv hd hmr => ?_⟩
  have := h.run fr cm ρ w hf hv hd hmr
  cases t with
  | ret xs => exact absurd rfl (ht xs)
  | _ => exact this

/-- **Integer specialization**: on a context whose values are all integer-classed (an integer
context, `CtxE`), `LowerTermOk` is `LowerTermOkT`. -/
theorem LowerTermOk.toT {W : Type} {isem : ISem CV W} {MR : MemRelTW W} {ctx : Ctx}
    {t : Clif.Terminator} {targets : List Label} {st st' : LState} {ms : List MInst}
    (h : LowerTermOk isem MR ctx t targets st st' ms) (hE : ∀ x, valClassOf ctx x = .int) :
    LowerTermOkT isem MR ctx t targets st st' ms := by
  refine ⟨h.mono, h.defs, fun fr cm ρ w hf hv hd hmr => ?_⟩
  have := h.run fr cm ρ w hf hv hd hmr
  cases t with
  | ret xs =>
    intro vals hg
    obtain ⟨hU, k, us, ops, ρ₁, w₁, outs, w₂, h1, h2, h3, h4, h5⟩ := this vals hg
    refine ⟨hU, k, us, ops, ρ₁, w₁, outs, w₂, h1, ?_, h3, h4, h5⟩
    have hm : xs.map (valClassOf ctx) = List.replicate xs.length .int := by
      rw [List.eq_replicate_iff]; simp [hE]
    rw [hm, retRegsT_int, h2, h3, getMany_length hg, List.range_eq_range']
  | _ => exact this

/-- The return registers of an integer context are `x0, x1, …`. -/
theorem valClassOf_int_of_ctxE {ctx : Ctx} (hE : CtxE ctx) : ∀ x, valClassOf ctx x = .int :=
  Driver.valClassOf_int hE

/-- **Root rule correctness (`lower`, terminators) over typed contexts**: whenever rule `r`
matches the `return`/`trap` at `ti` of a typed context, the code it appended satisfies
`LowerTermOkT`. -/
def LowerTermRuleOkT (isem : Sem) (MR : MemRelT) (p : Program) (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxT f ctx →
  ∀ (ti : Nat) (t : Clif.Terminator) (data : V), retOrTrap t = true → termData t = .ok data →
  ctx.insts[ti]? = some ⟨data, [], [], none⟩ →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n → ValsBelow ctx st →
    (∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ti]).run (st, tr) = .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ti]).run (st, tr) = .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧ LowerTermOkT isem MR ctx t [] st st' ms

/-- **The terminator roots of `lower` over typed contexts** (FloatsC7F): `trap` (964) and the
class-aware `return` (1037). -/
def LowerTermRulesCorrectT (p : Program) : Prop :=
  ∀ (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT), Refines F isem → MRStable F MR →
    ∀ r ∈ p.rulesOf TId.lower, termRootRule r = true → LowerTermRuleOkT isem MR p r

/-- The other rules of `lower` never match a `return`/`trap` of a typed context. -/
def TermUnmatchableT (p : Program) : Prop :=
  ∀ r ∈ p.rulesOf TId.lower, termRootRule r = false →
  ∀ (f : Clif.Function) (ctx : Ctx), CtxT f ctx →
  ∀ (ti : Nat) (t : Clif.Terminator) (data : V), retOrTrap t = true → termData t = .ok data →
  ctx.insts[ti]? = some ⟨data, [], [], none⟩ →
  ∀ (cfg : Config) (m : Nat) (s : LState × Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId),
    (matchRule p (sem ctx) cfg m r [.inst ti]).run s ≠ .ok (some env', s1)

/-- **Root rule correctness (`lower_branch`) over typed contexts** (`BranchRuleOk` with
`CtxT`; the branch clauses of `LowerTermOk` are class-independent). -/
def BranchRuleOkT (isem : Sem) (MR : MemRelT) (p : Program) (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxT f ctx →
  ∀ (ti : Nat) (t : Clif.Terminator) (data : V) (targets : List Label), termData t = .ok data →
  ctx.insts[ti]? = some ⟨data, [], [], none⟩ → BrIdxTyped ctx t → TermIntPos ctx t →
  TargetsLen t targets →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n → ValsBelow ctx st →
    (∀ pre post, p.rulesOf TId.lower_branch = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ti, .labels targets]).run (st, tr) =
        .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ti, .labels targets]).run (st, tr) =
      .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧ LowerTermOk isem MR ctx t targets st st' ms

/-- **The closure roots of `lower_branch` over typed contexts** (FloatsC7F). -/
def BranchRulesCorrectT (p : Program) : Prop :=
  ∀ (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT),
    Refines F isem → MRStable F MR →
    ∀ r ∈ p.rulesOf TId.lower_branch, closureRoot r = true → BranchRuleOkT isem MR p r

/-- The root rules of `lower_branch` outside the closure never match a branch of a typed
context. -/
def BranchExcludedUnmatchableT (p : Program) : Prop :=
  ∀ r ∈ p.rulesOf TId.lower_branch, closureRoot r = false →
  ∀ (f : Clif.Function) (ctx : Ctx), CtxT f ctx →
  ∀ (ti : Nat) (t : Clif.Terminator) (data : V) (targets : List Label), retOrTrap t = false →
  termData t = .ok data → ctx.insts[ti]? = some ⟨data, [], [], none⟩ →
  ∀ (cfg : Config) (m : Nat) (s : LState × Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId),
    (matchRule p (sem ctx) cfg m r [.inst ti, .labels targets]).run s ≠ .ok (some env', s1)

/-- `TryRuleOk` over typed contexts. -/
def TryRuleOkT (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (exts : List Clif.ExtFunc) (outB : Nat) (p : Program) (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxT f ctx → ExternsIn f exts →
  ∀ (ti : Nat) (fn : Clif.FnRef) (args : List Nat) (et : Clif.ExnTable) (data : V)
    (sig : Clif.Signature) (items : List (Option Nat)) (targets : List Label) (info : TryInfo)
    (lo st1 : LState),
  (∀ e, f.extern? fn = some e → SigStackOk e.sig outB) →
  tryCallData f (.tryCall fn args et) = .ok data → TermIntPos ctx (.tryCall fn args et) →
  exnTableOpnd f et = .ok (sig, items) →
  ctx.insts[ti]? = some ⟨data, [], [], none⟩ → tryInfoOf sig items targets = some info →
  tryRegsOf sig lo = some (ctx.tryRegs, st1) → ValsBelow ctx lo →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n →
    st1.nextVreg ≤ st.nextVreg →
    (∀ pre post, p.rulesOf TId.lower_branch = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ti, .labels targets]).run (st, tr) =
        .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ti, .labels targets]).run (st, tr) =
      .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧
      LowerTryOk isem MR env cp ctx (.call fn args) info st st' ms

/-- **The `try_call` roots of `lower_branch` over typed contexts** (FloatsC7F). -/
def TryRulesCorrectT (p : Program) : Prop :=
  ∀ (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (exts : List Clif.ExtFunc) (sb : Nat) (syms : String → Option Nat) (outB : Nat),
    Refines F isem → MRStable F MR → MemRefines F sb syms isem → OutArgsOk F outB MR →
    CallsRefine F env exts MR isem →
    ∀ r ∈ p.rulesOf TId.lower_branch, tryRootRule r = true → TryRuleOkT isem MR env cp exts outB p r

/-- The other rules of `lower_branch` never match a `try_call` of a typed context. -/
def TryUnmatchableT (p : Program) : Prop :=
  ∀ r ∈ p.rulesOf TId.lower_branch, tryRootRule r = false →
  ∀ (f : Clif.Function) (ctx : Ctx), CtxT f ctx →
  ∀ (ti : Nat) (fn : Clif.FnRef) (args : List Nat) (et : Clif.ExnTable) (data : V)
    (targets : List Label),
  tryCallData f (.tryCall fn args et) = .ok data → ctx.insts[ti]? = some ⟨data, [], [], none⟩ →
  ∀ (cfg : Config) (m : Nat) (s : LState × Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId),
    (matchRule p (sem ctx) cfg m r [.inst ti, .labels targets]).run s ≠ .ok (some env', s1)

/-- `TryIndRuleOk` over typed contexts. -/
def TryIndRuleOkT (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (sigs : List Clif.Signature) (p : Program) (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxT f ctx →
  ∀ (ti : Nat) (callee : Nat) (args : List Nat) (et : Clif.ExnTable) (data : V)
    (sig : Clif.Signature) (items : List (Option Nat)) (targets : List Label) (info : TryInfo)
    (lo st1 : LState),
  tryCallData f (.tryCallIndirect callee args et) = .ok data →
  TermIntPos ctx (.tryCallIndirect callee args et) →
  exnTableOpnd f et = .ok (sig, items) → sig ∈ sigs → sig.params.length ≤ 8 →
  ctx.insts[ti]? = some ⟨data, [], [], none⟩ → tryInfoOf sig items targets = some info →
  tryRegsOf sig lo = some (ctx.tryRegs, st1) → ValsBelow ctx lo →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n →
    st1.nextVreg ≤ st.nextVreg →
    (∀ pre post, p.rulesOf TId.lower_branch = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ti, .labels targets]).run (st, tr) =
        .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ti, .labels targets]).run (st, tr) =
      .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧
      LowerTryOk isem MR env cp ctx (.callIndirect et.sig callee args) info st st' ms

/-- **The `try_call_indirect` root of `lower_branch` over typed contexts** (FloatsC7F). -/
def TryIndRulesCorrectT (p : Program) : Prop :=
  ∀ (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (sigs : List Clif.Signature),
    Refines F isem → MRStable F MR → IndCallsRefine env sigs MR isem →
    ∀ r ∈ p.rulesOf TId.lower_branch, tryIndRootRule r = true → TryIndRuleOkT isem MR env cp sigs p r

/-- The other rules of `lower_branch` never match a `try_call_indirect` of a typed context. -/
def TryIndUnmatchableT (p : Program) : Prop :=
  ∀ r ∈ p.rulesOf TId.lower_branch, tryIndRootRule r = false →
  ∀ (f : Clif.Function) (ctx : Ctx), CtxT f ctx →
  ∀ (ti : Nat) (callee : Nat) (args : List Nat) (et : Clif.ExnTable) (data : V)
    (targets : List Label),
  tryCallData f (.tryCallIndirect callee args et) = .ok data →
  ctx.insts[ti]? = some ⟨data, [], [], none⟩ →
  ∀ (cfg : Config) (m : Nat) (s : LState × Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId),
    (matchRule p (sem ctx) cfg m r [.inst ti, .labels targets]).run s ≠ .ok (some env', s1)

/-! ## From the typed rule families to every `lower`/`lower_branch` call -/

set_option maxRecDepth 20000 in
/-- **The typed statement dispatcher** (`lowerInstOk_of_rules` over a typed context): the
first matching root of `lower` on an instruction of a typed context is a non-closure root
(never matches, `lower_nonroot_nomatchT`), a float root (`LowerRulesCorrectT`,
`MemRulesCorrectRT`, `LowerRulesCorrectFT`), the float arm of `select`, or, on a subset-E
instruction, an integer root (`LowerRulesCorrectTI`, `MemRulesCorrectRTI`, `CallRulesCorrectT`,
`IndRulesCorrectT`); on another instruction of the typed scope no other closure root matches
(`NonEUnmatchableT`). -/
theorem lowerInstOk_of_rulesT (hrules : LowerRulesCorrectTI program)
    (hT : LowerRulesCorrectT program) (hFT : LowerRulesCorrectFT program)
    (hnE : NonEUnmatchableT program) (hcalls : CallRulesCorrectT program)
    (hind : IndRulesCorrectT program) (hmem : MemRulesCorrectRTI program)
    (hmemF : MemRulesCorrectRT program)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem)
    (hMR : MRStable F MR) {exts : List Clif.ExtFunc} (hcr : CallsRefine F env exts MR isem)
    {sigs : List Clif.Signature} (hicr : IndCallsRefine env sigs MR isem)
    (hMem : MemRefines F sb syms isem) (hFP : MemRefinesFP (fun _ => True) F sb isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxT f ctx) (hsc : InstScopeT ctx) {outB : Nat}
    (hout : OutArgsOk F outB MR)
    (hnorm : ExternsIn f exts) (hMRo : MemRelOk F sb syms f MR) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hsig : IndSigOk f sigs inst) (hst : StoreTyped ctx inst)
    (hstk : ∀ fn args e, inst = .call fn args → f.extern? fn = some e → SigStackOk e.sig outB)
    {cfg : Config} (hco : cfg.checkOverlap = false) {n : Nat}
    (hn : 1002 + (program.rulesOf TId.lower).length ≤ n) {ty : TypeId} {st : LState}
    {tr : Array RuleId} {out : V} {st' : LState} {tr' : Array RuleId} (hvb : ValsBelow ctx st)
    (h : (applyTerm program (sem ctx) cfg (n + 1) ty TId.lower [.inst ii]).run (st, tr) =
      .ok (some out, (st', tr'))) :
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx inst info.results st rss st' ms := by
  have hp := data_program
  change 1002 + (program.rulesOf 686).length ≤ n at hn
  obtain ⟨r, pre0, post0, hsplit, hpre0, m, env', s1, st2, tr2, hmn, hmatch, heval, hs⟩ :=
    applyTerm_internal_some_first hco hp.t686 term_686_kind rfl h
  have hr : r ∈ program.rulesOf TId.lower := by
    change r ∈ program.rulesOf 686; rw [hsplit]; simp
  have hfirst : ∀ pre post, program.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre,
      ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule program (sem ctx) cfg m' r' [.inst ii]).run (st, tr) = .ok (none, s') := by
    intro pre post hsp r' hr'
    have hnd : (pre0 ++ r :: post0).Nodup := hsplit ▸ lower_rules_nodup hp
    have hpre := prefix_unique_of_nodup hnd (hsplit.symm.trans hsp)
    subst hpre
    obtain ⟨m', hm', s', h'⟩ := hpre0 r' hr'
    exact ⟨m', by omega, s', h'⟩
  simp only [Prod.mk.injEq] at hs
  rw [← hs.1] at heval
  have hm1 : 1000 ≤ m := by omega
  have hn1 : 1000 ≤ n := by omega
  -- the float memory roots, under `MemRefinesR True` and `MemRefinesFP True`
  have hmF : floatMemRootRule r = true → ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧
      out = .regsVec rss ∧ LowerInstOk isem MR env cp ctx inst info.results st rss st' ms := by
    intro hfmem
    obtain ⟨ms, rss, h1, h2, h3⟩ := hmemF (fun _ => True) F sb syms isem MR env cp hR hMR
      (memRefinesR_of hMem) hFP r hr hfmem f ctx hctx.inv hMRo ii info inst hi hc cfg hco m n st tr
      env' s1 out st' tr2 hm1 hn1 hvb hfirst hmatch heval
    exact ⟨ms, rss, h1, h2, h3.toOk⟩
  have hmv : floatMoveRootRule r = true → ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧
      out = .regsVec rss ∧ LowerInstOk isem MR env cp ctx inst info.results st rss st' ms :=
    fun hfm => (hT F isem MR env cp hR hMR).1 r hr hfm f ctx hctx.inv ii info inst hi hc trivial
      cfg hco m n st tr env' s1 out st' tr2 hm1 hn1 hvb hfirst hmatch heval
  have har : floatArithRootRule r = true → ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧
      out = .regsVec rss ∧ LowerInstOk isem MR env cp ctx inst info.results st rss st' ms :=
    fun hfa => hFT F isem MR env cp hR hMR r hr hfa f ctx hctx.inv ii info inst hi hc trivial
      cfg hco m n st tr env' s1 out st' tr2 hm1 hn1 hvb hfirst hmatch heval
  cases hroot : closureRoot r
  · exact absurd hmatch (lower_nonroot_nomatchT_calls hctx.inv hsc hctx.calls hi hc hr
      (by rw [← closureRoot_eq]; exact hroot) cfg m (st, tr) env' s1)
  cases hE : Compile.instE inst
  · -- an instruction of the typed scope outside subset E
    cases hfm : floatMoveRootRule r
    · cases hfmem : floatMemRootRule r
      · cases hfa : floatArithRootRule r
        · by_cases hsel : r.id = 971 ∧ FloatSelect inst
          · exact (hT F isem MR env cp hR hMR).2 r hr hsel.1 f ctx hctx.inv ii info inst hi hc
              hsel.2 cfg hco m n st tr env' s1 out st' tr2 hm1 hn1 hvb hfirst hmatch heval
          · exact absurd hmatch (hnE r hr hroot hfm hfmem hfa f ctx hctx hsc ii info inst hi hc hE
              (fun h1 h2 => hsel ⟨h1, h2⟩) hst cfg m st tr env' s1 hfirst)
        · exact har hfa
      · exact hmF hfmem
    · exact hmv hfm
  · -- a subset-E instruction
    cases hcall : callRootRule r
    · cases hind' : indRootRule r
      · cases hm : memRootRule r
        · cases hfm : floatMoveRootRule r
          · cases hfa : floatArithRootRule r
            · exact hrules F isem MR env cp hR hMR r hr hroot hcall hind' hm hfm hfa f ctx hctx ii
                info inst hi hc hE cfg hco m n st tr env' s1 out st' tr2 hm1 hn1 hvb hfirst hmatch
                heval
            · exact har hfa
          · exact hmv hfm
        · cases hfmem : floatMemRootRule r
          · obtain ⟨ms, rss, h1, h2, h3⟩ := hmem (fun _ => True) F sb syms isem MR env cp hR hMR
              (memRefinesR_of hMem) r hr hm hfmem f ctx hctx hMRo ii info inst hi hc hE cfg hco m n
              st tr env' s1 out st' tr2 hm1 hn1 hvb hfirst hmatch heval
            exact ⟨ms, rss, h1, h2, h3.toOk⟩
          · exact hmF hfmem
      · exact hind F isem MR env cp sigs hR hMR hicr r hr hind' f ctx hctx ii info inst hi hc hE hsig
          cfg hco m n st tr env' s1 out st' tr2 hm1 hn1 hvb hfirst hmatch heval
    · exact hcalls F isem MR env cp exts sb syms outB hR hMR hMem hout hcr r hr hcall f ctx hctx
        hnorm ii info inst hi hc hE hstk cfg hco m n st tr env' s1 out st' tr2 hm1 hn1 hvb hfirst
        hmatch heval

set_option maxRecDepth 20000 in
/-- `lowerInstOk_of_rulesT` for the backend's own call (`runTerm ctx "lower" [.inst ii]`). -/
theorem lowerInstOk_runTermT (hrules : LowerRulesCorrectTI program)
    (hT : LowerRulesCorrectT program) (hFT : LowerRulesCorrectFT program)
    (hnE : NonEUnmatchableT program) (hcalls : CallRulesCorrectT program)
    (hind : IndRulesCorrectT program) (hmem : MemRulesCorrectRTI program)
    (hmemF : MemRulesCorrectRT program)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem) (hMR : MRStable F MR)
    {exts : List Clif.ExtFunc} (hcr : CallsRefine F env exts MR isem)
    {sigs : List Clif.Signature} (hicr : IndCallsRefine env sigs MR isem)
    (hMem : MemRefines F sb syms isem) (hFP : MemRefinesFP (fun _ => True) F sb isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxT f ctx) (hsc : InstScopeT ctx) {outB : Nat}
    (hout : OutArgsOk F outB MR)
    (hnorm : ExternsIn f exts) (hMRo : MemRelOk F sb syms f MR) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hsig : IndSigOk f sigs inst) (hst : StoreTyped ctx inst)
    (hstk : ∀ fn args e, inst = .call fn args → f.extern? fn = some e → SigStackOk e.sig outB)
    {st : LState} {out : V} {st' : LState} {tr : List RuleId} (hvb : ValsBelow ctx st)
    (h : runTerm ctx "lower" [.inst ii] st = .ok (some out, st', tr)) :
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx inst info.results st rss st' ms := by
  unfold runTerm Interp.run at h
  rw [program_termByName_lower] at h
  dsimp only at h
  cases ha : (applyTerm program (sem ctx) {} 1000000 T.lower.ret T.lower.id [.inst ii]).run
      (st, #[]) with
  | error e => rw [ha] at h; cases h
  | ok q =>
    obtain ⟨v, st2, tr2⟩ := q
    rw [ha] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    injection h with h
    injection h with h1 h2
    subst h1
    injection h2 with h2 _
    subst h2
    have hlen : (program.rulesOf TId.lower).length ≤ 1000 := by
      rw [show TId.lower = 686 from rfl, data_program.r686]; decide
    obtain ⟨ms, rss, h1, h2, h3⟩ := lowerInstOk_of_rulesT hrules hT hFT hnE hcalls hind hmem hmemF
      hR hMR hcr hicr hMem hFP hctx hsc hout hnorm hMRo hi hc hsig hst hstk rfl (by omega) hvb ha
    exact ⟨ms, rss, by simpa using h1, h2, h3⟩

theorem lowerTermOk_of_rulesT {p : Program} (hp : Data p) (hrules : LowerTermRulesCorrectT p)
    (hun : TermUnmatchableT p) {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT}
    (hR : Refines F isem) (hMR : MRStable F MR) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxT f ctx) {ti : Nat} {t : Clif.Terminator} {data : V} (hrt : retOrTrap t = true)
    (hd : termData t = .ok data) (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩)
    {cfg : Config} (hco : cfg.checkOverlap = false) {n : Nat}
    (hn : 1002 + (p.rulesOf TId.lower).length ≤ n) {ty : TypeId} {st : LState}
    {tr : Array RuleId} {out : V} {st' : LState} {tr' : Array RuleId} (hvb : ValsBelow ctx st)
    (h : (applyTerm p (sem ctx) cfg (n + 1) ty TId.lower [.inst ti]).run (st, tr) =
      .ok (some out, (st', tr'))) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧ LowerTermOkT isem MR ctx t [] st st' ms := by
  change 1002 + (p.rulesOf 686).length ≤ n at hn
  obtain ⟨r, pre0, post0, hsplit, hpre0, m, env', s1, st2, tr2, hmn, hmatch, heval, hs⟩ :=
    applyTerm_internal_some_first hco hp.t686 term_686_kind rfl h
  have hr : r ∈ p.rulesOf TId.lower := by
    change r ∈ p.rulesOf 686; rw [hsplit]; simp
  have hfirst : ∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ti]).run (st, tr) = .ok (none, s') := by
    intro pre post hsp r' hr'
    have hnd : (pre0 ++ r :: post0).Nodup := hsplit ▸ lower_rules_nodup hp
    have hpre := prefix_unique_of_nodup hnd (hsplit.symm.trans hsp)
    subst hpre
    obtain ⟨m', hm', s', h'⟩ := hpre0 r' hr'
    exact ⟨m', by omega, s', h'⟩
  simp only [Prod.mk.injEq] at hs
  rw [← hs.1] at heval
  cases hroot : termRootRule r
  · exact absurd hmatch (hun r hr hroot f ctx hctx ti t data hrt hd hi cfg m (st, tr) env' s1)
  · exact hrules F isem MR hR hMR r hr hroot f ctx hctx ti t data hrt hd hi cfg hco m n st tr
      env' s1 out st' tr2 (by omega) (by omega) hvb hfirst hmatch heval

theorem branchOk_of_rulesT {p : Program} (hp : Data p) (hrules : BranchRulesCorrectT p)
    (hex : BranchExcludedUnmatchableT p) {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT}
    (hR : Refines F isem) (hMR : MRStable F MR) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxT f ctx) {ti : Nat} {t : Clif.Terminator} {data : V} {targets : List Label}
    (hrt : retOrTrap t = false) (hd : termData t = .ok data)
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) (hbt : BrIdxTyped ctx t)
    (hip : TermIntPos ctx t)
    (htl : TargetsLen t targets) {cfg : Config} (hco : cfg.checkOverlap = false) {n : Nat}
    (hn : 1002 + (p.rulesOf TId.lower_branch).length ≤ n) {ty : TypeId} {st : LState}
    {tr : Array RuleId} {out : V} {st' : LState} {tr' : Array RuleId} (hvb : ValsBelow ctx st)
    (h : (applyTerm p (sem ctx) cfg (n + 1) ty TId.lower_branch [.inst ti, .labels targets]).run
      (st, tr) = .ok (some out, (st', tr'))) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧ LowerTermOk isem MR ctx t targets st st' ms := by
  change 1002 + (p.rulesOf 687).length ≤ n at hn
  obtain ⟨r, pre0, post0, hsplit, hpre0, m, env', s1, st2, tr2, hmn, hmatch, heval, hs⟩ :=
    applyTerm_internal_some_first hco hp.t687 term_687_kind rfl h
  have hr : r ∈ p.rulesOf TId.lower_branch := by
    change r ∈ p.rulesOf 687; rw [hsplit]; simp
  have hfirst : ∀ pre post, p.rulesOf TId.lower_branch = pre ++ r :: post → ∀ r' ∈ pre,
      ∃ m', 1000 ≤ m' ∧ ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ti, .labels targets]).run
        (st, tr) = .ok (none, s') := by
    intro pre post hsp r' hr'
    have hnd : (pre0 ++ r :: post0).Nodup := hsplit ▸ lower_branch_rules_nodup hp
    have hpre := prefix_unique_of_nodup hnd (hsplit.symm.trans hsp)
    subst hpre
    obtain ⟨m', hm', s', h'⟩ := hpre0 r' hr'
    exact ⟨m', by omega, s', h'⟩
  simp only [Prod.mk.injEq] at hs
  rw [← hs.1] at heval
  cases hroot : closureRoot r
  · exact absurd hmatch (hex r hr hroot f ctx hctx ti t data targets hrt hd hi cfg m (st, tr) env' s1)
  · exact hrules F isem MR hR hMR r hr hroot f ctx hctx ti t data targets hd hi hbt hip htl cfg hco m n st
      tr env' s1 out st' tr2 (by omega) (by omega) hvb hfirst hmatch heval

set_option maxRecDepth 20000 in
/-- `lowerTermOk_of_rulesT` for the exported program and the backend's call
(`runTerm ctx "lower" [.inst ti]` on a `return`/`trap`). -/
theorem lowerTermOk_runTermT (hrules : LowerTermRulesCorrectT program)
    (hun : TermUnmatchableT program) {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT}
    (hR : Refines F isem) (hMR : MRStable F MR) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxT f ctx) {ti : Nat} {t : Clif.Terminator} {data : V} (hrt : retOrTrap t = true)
    (hd : termData t = .ok data) (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩)
    {st : LState} {out : V} {st' : LState} {tr : List RuleId} (hvb : ValsBelow ctx st)
    (h : runTerm ctx "lower" [.inst ti] st = .ok (some out, st', tr)) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧ LowerTermOkT isem MR ctx t [] st st' ms := by
  unfold runTerm Interp.run at h
  rw [program_termByName_lower] at h
  dsimp only at h
  cases ha : (applyTerm program (sem ctx) {} 1000000 T.lower.ret T.lower.id [.inst ti]).run
      (st, #[]) with
  | error e => rw [ha] at h; cases h
  | ok q =>
    obtain ⟨v, st2, tr2⟩ := q
    rw [ha] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    injection h with h
    injection h with h1 h2
    subst h1
    injection h2 with h2 _
    subst h2
    have hlen : (program.rulesOf TId.lower).length ≤ 1000 := by
      rw [show TId.lower = 686 from rfl, data_program.r686]; decide
    obtain ⟨ms, h1, h2⟩ := lowerTermOk_of_rulesT data_program hrules hun hR hMR hctx hrt hd hi
      rfl (by omega) hvb ha
    exact ⟨ms, by simpa using h1, h2⟩

set_option maxRecDepth 20000 in
/-- `branchOk_of_rulesT` for the exported program and the backend's call
(`runTerm ctx "lower_branch" [.inst ti, .labels targets]`). -/
theorem branchOk_runTermT (hrules : BranchRulesCorrectT program)
    (hex : BranchExcludedUnmatchableT program) {F : BitVec 64 → Prop} {isem : Sem}
    {MR : MemRelT} (hR : Refines F isem) (hMR : MRStable F MR) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxT f ctx) {ti : Nat} {t : Clif.Terminator} {data : V} {targets : List Label}
    (hrt : retOrTrap t = false) (hd : termData t = .ok data)
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) (hbt : BrIdxTyped ctx t)
    (hip : TermIntPos ctx t)
    (htl : TargetsLen t targets) {st : LState} {out : V} {st' : LState} {tr : List RuleId}
    (hvb : ValsBelow ctx st)
    (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] st = .ok (some out, st', tr)) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧ LowerTermOk isem MR ctx t targets st st' ms := by
  unfold runTerm Interp.run at h
  rw [program_termByName_lower_branch] at h
  dsimp only at h
  cases ha : (applyTerm program (sem ctx) {} 1000000 T.lower_branch.ret T.lower_branch.id
      [.inst ti, .labels targets]).run (st, #[]) with
  | error e => rw [ha] at h; cases h
  | ok q =>
    obtain ⟨v, st2, tr2⟩ := q
    rw [ha] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    injection h with h
    injection h with h1 h2
    subst h1
    injection h2 with h2 _
    subst h2
    have hlen : (program.rulesOf TId.lower_branch).length ≤ 1000 := by
      rw [show TId.lower_branch = 687 from rfl, data_program.r687]; decide
    obtain ⟨ms, h1, h2⟩ := branchOk_of_rulesT data_program hrules hex hR hMR hctx hrt hd hi hbt hip htl
      rfl (by omega) hvb ha
    exact ⟨ms, by simpa using h1, h2⟩

theorem tryOk_of_rulesT {p : Program} (hp : Data p) (hrules : TryRulesCorrectT p)
    (hun : TryUnmatchableT p) {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} {exts : List Clif.ExtFunc}
    (hR : Refines F isem) (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefines F sb syms isem) {outB : Nat} (hout : OutArgsOk F outB MR)
    (hcr : CallsRefine F env exts MR isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxT f ctx)
    (hext : ExternsIn f exts) {ti : Nat} {fn : Clif.FnRef} {args : List Nat} {et : Clif.ExnTable}
    {data : V} {sig : Clif.Signature} {items : List (Option Nat)} {targets : List Label}
    {info : TryInfo} {lo st1 : LState} (hra : ∀ e, f.extern? fn = some e → SigStackOk e.sig outB)
    (hd : tryCallData f (.tryCall fn args et) = .ok data)
    (hip : TermIntPos ctx (.tryCall fn args et)) (he : exnTableOpnd f et = .ok (sig, items))
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) (hinfo : tryInfoOf sig items targets = some info)
    (htr : tryRegsOf sig lo = some (ctx.tryRegs, st1)) (hvb : ValsBelow ctx lo)
    {cfg : Config} (hco : cfg.checkOverlap = false) {n : Nat}
    (hn : 1002 + (p.rulesOf TId.lower_branch).length ≤ n) {ty : TypeId} {st : LState}
    {tr : Array RuleId} {out : V} {st' : LState} {tr' : Array RuleId}
    (hst : st1.nextVreg ≤ st.nextVreg)
    (h : (applyTerm p (sem ctx) cfg (n + 1) ty TId.lower_branch [.inst ti, .labels targets]).run
      (st, tr) = .ok (some out, (st', tr'))) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧
      LowerTryOk isem MR env cp ctx (.call fn args) info st st' ms := by
  change 1002 + (p.rulesOf 687).length ≤ n at hn
  obtain ⟨r, pre0, post0, hsplit, hpre0, m, env', s1, st2, tr2, hmn, hmatch, heval, hs⟩ :=
    applyTerm_internal_some_first hco hp.t687 term_687_kind rfl h
  have hr : r ∈ p.rulesOf TId.lower_branch := by
    change r ∈ p.rulesOf 687; rw [hsplit]; simp
  have hfirst : ∀ pre post, p.rulesOf TId.lower_branch = pre ++ r :: post → ∀ r' ∈ pre,
      ∃ m', 1000 ≤ m' ∧ ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ti, .labels targets]).run
        (st, tr) = .ok (none, s') := by
    intro pre post hsp r' hr'
    have hnd : (pre0 ++ r :: post0).Nodup := hsplit ▸ lower_branch_rules_nodup hp
    have hpre := prefix_unique_of_nodup hnd (hsplit.symm.trans hsp)
    subst hpre
    obtain ⟨m', hm', s', h'⟩ := hpre0 r' hr'
    exact ⟨m', by omega, s', h'⟩
  simp only [Prod.mk.injEq] at hs
  rw [← hs.1] at heval
  cases hroot : tryRootRule r
  · exact absurd hmatch (hun r hr hroot f ctx hctx ti fn args et data targets hd hi cfg m (st, tr) env' s1)
  · exact hrules F isem MR env cp exts sb syms outB hR hMR hMem hout hcr r hr hroot f ctx hctx hext ti fn
      args et data sig items targets info lo st1 hra hd hip he hi hinfo htr hvb cfg hco m n st tr env' s1
      out st' tr2 (by omega) (by omega) hst hfirst hmatch heval

set_option maxRecDepth 20000 in
/-- `tryOk_of_rulesT` for the exported program and the backend's call on a `try_call`. -/
theorem tryOk_runTermT (hrules : TryRulesCorrectT program) (hun : TryUnmatchableT program)
    {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    {exts : List Clif.ExtFunc} (hR : Refines F isem) (hMR : MRStable F MR) {sb : Nat}
    {syms : String → Option Nat} (hMem : MemRefines F sb syms isem) {outB : Nat}
    (hout : OutArgsOk F outB MR)
    (hcr : CallsRefine F env exts MR isem) {f : Clif.Function} {ctx : Ctx} (hctx : CtxT f ctx)
    (hext : ExternsIn f exts) {ti : Nat} {fn : Clif.FnRef}
    {args : List Nat} {et : Clif.ExnTable} {data : V} {sig : Clif.Signature}
    {items : List (Option Nat)} {targets : List Label} {info : TryInfo} {lo st1 : LState}
    (hra : ∀ e, f.extern? fn = some e → SigStackOk e.sig outB)
    (hd : tryCallData f (.tryCall fn args et) = .ok data)
    (hip : TermIntPos ctx (.tryCall fn args et)) (he : exnTableOpnd f et = .ok (sig, items))
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) (hinfo : tryInfoOf sig items targets = some info)
    (htr : tryRegsOf sig lo = some (ctx.tryRegs, st1)) (hvb : ValsBelow ctx lo)
    {st : LState} {out : V} {st' : LState} {tr : List RuleId} (hst : st1.nextVreg ≤ st.nextVreg)
    (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] st = .ok (some out, st', tr)) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧
      LowerTryOk isem MR env cp ctx (.call fn args) info st st' ms := by
  unfold runTerm Interp.run at h
  rw [program_termByName_lower_branch] at h
  dsimp only at h
  cases ha : (applyTerm program (sem ctx) {} 1000000 T.lower_branch.ret T.lower_branch.id
      [.inst ti, .labels targets]).run (st, #[]) with
  | error e => rw [ha] at h; cases h
  | ok q =>
    obtain ⟨v, st2, tr2⟩ := q
    rw [ha] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    injection h with h
    injection h with h1 h2
    subst h1
    injection h2 with h2 _
    subst h2
    have hlen : (program.rulesOf TId.lower_branch).length ≤ 1000 := by
      rw [show TId.lower_branch = 687 from rfl, data_program.r687]; decide
    obtain ⟨ms, h1, h2⟩ := tryOk_of_rulesT data_program hrules hun hR hMR hMem hout hcr hctx hext hra
      hd hip he hi hinfo htr hvb rfl (by omega) hst ha
    exact ⟨ms, by simpa using h1, h2⟩

theorem tryIndOk_of_rulesT {p : Program} (hp : Data p) (hrules : TryIndRulesCorrectT p)
    (hun : TryIndUnmatchableT p) {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} {sigs : List Clif.Signature}
    (hR : Refines F isem) (hMR : MRStable F MR) (hcr : IndCallsRefine env sigs MR isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxT f ctx) {ti callee : Nat} {args : List Nat}
    {et : Clif.ExnTable} {data : V} {sig : Clif.Signature} {items : List (Option Nat)}
    {targets : List Label} {info : TryInfo} {lo st1 : LState}
    (hd : tryCallData f (.tryCallIndirect callee args et) = .ok data)
    (hip : TermIntPos ctx (.tryCallIndirect callee args et))
    (he : exnTableOpnd f et = .ok (sig, items)) (hsig : sig ∈ sigs) (h8 : sig.params.length ≤ 8)
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) (hinfo : tryInfoOf sig items targets = some info)
    (htr : tryRegsOf sig lo = some (ctx.tryRegs, st1)) (hvb : ValsBelow ctx lo)
    {cfg : Config} (hco : cfg.checkOverlap = false) {n : Nat}
    (hn : 1002 + (p.rulesOf TId.lower_branch).length ≤ n) {ty : TypeId} {st : LState}
    {tr : Array RuleId} {out : V} {st' : LState} {tr' : Array RuleId}
    (hst : st1.nextVreg ≤ st.nextVreg)
    (h : (applyTerm p (sem ctx) cfg (n + 1) ty TId.lower_branch [.inst ti, .labels targets]).run
      (st, tr) = .ok (some out, (st', tr'))) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧
      LowerTryOk isem MR env cp ctx (.callIndirect et.sig callee args) info st st' ms := by
  change 1002 + (p.rulesOf 687).length ≤ n at hn
  obtain ⟨r, pre0, post0, hsplit, hpre0, m, env', s1, st2, tr2, hmn, hmatch, heval, hs⟩ :=
    applyTerm_internal_some_first hco hp.t687 term_687_kind rfl h
  have hr : r ∈ p.rulesOf TId.lower_branch := by
    change r ∈ p.rulesOf 687; rw [hsplit]; simp
  have hfirst : ∀ pre post, p.rulesOf TId.lower_branch = pre ++ r :: post → ∀ r' ∈ pre,
      ∃ m', 1000 ≤ m' ∧ ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ti, .labels targets]).run
        (st, tr) = .ok (none, s') := by
    intro pre post hsp r' hr'
    have hnd : (pre0 ++ r :: post0).Nodup := hsplit ▸ lower_branch_rules_nodup hp
    have hpre := prefix_unique_of_nodup hnd (hsplit.symm.trans hsp)
    subst hpre
    obtain ⟨m', hm', s', h'⟩ := hpre0 r' hr'
    exact ⟨m', by omega, s', h'⟩
  simp only [Prod.mk.injEq] at hs
  rw [← hs.1] at heval
  cases hroot : tryIndRootRule r
  · exact absurd hmatch
      (hun r hr hroot f ctx hctx ti callee args et data targets hd hi cfg m (st, tr) env' s1)
  · exact hrules F isem MR env cp sigs hR hMR hcr r hr hroot f ctx hctx ti callee args et data
      sig items targets info lo st1 hd hip he hsig h8 hi hinfo htr hvb cfg hco m n st tr env' s1 out st'
      tr2 (by omega) (by omega) hst hfirst hmatch heval

set_option maxRecDepth 20000 in
/-- `tryIndOk_of_rulesT` for the exported program and the backend's call on a
`try_call_indirect`. -/
theorem tryIndOk_runTermT (hrules : TryIndRulesCorrectT program) (hun : TryIndUnmatchableT program)
    {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    {sigs : List Clif.Signature} (hR : Refines F isem) (hMR : MRStable F MR)
    (hcr : IndCallsRefine env sigs MR isem) {f : Clif.Function} {ctx : Ctx} (hctx : CtxT f ctx)
    {ti callee : Nat} {args : List Nat} {et : Clif.ExnTable} {data : V} {sig : Clif.Signature}
    {items : List (Option Nat)} {targets : List Label} {info : TryInfo} {lo st1 : LState}
    (hd : tryCallData f (.tryCallIndirect callee args et) = .ok data)
    (hip : TermIntPos ctx (.tryCallIndirect callee args et))
    (he : exnTableOpnd f et = .ok (sig, items)) (hsig : sig ∈ sigs) (h8 : sig.params.length ≤ 8)
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) (hinfo : tryInfoOf sig items targets = some info)
    (htr : tryRegsOf sig lo = some (ctx.tryRegs, st1)) (hvb : ValsBelow ctx lo)
    {st : LState} {out : V} {st' : LState} {tr : List RuleId} (hst : st1.nextVreg ≤ st.nextVreg)
    (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] st = .ok (some out, st', tr)) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧
      LowerTryOk isem MR env cp ctx (.callIndirect et.sig callee args) info st st' ms := by
  unfold runTerm Interp.run at h
  rw [program_termByName_lower_branch] at h
  dsimp only at h
  cases ha : (applyTerm program (sem ctx) {} 1000000 T.lower_branch.ret T.lower_branch.id
      [.inst ti, .labels targets]).run (st, #[]) with
  | error e => rw [ha] at h; cases h
  | ok q =>
    obtain ⟨v, st2, tr2⟩ := q
    rw [ha] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    injection h with h
    injection h with h1 h2
    subst h1
    injection h2 with h2 _
    subst h2
    have hlen : (program.rulesOf TId.lower_branch).length ≤ 1000 := by
      rw [show TId.lower_branch = 687 from rfl, data_program.r687]; decide
    obtain ⟨ms, h1, h2⟩ := tryIndOk_of_rulesT data_program hrules hun hR hMR hcr hctx hd hip he hsig h8
      hi hinfo htr hvb rfl (by omega) hst ha
    exact ⟨ms, by simpa using h1, h2⟩

end Backend.Proof

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-! ## The driver's calls, for one context -/

/-- Every `lower` call `lowerFunction` makes on a statement of `f` in context `ctx` satisfies
`LowerInstOk` (`InstCalls` for one context: `instCallsT_of_rules` for a typed context). -/
def InstCallsT {W : Type} (f : Clif.Function) (ctx : Ctx) (sem : ISem CV W) (MR : MemRelTW W)
    (env : Clif.Env) (p : Clif.Program) : Prop :=
  ∀ ii info inst st rss st' tr,
    (∃ B ∈ f.blocks, ∃ stm ∈ B.body, stm.inst = inst) →
    ctx.insts[ii]? = some info →
    info.clif = some inst → IndSigOk f (indSigs f) inst → st.emitted = #[] → ValsBelow ctx st →
    runTerm ctx "lower" [.inst ii] st = .ok (some (.regsVec rss), st', tr) →
    LowerInstOk sem MR env p ctx inst info.results st rss st' st'.emitted.toList

/-- Every terminator call `lowerFunction` makes in context `ctx` satisfies `LowerTermOkT`
(`TermCalls` for one context, with class-aware returns). -/
def TermCallsT {W : Type} (ctx : Ctx) (sem : ISem CV W) (MR : MemRelTW W) : Prop :=
  ∀ ti t data targets out st st' tr, BrIdxTyped ctx t → TermIntPos ctx t → TargetsLen t targets →
    ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → ValsBelow ctx st →
    termData t = .ok data → st.emitted = #[] →
    runTerm (termCtx ctx ti data) (termCall t ti targets).1 (termCall t ti targets).2 st =
      .ok (some out, st', tr) →
    LowerTermOkT sem MR (termCtx ctx ti data) t targets st st' st'.emitted.toList

/-- Every `lower_branch` call `lowerFunction` makes on a `try_call` of `f` in context `ctx`
satisfies `LowerTryOk` (`TryCalls` for one context). -/
def TryCallsT {W : Type} (f : Clif.Function) (ctx : Ctx) (sem : ISem CV W) (MR : MemRelTW W)
    (env : Clif.Env) (p : Clif.Program) (outB : Nat) : Prop :=
  ∀ ti fn args et data sig items targets info trs lo st1 out st' tr,
    (∀ e, f.extern? fn = some e → SigStackOk e.sig outB) →
    tryCallData f (.tryCall fn args et) = .ok data → TermIntPos ctx (.tryCall fn args et) →
    exnTableOpnd f et = .ok (sig, items) → ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ →
    tryInfoOf sig items targets = some info → tryRegsOf sig lo = some (trs, st1) →
    ValsBelow ctx lo →
    runTerm (tryCtx ctx ti data trs) "lower_branch" [.inst ti, .labels targets]
      { st1 with emitted := #[] } = .ok (some out, st', tr) →
    LowerTryOk sem MR env p (tryCtx ctx ti data trs) (.call fn args) info
      { st1 with emitted := #[] } st' st'.emitted.toList

/-- Every `lower_branch` call `lowerFunction` makes on a `try_call_indirect` of `f` in context
`ctx` satisfies `LowerTryOk` (`TryIndCalls` for one context). -/
def TryIndCallsT {W : Type} (f : Clif.Function) (ctx : Ctx) (sem : ISem CV W) (MR : MemRelTW W)
    (env : Clif.Env) (p : Clif.Program) (sigs : List Clif.Signature) : Prop :=
  ∀ ti callee args et data sig items targets info trs lo st1 out st' tr,
    tryCallData f (.tryCallIndirect callee args et) = .ok data →
    TermIntPos ctx (.tryCallIndirect callee args et) →
    exnTableOpnd f et = .ok (sig, items) → sig ∈ sigs → sig.params.length ≤ 8 →
    ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ →
    tryInfoOf sig items targets = some info → tryRegsOf sig lo = some (trs, st1) →
    ValsBelow ctx lo →
    runTerm (tryCtx ctx ti data trs) "lower_branch" [.inst ti, .labels targets]
      { st1 with emitted := #[] } = .ok (some out, st', tr) →
    LowerTryOk sem MR env p (tryCtx ctx ti data trs) (.callIndirect et.sig callee args) info
      { st1 with emitted := #[] } st' st'.emitted.toList

/-! ### Integer specializations of the driver's calls -/

theorem InstCalls.toT {W : Type} {f : Clif.Function} {ctx : Ctx} {sem : ISem CV W}
    {MR : MemRelTW W} {env : Clif.Env} {p : Clif.Program} (h : InstCalls f sem MR env p)
    (hctx : CtxInv f ctx) (hE : Compile.functionE f = true) : InstCallsT f ctx sem MR env p :=
  fun ii info inst st rss st' tr hm hi hc hs he hvb hr =>
    h ctx ii info inst st rss st' tr hctx hm hE hi hc hs he hvb hr

theorem TermCalls.toT {W : Type} {f : Clif.Function} {ctx : Ctx} {sem : ISem CV W}
    {MR : MemRelTW W} (h : TermCalls sem MR) (hctx : CtxInv f ctx) : TermCallsT ctx sem MR := by
  intro ti t data targets out st st' tr hbt _ htl hph hvb hd hemp hr
  refine (h f ctx ti t data targets out st st' tr hctx hbt htl hph hvb hd hemp hr).toT ?_
  have hE : CtxE (termCtx ctx ti data) := (ctxInv_termCtx hctx hph data).valTyE
  exact valClassOf_int_of_ctxE hE

theorem TryCalls.toT {W : Type} {f : Clif.Function} {ctx : Ctx} {sem : ISem CV W}
    {MR : MemRelTW W} {env : Clif.Env} {p : Clif.Program} {outB : Nat}
    (h : TryCalls f sem MR env p outB) (hctx : CtxInv f ctx) : TryCallsT f ctx sem MR env p outB :=
  fun ti fn args et data sig items targets info trs lo st1 out st' tr hra hd _ =>
    h ctx ti fn args et data sig items targets info trs lo st1 out st' tr hctx hra hd

theorem TryIndCalls.toT {W : Type} {f : Clif.Function} {ctx : Ctx} {sem : ISem CV W}
    {MR : MemRelTW W} {env : Clif.Env} {p : Clif.Program} {sigs : List Clif.Signature}
    (h : TryIndCalls sem MR env p sigs) (hctx : CtxInv f ctx) :
    TryIndCallsT f ctx sem MR env p sigs :=
  fun ti callee args et data sig items targets info trs lo st1 out st' tr hd _ =>
    h f ctx ti callee args et data sig items targets info trs lo st1 out st' tr hctx hd

/-! ### From the typed rule families to the driver's calls -/

/-- Filling in the terminator's data at `buildCtx`'s placeholder keeps `CtxInvT`. -/
theorem ctxInvT_termCtx {f : Clif.Function} {ctx : Ctx} (h : CtxInvT f ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) (data : V) :
    CtxInvT f (termCtx ctx ti data) := by
  have hne : ∀ x d, ctx.defInst? x = some d → d ≠ ti := by
    intro x d hd e
    subst e
    obtain ⟨info, hi, hx⟩ := h.defInst x d hd
    rw [hph] at hi; cases hi; cases hx
  refine ⟨h.func, fun ii info inst hi hc => ?_, fun ii info inst hi hc => ?_, h.valueReg,
    h.typedReg, fun x d hd => ?_, fun x d info hd hi => ?_, h.slotOff, fun ii info hi => ?_,
    h.valTyM, fun ii info inst x hi hc hx => ?_, fun ii info inst hi hc => ?_⟩
  · by_cases e : ii = ti
    · subst e; rw [termCtx_insts_self hph] at hi; cases hi; cases hc
    · rw [termCtx_insts_ne e] at hi; exact h.data ii info inst hi hc
  · by_cases e : ii = ti
    · subst e; rw [termCtx_insts_self hph] at hi; cases hi; cases hc
    · rw [termCtx_insts_ne e] at hi; exact h.resTys ii info inst hi hc
  · rw [termCtx_insts_ne (hne x d hd)]; exact h.defInst x d hd
  · rw [termCtx_insts_ne (hne x d hd)] at hi; exact h.defClif x d info hd hi
  · by_cases e : ii = ti
    · subst e; rw [termCtx_insts_self hph] at hi; cases hi; intro t ht; cases ht
    · rw [termCtx_insts_ne e] at hi; exact h.resTysM ii info hi
  · by_cases e : ii = ti
    · subst e; rw [termCtx_insts_self hph] at hi; cases hi; cases hc
    · rw [termCtx_insts_ne e] at hi; exact h.addr64 ii info inst x hi hc hx
  · by_cases e : ii = ti
    · subst e; rw [termCtx_insts_self hph] at hi; cases hi; cases hc
    · rw [termCtx_insts_ne e] at hi; exact h.intOps ii info inst hi hc

/-- … and `CtxT`. -/
theorem ctxT_termCtx {f : Clif.Function} {ctx : Ctx} (h : CtxT f ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) (data : V) :
    CtxT f (termCtx ctx ti data) := by
  refine ⟨ctxInvT_termCtx h.inv hph data, fun ii info inst hi hc => ?_,
    fun ii info fn args e hi hc he => ?_⟩
  · by_cases e : ii = ti
    · subst e; rw [termCtx_insts_self hph] at hi; cases hi; cases hc
    · rw [termCtx_insts_ne e] at hi; exact h.scope ii info inst hi hc
  · by_cases e' : ii = ti
    · subst e'; rw [termCtx_insts_self hph] at hi; cases hi; cases hc
    · rw [termCtx_insts_ne e'] at hi; exact h.calls ii info fn args e hi hc he

/-- `CtxT` does not depend on the `try_call` vregs. -/
theorem ctxT_tryRegs {f : Clif.Function} {ctx : Ctx} (h : CtxT f ctx)
    (trs : List Reg × List Reg) : CtxT f { ctx with tryRegs := trs } :=
  ⟨⟨h.inv.func, h.inv.data, h.inv.resTys, h.inv.valueReg, h.inv.typedReg, h.inv.defInst,
    h.inv.defClif, h.inv.slotOff, h.inv.resTysM, h.inv.valTyM, h.inv.addr64, h.inv.intOps⟩,
    h.scope, h.calls⟩

/-- For `return`/`trap`, `LowerTermOkT` does not depend on the targets. -/
theorem lowerTermOkT_targets {isem : Sem} {MR : MemRelT} {ctx : Ctx} {t : Clif.Terminator}
    (hrt : retOrTrap t = true) {st st' : LState} {ms : List MInst}
    (h : LowerTermOkT isem MR ctx t [] st st' ms) (targets : List Label) :
    LowerTermOkT isem MR ctx t targets st st' ms := by
  cases t <;> simp [retOrTrap] at hrt <;> exact ⟨h.mono, h.defs, h.run⟩

/-- **From the typed rule families to the driver's `lower` calls** in a typed, store-typed
context `ctx` of `f` (whose memory relation satisfies `MemRelOk`, under the callee contract for
`f`'s externs, the indirect-call contract for its indirect-call signatures and the float accesses'
`MemRefinesFP`). -/
theorem instCallsT_of_rules (hrules : LowerRulesCorrectTI Isle.Aarch64.program)
    (hT : LowerRulesCorrectT Isle.Aarch64.program) (hFT : LowerRulesCorrectFT Isle.Aarch64.program)
    (hnE : NonEUnmatchableT Isle.Aarch64.program) (hcalls : CallRulesCorrectT Isle.Aarch64.program)
    (hind : IndRulesCorrectT Isle.Aarch64.program) (hmem : MemRulesCorrectRTI Isle.Aarch64.program)
    (hmemF : MemRulesCorrectRT Isle.Aarch64.program)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {sem : Sem}
    {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {f : Clif.Function} {ctx : Ctx}
    (hR : Refines F sem) (hMR : MRStable F MR) (hcr : CallsRefine F env (f.externs.map (·.2)) MR sem)
    (hicr : IndCallsRefine env (indSigs f) MR sem)
    (hMem : MemRefines F sb syms sem) (hFP : MemRefinesFP (fun _ => True) F sb sem) {outB : Nat}
    (hout : OutArgsOk F outB MR) (hstk : CallsStack f outB)
    (hMRo : MemRelOk F sb syms f MR) (hctx : CtxT f ctx) (hsc : InstScopeT ctx)
    (hst : StoresTyped ctx) :
    InstCallsT f ctx sem MR env p := by
  intro ii info inst st rss st' tr hmem' hi hc hsig hemp hvb hrun
  obtain ⟨B, hB, stm, hstm, rfl⟩ := hmem'
  obtain ⟨ms, rss', hem, hov, hok⟩ := lowerInstOk_runTermT hrules hT hFT hnE hcalls hind hmem hmemF
    (env := env) (cp := p) hR hMR hcr hicr hMem hFP hctx hsc hout (externsIn_self f) hMRo hi hc hsig
    (hst ii info _ hi hc)
    (fun fn args e hc he => hstk B hB stm hstm fn args e hc he) hvb hrun
  cases hov
  rw [hemp, Array.empty_append] at hem
  rw [hem, List.toList_toArray]
  exact hok

/-- **From the typed terminator rule families to the driver's terminator calls** in a typed
context. -/
theorem termCallsT_of_rules (hlt : LowerTermRulesCorrectT Isle.Aarch64.program)
    (hun : TermUnmatchableT Isle.Aarch64.program)
    (hbr : BranchRulesCorrectT Isle.Aarch64.program)
    (hbex : BranchExcludedUnmatchableT Isle.Aarch64.program) {F : BitVec 64 → Prop} {sem : Sem}
    {MR : MemRelT} (hR : Refines F sem) (hMR : MRStable F MR) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxT f ctx) : TermCallsT ctx sem MR := by
  intro ti t data targets out st st' tr hbt hip htl hph hvb hd hemp hrun
  have hctx' := ctxT_termCtx hctx hph data
  have hi := termCtx_insts_self hph data
  have hvb' : ValsBelow (termCtx ctx ti data) st := hvb
  have key : ∀ ms : List MInst, st'.emitted = st.emitted ++ ms.toArray → ms = st'.emitted.toList := by
    intro ms hem; rw [hemp, Array.empty_append] at hem; rw [hem, List.toList_toArray]
  cases hrt : retOrTrap t
  · have hc : termCall t ti targets = ("lower_branch", [.inst ti, .labels targets]) := by
      cases t <;> simp [retOrTrap] at hrt <;> rfl
    rw [hc] at hrun
    obtain ⟨ms, hem, hok⟩ := branchOk_runTermT hbr hbex hR hMR hctx' hrt hd hi hbt hip htl hvb' hrun
    rw [← key ms hem]
    exact hok.toT_of_not_ret (fun xs e => by subst e; cases hrt)
  · have hc : termCall t ti targets = ("lower", [.inst ti]) := by
      cases t <;> simp [retOrTrap] at hrt <;> rfl
    rw [hc] at hrun
    obtain ⟨ms, hem, hok⟩ := lowerTermOk_runTermT hlt hun hR hMR hctx' hrt hd hi hvb' hrun
    rw [← key ms hem]; exact lowerTermOkT_targets hrt hok targets

/-- **From the typed `try_call` rule families to the driver's `try_call` calls** in a typed
context. -/
theorem tryCallsT_of_rules (htr : TryRulesCorrectT Isle.Aarch64.program)
    (hun : TryUnmatchableT Isle.Aarch64.program) {F : BitVec 64 → Prop} {sem : Sem}
    {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {f : Clif.Function} {ctx : Ctx}
    (hR : Refines F sem)
    (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat} (hMem : MemRefines F sb syms sem)
    {outB : Nat} (hout : OutArgsOk F outB MR) (hcr : CallsRefine F env (f.externs.map (·.2)) MR sem)
    (hctx : CtxT f ctx) : TryCallsT f ctx sem MR env p outB := by
  intro ti fn args et data sig items targets info trs lo st1 out st' tr hra hd hip he hph
    hinfo hregs hvb hrun
  have hctx' := ctxT_tryRegs (ctxT_termCtx hctx hph data) trs
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hregs' : tryRegsOf sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := hregs
  have hvb' : ValsBelow (tryCtx ctx ti data trs) lo := hvb
  obtain ⟨ms, hem, hok⟩ := tryOk_runTermT htr hun hR hMR hMem hout hcr hctx' (externsIn_self f) hra
    hd hip he hi hinfo hregs' hvb' (st := { st1 with emitted := #[] }) (Nat.le_refl _) hrun
  have : ms = st'.emitted.toList := by
    simp only [Array.empty_append] at hem; rw [hem, List.toList_toArray]
  rw [← this]; exact hok

/-- **From the typed `try_call_indirect` rule families to the driver's calls** in a typed
context. -/
theorem tryIndCallsT_of_rules (htr : TryIndRulesCorrectT Isle.Aarch64.program)
    (hun : TryIndUnmatchableT Isle.Aarch64.program) {F : BitVec 64 → Prop} {sem : Sem}
    {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {sigs : List Clif.Signature}
    {f : Clif.Function} {ctx : Ctx}
    (hR : Refines F sem) (hMR : MRStable F MR) (hcr : IndCallsRefine env sigs MR sem)
    (hctx : CtxT f ctx) : TryIndCallsT f ctx sem MR env p sigs := by
  intro ti callee args et data sig items targets info trs lo st1 out st' tr hd hip he hsig
    h8 hph hinfo hregs hvb hrun
  have hctx' := ctxT_tryRegs (ctxT_termCtx hctx hph data) trs
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hregs' : tryRegsOf sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := hregs
  have hvb' : ValsBelow (tryCtx ctx ti data trs) lo := hvb
  obtain ⟨ms, hem, hok⟩ := tryIndOk_runTermT htr hun hR hMR hcr hctx' hd hip he hsig h8 hi
    hinfo hregs' hvb' (st := { st1 with emitted := #[] }) (Nat.le_refl _) hrun
  have : ms = st'.emitted.toList := by
    simp only [Array.empty_append] at hem; rw [hem, List.toList_toArray]
  rw [← this]; exact hok

end Backend.Proof.Driver
