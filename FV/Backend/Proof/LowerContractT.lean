import FV.Backend.Proof.LowerContract
import FV.Backend.Proof.DriverCheckTy
import FV.Backend.Proof.IselExclT

/-!
# The typed lowering contracts (S11e5 Stage C, slice 7)

The integer M4 obligations (`LowerRulesCorrect`, `MemRulesCorrect`, `CallRulesCorrect`, …,
`IselContract.lean`) quantify over the contexts of subset-E functions (`CtxInv`: every value an
`i8..i64` in an X register). A function of the typed movement scope (`Compile.functionET`) has a
float-capable context: `CtxInvT` (class-aware vregs, `f32`/`f64` values, integer operands in
integer positions), `InstScopeT` (its instructions in `Compile.instET`), integer extern
signatures. This file states the obligations over such contexts (`CtxT`), for the integer
instructions of a mixed context; the float families already proven over `CtxInvT`
(`LowerRulesCorrectT`, `MemRulesCorrectRT`, `LowerRulesCorrectFT`) are reused unchanged.

* `CtxT f ctx`: `CtxInvT f ctx ∧ InstScopeT ctx ∧` integer externs (`CtxInv.toCtxT`).
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
(`CtxInvT`), its instructions in the typed movement scope (`InstScopeT`), and the function's
externs with integer signatures (`Compile.functionET`: calls are integer-only). -/
structure CtxT (f : Clif.Function) (ctx : Ctx) : Prop where
  inv : CtxInvT f ctx
  scope : InstScopeT ctx
  externs : f.externs.all (Compile.sigE ·.2.sig) = true

/-- **Integer specialization**: a subset-E context is a typed one. -/
theorem CtxInv.toCtxT {f : Clif.Function} {ctx : Ctx} (h : CtxInv f ctx)
    (hE : Compile.functionE f = true) : CtxT f ctx := by
  refine ⟨h.toT, h.instScopeT, ?_⟩
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

/-- **The closure roots of `lower` other than the float ones never match a non-E instruction
of a typed context** (FloatsC7F): on an instruction of the typed scope outside subset E (a float
constant, `load`/`store` of a float, a `select` of floats, a `bitcast`), the first matching
closure root is a float-movement, float-memory or float-arithmetic root, or the `select` root
971 on a float `select`. Stated with the lowering's premise that the rules before `r` failed. -/
def NonEUnmatchableT (p : Program) : Prop :=
  ∀ r ∈ p.rulesOf TId.lower, closureRoot r = true → floatMoveRootRule r = false →
    floatMemRootRule r = false → floatArithRootRule r = false →
  ∀ (f : Clif.Function) (ctx : Ctx), CtxT f ctx →
  ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info →
    info.clif = some inst → Compile.instE inst = false → (r.id = 971 → ¬ FloatSelect inst) →
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
  ctx.insts[ti]? = some ⟨data, [], [], none⟩ → BrIdxTyped ctx t → TargetsLen t targets →
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
  tryCallData f (.tryCall fn args et) = .ok data → exnTableOpnd f et = .ok (sig, items) →
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
  ∀ ti t data targets out st st' tr, BrIdxTyped ctx t → TargetsLen t targets →
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
    tryCallData f (.tryCall fn args et) = .ok data →
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
  intro ti t data targets out st st' tr hbt htl hph hvb hd hemp hr
  refine (h f ctx ti t data targets out st st' tr hctx hbt htl hph hvb hd hemp hr).toT ?_
  have hE : CtxE (termCtx ctx ti data) := (ctxInv_termCtx hctx hph data).valTyE
  exact valClassOf_int_of_ctxE hE

theorem TryCalls.toT {W : Type} {f : Clif.Function} {ctx : Ctx} {sem : ISem CV W}
    {MR : MemRelTW W} {env : Clif.Env} {p : Clif.Program} {outB : Nat}
    (h : TryCalls f sem MR env p outB) (hctx : CtxInv f ctx) : TryCallsT f ctx sem MR env p outB :=
  fun ti fn args et data sig items targets info trs lo st1 out st' tr =>
    h ctx ti fn args et data sig items targets info trs lo st1 out st' tr hctx

theorem TryIndCalls.toT {W : Type} {f : Clif.Function} {ctx : Ctx} {sem : ISem CV W}
    {MR : MemRelTW W} {env : Clif.Env} {p : Clif.Program} {sigs : List Clif.Signature}
    (h : TryIndCalls sem MR env p sigs) (hctx : CtxInv f ctx) :
    TryIndCallsT f ctx sem MR env p sigs :=
  fun ti callee args et data sig items targets info trs lo st1 out st' tr =>
    h f ctx ti callee args et data sig items targets info trs lo st1 out st' tr hctx

end Backend.Proof.Driver
