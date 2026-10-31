import FV.Backend.Proof.LowerTotal
import FV.Backend.Proof.LowerLoopRunT
import FV.Backend.Proof.AbiClass

/-!
# Totality of the lowering: the driver on the typed scope (floats)

The typed twins of `LowerTotal.lean`'s `lowerFunction_ok` and `LowerTotalCtx.lean`'s
`buildCtx_ok`: `lowerFunction_okT` and `buildCtx_okT` prove the same totality with the typed
movement scope (`Compile.functionET`: subset E widened by the S11e4/S11f float data movement
and arithmetic) in place of subset E. The driver (`FV/Backend/Isel.lean`'s `lowerFunction`/
`buildCtx`) is class-agnostic — every loop matches `.vreg n _` — so each proof is the integer
one with the E-specific facts replaced:

* `ctx.valueReg? a = some (.vreg a .int)` (`CtxE`, `CtxFacts.vals_int`) becomes
  `ctx.valueReg? a = some (.vreg a (valClassOf ctx a))` (`CtxFacts.valsT`; `vregOf`);
* subset E's integer signatures (`functionE_sig_int`, `abiRetRegs_returns_int`) become the
  typed placement: `Compile.sigET` admits `f32`/`f64` parameters and returns, `sigArgs` accepts
  them (`sigArgs_okT`), and `abiRetRegs` succeeds for at most 8 returns of any class mix
  (`abiRetRegs_okT`, through `AbiClass.retRegsC_some`);
* `instData` accepts the float data movement (`instData_okT`: `f32const`/`f64const`, float
  `load`/`store`, `select`, `bitcast`), and its admitted result types are `valTyOk`
  (`tysOf_okT`), so `blockC_ofT` derives the class-agnostic `BlockC` from the typed scope and
  `buildCtx_okT` is `buildCtx_ok` with it.

Every other ingredient is reused from `LowerTotal.lean` (the loop machinery `forIn_ok`,
`entryLoop_ok`, `paramsPart_ok'`, `finishBlock_ok'`, `tryRegsOf_ok`, `exnTableOpnd_ok`,
`dataOk_of`, `sretBad_false`) — none of them mentions a register class. `lowerFunction_okT`
takes `LowerScopeT` (`LowerLoopCtxT.lean`) instead of the decider `lowerScopeTB` (whose
Backend-level soundness lives under `FV/E2E`), which decides it.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-! ## Typed type facts -/

theorem tyE_eq_eTy (t : Clif.Ty) : Compile.tyE t = eTy t := rfl

theorem tyM_ne_i128 {t : Clif.Ty} (h : Compile.tyM t = true) : t ≠ .i128 := by
  intro he; subst he; simp [Compile.tyM, Compile.tyE] at h

theorem valTyOk_of_tyE {ty : Clif.Ty} (h : Compile.tyE ty = true) : valTyOk ty = true := by
  cases ty <;> simp_all [valTyOk, eTy, Compile.tyE]

theorem valTyOk_of_isFloat {ty : Clif.Ty} (h : ty.isFloat = true) : valTyOk ty = true := by
  cases ty <;> simp_all [valTyOk, eTy, Compile.tyE]

/-! ## `instData` on the typed scope -/

/-- The instructions `instET` admits beyond subset E (`instE`): the float data movement. -/
theorem instET_cases {i : Clif.Inst} (h : Compile.instET i = true) :
    Compile.instE i = true ∨
    (∃ ty imm, i = .iconst ty imm) ∨ (∃ op ty fl p off, i = .load op ty fl p off) ∨
    (∃ op ty fl x p off, i = .store op ty fl x p off) ∨ (∃ ty c x y, i = .select ty c x y) ∨
    (∃ ty fl x, i = .bitcast ty fl x) := by
  cases i with
  | iconst ty imm =>
    cases ty
    · exact .inl (by simp [Compile.instE, Compile.tyE])
    · exact .inl (by simp [Compile.instE, Compile.tyE])
    · exact .inl (by simp [Compile.instE, Compile.tyE])
    · exact .inl (by simp [Compile.instE, Compile.tyE])
    · exact absurd h (by simp [Compile.instET, Compile.tyE])
    · exact .inr (.inl ⟨_, _, rfl⟩)
    · exact .inr (.inl ⟨_, _, rfl⟩)
  | unary op ty x => exact .inl h
  | binary op ty x y => exact .inl h
  | div op ty x y => exact .inl h
  | overflow op ty x y =>
    exact absurd (show Compile.instE (Clif.Inst.overflow op ty x y) = true from h)
      (by simp [Compile.instE])
  | carry op ty x y c =>
    exact absurd (show Compile.instE (Clif.Inst.carry op ty x y c) = true from h)
      (by simp [Compile.instE])
  | uaddOverflowTrap ty x y code =>
    exact absurd (show Compile.instE (Clif.Inst.uaddOverflowTrap ty x y code) = true from h)
      (by simp [Compile.instE])
  | icmp cc ty x y => exact .inl h
  | select ty c x y =>
    exact .inr (.inr (.inr (.inr (.inl ⟨_, _, _, _, rfl⟩))))
  | selectSpectreGuard ty c x y =>
    exact absurd (show Compile.instE (Clif.Inst.selectSpectreGuard ty c x y) = true from h)
      (by simp [Compile.instE])
  | bitselect ty c x y =>
    exact absurd (show Compile.instE (Clif.Inst.bitselect ty c x y) = true from h)
      (by simp [Compile.instE])
  | bmask ty x => exact .inl h
  | extend op ty x => exact .inl h
  | ireduce ty x => exact .inl h
  | iconcat ty lo hi =>
    exact absurd (show Compile.instE (Clif.Inst.iconcat ty lo hi) = true from h)
      (by simp [Compile.instE])
  | isplit ty x =>
    exact absurd (show Compile.instE (Clif.Inst.isplit ty x) = true from h)
      (by simp [Compile.instE])
  | load op ty fl p off =>
    simp only [Compile.instET, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨hfl, hty⟩ := h
    rcases hty with hty | ⟨-, -⟩
    · exact .inl (by simp [Compile.instE, hty, hfl])
    · exact .inr (.inr (.inl ⟨_, _, _, _, _, rfl⟩))
  | store op ty fl x p off =>
    simp only [Compile.instET, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨hfl, hty⟩ := h
    rcases hty with hty | ⟨-, -⟩
    · exact .inl (by simp [Compile.instE, hty, hfl])
    · exact .inr (.inr (.inr (.inl ⟨_, _, _, _, _, _, rfl⟩)))
  | stackAddr ty slot off => exact .inl h
  | call fn args => exact .inl h
  | callIndirect sig callee args => exact .inl h
  | funcAddr ty fn => exact .inl h
  | atomicRmw op ty fl p x => exact .inl h
  | atomicCas ty fl p e x => exact .inl h
  | atomicLoad ty fl p => exact .inl h
  | atomicStore ty fl x p => exact .inl h
  | fence => exact .inl h
  | bitcast ty fl x => exact .inr (.inr (.inr (.inr (.inr ⟨_, _, _, rfl⟩))))
  | trapz c code =>
    exact absurd (show Compile.instE (Clif.Inst.trapz c code) = true from h)
      (by simp [Compile.instE])
  | trapnz c code =>
    exact absurd (show Compile.instE (Clif.Inst.trapnz c code) = true from h)
      (by simp [Compile.instE])
  | nop => exact .inl h
  | symbolValue ty gv => exact .inl h
  | tlsValue ty gv => exact .inl h
  | float op ty args =>
    exact absurd (show Compile.instE (Clif.Inst.float op ty args) = true from h)
      (by simp [Compile.instE])

/-- Little-endian (or default) memory flags: `flagsE`. -/
theorem endianness_none_of_flagsE {fl : Clif.MemFlags} (h : Compile.flagsE fl = true) :
    (fl.endianness == some Clif.Endianness.big) = false := by
  simp only [Compile.flagsE, Bool.and_eq_true] at h
  rw [Option.isNone_iff_eq_none.mp h.1.1]; rfl

/-- `instData` succeeds on a statement of the typed movement scope satisfying `stmtInB`:
subset E's cases as in `instData_ok`, plus the float data movement `instET` adds
(`iconst.f32`/`iconst.f64`, float `load`/`store`, `select` and `bitcast` at `valTyOk` types). -/
theorem instData_okT {f : Clif.Function} {s : Clif.Stmt} (hT : Compile.instET s.inst = true)
    (hs : stmtInB f s = true) : ∃ d, instData f s.inst = .ok d := by
  rcases s with ⟨res, inst⟩
  have hT' : Compile.instET inst = true := hT
  rcases instET_cases hT' with hE | hiconst | hload | hstore | hselect | hbitcast
  · exact instData_ok (show Compile.instE (Clif.Stmt.inst ⟨res, inst⟩) = true from hE) hs
  · obtain ⟨ty, imm, rfl⟩ := hiconst
    cases ty <;> first
      | exact ⟨_, rfl⟩
      | exact absurd hT' (by simp [Compile.instET, Compile.tyE])
  · obtain ⟨op, ty, fl, p, off, rfl⟩ := hload
    simp only [Compile.instET, Bool.and_eq_true, Bool.or_eq_true] at hT'
    obtain ⟨hfl, hty⟩ := hT'
    have hbig := endianness_none_of_flagsE hfl
    rcases hty with hty | ⟨hty, hop⟩
    · have hty' : eTy ty = true := hty
      exact ⟨instDataV "Load" [opcodeV (loadOpcode op), .value p, .op (.memFlags fl), .int off],
        by simp [instData, hty', hbig, pure, Except.pure]⟩
    · refine ⟨instDataV "Load" [opcodeV (loadOpcode op), .value p, .op (.memFlags fl), .int off],
        ?_⟩
      cases ty with
      | i128 => exact absurd hty (by decide)
      | _ => simp [instData, eTy, hty, beq_iff_eq.mp hop, hbig, pure, Except.pure]
  · obtain ⟨op, ty, fl, x, p, off, rfl⟩ := hstore
    simp only [Compile.instET, Bool.and_eq_true, Bool.or_eq_true] at hT'
    obtain ⟨hfl, hty⟩ := hT'
    have hbig := endianness_none_of_flagsE hfl
    rcases hty with hty | ⟨hty, hop⟩
    · have hty' : eTy ty = true := hty
      exact ⟨instDataV "Store" [opcodeV (storeOpcode op), .values [x, p], .op (.memFlags fl),
          .int off],
        by simp [instData, hty', hbig, pure, Except.pure]⟩
    · refine ⟨instDataV "Store" [opcodeV (storeOpcode op), .values [x, p], .op (.memFlags fl),
          .int off], ?_⟩
      cases ty with
      | i128 => exact absurd hty (by decide)
      | _ => simp [instData, eTy, hty, beq_iff_eq.mp hop, hbig, pure, Except.pure]
  · obtain ⟨ty, c, x, y, rfl⟩ := hselect
    cases ty <;> first
      | exact ⟨_, rfl⟩
      | exact absurd hT' (by simp [Compile.instET, Compile.tyM, Compile.tyE])
  · obtain ⟨ty, fl, x, rfl⟩ := hbitcast
    cases ty <;> first
      | exact ⟨_, rfl⟩
      | exact absurd hT' (by simp [Compile.instET, Compile.tyM, Compile.tyE])

/-- The result types of a statement of the typed movement scope satisfying `stmtInB` are types
`buildCtx` admits (`valTyOk`: E's integers and `f32`/`f64`; `tysOf_ne` of `LowerTotalCtx.lean`
with `eTy` replaced), for a function with integer externs (S11f: the only fact of the scope
used). -/
theorem tysOf_okTB {f : Clif.Function} (hXE : f.externs.all (Compile.sigE ·.2.sig) = true)
    {s : Clif.Stmt} (hi : Compile.instET s.inst = true) (hs : stmtInB f s = true) :
    ∀ t ∈ tysOf f s, valTyOk t = true := by
  have hX : ∀ fn e, f.extern? fn = some e → ∀ p ∈ e.sig.returns, valTyOk p.ty = true := by
    intro fn e he p hp
    have := List.all_eq_true.mp hXE _ (Compile.lookup_mem he)
    simp only [Compile.sigE, Bool.and_eq_true, List.all_eq_true] at this
    exact valTyOk_of_tyE (this.2 p hp)
  rcases s with ⟨res, inst⟩
  have hi' : Compile.instET inst = true := hi
  rcases instET_cases hi' with hE | hiconst | hload | hstore | hselect | hbitcast
  · -- a subset-E instruction (`tysOf_ne`)
    unfold stmtInB at hs
    simp only [Bool.and_eq_true] at hs
    obtain ⟨-, hs⟩ := hs
    intro t ht
    cases inst with
    | call fn args =>
      cases h : f.extern? fn with
      | none => simp [tysOf, Clif.Inst.resultTypes, h] at ht
      | some e =>
        simp only [tysOf, Clif.Inst.resultTypes, h, Option.map_some, Option.getD_some,
          List.mem_map] at ht
        obtain ⟨p, hp, rfl⟩ := ht
        exact hX fn e h p hp
    | callIndirect sig c args =>
      cases h : f.sigDecls.lookup sig with
      | none => simp [tysOf, Clif.Inst.resultTypes, h] at ht
      | some sg =>
        simp only [tysOf, Clif.Inst.resultTypes, h, Option.map_some, Option.getD_some,
          List.mem_map] at ht
        obtain ⟨p, hp, rfl⟩ := ht
        simp only [h, Bool.and_eq_true, List.all_eq_true] at hs
        exact valTyOk_of_tyE (hs.1 p hp)
    | unary op ty x =>
      cases op <;> simp_all [tysOf, Clif.Inst.resultTypes, Compile.instE, Compile.unaryTyE,
        Compile.unaryE, Compile.tyE, eTy, valTyOk]
    | _ =>
      simp_all [tysOf, Clif.Inst.resultTypes, Compile.instE, Compile.tyE, eTy, valTyOk,
        Compile.flagsE]
  · -- a float `iconst`
    obtain ⟨ty, imm, rfl⟩ := hiconst
    simp only [Compile.instET, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hi'
    intro t ht
    simp only [tysOf, Clif.Inst.resultTypes, Option.getD_some, List.mem_singleton] at ht
    subst ht
    rcases hi' with (h | h) | ⟨h, -⟩
    · exact valTyOk_of_tyE h
    · exact valTyOk_of_isFloat (by first | (rw [h]; decide) | decide)
    · exact valTyOk_of_isFloat (by first | (rw [h]; decide) | decide)
  · -- a float `load`
    obtain ⟨op, ty, fl, p, off, rfl⟩ := hload
    simp only [Compile.instET, Bool.and_eq_true, Bool.or_eq_true] at hi'
    obtain ⟨-, hty⟩ := hi'
    intro t ht
    simp only [tysOf, Clif.Inst.resultTypes, Option.getD_some, List.mem_singleton] at ht
    subst ht
    rcases hty with hty | ⟨hty, -⟩
    · exact valTyOk_of_tyE hty
    · exact valTyOk_of_isFloat hty
  · -- a float `store` (it has no results)
    obtain ⟨op, ty, fl, x, p, off, rfl⟩ := hstore
    intro t ht
    simp [tysOf, Clif.Inst.resultTypes] at ht
  · -- a float `select`
    obtain ⟨ty, c, x, y, rfl⟩ := hselect
    simp only [Compile.instET] at hi'
    intro t ht
    simp only [tysOf, Clif.Inst.resultTypes, Option.getD_some, List.mem_singleton] at ht
    subst ht
    exact valTyOk_of_tyM hi'
  · -- a `bitcast`
    obtain ⟨ty, fl, x, rfl⟩ := hbitcast
    simp only [Compile.instET] at hi'
    intro t ht
    simp only [tysOf, Clif.Inst.resultTypes, Option.getD_some, List.mem_singleton] at ht
    subst ht
    exact valTyOk_of_tyM hi'

/-- The result types of a statement of the typed movement scope satisfying `stmtInB` are types
`buildCtx` admits (`tysOf_okTB`). -/
theorem tysOf_okT {f : Clif.Function} (hET : Compile.functionET f = true) {s : Clif.Stmt}
    (hi : Compile.instET s.inst = true) (hs : stmtInB f s = true) :
    ∀ t ∈ tysOf f s, valTyOk t = true := by
  simp only [Compile.functionET, Bool.and_eq_true] at hET
  exact tysOf_okTB hET.1.1.1.2 hi hs

/-! ## What `buildCtx` checks of every block holds -/

/-- `blockC_of` on the typed movement scope: `BlockC`/`StmtC` are class-agnostic (`valTyOk`
admits `f32`/`f64`), so only the E-specific ingredients change (`instData_okT`, `tysOf_okT`,
`tyM` of the block parameters). -/
theorem blockC_ofT {f : Clif.Function} (hET : Compile.functionET f = true)
    (hst : ∀ B ∈ f.blocks, ∀ s ∈ B.body, stmtInB f s = true) : ∀ B ∈ f.blocks, BlockC f B := by
  intro B hB
  have hET' := hET
  simp only [Compile.functionET, Bool.and_eq_true, List.all_eq_true] at hET'
  obtain ⟨⟨hp, hb⟩, -⟩ := hET'.1.1.2 B hB
  refine ⟨fun q hq => valTyOk_of_tyM (hp q hq), fun s hs => ?_⟩
  have hi := hb s hs
  have hin := hst B hB s hs
  refine ⟨instData_okT hi hin, ?_, fun t ht => valTyOk_of_tyM (tysOf_okT hET hi hin t ht)⟩
  have h1 := hin
  unfold stmtInB at h1
  simp only [Bool.and_eq_true] at h1
  obtain ⟨h1, -⟩ := h1
  split at h1
  · rename_i tys hty
    exact ⟨tys, hty, by simpa using h1⟩
  · cases h1

/-! ## `buildCtx` succeeds (typed) -/

/-- **`buildCtx` is total** as soon as every block passes `buildCtx`'s class-agnostic checks
(`BlockC`; S11f: for any scope that gives them). -/
theorem buildCtx_okC {f : Clif.Function} (hC : ∀ B ∈ f.blocks, BlockC f B)
    (hssa : (valueDefs f).Nodup) (hst : ∀ B ∈ f.blocks, ∀ s ∈ B.body, stmtInB f s = true) :
    ∃ ctx ranges st0, buildCtx f = .ok (ctx, ranges, st0) := by
  unfold buildCtx
  simp only [bind, Except.bind, pure, Except.pure, forIn_okYield]
  rw [forIn_eq_fold (blockStepM f) f.blocks _ ?blk]
  · dsimp only
    rw [← Array.forIn_toList, forIn_eq_fold (fun _ _ => PUnit.unit) _ _ ?ptr]
    · exact ⟨_, _, _, rfl⟩
    · intro info hi _
      have hm : List.foldl (blockStepM f) (Array.replicate (maxVOf f) none,
          Array.replicate (maxVOf f) none, #[], #[]) f.blocks = ctxModel f (maxVOf f) := rfl
      have hvt := fun p (hp : (p, Clif.Ty.i64) ∈ valTysOf f) => valTy_model hC hssa hp
      have hins : (ctxModel f (maxVOf f)).2.2.1.toList = instsOf f f.blocks := by
        unfold ctxModel; rw [blockFold]; simp
      unfold maxVOf at hm hvt hins
      rw [hm] at hi ⊢
      rw [hins] at hi
      rcases instsOf_mem hi with rfl | ⟨B, hB, s, hs, rfl⟩
      · rfl
      · have hin := hst B hB s hs
        unfold stmtInB at hin
        simp only [Bool.and_eq_true] at hin
        obtain ⟨-, hin⟩ := hin
        simp only [infoOf]
        cases hsi : s.inst <;> simp only [hsi] at hin <;> try rfl
        all_goals
          simp only [List.contains_iff_mem] at hin
          simp only [hvt _ hin]
          rfl
  · intro B hB a
    obtain ⟨hpar, hss⟩ := hC B hB
    rw [forIn_eq_fold parStepM B.params _ ?par]
    · dsimp only
      rw [forIn_eq_fold (stmtStepM f) B.body _ ?stm]
      · rfl
      · intro s hs a
        obtain ⟨⟨d, hd⟩, ⟨tys, hty, hlen⟩, hne⟩ := hss s hs
        have htys : tysOf f s = tys := by simp [tysOf, hty]
        rw [htys] at hne
        simp only [hd, hty, hlen, bne_self_eq_false, Bool.false_eq_true, ite_false]
        rw [forIn_eq_fold (resStepM a.2.2.size) _ _ ?res]
        · simp [stmtStepM, htys, infoOf, dataOf, hd]
        · intro p hp b
          have := hne p.2 (List.of_mem_zip hp).2
          simp [this, resStepM]
    · intro q hq vt
      simp [hpar q hq, parStepM]

/-- **`buildCtx` is total on the typed movement scope** (`buildCtx_ok` with `functionET` for
`functionE`): subset-E's integer block parameters, statement data and result types are
`valTyOk` types, the load/store addresses are the declared `i64` values — all `buildCtx`
checks, which are class-agnostic. -/
theorem buildCtx_okT {f : Clif.Function} (hET : Compile.functionET f = true)
    (hssa : (valueDefs f).Nodup) (hst : ∀ B ∈ f.blocks, ∀ s ∈ B.body, stmtInB f s = true) :
    ∃ ctx ranges st0, buildCtx f = .ok (ctx, ranges, st0) :=
  buildCtx_okC (blockC_ofT hET hst) hssa hst

/-! ## The ABI of a typed signature -/

/-- `sigArgs` computes on a `sigAbiOk` signature whose parameters are `tyM` types (E's
integers and `f32`/`f64`, so no `i128`). -/
theorem sigArgs_okT {s : Clif.Signature} (hA : sigAbiOk s = true)
    (hM : ∀ p ∈ s.params, Compile.tyM p.ty = true) : ∃ bytes, sigArgs s = .ok bytes := by
  unfold sigArgs
  refine lmapM_ok' _ fun p hp => ?_
  simp only [sigAbiOk, Bool.and_eq_true, List.all_eq_true] at hA
  have h1 := hA.1.1.1 p hp
  have h2 : p.ty ≠ .i128 := tyM_ne_i128 (hM p hp)
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h1
  rcases h1 with h1 | ⟨h1, h3⟩ <;> simp [pure, Except.pure, *]

/-- `abiRetRegs` computes for at most 8 returns (`retRegsC` of their classes: every class has
one register per return, and an `sret` signature without returns has the single struct pointer
in x0). -/
theorem abiRetRegs_okT {s : Clif.Signature} (h8 : s.returns.length ≤ 8) :
    ∃ ps, abiRetRegs s = some ps := by
  have h : ((sigRets s).map retClass).length ≤ 8 := by rw [List.length_map]; exact sigRets_le h8
  unfold abiRetRegs
  obtain ⟨ps, hp⟩ := retRegsC_some ((sigRets s).map retClass) 0 0 (by omega) (by omega)
  exact ⟨ps, hp⟩

/-! ## The value registers of `buildCtx`'s context (typed) -/

/-- Every value of `f` has its own vreg of its type's class (`CtxFacts.vals_int` without the
integer premise). -/
theorem CtxFacts.valsT {f : Clif.Function} {ctx : Ctx} {st0 : LState} (hF : CtxFacts f ctx st0) :
    ∀ x ∈ valueDefs f, x < st0.nextVreg ∧
      ctx.valueReg? x = some (.vreg x (valClassOf ctx x)) := by
  intro x hx
  obtain ⟨hlt, t, ht, hr⟩ := hF.vals x hx
  rw [show valClassOf ctx x = t.valClass from by simp [valClassOf, ht]]
  exact ⟨hlt, hr⟩

/-! ## The loop bodies (typed) -/

/-- A branch's argument registers never fail (typed registers). -/
theorem blockArgRegs_okT' {f : Clif.Function} {ctx : Ctx} {bc : Clif.BlockCall}
    {tb : Clif.Block}
    (htb : f.block? bc.block = some tb) (hn : tb.params.length = bc.args.length)
    (hr : ∀ a ∈ bc.args, ctx.valueReg? a = some (.vreg a (valClassOf ctx a))) :
    ∃ args, blockArgRegs ctx f bc = .ok args := by
  unfold blockArgRegs
  simp only [htb, hn, bne_self_eq_false, Bool.false_eq_true, ite_false, bind, Except.bind]
  obtain ⟨ys, hys⟩ := amapM_ok' (g := fun a => match ctx.valueReg? a with
    | some r => (pure r : Except String Reg)
    | none => throw s!"unknown value v{a}") bc.args fun a ha => by
      simp [hr a ha, pure, Except.pure]
  exact ⟨ys, hys⟩

/-- The results loop of a statement succeeds on single-register results (typed registers). -/
theorem resLoop_okT {ctx : Ctx} (results : List Nat) (rss : List (List Reg))
    (hr : ∀ r ∈ results, ctx.valueReg? r = some (.vreg r (valClassOf ctx r)))
    (hl : ∀ rs ∈ rss, rs.length = 1)
    (s : DState × Array MInst) : ∃ q, forIn (results.zip rss) s (resBody ctx) = .ok q := by
  refine forIn_ok' _ _ _ fun x hx b => ?_
  obtain ⟨r, rs⟩ := x
  have hr' := hr r (List.of_mem_zip hx).1
  obtain ⟨o, rfl⟩ := List.length_eq_one_iff.mp (hl rs (List.of_mem_zip hx).2)
  cases o <;> simp [resBody, hr', pure, Except.pure]

/-- A statement's lowering never fails: the ISLE run is `StmtProg`'s (typed registers). -/
theorem stmtBody_okT {ctx : Ctx} (hP : StmtProg ctx) {i : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[i]? = some info) (hc : info.clif = some inst)
    (hr : ∀ r ∈ info.results, ctx.valueReg? r = some (.vreg r (valClassOf ctx r)))
    (s : DState × Array MInst) :
    ∃ s', stmtBody ctx i s = .ok (.yield s') := by
  obtain ⟨rss, s', tr, hrun, hlen⟩ := hP i info inst { s.1.st with emitted := #[] } hi hc
  unfold stmtBody
  simp only [bind, Except.bind, hrun, getElem!_of hi]
  by_cases he : info.results = []
  · simp only [he, List.isEmpty_nil, Bool.not_true, Bool.and_false, Bool.false_eq_true,
      ite_false, List.zip_nil_left, List.forIn_nil, pure, Except.pure]
    exact ⟨_, rfl⟩
  · obtain ⟨hl1, hl2⟩ := hlen he
    obtain ⟨q, hq⟩ := resLoop_okT (ctx := ctx) info.results rss hr hl2 (s.1, #[])
    simp only [hl1, bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ite_false, hq,
      pure, Except.pure]
    exact ⟨_, rfl⟩

/-- A branch successor's edge never fails; it adds one target (typed registers). -/
theorem destBody_okT {f : Clif.Function} {ctx : Ctx} {bc : Clif.BlockCall} {tb : Clif.Block}
    (htb : f.block? bc.block = some tb) (hn : tb.params.length = bc.args.length)
    (hr : ∀ a ∈ bc.args, ctx.valueReg? a = some (.vreg a (valClassOf ctx a)))
    (s : DState × Array Label) :
    ∃ s', destBody f ctx bc s = .ok (.yield s') ∧ s'.2.size = s.2.size + 1 := by
  obtain ⟨tl, htl⟩ := blockIdx_of_block htb
  unfold destBody
  simp only [bind, Except.bind, htl]
  split
  · exact ⟨_, rfl, by simp⟩
  · obtain ⟨args, ha⟩ := blockArgRegs_okT' htb hn hr
    simp only [ha, pure, Except.pure]
    exact ⟨_, rfl, by simp⟩

/-- A `try_call` successor argument that `ArgOkT` accepts has a register (typed). -/
theorem tryArgE_okT' {ctx : Ctx} {rets pays : Array Reg} {nh k : Nat} {a : Clif.TryArg}
    (h : ArgOkT ctx nh rets.size pays.size k a) : ∃ r, tryArgE ctx rets pays nh k a = .ok r := by
  cases a with
  | val v => simp only [ArgOkT] at h; simp [tryArgE, h, pure, Except.pure]
  | ret i =>
    simp only [ArgOkT] at h
    simp [tryArgE, h.1, Array.getElem?_eq_getElem h.2, pure, Except.pure]
  | exn i =>
    simp only [ArgOkT] at h
    simp [tryArgE, h.1, Array.getElem?_eq_getElem h.2, pure, Except.pure]

/-- A `try_call` successor's edge never fails; it adds one target (typed registers). -/
theorem tryBody_okT {f : Clif.Function} {ctx : Ctx} {rets pays : Array Reg} {nh k : Nat}
    {td : Clif.TryDest} (h : TryDestOkT f ctx nh rets.size pays.size k td)
    (s : DState × Array Label) :
    ∃ s', tryBody f ctx rets pays nh (td, k) s = .ok (.yield s') ∧ s'.2.size = s.2.size + 1 := by
  obtain ⟨⟨tb, htb, hn⟩, ha⟩ := h
  obtain ⟨tl, htl⟩ := blockIdx_of_block htb
  obtain ⟨args, hargs⟩ := amapM_ok' (g := tryArgE ctx rets pays nh k) td.args
    fun a hm => tryArgE_okT' (ha a hm)
  unfold tryBody
  simp only [bind, Except.bind, htl, htb, hn, bne_self_eq_false, Bool.false_eq_true, ite_false,
    hargs, pure, Except.pure]
  exact ⟨_, rfl, by simp⟩

/-- What the driver needs of a `try_call`'s exception table (typed: the value arguments have
the registers `buildCtx` gives them, `ArgOkT`). -/
structure TryOkT (f : Clif.Function) (ctx : Ctx) (et : Clif.ExnTable) (sig : Clif.Signature)
    (items : List (Option Nat)) : Prop where
  opnd : exnTableOpnd f et = .ok (sig, items)
  rets : sig.returns.length ≤ 8
  i128 : (sig.returns.any fun x => x.ty == Clif.Ty.i128) = false
  items : items.length = et.handlers.length
  dests : ∀ k td, et.dests[k]? = some td →
    TryDestOkT f ctx et.handlers.length sig.returns.length (payloadRegs sig.callConv).length k td

/-- What the driver needs of a `try_call`'s exception table, from `tryInB`, the values'
registers and `LowerScopeT.tryRet` (typed). -/
theorem tryOk_ofT {f : Clif.Function} {ctx : Ctx} {et : Clif.ExnTable}
    (hin : tryInB f et = true)
    (hval : ∀ td ∈ et.dests, ∀ v, Clif.TryArg.val v ∈ td.args →
      ctx.valueReg? v = some (.vreg v (valClassOf ctx v)))
    (hret : ∀ sig, f.sigDecls.lookup et.sig = some sig → ∀ i, Clif.TryArg.ret i ∈ et.normal.args →
      i < sig.returns.length) :
    ∃ sig items, TryOkT f ctx et sig items := by
  unfold tryInB at hin
  cases hs : f.sigDecls.lookup et.sig with
  | none => simp [hs] at hin
  | some s =>
    simp only [hs, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hin
    obtain ⟨⟨⟨⟨⟨⟨⟨hint, hcc⟩, h8⟩, h128⟩, hitems⟩, hhand⟩, hnorm⟩, hnargs⟩ := hin
    obtain ⟨items, hex, hil⟩ := exnTableOpnd_ok hs hcc hint hitems
    have hpl := payloadRegs_length hcc
    refine ⟨s, items, hex, h8, ?_, by rw [hil, handlers_length hitems], fun k td hk => ?_⟩
    · simp only [List.any_eq_false, beq_iff_eq]
      intro x hx; simpa using h128 x hx
    · have htdm : td ∈ et.dests := List.mem_of_getElem? hk
      have hdest : ∀ td : Clif.TryDest, tryDestInB f td = true →
          ∃ tb, f.block? td.block = some tb ∧ tb.params.length = td.args.length := by
        intro td h
        unfold tryDestInB at h
        split at h
        · rename_i tb htb; exact ⟨tb, htb, by simpa using h⟩
        · cases h
      rw [hpl]
      by_cases hkh : k < et.handlers.length
      · have e : td = et.handlers[k] := by
          simp only [Clif.ExnTable.dests] at hk
          rw [List.getElem?_append_left hkh, List.getElem?_eq_getElem hkh] at hk
          exact (Option.some.inj hk).symm
        have hm : td ∈ et.handlers := by rw [e]; exact List.getElem_mem hkh
        obtain ⟨h1, h2⟩ := hhand td hm
        refine ⟨hdest td h1, fun a ha => ?_⟩
        have := h2 a ha
        cases a with
        | val v => exact hval td htdm v ha
        | ret i => simp at this
        | exn i => exact ⟨by omega, by simpa using this⟩
      · have hkl : k < et.dests.length := (List.getElem?_eq_some_iff.mp hk).1
        have hke : k = et.handlers.length := by
          simp only [Clif.ExnTable.dests, List.length_append, List.length_singleton] at hkl
          omega
        have e : td = et.normal := by
          simp only [Clif.ExnTable.dests] at hk
          rw [List.getElem?_append_right (by omega), hke, Nat.sub_self] at hk
          simpa using hk.symm
        subst e
        refine ⟨hdest _ hnorm, fun a ha => ?_⟩
        have := hnargs a ha
        cases a with
        | val v => exact hval _ htdm v ha
        | ret i => exact ⟨hkh, hret s hs i ha⟩
        | exn i => simp at this

/-- A `try_call` terminator never fails: the ISLE run is `TryProg`'s (typed registers). -/
theorem tryTerm_okT {f : Clif.Function} {ctx : Ctx} (hP : TryProg f ctx) {b : Clif.Block}
    (hb : b ∈ f.blocks) {bi ti : Nat} (hti : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩)
    {code : Array MInst} {d : DState} {data : V} {et : Clif.ExnTable} (het : IsTryWith b.term et)
    (hdata : tryCallData f b.term = .ok data) {sig : Clif.Signature} {items : List (Option Nat)}
    (hT : TryOkT f ctx et sig items) (hpar : ∀ q ∈ b.params, ∃ r, ctx.valueReg? q.1 = some r) :
    ∃ d', tryTerm f ctx b bi ti code d (termCtx ctx ti data) et = .ok (.yield d') := by
  obtain ⟨rets, pays, st', hreg, hrl, hpl⟩ := tryRegsOf_ok hT.rets d.st
  have hregC : tryRegsOfC sig d.st = some ((rets, pays), st') := by
    rw [tryRegsOfC_eq (sigRets_classes_int (sigIntB_iff.mp (exnTableOpnd_int hT.opnd)).2)]
    exact hreg
  unfold tryTerm
  simp only [bind, Except.bind, exnTableOpndC_of hT.opnd, hregC, hT.i128, Bool.false_eq_true,
    ite_false]
  obtain ⟨s, hs, hsz⟩ := forIn_ok (tryBody f ctx rets.toArray pays.toArray et.handlers.length)
    (fun j (s : DState × Array Label) => s.2.size = j) et.dests.zipIdx 0 ({ d with st := st' }, #[])
    rfl (fun x hx j s hj => by
      obtain ⟨td, k⟩ := x
      have hk := List.mem_zipIdx_iff_getElem?.mp hx
      have h := hT.dests k td hk
      have e1 : rets.toArray.size = rets.length := by simp
      have e2 : pays.toArray.size = pays.length := by simp
      rw [← hrl, ← hpl, ← e1, ← e2] at h
      obtain ⟨s', h1, h2⟩ := tryBody_okT h s
      exact ⟨s', h1, by rw [h2, hj]⟩)
  rw [hs]
  simp only [List.length_zipIdx, Nat.zero_add] at hsz
  have hlen : s.2.toList.length = items.length + 1 := by
    rw [Array.length_toList, hsz, hT.items]; simp [Clif.ExnTable.dests]
  have hti' : ti < ctx.insts.size := (Array.getElem?_eq_some_iff.mp hti).1
  obtain ⟨v, s', tr, c, hrun, hc⟩ := hP ti b.term et data sig items (rets, pays) d.st st'
    s.2.toList { s.1.st with emitted := #[] } hti' hti ⟨b, hb, rfl⟩ (exnOf_of het) hdata hT.opnd
    hreg hlen
  simp only [tryInfoOf, hlen, bne_self_eq_false, Bool.false_eq_true, ite_false]
  refine finishBlock_ok' (v := v) (st := s') (n := tr) ?_ (fun _ _ => ⟨c, hc⟩) hpar
  rw [termCall_try het]
  simpa [tryCallF, tryCtx] using hrun

/-- A terminator's lowering never fails: the ISLE runs are `TermProg`'s and `TryProg`'s (typed
registers). -/
theorem termPart_okT' {f : Clif.Function} {ctx : Ctx} (hP : IselProg f ctx) {b : Clif.Block}
    (hb : b ∈ f.blocks) {bi stop : Nat}
    (hti : ctx.insts[stop - 1]? = some ⟨.op .unit, [], [], none⟩) {code : Array MInst}
    {d : DState} {data : V} (hdata : DataOk f b.term data) (hsret : sretBad f b.term = false)
    (hdests : ∀ bc ∈ dests b.term, ∃ tb, f.block? bc.block = some tb ∧
      tb.params.length = bc.args.length ∧
      ∀ a ∈ bc.args, ctx.valueReg? a = some (.vreg a (valClassOf ctx a)))
    (htry : ∀ et, IsTryWith b.term et → ∃ sig items, TryOkT f ctx et sig items)
    (hpar : ∀ q ∈ b.params, ∃ r, ctx.valueReg? q.1 = some r) :
    ∃ d', termPart f ctx b bi stop code d data = .ok (.yield d') := by
  have hti' : stop - 1 < ctx.insts.size := (Array.getElem?_eq_some_iff.mp hti).1
  unfold termPart
  rw [hsret]
  simp only [Bool.false_eq_true, ite_false]
  split
  · rename_i bc heq
    obtain ⟨tb, htb, hn, hr⟩ := hdests bc (by rw [heq]; simp [dests])
    obtain ⟨ja, hja⟩ := blockArgRegs_okT' htb hn hr
    obtain ⟨tl, htl⟩ := blockIdx_of_block htb
    simp only [bind, Except.bind, hja, htl]
    have hd : termData (abiTerm f b.term) = .ok data := by
      rw [heq] at hdata ⊢; exact hdata
    obtain ⟨v, s', tr, hrun⟩ := hP.term (stop - 1) b.term data [tl] { d.st with emitted := #[] }
      hti' hti ⟨b, hb, rfl⟩ (by rw [heq]; rfl) hd (by rw [heq]; rfl)
    exact finishBlock_ok' (v := v) (st := s') (n := tr) hrun (fun _ h => nomatch h) hpar
  · rename_i fn args et heq
    have het : IsTryWith b.term et := .inl ⟨fn, args, heq⟩
    obtain ⟨sig, items, hT⟩ := htry et het
    have hd : tryCallData f b.term = .ok data := by
      rw [heq] at hdata ⊢; exact hdata
    exact tryTerm_okT hP.try_ hb hti het hd hT hpar
  · rename_i c args et heq
    have het : IsTryWith b.term et := .inr ⟨c, args, heq⟩
    obtain ⟨sig, items, hT⟩ := htry et het
    have hd : tryCallData f b.term = .ok data := by
      rw [heq] at hdata ⊢; exact hdata
    exact tryTerm_okT hP.try_ hb hti het hd hT hpar
  · rename_i h1 h2 h3
    have hnt : b.term.isTry = false := by
      cases ht : b.term with
      | tryCall fn args et => exact absurd ht (h2 fn args et)
      | tryCallIndirect c args et => exact absurd ht (h3 c args et)
      | _ => rfl
    have hd : termData (abiTerm f b.term) = .ok data := by
      unfold DataOk at hdata
      split at hdata
      · rename_i fn args et ht; exact absurd ht (h2 fn args et)
      · rename_i c args et ht; exact absurd ht (h3 c args et)
      · exact hdata
    obtain ⟨s, hs, hsz⟩ := forIn_ok (destBody f ctx)
      (fun j (s : DState × Array Label) => s.2.size = j)
      (destsOf b.term) 0 (d, #[]) rfl (fun bc hbc j s hj => by
        rw [destsOf_eq] at hbc
        obtain ⟨tb, htb, hn, hr⟩ := hdests bc hbc
        obtain ⟨s', h1, h2⟩ := destBody_okT htb hn hr s
        exact ⟨s', h1, by rw [h2, hj]⟩)
    simp only [bind, Except.bind, hs]
    obtain ⟨v, s', tr, hrun⟩ := hP.term (stop - 1) b.term data s.2.toList
      { s.1.st with emitted := #[] } hti' hti ⟨b, hb, rfl⟩ hnt hd (by simp [hsz])
    exact finishBlock_ok' (v := v) (st := s') (n := tr) hrun (fun _ h => nomatch h) hpar

/-- A block's statements and terminator never fail (typed registers). -/
theorem bodyPart_okT' {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (sp : CtxSpec f ctx ranges st0) (hP : IselProg f ctx) {bi : Nat} {B : Clif.Block}
    (hB : f.blocks[bi]? = some B) (hdata : ∃ data, DataOk f B.term data)
    (hsret : sretBad f B.term = false)
    (hdests : ∀ bc ∈ dests B.term, ∃ tb, f.block? bc.block = some tb ∧
      tb.params.length = bc.args.length ∧
      ∀ a ∈ bc.args, ctx.valueReg? a = some (.vreg a (valClassOf ctx a)))
    (htry : ∀ et, IsTryWith B.term et → ∃ sig items, TryOkT f ctx et sig items)
    (hpar : ∀ q ∈ B.params, ∃ r, ctx.valueReg? q.1 = some r) (d : DState) (code : Array MInst) :
    ∃ d', bodyPart f ctx B bi (blockStart f bi) (blockStart f bi + B.body.length + 1) d code =
      .ok (.yield d') := by
  have hBm := List.mem_of_getElem? hB
  have hti : ctx.insts[blockStart f bi + B.body.length + 1 - 1]? =
      some ⟨.op .unit, [], [], none⟩ := by
    rw [Nat.add_sub_cancel]; exact sp.facts.term bi B hB
  obtain ⟨data, hd⟩ := hdata
  unfold bodyPart
  simp only [bind, Except.bind]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.add_sub_cancel_left, Nat.add_one_sub_one, Nat.div_one]
  obtain ⟨s, hs⟩ := forIn_ok' (stmtBody ctx) (List.range' (blockStart f bi) B.body.length)
    (d, code)
    (fun i hi s => by
      obtain ⟨h1, h2⟩ := List.mem_range'_1.mp hi
      obtain ⟨j, rfl⟩ : ∃ j, i = blockStart f bi + j := ⟨i - blockStart f bi, by omega⟩
      have hj : j < B.body.length := by omega
      obtain ⟨info, hinfo, hc, hr⟩ := sp.facts.stmt bi B j _ hB (List.getElem?_eq_getElem hj)
      refine stmtBody_okT hP.stmt hinfo hc (fun r hr' => ?_) s
      rw [hr] at hr'
      refine (sp.facts.valsT r ?_).2
      simp only [valueDefs, List.mem_flatMap, List.mem_append]
      exact ⟨B, hBm, .inr ⟨_, List.getElem_mem hj, hr'⟩⟩)
  rw [hs]
  dsimp only
  split
  · rename_i fn args et heq
    have hd' : tryCallData f B.term = .ok data := by
      unfold DataOk at hd; rw [heq] at hd ⊢; exact hd
    simp only [tryCallDataC_of hd']
    exact termPart_okT' hP hBm hti (by rwa [heq] at hd ⊢) hsret hdests htry hpar
  · rename_i c args et heq
    have hd' : tryCallData f B.term = .ok data := by
      unfold DataOk at hd; rw [heq] at hd ⊢; exact hd
    simp only [tryCallDataC_of hd']
    exact termPart_okT' hP hBm hti (by rwa [heq] at hd ⊢) hsret hdests htry hpar
  · rename_i h2 h3
    have hd' : termData (abiTerm f B.term) = .ok data := by
      unfold DataOk at hd
      split at hd
      · rename_i fn args et ht; exact absurd ht (h2 fn args et)
      · rename_i c args et ht; exact absurd ht (h3 c args et)
      · exact hd
    simp only [hd']
    exact termPart_okT' hP hBm hti hd hsret hdests htry hpar

/-- A block's lowering never fails (typed registers). -/
theorem blockBody_okT' {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (sp : CtxSpec f ctx ranges st0) (hP : IselProg f ctx) {paramBytes : List Nat} {bi : Nat}
    {B : Clif.Block} (hB : f.blocks[bi]? = some B)
    (hent : ∃ locs n, sigArgLocs f.sig = .ok (locs, n)) (hdata : ∃ data, DataOk f B.term data)
    (hsret : sretBad f B.term = false)
    (hdests : ∀ bc ∈ dests B.term, ∃ tb, f.block? bc.block = some tb ∧
      tb.params.length = bc.args.length ∧
      ∀ a ∈ bc.args, ctx.valueReg? a = some (.vreg a (valClassOf ctx a)))
    (htry : ∀ et, IsTryWith B.term et → ∃ sig items, TryOkT f ctx et sig items)
    (hpar : ∀ q ∈ B.params, ∃ r, ctx.valueReg? q.1 = some r) (d : DState) :
    ∃ d', blockBody f ctx ranges paramBytes (B, bi) d = .ok (.yield d') := by
  unfold blockBody
  simp only [getElem!_of (sp.ranges bi B hB)]
  split
  · obtain ⟨locs, n, hl⟩ := hent
    simp only [bind, Except.bind, hl]
    obtain ⟨s, hs⟩ := entryLoop_ok (ctx := ctx) ((B.params.zip locs).zip paramBytes)
      (fun x hx => hpar _ (List.of_mem_zip (List.of_mem_zip hx).1).1) (#[], #[])
    rw [hs]
    exact bodyPart_okT' sp hP hB hdata hsret hdests htry hpar _ _
  · exact bodyPart_okT' sp hP hB hdata hsret hdests htry hpar _ _

/-! ## The driver is total (typed) -/

/-- **Totality of the lowering driver** for any scope whose blocks pass `buildCtx`'s checks
(`hC`), with `Compile.sigET` signature, `termE` terminators, a nonempty body and in-range
`try_call` returns (S11f: the scope-specific facts `lowerFunction_okT` takes from
`Compile.functionET`/`LowerScopeT`): on input with `sigAbiOk`, dominance, branch arity, entry
parameters and `driverInB`, `lowerFunction` succeeds as soon as the ISLE runs on `buildCtx`'s
context make progress (`IselProg`). -/
theorem lowerFunction_okG {f : Clif.Function}
    (hC : (∀ B ∈ f.blocks, ∀ s ∈ B.body, stmtInB f s = true) → ∀ B ∈ f.blocks, BlockC f B)
    (hsigET : Compile.sigET f.sig = true) (hterm : ∀ B ∈ f.blocks, Compile.termE B.term = true)
    (hne : f.blocks ≠ [])
    (htr : ∀ B ∈ f.blocks, ∀ et, IsTryWith B.term et → ∀ sig, f.sigDecls.lookup et.sig = some sig →
      ∀ i, Clif.TryArg.ret i ∈ et.normal.args → i < sig.returns.length)
    (hsig : sigAbiOk f.sig = true) (hdom : dominatedB f = true)
    (har : Spill.arityOkB f = true) (hent : Spill.entryParamsB f = true)
    (hin : driverInB f = true)
    (hprog : ∀ ctx ranges st0, buildCtx f = .ok (ctx, ranges, st0) → IselProg f ctx) :
    ∃ vc, lowerFunction f = .ok vc := by
  simp only [driverInB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hin
  obtain ⟨⟨hcc, h8⟩, hbl⟩ := hin
  have hssa : (valueDefs f).Nodup := by
    simp only [dominatedB, Bool.and_eq_true] at hdom; exact nodupB_sound hdom.1
  have hst : ∀ B ∈ f.blocks, ∀ s ∈ B.body, stmtInB f s = true := fun B hB s hs => (hbl B hB).1 s hs
  obtain ⟨ctx, ranges, st0, hb⟩ := buildCtx_okC (hC hst) hssa hst
  have sp := ctxSpec_of hb
  have hP := hprog _ _ _ hb
  have hd := dominated_of hdom
  have hreg : ∀ x ∈ valueDefs f, ctx.valueReg? x = some (.vreg x (valClassOf ctx x)) :=
    fun x hx => (sp.facts.valsT x hx).2
  simp only [Compile.sigET, Bool.and_eq_true, List.all_eq_true] at hsigET
  obtain ⟨hMp, hMr⟩ := hsigET
  obtain ⟨bytes, hbytes⟩ := sigArgs_okT hsig hMp
  obtain ⟨locs, n, hlocs⟩ := sigArgLocs_ok hbytes
  have h2 : (f.sig.returns.any (·.ty == .i128)) = false := by
    simp only [List.any_eq_false, beq_iff_eq]
    intro x hx
    exact tyM_ne_i128 (hMr x hx)
  have h3 : (f.sig.params.any (·.purpose == .sret) && !f.sig.returns.isEmpty) = false := by
    simp only [sigAbiOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hsig
    rcases hsig.2 with h | h <;> simp [h]
  obtain ⟨ps, hps⟩ := abiRetRegs_okT h8
  rw [lowerFunction_eq]
  unfold lowerFunction'
  simp only [hcc, Bool.not_true, Bool.false_eq_true, ite_false, bind, Except.bind, sigParamBytes,
    hbytes, h2, h3, hps, Option.isNone_some, hb]
  obtain ⟨dF, hF⟩ := forIn_ok' (blockBody f ctx ranges bytes) f.blocks.zipIdx
    ({ st := st0, alias := #[], nextLabel := f.blocks.length } : DState) (fun x hx d => by
      obtain ⟨B, bi⟩ := x
      have hB : f.blocks[bi]? = some B := List.mem_zipIdx_iff_getElem?.mp hx
      have hBm := List.mem_of_getElem? hB
      have huse := (hd.uses ctx ranges st0 hb bi B hB).2
      have hT := (hbl B hBm).2
      have hbT' := hterm B hBm
      refine blockBody_okT' sp hP hB ⟨locs, n, hlocs⟩ (dataOk_of hbT' hT)
        (sretBad_false hne hent _) (fun bc hbc => ?_) (fun et het => ?_)
        (fun q hq => ⟨_, hreg q.1 ?_⟩) d
      · obtain ⟨tb, htb⟩ := Option.isSome_iff_exists.mp (termInB_dests hT bc hbc)
        exact ⟨tb, htb, Spill.arityOk_of har B hBm bc hbc tb htb, fun a ha =>
          hreg a (availOf_defs (huse a (dests_args_mem hbc ha)))⟩
      · exact tryOk_ofT (termInB_try het hT)
          (fun td htd v hv => hreg v (availOf_defs (huse v (try_vals_mem het htd hv))))
          (htr B hBm et het)
      · simp only [valueDefs, List.mem_flatMap, List.mem_append, List.mem_map]
        exact ⟨B, hBm, .inl ⟨q, hq, rfl⟩⟩)
  rw [hF]
  exact ⟨_, rfl⟩

/-- **Totality of the lowering driver on the typed scope** (`lowerFunction_ok` with
`Compile.functionET` for `Compile.functionE`): on input in the typed scope (`sigAbiOk`,
dominance, `LowerScopeT`, branch arity, entry parameters) satisfying `driverInB`,
`lowerFunction` succeeds as soon as the ISLE runs on `buildCtx`'s context make progress
(`IselProg`). -/
theorem lowerFunction_okT {f : Clif.Function} (hET : Compile.functionET f = true)
    (hsig : sigAbiOk f.sig = true) (hdom : dominatedB f = true) (hs : LowerScopeT f)
    (har : Spill.arityOkB f = true) (hent : Spill.entryParamsB f = true)
    (hin : driverInB f = true)
    (hprog : ∀ ctx ranges st0, buildCtx f = .ok (ctx, ranges, st0) → IselProg f ctx) :
    ∃ vc, lowerFunction f = .ok vc := by
  have hET' := hET
  simp only [Compile.functionET, Bool.and_eq_true, List.all_eq_true] at hET'
  exact lowerFunction_okG (blockC_ofT hET) hET'.1.1.1.1.1 (fun B hB => (hET'.1.1.2 B hB).2)
    hs.nonempty hs.tryRet hsig hdom har hent hin hprog

/-! ## Non-vacuity -/

/-- **Non-vacuity of `buildCtx_okT`**: the loop witness of `FV/E2E/LowerDirect.lean`
(`driverWitness`, `LowerTotal.lean`) satisfies its input conditions; with `driverInB_witness`
it also satisfies every decidable hypothesis of `lowerFunction_okT` but `IselProg`. -/
theorem buildCtx_okT_witness :
    (Compile.functionET driverWitness && decide ((valueDefs driverWitness).Nodup) &&
      driverWitness.blocks.all fun B => B.body.all (stmtInB driverWitness)) = true := by
  decide

end Backend.Proof.Driver
