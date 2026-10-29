module

public import FV.Backend.Proof.LowerLoopCtx

@[expose] public section

/-!
# Totality of the lowering: `buildCtx` (V7)

`buildCtx` (`FV/Backend/Isel.lean`) fails only at its own checks:

* a block parameter of type `i128` — excluded by subset E (`Compile.functionE`: `tyE` of every
  block parameter);
* `instData` of a statement fails — excluded by subset E (`instE`: the opcode, the `i128` types,
  `bswap.i8`, big-endian flags) and by `stmtInB` (`symbol_value`/`tls_value` of a declared global
  of the right kind, `call` of a declared AAPCS64 callee, `call_indirect` of a declared signature);
* `resultTypes` fails (`call` of an undeclared callee, `call_indirect` of an undeclared signature)
  or the number of results differs from it — excluded by `stmtInB`'s result count;
* a result of type `i128` — excluded by subset E (`instE`, the callees' signatures `sigE`) and,
  for `call_indirect`, by `stmtInB`;
* the address of a `load`/`store` is not an `i64` — excluded by `stmtInB` (`(p, i64)` among the
  declared value types `valTysOf`) together with SSA (`(valueDefs f).Nodup`, from `dominatedB`).

`buildCtx_ok` proves that `buildCtx` succeeds under these conditions.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-! ## The input conditions -/

/-- The value types the input declares: block parameters, and statement results with the
types of their instruction (`resultTypes`, as `buildCtx` computes them). -/
def valTysOf (f : Clif.Function) : List (Clif.ValueId × Clif.Ty) :=
  f.blocks.flatMap fun B => B.params ++ B.body.flatMap fun s => s.results.zip (tysOf f s)

/-- **The statement conditions of the driver's totality.** Each is a rule of Cranelift's
verifier (`verifier/mod.rs`) or of its aarch64 ABI:

* the number of results is the number of the instruction's result types (the callee's declared
  returns for a `call`/`call_indirect`, which must be declared: `verify_inst`/`typecheck_results`);
* `symbol_value` names a `symbol` global and `tls_value` a `symbol tls` one without offset
  (`verify_global_value`; Cranelift's `elf_gd` TLS rule drops the offset, so one is rejected);
* a `call`'s callee is declared with an AAPCS64 calling convention (`system_v`/`fast`/default:
  the conventions the aarch64 ABI lowers as AAPCS64) and an integer signature (`sigIntB`: the
  lowering's calls pass integers only);
* a `call_indirect`'s signature has integer parameters and returns (`sigIntB`) and returns no
  `i128` (legalized away before lowering);
* a `load`/`store` address is a declared `i64` value (`verify_is_address`: the pointer width). -/
def stmtInB (f : Clif.Function) (s : Clif.Stmt) : Bool :=
  (match s.inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·) with
    | some tys => tys.length == s.results.length
    | none => false) &&
  match s.inst with
  | .symbolValue _ gv => match f.globals.lookup gv with
    | some (.symbol ..) => true
    | _ => false
  | .tlsValue _ gv => match f.globals.lookup gv with
    | some (.tlsSymbol _ 0 _) => true
    | _ => false
  | .call fn _ => match f.extern? fn with
    | some e => aapcsConv e.sig.callConv && sigIntB e.sig
    | none => false
  | .callIndirect sig _ _ => match f.sigDecls.lookup sig with
    | some s => s.returns.all (eTy ·.ty) && sigIntB s
    | none => false
  | .load _ _ _ p _ | .store _ _ _ _ p _ => (valTysOf f).contains (p, .i64)
  | _ => true

/-! ## Loops that always yield -/

/-- A loop whose body yields `g b a` on every element is the fold. -/
theorem forIn_eq_fold {ε α β : Type} {body : α → β → Except ε (ForInStep β)} (g : β → α → β) :
    ∀ (l : List α) (init : β), (∀ a ∈ l, ∀ b, body a b = .ok (.yield (g b a))) →
      forIn l init body = .ok (l.foldl g init)
  | [], _, _ => rfl
  | a :: l, init, h => by
    rw [List.forIn_cons, h a List.mem_cons_self]
    exact forIn_eq_fold g l _ fun x hx => h x (List.mem_cons_of_mem _ hx)

/-! ## Statements -/

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {k : α} {b : β}
    (h : l.lookup k = some b) : (k, b) ∈ l := by
  obtain ⟨l1, l2, rfl, -⟩ := List.lookup_eq_some_iff.mp h
  simp

/-- `instData` succeeds on a statement of subset E satisfying `stmtInB`. -/
theorem instData_ok {f : Clif.Function} {s : Clif.Stmt} (hE : Compile.instE s.inst = true)
    (hs : stmtInB f s = true) : ∃ d, instData f s.inst = .ok d := by
  unfold stmtInB at hs
  rcases s with ⟨res, inst⟩
  simp only [Bool.and_eq_true] at hs
  obtain ⟨-, hs⟩ := hs
  cases inst with
  | unary op ty x => cases op <;> simp_all [instData, Compile.instE, Compile.unaryTyE,
      Compile.unaryE, Compile.tyE, eTy, unaryOpcode, pure, Except.pure]
  | binary op ty x y => cases op <;> simp_all [instData, Compile.instE, Compile.binaryE,
      Compile.tyE, eTy, binaryOpcode, pure, Except.pure]
  | atomicRmw op ty fl p x => cases op <;> simp_all [instData, Compile.instE, Compile.tyE,
      Compile.flagsE, eTy, rmwOpName, pure, Except.pure]
  | call fn args =>
    cases h : f.extern? fn <;> simp_all [instData, pure, Except.pure]
  | callIndirect sig c args =>
    cases h : f.sigDecls.lookup sig <;> simp_all [instData, pure, Except.pure]
  | symbolValue ty gv =>
    cases h : f.globals.lookup gv with
    | none => simp_all
    | some g => cases g <;> simp_all [instData, Compile.instE, pure, Except.pure]
  | tlsValue ty gv =>
    cases h : f.globals.lookup gv with
    | none => simp_all
    | some g =>
      cases g with
      | tlsSymbol n o c =>
        by_cases ho : o = 0
        · subst ho; simp_all [instData, Compile.instE, pure, Except.pure]
        · simp only [h] at hs; split at hs <;> simp_all
      | _ => simp_all [Compile.instE]
  | _ =>
    simp_all [instData, Compile.instE, Compile.tyE, eTy, valTyOk, Compile.flagsE, pure, Except.pure]

/-- The result types of a statement of subset E satisfying `stmtInB` are integer types of E
(not `i128`, no floats). -/
theorem tysOf_ne {f : Clif.Function} (hE : Compile.functionE f = true) {s : Clif.Stmt}
    (hi : Compile.instE s.inst = true) (hs : stmtInB f s = true) : ∀ t ∈ tysOf f s, eTy t = true := by
  have hX : ∀ fn e, f.extern? fn = some e → ∀ p ∈ e.sig.returns, eTy p.ty = true := by
    intro fn e he p hp
    simp only [Compile.functionE, Bool.and_eq_true, List.all_eq_true] at hE
    have := hE.1.2 _ (lookup_mem (show f.externs.lookup fn = some e from he))
    simp only [Compile.sigE, Bool.and_eq_true, List.all_eq_true] at this
    simpa [eTy, Compile.tyE] using this.2 p hp
  unfold stmtInB at hs
  rcases s with ⟨res, inst⟩
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
      exact hs.1 p hp
  | unary op ty x =>
    cases op <;> simp_all [tysOf, Clif.Inst.resultTypes, Compile.instE, Compile.unaryTyE,
      Compile.unaryE, Compile.tyE, eTy]
  | _ =>
    simp_all [tysOf, Clif.Inst.resultTypes, Compile.instE, Compile.tyE, Compile.binaryE,
      Compile.flagsE, eTy]

/-- What `buildCtx` checks of every block holds. -/
theorem blockC_of {f : Clif.Function} (hE : Compile.functionE f = true)
    (hst : ∀ B ∈ f.blocks, ∀ s ∈ B.body, stmtInB f s = true) : ∀ B ∈ f.blocks, BlockC f B := by
  intro B hB
  have hE' := hE
  simp only [Compile.functionE, Bool.and_eq_true, List.all_eq_true] at hE'
  obtain ⟨⟨hp, hb⟩, -⟩ := hE'.2 B hB
  have hv : ∀ t, eTy t = true → valTyOk t = true := fun t h => by simp [valTyOk, h]
  refine ⟨fun q hq => hv _ (by simpa [Compile.tyE, eTy] using hp q hq), fun s hs => ?_⟩
  have hi := hb s hs
  have hin := hst B hB s hs
  refine ⟨instData_ok hi hin, ?_, fun t ht => hv t (tysOf_ne hE hi hin t ht)⟩
  have h1 := hin
  unfold stmtInB at h1
  simp only [Bool.and_eq_true] at h1
  obtain ⟨h1, -⟩ := h1
  split at h1
  · rename_i tys hty
    exact ⟨tys, hty, by simpa using h1⟩
  · cases h1

/-! ## The model's value types -/

/-- With SSA input, the model's type of a declared `i64` value is `i64`. -/
theorem valTy_model {f : Clif.Function} (hC : ∀ B ∈ f.blocks, BlockC f B)
    (hssa : (valueDefs f).Nodup) {p : Nat} (hp : (p, .i64) ∈ valTysOf f) :
    (((ctxModel f (maxVOf f)).1)[p]?).join = some (.int 64) := by
  unfold ctxModel
  rw [blockFold]
  simp only
  have hW : (p, CTy.int 64) ∈ f.blocks.flatMap (blockTyW f) := by
    simp only [valTysOf, List.mem_flatMap, List.mem_append] at hp
    obtain ⟨B, hB, hp | ⟨s, hs, hz⟩⟩ := hp
    · simp only [List.mem_flatMap, blockTyW, List.mem_append, List.mem_map]
      exact ⟨B, hB, .inl ⟨_, hp, rfl⟩⟩
    · simp only [List.mem_flatMap, blockTyW, List.mem_append, tyWrites, List.mem_map]
      exact ⟨B, hB, .inr ⟨s, hs, _, hz, rfl⟩⟩
  have hWf := tyW_fst hC
  have hx : p ∈ valueDefs f := by
    rw [valueDefs, ← hWf]; exact List.mem_map.mpr ⟨_, hW, rfl⟩
  have hWn : ((f.blocks.flatMap (blockTyW f)).map Prod.fst).Nodup := by
    rw [hWf]; exact hssa
  rw [setW_get, lastOf_nodup hWn hW]
  simp [maxV_bound f p hx]

/-! ## `buildCtx` succeeds -/

/-- **`buildCtx` is total on its input conditions**: subset E, SSA (from `dominatedB`) and
`stmtInB` of every statement. -/
theorem buildCtx_ok {f : Clif.Function} (hE : Compile.functionE f = true)
    (hssa : (valueDefs f).Nodup) (hst : ∀ B ∈ f.blocks, ∀ s ∈ B.body, stmtInB f s = true) :
    ∃ ctx ranges st0, buildCtx f = .ok (ctx, ranges, st0) := by
  have hC := blockC_of hE hst
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

end Backend.Proof.Driver
