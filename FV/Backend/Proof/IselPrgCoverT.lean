import FV.Backend.Proof.IselPrgCover
import FV.Backend.Proof.IselPrgRootT
import FV.Backend.Proof.IselPrgExtSoundT

/-!
# Progress of the ISLE lowering over the typed scope: the driver's roots are table roots

`IselPrgCover` for the typed scope (`PInvT`, the roots of `IselPrgRootT`):

* `stmt_rootT`: a statement's `lower [.inst ii]`: its form `formOfT f c` describes `.inst ii`, is
  one of `stmtFormsT`, and every output `stmtOut` describes has one single register per result.
  E statements are V7's (`stmt_rootE`: `stmt_root` with integer operands by `PInvT.intArgsOf`);
  the float movement statements are the typed scope's forms;
* `term_rootT`: a non-`try_call` terminator's `lower`/`lower_branch` call (`termCall`) in its
  context `termCtx`: a `return` of values of the typed scope, a branch condition in an integer
  position (`PInvT.termIntOf`);
* `try_rootT`: a `try_call`'s `lower_branch` call in its context `tryCtx`.
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Isle Isle.Aarch64

section
variable {f : Clif.Function} {ctx : Ctx}

theorem γ_aVT {x : Nat} (h : (ctx.valueType? x).isSome) (hi : IntPos ctx x) :
    γ f ctx aV (.value x) := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
  simp only [aV, γ]
  exact ⟨x, t, rfl, ht, hi t ht⟩

theorem γ_aVMTB (hP : PInvTB f ctx) {x : Nat} (h : (ctx.valueType? x).isSome) :
    γ f ctx aVM (.value x) := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
  simp only [aVM, γ]
  exact ⟨x, t, rfl, ht, hP.ctxInv.valTyM x t ht⟩

theorem γ_aVMT (hP : PInvT f ctx) {x : Nat} (h : (ctx.valueType? x).isSome) :
    γ f ctx aVM (.value x) := γ_aVMTB hP.toB h

theorem γ_tyCallTB (hP : PInvTB f ctx) {ii : Nat} {info : IInfo} {c : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some c) (hE : Compile.instE c = true) :
    γ f ctx tyCall (.ty (info.resTys.head?.getD .invalid)) := by
  apply γ_ty_mem
  cases h : info.resTys with
  | nil => simp
  | cons t ts =>
    have := hP.resE ii info c hi hc hE t (by simp [h])
    simp [this]

theorem γ_tyCallT (hP : PInvT f ctx) {ii : Nat} {info : IInfo} {c : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some c) (hE : Compile.instE c = true) :
    γ f ctx tyCall (.ty (info.resTys.head?.getD .invalid)) := γ_tyCallTB hP.toB hi hc hE

end

set_option maxRecDepth 100000 in
/-- `stmt_root` for an E statement of a float-capable context (`PInvTB`): its operands are in
integer positions (`instArgs_intArgs`), its results E's integers (`PInvTB.resE`). -/
theorem stmt_rootEB {f : Clif.Function} {ctx : Ctx} (hP : PInvTB f ctx) {ii : Nat} {info : IInfo}
    {c : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some c)
    (hE : Compile.instE c = true) :
    γ f ctx (formOf f c) (.inst ii) ∧ formOf f c ∈ stmtForms ∧
      (info.results ≠ [] → ∀ rss, γ f ctx (stmtOut (formOf f c)) (.regsVec rss) →
        rss.length = info.results.length ∧ ∀ rs ∈ rss, rs.length = 1) := by
  have hctx := hP.ctxInv
  have hd := hctx.data ii info c hi hc
  obtain ⟨tys, hty, hrt, hlen⟩ := hctx.resTys ii info c hi hc
  have hof := hP.clifOf ii info c hi hc
  have hV : ∀ x ∈ Driver.instArgs c, γ f ctx aV (.value x) := fun x hx =>
    γ_aVT (hP.argsTyped c hof x hx) (hP.intArgsOf c hof x (instArgs_intArgs hE hx))
  have hR := hP.resTyped ii info hi
  have hT1 : ∀ ty, tys = [ty] →
      γ f ctx (tyOf ty) (.ty (info.resTys.head?.getD .invalid)) ∧ info.results.length = 1 := by
    intro ty h; subst h; rw [hrt]; exact ⟨γ_ty_mem (by simp), by simpa using hlen⟩
  have hT0 : tys = [] →
      γ f ctx tyNone (.ty (info.resTys.head?.getD .invalid)) ∧ info.results = [] := by
    intro h; subst h; rw [hrt]; exact ⟨γ_ty_mem (by simp), by simpa using hlen⟩
  cases c
  case iconst ty imm =>
    obtain ⟨hT, hl⟩ := hT1 ty (by simpa [Clif.Inst.resultTypes] using hty.symm)
    simp only [instData] at hd
    prg_split
    all_goals first
      | (exfalso; subst_vars; revert hE; simp [Compile.instE, Compile.tyE]; done)
      | exact ⟨γ_inst hi hT (by rw [← hd]; prg_data) hR, sf_iconst (by prg_ety) imm,
          out_n (stmtOut_single (ofClif_ne _) (by decide) (by decide)) fun _ => hl⟩
  case unary op ty x =>
    obtain ⟨hT, hl⟩ := hT1 ty (by simpa [Clif.Inst.resultTypes] using hty.symm)
    cases op <;> simp only [instData, unaryOpcode] at hd <;> prg_split
    all_goals exact ⟨γ_inst hi hT (by rw [← hd]; prg_data) hR,
      sf_unary (by decide) (by prg_ety)
        (by revert hE; cases ty <;> simp [Compile.instE, Compile.unaryTyE, Compile.unaryE]) x,
      out_n (stmtOut_single (ofClif_ne _) (by decide) (by decide)) fun _ => hl⟩
  case binary op ty x y =>
    obtain ⟨hT, hl⟩ := hT1 ty (by simpa [Clif.Inst.resultTypes] using hty.symm)
    cases op <;> simp only [instData, binaryOpcode] at hd <;> prg_split
    all_goals exact ⟨γ_inst hi hT (by rw [← hd]; prg_data) hR,
      sf_binary (by decide) (by prg_ety) x y,
      out_n (stmtOut_single (ofClif_ne _) (by decide) (by decide)) fun _ => hl⟩
  case div op ty x y =>
    obtain ⟨hT, hl⟩ := hT1 ty (by simpa [Clif.Inst.resultTypes] using hty.symm)
    cases op <;> simp only [instData, divOpcode] at hd <;> prg_split
    all_goals exact ⟨γ_inst hi hT (by rw [← hd]; prg_data) hR, sf_div _ (by prg_ety) x y,
      out_n (stmtOut_single (ofClif_ne _) (by decide) (by decide)) fun _ => hl⟩
  case icmp cc ty x y =>
    obtain ⟨hT, hl⟩ := hT1 .i8 (by simpa [Clif.Inst.resultTypes] using hty.symm)
    cases cc <;> simp only [instData, intccName] at hd <;> prg_split
    all_goals exact ⟨γ_inst hi hT (by rw [← hd]; prg_data) hR, sf_icmp _ ty x y,
      out_n (stmtOut_single (by decide) (by decide) (by decide)) fun _ => hl⟩
  case extend op ty x =>
    obtain ⟨hT, hl⟩ := hT1 ty (by simpa [Clif.Inst.resultTypes] using hty.symm)
    cases op <;> simp only [instData, show (Clif.ExtendOp.uextend == Clif.ExtendOp.uextend) = true from rfl,
      show (Clif.ExtendOp.sextend == Clif.ExtendOp.uextend) = false from rfl, ↓reduceIte,
      Bool.false_eq_true] at hd <;> prg_split
    all_goals exact ⟨γ_inst hi hT (by rw [← hd]; prg_data) hR, sf_extend _ (by prg_ety) x,
      out_n (stmtOut_single (ofClif_ne _) (by decide) (by decide)) fun _ => hl⟩
  case ireduce ty x =>
    obtain ⟨hT, hl⟩ := hT1 ty (by simpa [Clif.Inst.resultTypes] using hty.symm)
    simp only [instData] at hd
    prg_split
    exact ⟨γ_inst hi hT (by rw [← hd]; prg_data) hR, sf_ireduce (by prg_ety) x,
      out_n (stmtOut_single (ofClif_ne _) (by decide) (by decide)) fun _ => hl⟩
  case load op ty fl p off =>
    obtain ⟨hT, hl⟩ := hT1 ty (by simpa [Clif.Inst.resultTypes] using hty.symm)
    cases op <;> simp only [instData, loadOpcode] at hd <;> prg_split
    all_goals exact ⟨γ_inst hi hT (by rw [← hd]; prg_data) hR, sf_load _ (by prg_ety) fl p off,
      out_n (stmtOut_single (ofClif_ne _) (by decide) (by decide)) fun _ => hl⟩
  case store op ty fl x p off =>
    obtain ⟨hT, hl⟩ := hT0 (by simpa [Clif.Inst.resultTypes] using hty.symm)
    cases op <;> simp only [instData, storeOpcode] at hd <;> prg_split
    all_goals exact ⟨γ_inst hi hT (by rw [← hd]; prg_data) hR, sf_store _ ty fl x p off,
      out_none hl⟩
  case select ty c x y =>
    obtain ⟨hT, hl⟩ := hT1 ty (by simpa [Clif.Inst.resultTypes] using hty.symm)
    simp only [instData] at hd
    prg_split
    exact ⟨γ_inst hi hT (by rw [← hd]; prg_data) hR, sf_select (by prg_ety) c x y,
      out_n (stmtOut_single (ofClif_ne _) (by decide) (by decide)) fun _ => hl⟩
  case nop =>
    obtain ⟨hT, hl⟩ := hT0 (by simpa [Clif.Inst.resultTypes] using hty.symm)
    simp only [instData] at hd
    prg_split
    exact ⟨γ_inst hi hT (by rw [← hd]; prg_data) hR, sf_nop, out_none hl⟩
  case fence =>
    obtain ⟨hT, hl⟩ := hT0 (by simpa [Clif.Inst.resultTypes] using hty.symm)
    simp only [instData] at hd
    prg_split
    exact ⟨γ_inst hi hT (by rw [← hd]; prg_data) hR, sf_fence, out_none hl⟩
  case bmask ty x =>
    obtain ⟨hT, hl⟩ := hT1 ty (by simpa [Clif.Inst.resultTypes] using hty.symm)
    simp only [instData] at hd
    prg_split
    exact ⟨γ_inst hi hT (by rw [← hd]; prg_data) hR, sf_bmask (by prg_ety) x,
      out_n (stmtOut_single (ofClif_ne _) (by decide) (by decide)) fun _ => hl⟩
  case atomicLoad ty fl p =>
    obtain ⟨hT, hl⟩ := hT1 ty (by simpa [Clif.Inst.resultTypes] using hty.symm)
    simp only [instData] at hd
    prg_split
    exact ⟨γ_inst hi hT (by rw [← hd]; prg_data) hR, sf_atomicLoad (by prg_ety) fl p,
      out_n (stmtOut_single (ofClif_ne _) (by decide) (by decide)) fun _ => hl⟩
  case atomicStore ty fl x p =>
    obtain ⟨hT, hl⟩ := hT0 (by simpa [Clif.Inst.resultTypes] using hty.symm)
    simp only [instData] at hd
    prg_split
    exact ⟨γ_inst hi hT (by rw [← hd]; prg_data) hR, sf_atomicStore ty fl x p, out_none hl⟩
  case atomicRmw op ty fl p x =>
    obtain ⟨hT, hl⟩ := hT1 ty (by simpa [Clif.Inst.resultTypes] using hty.symm)
    cases op <;> simp only [instData, rmwOpName] at hd <;> prg_split
    all_goals exact ⟨γ_inst hi hT (by rw [← hd]; prg_data) hR, sf_atomicRmw _ (by prg_ety) fl p x,
      out_n (stmtOut_single (ofClif_ne _) (by decide) (by decide)) fun _ => hl⟩
  case atomicCas ty fl p e x =>
    obtain ⟨hT, hl⟩ := hT1 ty (by simpa [Clif.Inst.resultTypes] using hty.symm)
    simp only [instData] at hd
    prg_split
    exact ⟨γ_inst hi hT (by rw [← hd]; prg_data) hR, sf_atomicCas (by prg_ety) fl p e x,
      out_n (stmtOut_single (ofClif_ne _) (by decide) (by decide)) fun _ => hl⟩
  case stackAddr ty s off =>
    obtain ⟨hT, hl⟩ := hT1 ty (by simpa [Clif.Inst.resultTypes] using hty.symm)
    simp only [instData] at hd
    prg_split
    refine ⟨γ_inst hi hT (by rw [← hd]; prg_data; exact γ_op ⟨s, rfl, hP.slots ty s off hof⟩) hR,
      sf_stackAddr (by prg_ety) s off,
      out_n (stmtOut_single (ofClif_ne _) (by decide) (by decide)) fun _ => hl⟩
  case symbolValue ty gv =>
    have hty' : ty = .i64 := by simpa [Compile.instE] using hE
    subst hty'
    obtain ⟨hT, hl⟩ := hT1 .i64 (by simpa [Clif.Inst.resultTypes] using hty.symm)
    simp only [instData] at hd
    prg_split
    refine ⟨γ_inst hi hT (by
      rw [← hd]; prg_data
      exact γ_op ⟨gv, _, _, _, rfl, by rw [hctx.func]; assumption⟩) hR,
      sf_symbolValue gv, out_n (stmtOut_single (by decide) (by decide) (by decide)) fun _ => hl⟩
  case tlsValue ty gv =>
    have hty' : ty = .i64 := by simpa [Compile.instE] using hE
    subst hty'
    obtain ⟨hT, hl⟩ := hT1 .i64 (by simpa [Clif.Inst.resultTypes] using hty.symm)
    simp only [instData] at hd
    prg_split
    refine ⟨γ_inst hi hT (by
      rw [← hd]; prg_data
      exact γ_op ⟨gv, _, _, _, rfl, by rw [hctx.func]; assumption⟩) hR,
      sf_tlsValue gv, out_n (stmtOut_single (by decide) (by decide) (by decide)) fun _ => hl⟩
  case funcAddr ty fn =>
    have hty' : ty = .i64 := by simpa [Compile.instE] using hE
    subst hty'
    obtain ⟨hT, hl⟩ := hT1 .i64 (by simpa [Clif.Inst.resultTypes] using hty.symm)
    obtain ⟨e, he, hs⟩ := hP.callees _ fn hof (.inr ⟨.i64, rfl⟩)
    simp only [instData] at hd
    prg_split
    refine ⟨γ_inst hi hT (by
      rw [← hd]; prg_data
      exact γ_op ⟨fn, e, rfl, by rw [hctx.func]; exact he, hs, .inl rfl⟩) hR,
      sf_funcAddr fn, out_n (stmtOut_single (by decide) (by decide) (by decide)) fun _ => hl⟩
  case call fn args =>
    obtain ⟨e, he, hs⟩ := hP.callees _ fn hof (.inl ⟨args, rfl⟩)
    simp only [Clif.Inst.resultTypes, he, Option.map_some, Option.some.injEq] at hty
    simp only [instData, he] at hd
    split at hd
    case isFalse => cases hd
    simp only [pure, Except.pure, Except.ok.injEq] at hd
    refine ⟨γ_inst hi (γ_tyCallTB hP hi hc hE) (by
      rw [← hd]; prg_data
      · exact γ_valsMin (Nat.zero_le _) fun x hx =>
          hP.argsTyped _ hof x (by simpa [Driver.instArgs] using hx)
      · exact γ_op ⟨fn, e, rfl, by rw [hctx.func]; exact he, hs, .inr (by simp [retsOf, he])⟩) hR,
      sf_call (by simpa [retsOf, he] using hs.2) args,
      out_n (a := formOf f (.call fn args)) (n := retsOf f fn) rfl fun hne => ?_⟩
    have hr : e.sig.returns ≠ [] := by
      intro h; apply hne
      rw [← List.length_eq_zero_iff, hlen, ← hty, h]; rfl
    simp [retsOf, he, sigRets_of_ne hr, hlen, ← hty]
  case callIndirect sig callee args =>
    cases hsd : f.sigDecls.lookup sig with
    | none => simp [instData, hsd, throw, throwThe, MonadExceptOf.throw] at hd
    | some s =>
      have hs := hP.indSigs sig callee args s hof hsd
      simp only [Clif.Inst.resultTypes, hsd, Option.map_some, Option.some.injEq] at hty
      simp only [instData, hsd] at hd
      split at hd
      case isFalse => cases hd
      simp only [pure, Except.pure, Except.ok.injEq] at hd
      refine ⟨γ_inst hi (γ_tyCallTB hP hi hc hE) (by
        rw [← hd]; prg_data
        · exact γ_valsMin (by simp) fun x hx =>
            hP.argsTyped _ hof x (by simpa [Driver.instArgs] using hx)
        · exact γ_op ⟨s, rfl, hs, .inr (by simp [sigRetsOf, hsd])⟩) hR,
        sf_callIndirect (by simpa [sigRetsOf, hsd] using hs.2) callee args,
        out_n (a := formOf f (.callIndirect sig callee args)) (n := sigRetsOf f sig) rfl fun hne => ?_⟩
      have hr : s.returns ≠ [] := by
        intro h; apply hne
        rw [← List.length_eq_zero_iff, hlen, ← hty, h]; rfl
      simp [sigRetsOf, hsd, sigRets_of_ne hr, hlen, ← hty]
  -- `bitcast` (S11e4) is outside E
  case bitcast => exact absurd hE (by simp [Compile.instE])
  case float => exact absurd hE (by simp [Compile.instE])
  all_goals simp [instData, throw, throwThe, MonadExceptOf.throw] at hd

set_option maxRecDepth 100000 in
/-- `stmt_root` for an E statement of a float-capable context (`stmt_rootEB` under `PInvT`). -/
theorem stmt_rootE {f : Clif.Function} {ctx : Ctx} (hP : PInvT f ctx) {ii : Nat} {info : IInfo}
    {c : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some c)
    (hE : Compile.instE c = true) :
    γ f ctx (formOf f c) (.inst ii) ∧ formOf f c ∈ stmtForms ∧
      (info.results ≠ [] → ∀ rss, γ f ctx (stmtOut (formOf f c)) (.regsVec rss) →
        rss.length = info.results.length ∧ ∀ rs ∈ rss, rs.length = 1) :=
  stmt_rootEB hP.toB hi hc hE


/-! ## The typed statement forms in `stmtFormsT` -/

/-- `stmtForms` is a prefix of `stmtFormsT`. -/
theorem mem_stmtFormsT_of {F : PA} (h : F ∈ stmtForms) : F ∈ stmtFormsT := by
  unfold stmtFormsT; iterate 5 apply List.mem_append_left
  exact h

/-- The form of an `f32const`. -/
def fF32 : PA := .inst (tyOf .f32) (idat VIdx.InstructionData.UnaryIeee32
  [opc VIdx.Opcode.F32const, aU32])
/-- The form of an `f64const`. -/
def fF64 : PA := .inst (tyOf .f64) (idat VIdx.InstructionData.UnaryIeee64
  [opc VIdx.Opcode.F64const, aU64])
/-- The form of a float `load`. -/
def fLoad (ty : Clif.Ty) : PA := .inst (tyOf ty) (idat VIdx.InstructionData.Load
  [opc VIdx.Opcode.Load, aV, .op .memFlags none, .int none none])
/-- The form of a float `store`. -/
def fStore : PA := .inst tyNone (idat VIdx.InstructionData.Store
  [opc VIdx.Opcode.Store, .vals [aVM, aV], .op .memFlags none, .int none none])
/-- The form of a float `select`. -/
def fSelect (ty : Clif.Ty) : PA := .inst (tyOf ty) (idat VIdx.InstructionData.Ternary
  [opc VIdx.Opcode.Select, .vals [aV, aVM, aVM]])
/-- The form of a `bitcast`. -/
def fBitcast (ty : Clif.Ty) : PA := .inst (tyOf ty) (idat VIdx.InstructionData.LoadNoOffset
  [opc VIdx.Opcode.Bitcast, aVM, .any])

theorem sfT_f32 : fF32 ∈ stmtFormsT := by
  unfold stmtFormsT; iterate 4 apply List.mem_append_left
  apply List.mem_append_right; exact List.mem_cons_self

theorem sfT_f64 : fF64 ∈ stmtFormsT := by
  unfold stmtFormsT; iterate 4 apply List.mem_append_left
  apply List.mem_append_right; exact List.mem_cons_of_mem _ List.mem_cons_self

theorem sfT_load {ty : Clif.Ty} (h : ty = .f32 ∨ ty = .f64) : fLoad ty ∈ stmtFormsT := by
  unfold stmtFormsT; iterate 3 apply List.mem_append_left
  apply List.mem_append_right
  rcases h with rfl | rfl
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

theorem sfT_store : fStore ∈ stmtFormsT := by
  unfold stmtFormsT; iterate 2 apply List.mem_append_left
  apply List.mem_append_right; exact List.mem_cons_self

theorem sfT_select {ty : Clif.Ty} (h : ty = .f32 ∨ ty = .f64) : fSelect ty ∈ stmtFormsT := by
  unfold stmtFormsT; apply List.mem_append_left
  apply List.mem_append_right
  rcases h with rfl | rfl
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

theorem sfT_bitcast {ty : Clif.Ty} (h : ty ∈ eTys ++ fTys) : fBitcast ty ∈ stmtFormsT := by
  unfold stmtFormsT
  apply List.mem_append_right
  simp only [eTys, fTys, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))

/-! ## Statement roots over the typed scope -/

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- **A statement's root over a float-capable context**, for a statement of the typed scope
(`hET`): the form `formOfT` of its instruction describes `.inst ii`, is a statement root of the
typed table, and every output `stmtOut` describes has one single register per result. -/
theorem stmt_rootTB {f : Clif.Function} {ctx : Ctx} (hP : PInvTB f ctx) {ii : Nat} {info : IInfo}
    {c : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some c)
    (hET : Compile.instET c = true) :
    γ f ctx (formOfT f c) (.inst ii) ∧ formOfT f c ∈ stmtFormsT ∧
      (info.results ≠ [] → ∀ rss, γ f ctx (stmtOut (formOfT f c)) (.regsVec rss) →
        rss.length = info.results.length ∧ ∀ rs ∈ rss, rs.length = 1) := by
  by_cases hE : Compile.instE c = true
  · have hf : formOfT f c = formOf f c := by simp [formOfT, hE]
    rw [hf]
    obtain ⟨h1, h2, h3⟩ := stmt_rootEB hP hi hc hE
    exact ⟨h1, mem_stmtFormsT_of h2, h3⟩
  have hctx := hP.ctxInv
  have hd := hctx.data ii info c hi hc
  obtain ⟨tys, hty, hrt, hlen⟩ := hctx.resTys ii info c hi hc
  have hof := hP.clifOf ii info c hi hc
  have hargs := hP.argsTyped c hof
  have hint := hP.intArgsOf c hof
  have hR := hP.resTyped ii info hi
  have hT1 : ∀ ty, tys = [ty] →
      γ f ctx (tyOf ty) (.ty (info.resTys.head?.getD .invalid)) ∧ info.results.length = 1 := by
    intro ty h; subst h; rw [hrt]; exact ⟨γ_ty_mem (by simp), by simpa using hlen⟩
  have hT0 : tys = [] →
      γ f ctx tyNone (.ty (info.resTys.head?.getD .invalid)) ∧ info.results = [] := by
    intro h; subst h; rw [hrt]; exact ⟨γ_ty_mem (by simp), by simpa using hlen⟩
  have hsingle : ∀ ty k fs, k ≠ VIdx.InstructionData.Call → k ≠ VIdx.InstructionData.CallIndirect →
      info.results.length = 1 → info.results ≠ [] → ∀ rss,
        γ f ctx (stmtOut (.inst (tyOf ty) (.data tyInstData k fs))) (.regsVec rss) →
        rss.length = info.results.length ∧ ∀ rs ∈ rss, rs.length = 1 :=
    fun ty k fs h1 h2 hl => out_n (stmtOut_single (ofClif_ne ty) h1 h2) fun _ => hl
  have hform : formOfT f c = match c with
    | .iconst ty _ => if ty = .f32 then fF32 else fF64
    | .load _ ty _ _ _ => fLoad ty
    | .store _ _ _ _ _ _ => fStore
    | .select ty _ _ _ => fSelect ty
    | .bitcast ty _ _ => fBitcast ty
    | _ => .bot := by
    unfold formOfT; rw [if_neg hE]; cases c <;> rfl
  rw [hform]
  cases c
  case iconst ty imm =>
    simp only [Compile.instET, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hET
    obtain ⟨hT, hl⟩ := hT1 ty (by simpa [Clif.Inst.resultTypes] using hty.symm)
    have := imm.isLt
    rcases hET with (hT' | rfl) | ⟨rfl, -⟩
    · exact absurd (by simp [Compile.instE, hT']) hE
    · simp [instData, eTy, Clif.Ty.isInt, pure, Except.pure] at hd
      refine ⟨γ_inst hi hT ?_ hR, sfT_f32, hsingle .f32 _ _ (by decide) (by decide) hl⟩
      rw [← hd]
      refine γ_instDataV (by rfl) (γL_cons' (γ_opcodeV (by rfl)) (γL_cons' ?_ γL_nil'))
      exact ⟨_, rfl, by simp, by simp [Clif.Ty.width] at this ⊢; omega⟩
    · simp [instData, eTy, Clif.Ty.isInt, pure, Except.pure] at hd
      refine ⟨γ_inst hi hT ?_ hR, sfT_f64, hsingle .f64 _ _ (by decide) (by decide) hl⟩
      rw [← hd]
      refine γ_instDataV (by rfl) (γL_cons' (γ_opcodeV (by rfl)) (γL_cons' ?_ γL_nil'))
      exact ⟨_, rfl, by simp, by simp [Clif.Ty.width] at this ⊢; omega⟩
  case load op ty fl p off =>
    simp only [Compile.instET, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hET
    obtain ⟨hfl, hT' | ⟨hfloat, rfl⟩⟩ := hET
    · exact absurd (by simp [Compile.instE, hT', hfl]) hE
    obtain ⟨hT, hl⟩ := hT1 ty (by simpa [Clif.Inst.resultTypes] using hty.symm)
    have hty2 : ty = .f32 ∨ ty = .f64 := by revert hfloat; cases ty <;> simp [Clif.Ty.isFloat]
    simp only [instData] at hd
    split at hd
    · cases hd
    split at hd
    · cases hd
    rename_i hbig
    simp only [pure, Except.pure, Except.ok.injEq] at hd
    refine ⟨γ_inst hi hT ?_ hR, sfT_load hty2, hsingle ty _ _ (by decide) (by decide) hl⟩
    rw [← hd]
    exact γ_instDataV (by rfl) (γL_cons' (γ_opcodeV (by rfl)) (γL_cons'
      (γ_aVT (hargs p (by simp [Driver.instArgs])) (hint p (by simp [intArgs])))
      (γL_cons' (γ_memFlags hbig) (γL_cons' (γ_int_any _) γL_nil'))))
  case store op ty fl x p off =>
    simp only [Compile.instET, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hET
    obtain ⟨hfl, hT' | ⟨hfloat, rfl⟩⟩ := hET
    · exact absurd (by simp [Compile.instE, hT', hfl]) hE
    obtain ⟨hT, hl⟩ := hT0 (by simpa [Clif.Inst.resultTypes] using hty.symm)
    simp only [instData] at hd
    split at hd
    · cases hd
    split at hd
    · cases hd
    rename_i hbig
    simp only [pure, Except.pure, Except.ok.injEq] at hd
    refine ⟨γ_inst hi hT ?_ hR, sfT_store, out_none hl⟩
    rw [← hd]
    have hp : p ∈ intArgs (.store .store ty fl x p off) := by
      show p ∈ (if ty.isFloat then [p] else [x, p])
      rw [if_pos hfloat]; exact List.mem_singleton_self _
    exact γ_instDataV (by rfl) (γL_cons' (γ_opcodeV (by rfl)) (γL_cons'
      (γ_vals (γL_cons' (γ_aVMTB hP (hargs x (by simp [Driver.instArgs])))
        (γL_cons' (γ_aVT (hargs p (by simp [Driver.instArgs])) (hint p hp)) γL_nil')))
      (γL_cons' (γ_memFlags hbig) (γL_cons' (γ_int_any _) γL_nil'))))
  case select ty c x y =>
    simp only [Compile.instET, Compile.tyM, Bool.or_eq_true] at hET
    rcases hET with hT' | hfloat
    · exact absurd (by simp [Compile.instE, hT']) hE
    obtain ⟨hT, hl⟩ := hT1 ty (by simpa [Clif.Inst.resultTypes] using hty.symm)
    have hty2 : ty = .f32 ∨ ty = .f64 := by revert hfloat; cases ty <;> simp [Clif.Ty.isFloat]
    simp only [instData] at hd
    split at hd
    · simp only [pure, Except.pure, Except.ok.injEq] at hd
      have hcI : c ∈ intArgs (.select ty c x y) := by
        show c ∈ (if ty.isFloat then [c] else [c, x, y])
        rw [if_pos hfloat]; exact List.mem_singleton_self _
      refine ⟨γ_inst hi hT ?_ hR, sfT_select hty2, hsingle ty _ _ (by decide) (by decide) hl⟩
      rw [← hd]
      exact γ_instDataV (by rfl) (γL_cons' (γ_opcodeV (by rfl)) (γL_cons'
        (γ_vals (γL_cons' (γ_aVT (hargs c (by simp [Driver.instArgs])) (hint c hcI))
          (γL_cons' (γ_aVMTB hP (hargs x (by simp [Driver.instArgs])))
            (γL_cons' (γ_aVMTB hP (hargs y (by simp [Driver.instArgs]))) γL_nil')))) γL_nil'))
    · cases hd
  case bitcast ty fl x =>
    simp only [Compile.instET, Compile.tyM, Bool.or_eq_true] at hET
    obtain ⟨hT, hl⟩ := hT1 ty (by simpa [Clif.Inst.resultTypes] using hty.symm)
    have hty2 : ty ∈ eTys ++ fTys := by
      revert hET; cases ty <;> simp [eTys, fTys, Compile.tyE, Clif.Ty.isFloat, Clif.Ty.isInt]
    simp only [instData] at hd
    split at hd
    · simp only [pure, Except.pure, Except.ok.injEq] at hd
      refine ⟨γ_inst hi hT ?_ hR, sfT_bitcast hty2, hsingle ty _ _ (by decide) (by decide) hl⟩
      rw [← hd]
      exact γ_instDataV (by rfl) (γL_cons' (γ_opcodeV (by rfl)) (γL_cons'
        (γ_aVMTB hP (hargs x (by simp [Driver.instArgs]))) (γL_cons' trivial γL_nil')))
    · cases hd
  all_goals exact absurd (by simpa [Compile.instET] using hET) hE

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- **A statement's root over the typed scope** (`stmt_rootTB` under `PInvT`): the form
`formOfT` of its instruction describes `.inst ii`, is a statement root of the typed table, and
every output `stmtOut` describes has one single register per result. -/
theorem stmt_rootT {f : Clif.Function} {ctx : Ctx} (hP : PInvT f ctx) {ii : Nat} {info : IInfo}
    {c : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some c) :
    γ f ctx (formOfT f c) (.inst ii) ∧ formOfT f c ∈ stmtFormsT ∧
      (info.results ≠ [] → ∀ rss, γ f ctx (stmtOut (formOfT f c)) (.regsVec rss) →
        rss.length = info.results.length ∧ ∀ rs ∈ rss, rs.length = 1) :=
  stmt_rootTB hP.toB hi hc (hP.instET c (hP.clifOf ii info c hi hc))

end Backend.Proof.Prg
