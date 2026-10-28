import FV.Backend.Proof.IselPrgCoverT
import FV.Backend.Proof.IselPrgRootTF
import FV.Clif.FloatFacts

/-!
# Progress of the ISLE lowering over the float scope: the statements' roots (S11f, #35)

`stmt_rootTF`: a statement's `lower [.inst ii]` over a context of the float scope (`PInvTF`): its
form `formOfTF f c` describes `.inst ii`, is one of `stmtFormsTF`, and every output `stmtOut`
describes has one single register per result. The typed movement scope's statements are
`stmt_rootTB`'s; a float operation's operands are typed values (`aVM`), integers in the
`intOperandsF` position of an `fcvt_from_*` (`aV`, `PInvTF.intOpsFOf`) and floats in the
`floatOperands` positions of an `fcmp` and of a saturating conversion (`aVF`,
`PInvTF.floatOpsOf`).
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Isle Isle.Aarch64

/-! ## The float forms in `stmtFormsTF` -/

theorem sfF_bin {op : Clif.FOp} (hop : op ∈ fBinOps) {ty : Clif.Ty} (hty : ty ∈ fTys) :
    fFormBin op ty ∈ stmtFormsTF := by
  unfold stmtFormsTF fFormsTF; apply List.mem_append_right; iterate 5 apply List.mem_append_left
  exact List.mem_flatMap.2 ⟨op, hop, List.mem_map.2 ⟨ty, hty, rfl⟩⟩

theorem sfF_un {op : Clif.FOp} (hop : op ∈ fUnOps) {ty : Clif.Ty} (hty : ty ∈ fTys) :
    fFormUn op ty ∈ stmtFormsTF := by
  unfold stmtFormsTF fFormsTF; apply List.mem_append_right; iterate 4 apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_flatMap.2 ⟨op, hop, List.mem_map.2 ⟨ty, hty, rfl⟩⟩

theorem sfF_promote : fFormUn .fpromote .f64 ∈ stmtFormsTF := by
  unfold stmtFormsTF fFormsTF; apply List.mem_append_right; iterate 3 apply List.mem_append_left
  apply List.mem_append_right; exact List.mem_cons_self

theorem sfF_demote : fFormUn .fdemote .f32 ∈ stmtFormsTF := by
  unfold stmtFormsTF fFormsTF; apply List.mem_append_right; iterate 3 apply List.mem_append_left
  apply List.mem_append_right; exact List.mem_cons_of_mem _ List.mem_cons_self

theorem sfF_from {op : Clif.FOp} (hop : op ∈ fFromOps) {ty : Clif.Ty} (hty : ty ∈ fTys) :
    fFormUn op ty ∈ stmtFormsTF := by
  unfold stmtFormsTF fFormsTF; apply List.mem_append_right; iterate 2 apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_flatMap.2 ⟨op, hop, List.mem_map.2 ⟨ty, hty, rfl⟩⟩

theorem sfF_to {op : Clif.FOp} (hop : op ∈ fToOps) {ty : Clif.Ty} (hty : ty ∈ [Clif.Ty.i32, .i64]) :
    fFormUn op ty ∈ stmtFormsTF := by
  unfold stmtFormsTF fFormsTF; apply List.mem_append_right; apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_flatMap.2 ⟨op, hop, List.mem_map.2 ⟨ty, hty, rfl⟩⟩

theorem sfF_cmp {cc : Clif.FloatCC} (hcc : fccOk cc = true) : fFormCmp cc ∈ stmtFormsTF := by
  unfold stmtFormsTF fFormsTF; apply List.mem_append_right; apply List.mem_append_right
  exact List.mem_map.2 ⟨cc, by cases cc <;> simp_all [fccOk, fCCs], rfl⟩

/-- The forms of the typed movement scope are the float scope's. -/
theorem formOfTF_of_instET {f : Clif.Function} {c : Clif.Inst} (h : Compile.instET c = true) :
    formOfTF f c = formOfT f c := by
  cases c with
  | float op ty args => simp [Compile.instET, Compile.instE] at h
  | _ => rfl

theorem fTys_of_isFloat {ty : Clif.Ty} (h : ty.isFloat = true) : ty ∈ fTys := by
  cases ty <;> simp_all [fTys, Clif.Ty.isFloat]

set_option maxRecDepth 100000 in
/-- The `FloatCC` value of an `fcmp`'s condition is variant `fccIdxF`. -/
theorem mkVariant_floatccF (cc : Clif.FloatCC) :
    mkVariant TyId.FloatCC (floatccName cc) = .data TyId.FloatCC (fccIdxF cc) [] := by
  cases cc <;> rfl

/-! ## Statement roots over the float scope -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **A statement's root over the float scope**: the form `formOfTF` of its instruction describes
`.inst ii`, is a statement root of the float scope's table, and every output `stmtOut` describes
has one single register per result. -/
theorem stmt_rootTF {f : Clif.Function} {ctx : Ctx} (hP : PInvTF f ctx) {ii : Nat} {info : IInfo}
    {c : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some c) :
    γ f ctx (formOfTF f c) (.inst ii) ∧ formOfTF f c ∈ stmtFormsTF ∧
      (info.results ≠ [] → ∀ rss, γ f ctx (stmtOut (formOfTF f c)) (.regsVec rss) →
        rss.length = info.results.length ∧ ∀ rs ∈ rss, rs.length = 1) := by
  have hof := hP.clifOf ii info c hi hc
  by_cases hET : Compile.instET c = true
  · rw [formOfTF_of_instET hET]
    obtain ⟨h1, h2, h3⟩ := stmt_rootTB hP.toPInvTB hi hc hET
    exact ⟨h1, List.mem_append_left _ h2, h3⟩
  have hF := hP.instETF c hof
  have hctx := hP.ctxInv
  have hd := hctx.data ii info c hi hc
  obtain ⟨tys, hty, hrt, hlen⟩ := hctx.resTys ii info c hi hc
  have hargs := hP.argsTyped c hof
  have hint := hP.intOpsFOf c hof
  have hflo := hP.floatOpsOf c hof
  have hR := hP.resTyped ii info hi
  cases c
  case float op ty args =>
    rw [Clif.resultTypes_float] at hty
    obtain rfl : tys = [Clif.floatResTy op ty] := (Option.some.inj hty).symm
    have hT1 : γ f ctx (tyOf (Clif.floatResTy op ty)) (.ty (info.resTys.head?.getD .invalid)) ∧
        info.results.length = 1 := by
      rw [hrt]; exact ⟨γ_ty_mem (by simp [tyOf]), by simpa using hlen⟩
    have hTa : ∀ x ∈ args, (ctx.valueType? x).isSome := fun x hx =>
      hargs x (by simpa [Driver.instArgs] using hx)
    have hFl : ∀ x ∈ Compile.floatOperands (.float op ty args), γ f ctx aVF (.value x) := by
      intro x hx
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp
        (hargs x (by cases op <;> rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩ <;>
          simp_all [Compile.floatOperands, Driver.instArgs]))
      simp only [aVF, γ]
      refine ⟨x, t, rfl, ht, ?_⟩
      rcases hflo x hx t ht with rfl | rfl <;> simp
    rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨z, zs⟩⟩⟩
    · simp [instData, throw, throwThe, MonadExceptOf.throw] at hd
    · cases op <;> simp only [instData, fUnaryOpcode, fCvtOpcode] at hd
      all_goals first
        | (simp [throw, throwThe, MonadExceptOf.throw] at hd; done)
        | (split at hd
           · rename_i htyok
             simp only [pure, Except.pure, Except.ok.injEq] at hd
             simp only [Clif.floatResTy] at hT1
             simp only [formOfTF, fFormUn, fArgOf]
             refine ⟨γ_inst hi hT1.1 ?_ hR, ?_,
               out_n (stmtOut_single (ofClif_ne _) (by decide) (by decide)) fun _ => hT1.2⟩
             · rw [← hd]
               refine γ_instDataV rfl (γL_cons' (γ_opcodeV rfl) (γL_cons' ?_ γL_nil'))
               first
                 | exact γ_aVMTB hP.toPInvTB (hTa x (by simp))
                 | exact γ_aVT (hTa x (by simp)) (hint x (by simp [Compile.intOperandsF]))
                 | exact hFl x (by simp [Compile.floatOperands])
             · first
                 | exact sfF_un (by simp [fUnOps]) (fTys_of_isFloat (by simpa [fTyOk] using htyok))
                 | exact sfF_from (by simp [fFromOps])
                     (fTys_of_isFloat (by simpa [fCvtTyOk] using htyok))
                 | (have : ty = .f64 := by simpa [fTyOk] using htyok
                    subst this; exact sfF_promote)
                 | (have : ty = .f32 := by simpa [fTyOk] using htyok
                    subst this; exact sfF_demote)
                 | exact sfF_to (by simp [fToOps]) (by
                     simp only [fCvtTyOk, Bool.or_eq_true, beq_iff_eq] at htyok
                     rcases htyok with rfl | rfl <;> simp)
           · simp [throw, throwThe, MonadExceptOf.throw] at hd)
    · cases op <;> simp only [instData, fBinaryOpcode] at hd
      all_goals first
        | (simp [throw, throwThe, MonadExceptOf.throw] at hd; done)
        | (split at hd
           · rename_i htyok
             simp only [pure, Except.pure, Except.ok.injEq] at hd
             first
               | (simp only [Clif.floatResTy] at hT1
                  simp only [formOfTF, fFormBin]
                  refine ⟨γ_inst hi hT1.1 ?_ hR,
                    sfF_bin (by simp [fBinOps]) (fTys_of_isFloat (by simpa [fTyOk] using htyok)),
                    out_n (stmtOut_single (ofClif_ne _) (by decide) (by decide)) fun _ => hT1.2⟩
                  rw [← hd]
                  exact γ_instDataV rfl (γL_cons' (γ_opcodeV rfl) (γL_cons'
                    (γ_vals (γL_cons' (γ_aVMTB hP.toPInvTB (hTa x (by simp)))
                      (γL_cons' (γ_aVMTB hP.toPInvTB (hTa y (by simp))) γL_nil'))) γL_nil')))
               | (simp only [Clif.floatResTy] at hT1
                  simp only [Bool.and_eq_true] at htyok
                  simp only [formOfTF, fFormCmp]
                  refine ⟨γ_inst hi hT1.1 ?_ hR, sfF_cmp htyok.2,
                    out_n (stmtOut_single (by decide) (by decide) (by decide)) fun _ => hT1.2⟩
                  rw [← hd]
                  refine γ_instDataV rfl (γL_cons' (γ_opcodeV rfl) (γL_cons'
                    (γ_vals (γL_cons' (hFl x (by simp [Compile.floatOperands]))
                      (γL_cons' (hFl y (by simp [Compile.floatOperands])) γL_nil'))) (γL_cons' ?_ γL_nil')))
                  rw [mkVariant_floatccF]
                  exact ⟨[], rfl, trivial⟩)
           · simp [throw, throwThe, MonadExceptOf.throw] at hd)
    · simp [instData, throw, throwThe, MonadExceptOf.throw] at hd
  all_goals exact absurd (by simpa [Compile.instETF, Compile.instETA, Compile.fArithET,
    Compile.fCvtET, Compile.fCmpET] using hF) hET

end Backend.Proof.Prg
