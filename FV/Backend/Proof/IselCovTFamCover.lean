import FV.Backend.Proof.IselCovTExt
import FV.Backend.Proof.LowerContractT
import FV.Backend.Proof.LowerCertT
import FV.Backend.Proof.IselPrgCtx
import FV.Backend.Proof.LowerTotal
import FV.Backend.Proof.LowerDecide
import FV.Compile.SelectTyped
import FV.Backend.Proof.IselCovTCall

/-!
# Form coverage over float-capable contexts (typed V3): the statements' families

`famCover_of`: in `buildCtx`'s context of a function of the typed scope (`LowerScopeT`, SSA and
dominance `dominatedB`, class-checked float `store`s and `select`s), every statement belongs to
an instruction family of `famTab` (`FamCover`): its result types and values are the family's
(SSA: a result's value type is its result type, `CtxFacts.types`), and its `InstructionData`
is described by the family's data: integer operands are `IntPos` (`CtxInvT.intOps`), the value
of a float `store` and the operands of a float `select` have float types (dominance: they are
typed; `storeTypedB`/`selectTypedB`: of the float class).
-/

namespace Backend.Proof.CovT

open Backend Backend.Proof Backend.Proof.Driver Isle Isle.Aarch64

set_option maxRecDepth 20000

section Helpers
variable {ctx : Ctx}

theorem valIn_type {x : Nat} {t : CTy} {ts : List CTy} (ht : ctx.valueType? x = some t)
    (hm : t ∈ ts) : ValIn ctx x ts :=
  ⟨fun t' h => by rw [ht] at h; cases h; exact hm, fun h => by rw [ht] at h; cases h⟩

theorem valIn_E {x : Nat} (h : IntPos ctx x) : ValIn ctx x eCTys :=
  ⟨h, fun _ => ⟨.int 8, by simp [eCTys], rfl⟩⟩

theorem valIn_F {x : Nat} (hty : (ctx.valueType? x).isSome)
    (hcls : ∀ t, ctx.valueType? x = some t → t.valClass = .float)
    (hM : ∀ t, ctx.valueType? x = some t → t ∈ mCTys) : ValIn ctx x fCTys := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hty
  refine valIn_type ht ?_
  have hc := hcls t ht
  have hm := hM t ht
  simp only [mCTys, eCTys, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> first
    | (simp [CTy.valClass, CTy.regClass?] at hc; done)
    | simp [fCTys]

theorem γ_c0V {v : V} (hr : v.regsIn = []) (hc : Cov.covV v = true) : γP ctx noInst AT.c0 v := by
  show γP ctx noInst (.flat 0 true) v
  exact ⟨fun r h => (by rw [hr] at h; simp at h), fun _ => covV_of_cov hc⟩

theorem γ_opAlts {name : String} {os : List Nat}
    (h : os.any (fun k => variantIdx tyOpcode name == some k) = true) :
    γP ctx noInst (opAlts os) (opcodeV name) := by
  obtain ⟨k, hk, he⟩ := List.any_eq_true.mp h
  have he : variantIdx tyOpcode name = some k := by simpa using he
  unfold opcodeV mkVariant
  rw [he]
  show γAnyP ctx noInst (os.map fun o => AT.data tyOpcode o []) (.data tyOpcode k [])
  rw [γAnyP_iff]
  exact ⟨.data tyOpcode k [], List.mem_map.mpr ⟨k, hk, rfl⟩, ⟨[], rfl, trivial⟩⟩

theorem γ_idata {name : String} {k : Nat} {fs : List AT} {vs : List V}
    (hk : variantIdx tyInstData name = some k) (hl : γLP ctx noInst fs vs) :
    γP ctx noInst (idata k fs) (instDataV name vs) := by
  unfold instDataV mkVariant idata
  rw [hk]
  exact ⟨vs, rfl, hl⟩

theorem γ_val {x : Nat} {ts : List CTy} (h : ValIn ctx x ts) : γP ctx noInst (.val ts) (.value x) :=
  ⟨x, rfl, h⟩

theorem γ_vals2 {x y : Nat} {a b : List CTy} (hx : ValIn ctx x a) (hy : ValIn ctx y b) :
    γP ctx noInst (.vals [a, b]) (.values [x, y]) := by
  refine ⟨[x, y], rfl, rfl, fun i z ts h1 h2 => ?_⟩
  rcases i with _ | _ | i <;> simp at h1 h2 <;> (subst h1; subst h2) <;> assumption

theorem γ_vals3 {x y z : Nat} {a b c : List CTy} (hx : ValIn ctx x a) (hy : ValIn ctx y b)
    (hz : ValIn ctx z c) : γP ctx noInst (.vals [a, b, c]) (.values [x, y, z]) := by
  refine ⟨[x, y, z], rfl, rfl, fun i w ts h1 h2 => ?_⟩
  rcases i with _ | _ | _ | i <;> simp at h1 h2 <;> (subst h1; subst h2) <;> assumption

theorem γ_valsAll {xs : List Nat} {ts : List CTy} (h : ∀ x ∈ xs, ValIn ctx x ts) :
    γP ctx noInst (.valsAll ts) (.values xs) := ⟨xs, rfl, h⟩

/-- The four conjuncts of `FamOk` from the result types. -/
theorem famOk_of {F : Fam} {info : IInfo}
    (hrv : ∀ (m : Nat) r t, info.results[m]? = some r → info.resTys[m]? = some t →
      ctx.valueType? r = some t)
    (hlen : info.results.length = info.resTys.length)
    (hres : ∀ t ∈ info.resTys, t ∈ F.res ∧ t ∈ F.all)
    (hhead : info.resTys.head?.getD .invalid ∈ F.res) (hd : γP ctx noInst F.data info.data) :
    FamOk ctx F info := by
  have key : ∀ x ∈ info.results, ∃ t, ctx.valueType? x = some t ∧ t ∈ info.resTys := by
    intro x hx
    obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hx
    have hlt : m < info.resTys.length := hlen ▸ (List.getElem?_eq_some_iff.mp hm).1
    exact ⟨_, hrv m x _ hm (List.getElem?_eq_getElem hlt), List.getElem_mem hlt⟩
  refine ⟨hhead, fun x hx => ?_, fun x hx => ?_, hd⟩
  · obtain ⟨t, ht, hm⟩ := key x (List.mem_of_mem_head? hx)
    exact valIn_type ht (hres t hm).1
  · obtain ⟨t, ht, hm⟩ := key x hx
    exact valIn_type ht (hres t hm).2

theorem ofClif_eCTys {ty : Clif.Ty} (h : Compile.tyE ty = true) : CTy.ofClif ty ∈ eCTys := by
  cases ty <;> simp_all [Compile.tyE, Clif.Ty.isInt, CTy.ofClif, eCTys]

theorem ofClif_eTy {ty : Clif.Ty} (h : eTy ty = true) : CTy.ofClif ty ∈ eCTys := by
  cases ty <;> simp_all [eTy, Clif.Ty.isInt, CTy.ofClif, eCTys]

theorem ofClif_fCTys {ty : Clif.Ty} (h : ty.isFloat = true) : CTy.ofClif ty ∈ fCTys := by
  cases ty <;> simp_all [Clif.Ty.isFloat, CTy.ofClif, fCTys]

theorem valClass_ofClif_float {ty : Clif.Ty} (h : ty.isFloat = true) :
    (CTy.ofClif ty).valClass = .float := by
  cases ty <;> simp_all [Clif.Ty.isFloat, CTy.ofClif, CTy.valClass, CTy.regClass?]

end Helpers

/-- The memory flags, an offset, a `ty`-free operand: no registers, no `MInst`. -/
theorem γ_c0_op {ctx : Ctx} {o : Opnd} (hr : (V.op o).regsIn = []) : γP ctx noInst AT.c0 (.op o) :=
  γ_c0V hr rfl

theorem γ_c0_int {ctx : Ctx} {i : Int} : γP ctx noInst AT.c0 (.int i) :=
  γ_c0V rfl rfl


theorem γ_c0_variant {ctx : Ctx} {ty : TypeId} {name : String} (hty : ty ≠ tyMInst) :
    γP ctx noInst AT.c0 (mkVariant ty name []) :=
  γ_c0V (by unfold mkVariant; split <;> simp [V.regsIn, Flow.regsInL, Flow.opRegs]) (Cov.covV_mkVariant hty rfl)

theorem ofClif_int_mCTys {u : Clif.Ty} (hi : u.isInt = true) (hm : CTy.ofClif u ∈ mCTys) :
    CTy.ofClif u ∈ eCTys := by
  cases u <;> simp_all [Clif.Ty.isInt, CTy.ofClif, mCTys, eCTys]

/-- `FamOk`'s result conjuncts for a single result of an E type. -/
theorem resE1 {info : IInfo} {ty : Clif.Ty} (hres : info.resTys = [CTy.ofClif ty])
    (h : Compile.tyE ty = true) {F : Fam} (hr : eCTys ⊆ F.res) (ha : eCTys ⊆ F.all) :
    (∀ t ∈ info.resTys, t ∈ F.res ∧ t ∈ F.all) ∧ info.resTys.head?.getD .invalid ∈ F.res := by
  rw [hres]
  refine ⟨fun t ht => ?_, by simpa using hr (ofClif_eCTys h)⟩
  simp at ht; subst ht; exact ⟨hr (ofClif_eCTys h), ha (ofClif_eCTys h)⟩

/-- `FamOk`'s result conjuncts for a single float result. -/
theorem resF1 {info : IInfo} {ty : Clif.Ty} (hres : info.resTys = [CTy.ofClif ty])
    (h : ty.isFloat = true) {F : Fam} (hr : fCTys ⊆ F.res) (ha : fCTys ⊆ F.all) :
    (∀ t ∈ info.resTys, t ∈ F.res ∧ t ∈ F.all) ∧ info.resTys.head?.getD .invalid ∈ F.res := by
  rw [hres]
  refine ⟨fun t ht => ?_, by simpa using hr (ofClif_fCTys h)⟩
  simp at ht; subst ht; exact ⟨hr (ofClif_fCTys h), ha (ofClif_fCTys h)⟩

/-- `FamOk`'s result conjuncts without results. -/
theorem res0 {info : IInfo} (hres : info.resTys = []) {F : Fam} (hr : CTy.invalid ∈ F.res) :
    (∀ t ∈ info.resTys, t ∈ F.res ∧ t ∈ F.all) ∧ info.resTys.head?.getD .invalid ∈ F.res := by
  rw [hres]; exact ⟨fun t ht => (by cases ht), by simpa using hr⟩

set_option maxHeartbeats 4000000 in
/-- **Every statement belongs to an instruction family**, for a float-capable context whose
statements are of the typed scope (`instET`) or float operations that belong to a family (`hF`):
`famCover_of`'s proof, for the typed scope and the float scope (`famCover_ofF`). -/
theorem famCover_ofG {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (hctx : CtxInvT f ctx) (hx : f.externs.all (Compile.sigE ·.2.sig) = true)
    (hETs : ∀ B ∈ f.blocks, ∀ s ∈ B.body,
      Compile.instET s.inst = true ∨ ∃ op ty args, s.inst = .float op ty args)
    (hF : ∀ (j : Nat) info op ty args, ctx.insts[j]? = some info →
      info.clif = some (.float op ty args) →
      ∃ (i : Nat) (F : Fam), famTab[i]? = some F ∧ FamOk ctx F info)
    (hdom : dominatedB f = true) (hst : Compile.storeTypedB f = true)
    (hsel : Compile.selectTypedB f = true) (hb : buildCtx f = .ok (ctx, ranges, st0)) :
    FamCover ctx := by
  have sp := ctxSpec_of hb
  have hd := dominated_of hdom
  intro j info c hj hc
  obtain ⟨B, hB, s, hsB, -, hcs⟩ := sp.inst_of hj hc
  have hdata := hctx.data j info c hj hc
  obtain ⟨tys, htys, hres, hlen0⟩ := hctx.resTys j info c hj hc
  have hlen : info.results.length = info.resTys.length := by rw [hres, hlen0]; simp
  have hrv := (sp.facts.types hd.ssa).1 j info hj
  have hint := hctx.intOps j info c hj hc
  rcases hETs B hB s hsB with hET | ⟨op, ty, args, hfl⟩
  rotate_left
  · rw [hfl] at hcs; subst hcs; exact hF j info op ty args hj hc
  rw [← hcs] at hET
  have htyped : ∀ y ∈ instArgs c, (ctx.valueType? y).isSome := by
    intro y hy
    obtain ⟨bi, hbi, e⟩ := List.getElem_of_mem hB
    obtain ⟨jj, hjj, e'⟩ := List.getElem_of_mem hsB
    have hB' : f.blocks[bi]? = some B := by rw [List.getElem?_eq_getElem hbi, e]
    have hs' : B.body[jj]? = some s := by rw [List.getElem?_eq_getElem hjj, e']
    rw [hcs] at hy
    exact Prg.typed_of_def sp (availOf_defs ((hd.uses ctx ranges st0 hb bi B hB').1 jj s hs' y hy))
  have hM := hctx.valTyM
  -- the result types
  have hresE : (∀ t ∈ tys, Compile.tyE t = true) →
      ∀ t ∈ info.resTys, t ∈ eCTys := by
    intro h t ht
    rw [hres] at ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    exact ofClif_eCTys (h u hu)
  cases c with
  | iconst ty imm =>
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
    subst htys
    simp only [instData] at hdata
    split at hdata
    · rename_i hty
      simp only [pure, Except.pure, Except.ok.injEq] at hdata
      refine ⟨0, _, rfl, famOk_of hrv hlen (fun t ht => ?_) ?_ ?_⟩
      · rw [hres] at ht; simp at ht; subst ht; exact ⟨ofClif_eTy hty, ofClif_eTy hty⟩
      · rw [hres]; exact ofClif_eTy hty
      · rw [← hdata]
        exact γ_idata (by decide) ⟨γ_opAlts (by decide), γ_c0_int, trivial⟩
    split at hdata
    · rename_i hty
      subst hty
      simp only [pure, Except.pure, Except.ok.injEq] at hdata
      refine ⟨21, _, rfl, famOk_of hrv hlen (fun t ht => ?_) ?_ ?_⟩
      · rw [hres] at ht; simp at ht; subst ht; simp [famTab, CTy.ofClif, fCTys]
      · rw [hres]; simp [famTab, CTy.ofClif, fCTys]
      · rw [← hdata]
        exact γ_idata (by decide) ⟨γ_opAlts (by decide), γ_c0_int, trivial⟩
    split at hdata
    · rename_i hty
      subst hty
      simp only [pure, Except.pure, Except.ok.injEq] at hdata
      refine ⟨22, _, rfl, famOk_of hrv hlen (fun t ht => ?_) ?_ ?_⟩
      · rw [hres] at ht; simp at ht; subst ht; simp [famTab, CTy.ofClif, fCTys]
      · rw [hres]; simp [famTab, CTy.ofClif, fCTys]
      · rw [← hdata]
        exact γ_idata (by decide) ⟨γ_opAlts (by decide), γ_c0_int, trivial⟩
    · cases hdata

  | unary op ty x =>
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
    subst htys
    simp only [List.map_cons, List.map_nil] at hres
    have hE : Compile.tyE ty = true := by
      simp only [Compile.instET, Compile.instE, Compile.unaryTyE] at hET
      split at hET <;> simp_all
    have he : eTy ty = true := hE
    have hx := valIn_E (hint x (by simp [intArgs]))
    cases op <;> simp only [Compile.instET, Compile.instE, Compile.unaryTyE, Compile.unaryE,
      Bool.false_and, Bool.and_false, reduceCtorEq] at hET
    all_goals simp [instData, unaryOpcode, he, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hdata
    all_goals try (split at hdata; · simp_all)
    all_goals try simp only [Except.ok.injEq] at hdata
    all_goals (
      obtain ⟨hR1, hR2⟩ := resE1 hres hE (F := famTab[1]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes])
      exact ⟨1, _, rfl, famOk_of hrv hlen hR1 hR2
        (by rw [← hdata]; exact γ_idata (by decide) ⟨γ_opAlts (by decide), γ_val hx, trivial⟩)⟩)

  | binary op ty x y =>
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
    subst htys
    simp only [List.map_cons, List.map_nil] at hres
    have hE : Compile.tyE ty = true := by
      simp only [Compile.instET, Compile.instE, Bool.and_eq_true] at hET; exact hET.2
    have he : eTy ty = true := hE
    have hxy := γ_vals2 (ctx := ctx) (valIn_E (hint x (by simp [intArgs]))) (valIn_E (hint y (by simp [intArgs])))
    cases op <;> simp only [Compile.instET, Compile.instE, Compile.binaryE, Bool.false_and,
      reduceCtorEq] at hET
    all_goals simp [instData, binaryOpcode, he, pure, Except.pure] at hdata
    all_goals (
      obtain ⟨hR1, hR2⟩ := resE1 hres hE (F := famTab[2]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes])
      exact ⟨2, _, rfl, famOk_of hrv hlen hR1 hR2
        (by rw [← hdata]; exact γ_idata (by decide) ⟨γ_opAlts (by decide), hxy, trivial⟩)⟩)
  | div op ty x y =>
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
    subst htys
    simp only [List.map_cons, List.map_nil] at hres
    have hE : Compile.tyE ty = true := by
      simpa [Compile.instET, Compile.instE] using hET
    have he : eTy ty = true := hE
    have hxy := γ_vals2 (ctx := ctx) (valIn_E (hint x (by simp [intArgs]))) (valIn_E (hint y (by simp [intArgs])))
    cases op <;> simp [instData, divOpcode, he, pure, Except.pure] at hdata
    all_goals (
      obtain ⟨hR1, hR2⟩ := resE1 hres hE (F := famTab[2]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes])
      exact ⟨2, _, rfl, famOk_of hrv hlen hR1 hR2
        (by rw [← hdata]; exact γ_idata (by decide) ⟨γ_opAlts (by decide), hxy, trivial⟩)⟩)
  | icmp cc ty x y =>
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
    subst htys
    simp only [List.map_cons, List.map_nil] at hres
    have hE : Compile.tyE ty = true := by
      simpa [Compile.instET, Compile.instE] using hET
    have he : eTy ty = true := hE
    have hxy := γ_vals2 (ctx := ctx) (valIn_E (hint x (by simp [intArgs]))) (valIn_E (hint y (by simp [intArgs])))
    simp [instData, he, pure, Except.pure] at hdata
    obtain ⟨hR1, hR2⟩ := resE1 hres (ty := .i8) rfl (F := famTab[3]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes])
    exact ⟨3, _, rfl, famOk_of hrv hlen hR1 hR2
      (by rw [← hdata]; exact γ_idata (by decide) ⟨γ_opAlts (by decide), hxy, γ_c0_variant (by decide), trivial⟩)⟩
  | extend op ty x =>
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
    subst htys
    simp only [List.map_cons, List.map_nil] at hres
    have hE : Compile.tyE ty = true := by
      simpa [Compile.instET, Compile.instE] using hET
    have he : eTy ty = true := hE
    have hx := valIn_E (hint x (by simp [intArgs]))
    cases op <;> simp [instData, he, pure, Except.pure] at hdata
    all_goals (
      obtain ⟨hR1, hR2⟩ := resE1 hres hE (F := famTab[1]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes])
      exact ⟨1, _, rfl, famOk_of hrv hlen hR1 hR2
        (by rw [← hdata]; exact γ_idata (by decide) ⟨γ_opAlts (by decide), γ_val hx, trivial⟩)⟩)
  | ireduce ty x =>
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
    subst htys
    simp only [List.map_cons, List.map_nil] at hres
    have hE : Compile.tyE ty = true := by
      simpa [Compile.instET, Compile.instE] using hET
    have he : eTy ty = true := hE
    have hx := valIn_E (hint x (by simp [intArgs]))
    simp [instData, he, pure, Except.pure] at hdata
    obtain ⟨hR1, hR2⟩ := resE1 hres hE (F := famTab[1]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes])
    exact ⟨1, _, rfl, famOk_of hrv hlen hR1 hR2
      (by rw [← hdata]; exact γ_idata (by decide) ⟨γ_opAlts (by decide), γ_val hx, trivial⟩)⟩
  | bmask ty x =>
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
    subst htys
    simp only [List.map_cons, List.map_nil] at hres
    have hE : Compile.tyE ty = true := by
      simpa [Compile.instET, Compile.instE] using hET
    have he : eTy ty = true := hE
    have hx := valIn_E (hint x (by simp [intArgs]))
    simp [instData, he, pure, Except.pure] at hdata
    obtain ⟨hR1, hR2⟩ := resE1 hres hE (F := famTab[1]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes])
    exact ⟨1, _, rfl, famOk_of hrv hlen hR1 hR2
      (by rw [← hdata]; exact γ_idata (by decide) ⟨γ_opAlts (by decide), γ_val hx, trivial⟩)⟩
  | load op ty fl p off =>
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
    subst htys
    simp only [List.map_cons, List.map_nil] at hres
    have hp := valIn_E (hint p (by simp [intArgs]))
    have hfl : γP ctx noInst AT.c0 (.op (.memFlags fl)) := γ_c0V rfl rfl
    simp only [instData] at hdata
    split at hdata
    · cases hdata
    split at hdata
    · cases hdata
    simp only [pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Except.ok.injEq, reduceCtorEq] at hdata
    by_cases he : eTy ty = true
    · have hE : Compile.tyE ty = true := he
      obtain ⟨hR1, hR2⟩ := resE1 hres hE (F := famTab[4]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes])
      refine ⟨4, _, rfl, famOk_of hrv hlen hR1 hR2 ?_⟩
      rw [← hdata]
      refine γ_idata (by decide) ⟨?_, γ_val hp, hfl, γ_c0_int, trivial⟩
      cases op <;> exact γ_opAlts (by decide)
    · have hf : ty.isFloat = true ∧ op = .load := by
        simp only [Compile.instET, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hET
        rcases hET.2 with h | h
        · exact absurd h he
        · exact h
      obtain ⟨hF, rfl⟩ := hf
      obtain ⟨hR1, hR2⟩ := resF1 hres hF (F := famTab[5]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes])
      exact ⟨5, _, rfl, famOk_of hrv hlen hR1 hR2 (by
        rw [← hdata]
        exact γ_idata (by decide) ⟨γ_opAlts (by decide), γ_val hp, hfl, γ_c0_int, trivial⟩)⟩
  | store op ty fl x p off =>
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
    subst htys
    simp only [List.map_nil] at hres
    have hfl : γP ctx noInst AT.c0 (.op (.memFlags fl)) := γ_c0V rfl rfl
    simp only [instData] at hdata
    split at hdata
    · cases hdata
    split at hdata
    · cases hdata
    simp only [pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Except.ok.injEq, reduceCtorEq] at hdata
    obtain ⟨hR1, hR2⟩ := res0 hres (F := famTab[6]) (by simp [famTab, noRes])
    by_cases hF : ty.isFloat = true
    · have hop : op = .store := by
        simp only [Compile.instET, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hET
        rcases hET.2 with h | h
        · simp [Compile.tyE, Clif.Ty.isInt] at h; cases ty <;> simp_all [Clif.Ty.isFloat]
        · exact h.2
      subst hop
      have hp := valIn_E (hint p (by cases ty <;> simp_all [intArgs, Clif.Ty.isFloat]))
      have hcl := sp.class_of_argClassOk
        (Compile.storeTypedB_sound hst B hB s hsB .store ty fl x p off hcs.symm hF)
        (by cases ty <;> simp_all [valTyOk, Clif.Ty.isFloat])
      have hx : ValIn ctx x fCTys := valIn_F (htyped x (by simp [instArgs]))
        (fun t ht => (hcl t ht).trans (valClass_ofClif_float hF)) (hM x)
      obtain ⟨hR1, hR2⟩ := res0 hres (F := famTab[7]) (by simp [famTab, noRes])
      exact ⟨7, _, rfl, famOk_of hrv hlen hR1 hR2 (by
        rw [← hdata]
        exact γ_idata (by decide) ⟨γ_opAlts (by decide), γ_vals2 hx hp, hfl, γ_c0_int, trivial⟩)⟩
    · have hxp := γ_vals2 (ctx := ctx) (valIn_E (hint x (by cases ty <;> simp_all [intArgs, Clif.Ty.isFloat])))
        (valIn_E (hint p (by cases ty <;> simp_all [intArgs, Clif.Ty.isFloat])))
      refine ⟨6, _, rfl, famOk_of hrv hlen hR1 hR2 ?_⟩
      rw [← hdata]
      refine γ_idata (by decide) ⟨?_, hxp, hfl, γ_c0_int, trivial⟩
      cases op <;> exact γ_opAlts (by decide)
  | select ty c x y =>
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
    subst htys
    simp only [List.map_cons, List.map_nil] at hres
    simp only [instData] at hdata
    split at hdata
    rotate_left
    · cases hdata
    rename_i hv
    simp only [pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Except.ok.injEq, reduceCtorEq] at hdata
    by_cases hF : ty.isFloat = true
    · have hc' := valIn_E (hint c (by cases ty <;> simp_all [intArgs, Clif.Ty.isFloat]))
      obtain ⟨h1, h2⟩ := Compile.selectTypedB_sound hsel B hB s hsB ty c x y hcs.symm hF
      have hx : ValIn ctx x fCTys := valIn_F (htyped x (by simp [instArgs]))
        (fun t ht => (sp.class_of_argClassOk h1 hv t ht).trans (valClass_ofClif_float hF)) (hM x)
      have hy : ValIn ctx y fCTys := valIn_F (htyped y (by simp [instArgs]))
        (fun t ht => (sp.class_of_argClassOk h2 hv t ht).trans (valClass_ofClif_float hF)) (hM y)
      obtain ⟨hR1, hR2⟩ := resF1 hres hF (F := famTab[9]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes])
      exact ⟨9, _, rfl, famOk_of hrv hlen hR1 hR2 (by
        rw [← hdata]
        exact γ_idata (by decide) ⟨γ_opAlts (by decide), γ_vals3 hc' hx hy, trivial⟩)⟩
    · have hE : Compile.tyE ty = true := by
        cases ty <;> simp_all [valTyOk, eTy, Compile.tyE, Clif.Ty.isFloat]
      have h3 := γ_vals3 (ctx := ctx) (valIn_E (hint c (by cases ty <;> simp_all [intArgs, Clif.Ty.isFloat])))
        (valIn_E (hint x (by cases ty <;> simp_all [intArgs, Clif.Ty.isFloat]))) (valIn_E (hint y (by cases ty <;> simp_all [intArgs, Clif.Ty.isFloat])))
      obtain ⟨hR1, hR2⟩ := resE1 hres hE (F := famTab[8]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes])
      exact ⟨8, _, rfl, famOk_of hrv hlen hR1 hR2 (by
        rw [← hdata]
        exact γ_idata (by decide) ⟨γ_opAlts (by decide), h3, trivial⟩)⟩
  | bitcast ty fl x =>
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
    subst htys
    simp only [List.map_cons, List.map_nil] at hres
    have hfl : γP ctx noInst AT.c0 (.op (.memFlags fl)) := γ_c0V rfl rfl
    have hx := γ_val (valIn_any hctx x)
    simp only [instData] at hdata
    split at hdata
    rotate_left
    · cases hdata
    rename_i hv
    simp only [pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Except.ok.injEq, reduceCtorEq] at hdata
    by_cases hF : ty.isFloat = true
    · obtain ⟨hR1, hR2⟩ := resF1 hres hF (F := famTab[23]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes])
      exact ⟨23, _, rfl, famOk_of hrv hlen hR1 hR2 (by
        rw [← hdata]
        exact γ_idata (by decide) ⟨γ_opAlts (by decide), hx, hfl, trivial⟩)⟩
    · have hE : Compile.tyE ty = true := by
        cases ty <;> simp_all [valTyOk, eTy, Compile.tyE, Clif.Ty.isFloat]
      obtain ⟨hR1, hR2⟩ := resE1 hres hE (F := famTab[17]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes])
      exact ⟨17, _, rfl, famOk_of hrv hlen hR1 hR2 (by
        rw [← hdata]
        exact γ_idata (by decide) ⟨γ_opAlts (by decide), hx, hfl, trivial⟩)⟩
  | nop =>
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
    subst htys
    simp only [List.map_nil] at hres
    simp only [instData, pure, Except.pure, Except.ok.injEq] at hdata
    obtain ⟨hR1, hR2⟩ := res0 hres (F := famTab[10]) (by simp [famTab, noRes])
    exact ⟨10, _, rfl, famOk_of hrv hlen hR1 hR2 (by
      rw [← hdata]; exact γ_idata (by decide) ⟨γ_opAlts (by decide), trivial⟩)⟩
  | fence =>
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
    subst htys
    simp only [List.map_nil] at hres
    simp only [instData, pure, Except.pure, Except.ok.injEq] at hdata
    obtain ⟨hR1, hR2⟩ := res0 hres (F := famTab[10]) (by simp [famTab, noRes])
    exact ⟨10, _, rfl, famOk_of hrv hlen hR1 hR2 (by
      rw [← hdata]; exact γ_idata (by decide) ⟨γ_opAlts (by decide), trivial⟩)⟩
  | symbolValue ty gv =>
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
    subst htys
    simp only [List.map_cons, List.map_nil] at hres
    have hty : ty = .i64 := by simpa [Compile.instET, Compile.instE] using hET
    subst hty
    simp only [instData] at hdata
    split at hdata
    · cases hdata
    split at hdata <;> simp only [pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Except.ok.injEq, reduceCtorEq] at hdata
    obtain ⟨hR1, hR2⟩ := resE1 hres (ty := .i64) rfl (F := famTab[11]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes])
    exact ⟨11, _, rfl, famOk_of hrv hlen hR1 hR2 (by
      rw [← hdata]; exact γ_idata (by decide) ⟨γ_opAlts (by decide), γ_c0V rfl rfl, trivial⟩)⟩
  | tlsValue ty gv =>
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
    subst htys
    simp only [List.map_cons, List.map_nil] at hres
    have hty : ty = .i64 := by simpa [Compile.instET, Compile.instE] using hET
    subst hty
    simp only [instData] at hdata
    split at hdata
    · cases hdata
    split at hdata <;> simp only [pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Except.ok.injEq, reduceCtorEq] at hdata
    obtain ⟨hR1, hR2⟩ := resE1 hres (ty := .i64) rfl (F := famTab[11]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes])
    exact ⟨11, _, rfl, famOk_of hrv hlen hR1 hR2 (by
      rw [← hdata]; exact γ_idata (by decide) ⟨γ_opAlts (by decide), γ_c0V rfl rfl, trivial⟩)⟩
  | stackAddr ty slot off =>
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
    subst htys
    simp only [List.map_cons, List.map_nil] at hres
    have hE : Compile.tyE ty = true := by simpa [Compile.instET, Compile.instE] using hET
    simp only [instData, pure, Except.pure, Except.ok.injEq] at hdata
    obtain ⟨hR1, hR2⟩ := resE1 hres hE (F := famTab[12]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes])
    exact ⟨12, _, rfl, famOk_of hrv hlen hR1 hR2 (by
      rw [← hdata]
      exact γ_idata (by decide) ⟨γ_opAlts (by decide), γ_c0V rfl rfl, γ_c0_int, trivial⟩)⟩
  | call fn args =>
    simp only [instData] at hdata
    split at hdata
    rotate_left
    · cases hdata
    rename_i ext hext
    split at hdata
    rotate_left
    · cases hdata
    simp only [pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Except.ok.injEq, reduceCtorEq] at hdata
    simp only [Clif.Inst.resultTypes, hext, Option.map_some, Option.some.injEq] at htys
    subst htys
    have hsig := List.all_eq_true.mp hx _ (Compile.lookup_mem hext)
    simp only [Compile.sigE, Bool.and_eq_true, List.all_eq_true] at hsig
    have hrE : ∀ t ∈ info.resTys, t ∈ eCTys := by
      intro t ht
      rw [hres] at ht
      simp only [List.map_map, List.mem_map, Function.comp_apply] at ht
      obtain ⟨p, hp, rfl⟩ := ht
      exact ofClif_eCTys (hsig.2 p hp)
    refine ⟨13, _, rfl, famOk_of hrv hlen (fun t ht => ?_) ?_ ?_⟩
    · have := hrE t ht
      exact ⟨by simp [famTab, this], by simpa [famTab] using this⟩
    · cases hr : info.resTys with
      | nil => simp [famTab, noRes]
      | cons t ts => simp [famTab, hrE t (by rw [hr]; simp)]
    · rw [← hdata]
      exact γ_idata (by decide) ⟨γ_opAlts (by decide),
        γ_valsAll fun x hx => valIn_E (hint x (by simpa [intArgs] using hx)), γ_c0V rfl rfl, trivial⟩
  | callIndirect sig callee args =>
    simp only [instData] at hdata
    split at hdata
    rotate_left
    · cases hdata
    rename_i sd hsd
    split at hdata
    rotate_left
    · cases hdata
    rename_i hint'
    simp only [pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Except.ok.injEq, reduceCtorEq] at hdata
    simp only [Clif.Inst.resultTypes, hsd, Option.map_some, Option.some.injEq] at htys
    subst htys
    have hrE : ∀ t ∈ info.resTys, t ∈ eCTys := by
      intro t ht
      have hm := hctx.resTysM j info hj t ht
      rw [hres] at ht
      simp only [List.map_map, List.mem_map, Function.comp_apply] at ht
      obtain ⟨p, hp, rfl⟩ := ht
      simp only [sigIntB, Bool.and_eq_true, List.all_eq_true] at hint'
      exact ofClif_int_mCTys (hint'.2 p hp) hm
    refine ⟨14, _, rfl, famOk_of hrv hlen (fun t ht => ?_) ?_ ?_⟩
    · have := hrE t ht
      exact ⟨by simp [famTab, this], by simpa [famTab] using this⟩
    · cases hr : info.resTys with
      | nil => simp [famTab, noRes]
      | cons t ts => simp [famTab, hrE t (by rw [hr]; simp)]
    · rw [← hdata]
      exact γ_idata (by decide) ⟨γ_opAlts (by decide),
        γ_valsAll fun x hx => valIn_E (hint x (by simpa [intArgs] using hx)), γ_c0V rfl rfl, trivial⟩
  | funcAddr ty fn =>
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
    subst htys
    simp only [List.map_cons, List.map_nil] at hres
    have hty : ty = .i64 := by simpa [Compile.instET, Compile.instE] using hET
    subst hty
    simp only [instData] at hdata
    split at hdata
    · cases hdata
    simp only [pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Except.ok.injEq, reduceCtorEq] at hdata
    obtain ⟨hR1, hR2⟩ := resE1 hres (ty := .i64) rfl (F := famTab[15]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes])
    exact ⟨15, _, rfl, famOk_of hrv hlen hR1 hR2 (by
      rw [← hdata]; exact γ_idata (by decide) ⟨γ_opAlts (by decide), γ_c0V rfl rfl, trivial⟩)⟩
  | atomicLoad ty fl p =>
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
    subst htys
    simp only [List.map_cons, List.map_nil] at hres
    have hE : Compile.tyE ty = true := by
      simp only [Compile.instET, Compile.instE, Bool.and_eq_true] at hET; exact hET.1
    simp only [instData] at hdata
    split at hdata
    · cases hdata
    split at hdata
    · cases hdata
    simp only [pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Except.ok.injEq, reduceCtorEq] at hdata
    obtain ⟨hR1, hR2⟩ := resE1 hres hE (F := famTab[16]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes])
    exact ⟨16, _, rfl, famOk_of hrv hlen hR1 hR2 (by
      rw [← hdata]
      exact γ_idata (by decide) ⟨γ_opAlts (by decide), γ_val (valIn_E (hint p (by simp [intArgs]))), γ_c0V rfl rfl, trivial⟩)⟩
  | atomicStore ty fl x p =>
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
    subst htys
    simp only [List.map_nil] at hres
    simp only [instData] at hdata
    split at hdata
    · cases hdata
    split at hdata
    · cases hdata
    simp only [pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Except.ok.injEq, reduceCtorEq] at hdata
    obtain ⟨hR1, hR2⟩ := res0 hres (F := famTab[18]) (by simp [famTab, noRes])
    exact ⟨18, _, rfl, famOk_of hrv hlen hR1 hR2 (by
      rw [← hdata]
      exact γ_idata (by decide) ⟨γ_opAlts (by decide), γ_vals2 (valIn_E (hint x (by simp [intArgs]))) (valIn_E (hint p (by simp [intArgs]))),
        γ_c0V rfl rfl, trivial⟩)⟩
  | atomicRmw op ty fl p x =>
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
    subst htys
    simp only [List.map_cons, List.map_nil] at hres
    have hE : Compile.tyE ty = true := by
      simp only [Compile.instET, Compile.instE, Bool.and_eq_true] at hET; exact hET.1
    simp only [instData] at hdata
    split at hdata
    · cases hdata
    split at hdata
    · cases hdata
    split at hdata
    rotate_left
    · cases hdata
    simp only [pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Except.ok.injEq, reduceCtorEq] at hdata
    obtain ⟨hR1, hR2⟩ := resE1 hres hE (F := famTab[19]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes])
    exact ⟨19, _, rfl, famOk_of hrv hlen hR1 hR2 (by
      rw [← hdata]
      exact γ_idata (by decide) ⟨γ_opAlts (by decide), γ_vals2 (valIn_E (hint p (by simp [intArgs]))) (valIn_E (hint x (by simp [intArgs]))),
        γ_c0V rfl rfl, γ_c0_variant (by decide), trivial⟩)⟩
  | atomicCas ty fl p e x =>
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
    subst htys
    simp only [List.map_cons, List.map_nil] at hres
    have hE : Compile.tyE ty = true := by
      simp only [Compile.instET, Compile.instE, Bool.and_eq_true] at hET; exact hET.1
    simp only [instData] at hdata
    split at hdata
    · cases hdata
    split at hdata
    · cases hdata
    simp only [pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Except.ok.injEq, reduceCtorEq] at hdata
    obtain ⟨hR1, hR2⟩ := resE1 hres hE (F := famTab[20]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes]) (by simp only [List.subset_def]; intro t ht; simp_all [famTab, eCTys, fCTys, noRes])
    exact ⟨20, _, rfl, famOk_of hrv hlen hR1 hR2 (by
      rw [← hdata]
      exact γ_idata (by decide) ⟨γ_opAlts (by decide), γ_vals3 (valIn_E (hint p (by simp [intArgs]))) (valIn_E (hint e (by simp [intArgs]))) (valIn_E (hint x (by simp [intArgs]))),
        γ_c0V rfl rfl, trivial⟩)⟩
  | _ => simp [Compile.instET, Compile.instE] at hET

/-- **Every statement of a typed-scope function belongs to an instruction family.** -/
theorem famCover_of {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (hs : LowerScopeT f) (hdom : dominatedB f = true) (hst : Compile.storeTypedB f = true)
    (hsel : Compile.selectTypedB f = true) (hb : buildCtx f = .ok (ctx, ranges, st0)) :
    FamCover ctx := by
  refine famCover_ofG (ctxInvT_of hs hb) (externsE_of hs.subsetT) (fun B hB s hsB => ?_)
    (fun j info op ty args hj hc => ?_) hdom hst hsel hb
  · have h := hs.subsetT
    simp only [Compile.functionET, Bool.and_eq_true, List.all_eq_true] at h
    exact .inl ((h.1.1.2 B hB).1.2 s hsB)
  · obtain ⟨B, hB, s, hsB, -, hcs⟩ := (ctxSpec_of hb).inst_of hj hc
    have h := hs.subsetT
    simp only [Compile.functionET, Bool.and_eq_true, List.all_eq_true] at h
    have := (h.1.1.2 B hB).1.2 s hsB
    rw [← hcs] at this
    simp [Compile.instET, Compile.instE] at this

theorem famOk_nores {ctx : Ctx} {F : Fam} {data : V} (hr : CTy.invalid ∈ F.res)
    (hd : γP ctx noInst F.data data) : FamOk ctx F ⟨data, [], [], none⟩ :=
  ⟨by simpa using hr, fun x hx => by simp at hx, fun x hx => by simp at hx, hd⟩

set_option maxHeartbeats 4000000 in
/-- **A terminator belongs to a terminator family** (as the data of its slot: no results), for a
float-capable context whose terminators' integer positions are integer values (`hops`):
`termFam_of`'s proof, for the typed scope and the float scope. -/
theorem termFam_ofG {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx)
    {B : Clif.Block} {data : V}
    (hops : ∀ x ∈ Compile.termIntOperands B.term, ValIn ctx x eCTys)
    (hd : termData (abiTerm f B.term) = .ok data ∨ tryCallData f B.term = .ok data) :
    ∃ (i : Nat) (F : Fam), famTab[i]? = some F ∧ FamOk ctx F ⟨data, [], [], none⟩ := by
  rcases hd with hd | hd
  · cases ht : B.term with
    | jump bc =>
      rw [ht] at hd
      simp only [abiTerm, termData, pure, Except.pure, Except.ok.injEq] at hd
      subst hd
      exact ⟨24, _, rfl, famOk_nores (by simp [famTab, noRes])
        (γ_idata (by decide) ⟨γ_opAlts (by decide), γ_c0V rfl rfl, trivial⟩)⟩
    | brif c a b =>
      rw [ht] at hd hops
      simp only [abiTerm, termData, pure, Except.pure, Except.ok.injEq] at hd
      subst hd
      exact ⟨25, _, rfl, famOk_nores (by simp [famTab, noRes])
        (γ_idata (by decide) ⟨γ_opAlts (by decide),
          γ_val (hops c (by simp [Compile.termIntOperands])), γ_c0V rfl rfl, trivial⟩)⟩
    | brTable x d tb =>
      rw [ht] at hd hops
      simp only [abiTerm, termData, pure, Except.pure, Except.ok.injEq] at hd
      subst hd
      exact ⟨26, _, rfl, famOk_nores (by simp [famTab, noRes])
        (γ_idata (by decide) ⟨γ_opAlts (by decide),
          γ_val (hops x (by simp [Compile.termIntOperands])), γ_c0V rfl rfl, trivial⟩)⟩
    | ret vs =>
      rw [ht] at hd
      simp only [abiTerm, termData, pure, Except.pure, Except.ok.injEq] at hd
      subst hd
      exact ⟨27, _, rfl, famOk_nores (by simp [famTab, noRes])
        (γ_idata (by decide) ⟨γ_opAlts (by decide),
          γ_valsAll fun x _ => valIn_any hctx x, trivial⟩)⟩
    | trap c =>
      rw [ht] at hd
      simp only [abiTerm, termData, pure, Except.pure, Except.ok.injEq] at hd
      subst hd
      exact ⟨28, _, rfl, famOk_nores (by simp [famTab, noRes])
        (γ_idata (by decide) ⟨γ_opAlts (by decide), γ_c0V rfl rfl, trivial⟩)⟩
    | returnCall fn args =>
      rw [ht] at hd; simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
    | tryCall fn args et =>
      rw [ht] at hd; simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
    | tryCallIndirect callee args et =>
      rw [ht] at hd; simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
  · cases ht : B.term with
    | tryCall fn args et =>
      rw [ht] at hd hops
      simp only [tryCallData, bind, Except.bind] at hd
      split at hd
      · cases hd
      rename_i q hq
      obtain ⟨sig, items⟩ := q
      simp only at hd
      repeat' (split at hd)
      all_goals try (simp [throw, throwThe, MonadExceptOf.throw] at hd; done)
      all_goals (
        simp only [pure, Except.pure, Except.ok.injEq] at hd
        subst hd
        exact ⟨29, _, rfl, famOk_nores (by simp [famTab, noRes])
          (γ_idata (by decide) ⟨γ_opAlts (by decide),
            γ_valsAll fun x hx => hops x (by simpa [Compile.termIntOperands] using hx),
            γ_c0V rfl rfl, γ_c0V rfl rfl, trivial⟩)⟩)
    | tryCallIndirect callee args et =>
      rw [ht] at hd hops
      simp only [tryCallData, bind, Except.bind] at hd
      split at hd
      · cases hd
      rename_i q hq
      obtain ⟨sig, items⟩ := q
      simp only [pure, Except.pure, Except.ok.injEq] at hd
      subst hd
      exact ⟨30, _, rfl, famOk_nores (by simp [famTab, noRes])
        (γ_idata (by decide) ⟨γ_opAlts (by decide),
          γ_valsAll fun x hx => hops x (by simpa [Compile.termIntOperands] using hx),
          γ_c0V rfl rfl, trivial⟩)⟩
    | _ => rw [ht] at hd; simp [tryCallData, throw, throwThe, MonadExceptOf.throw] at hd

/-- **A terminator of a typed-scope function belongs to a terminator family** (as the data of
its slot: no results). -/
theorem termFam_of {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (hs : LowerScopeT f) (hdom : dominatedB f = true) (hb : buildCtx f = .ok (ctx, ranges, st0))
    {B : Clif.Block} (hB : B ∈ f.blocks) {data : V}
    (hd : termData (abiTerm f B.term) = .ok data ∨ tryCallData f B.term = .ok data) :
    ∃ (i : Nat) (F : Fam), famTab[i]? = some F ∧ FamOk ctx F ⟨data, [], [], none⟩ := by
  have sp := ctxSpec_of hb
  refine termFam_ofG (ctxInvT_of hs hb) (fun x hx => ?_) hd
  refine valIn_E fun t ht => ?_
  have h := hs.subsetT
  simp only [Compile.functionET, Compile.opsTypedT, Bool.and_eq_true, List.all_eq_true] at h
  have h2 := (h.1.2 B hB).2 x hx
  exact sp.eCTys_of_not_floatDef ht (by simpa using h2)

/-- With SSA, the results of a statement whose result types are E types are of class `int`. -/
theorem results_int {ctx : Ctx} {info : IInfo}
    (hrv : ∀ (m : Nat) r t, info.results[m]? = some r → info.resTys[m]? = some t →
      ctx.valueType? r = some t)
    (hlen : info.results.length = info.resTys.length) (hE : ∀ t ∈ info.resTys, t ∈ eCTys) :
    ∀ x ∈ info.results, valClassOf ctx x = .int := by
  intro x hx
  obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hx
  have hlt : m < info.resTys.length := hlen ▸ (List.getElem?_eq_some_iff.mp hm).1
  have hv := hrv m x _ hm (List.getElem?_eq_getElem hlt)
  have ht := hE _ (List.getElem_mem hlt)
  simp only [valClassOf, hv, Option.map_some, Option.getD_some]
  simp only [eCTys, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with h | h | h | h <;> rw [h] <;> rfl

set_option maxHeartbeats 4000000 in
/-- **The results of a `call`/`call_indirect` are of class `int`** in a float-capable context of a
function with integer externs (`sigIntB` signatures; SSA types): `callRes_int`'s proof. -/
theorem callRes_intG {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (hctx : CtxInvT f ctx) (hx : f.externs.all (Compile.sigE ·.2.sig) = true)
    (hdom : dominatedB f = true) (hb : buildCtx f = .ok (ctx, ranges, st0))
    {j : Nat} {info : IInfo} {c : Clif.Inst} (hj : ctx.insts[j]? = some info)
    (hc : info.clif = some c) (hcall : Cov.CallInst c) :
    ∀ x ∈ info.results, valClassOf ctx x = .int := by
  have sp := ctxSpec_of hb
  have hd := dominated_of hdom
  have hdata := hctx.data j info c hj hc
  obtain ⟨tys, htys, hres, hlen0⟩ := hctx.resTys j info c hj hc
  have hlen : info.results.length = info.resTys.length := by rw [hres, hlen0]; simp
  have hrv := (sp.facts.types hd.ssa).1 j info hj
  refine results_int hrv hlen ?_
  cases c with
  | call fn args =>
    simp only [instData] at hdata
    split at hdata
    rotate_left
    · cases hdata
    rename_i ext hext
    simp only [Clif.Inst.resultTypes, hext, Option.map_some, Option.some.injEq] at htys
    subst htys
    have hsig := List.all_eq_true.mp hx _ (Compile.lookup_mem hext)
    simp only [Compile.sigE, Bool.and_eq_true, List.all_eq_true] at hsig
    intro t ht
    rw [hres] at ht
    simp only [List.map_map, List.mem_map, Function.comp_apply] at ht
    obtain ⟨p, hp, rfl⟩ := ht
    exact ofClif_eCTys (hsig.2 p hp)
  | callIndirect sig callee args =>
    simp only [instData] at hdata
    split at hdata
    rotate_left
    · cases hdata
    rename_i sd hsd
    split at hdata
    rotate_left
    · cases hdata
    rename_i hint'
    simp only [Clif.Inst.resultTypes, hsd, Option.map_some, Option.some.injEq] at htys
    subst htys
    intro t ht
    have hm := hctx.resTysM j info hj t ht
    rw [hres] at ht
    simp only [List.map_map, List.mem_map, Function.comp_apply] at ht
    obtain ⟨p, hp, rfl⟩ := ht
    simp only [sigIntB, Bool.and_eq_true, List.all_eq_true] at hint'
    exact ofClif_int_mCTys (hint'.2 p hp) hm
  | _ => simp [Cov.CallInst] at hcall

/-- **The results of a `call`/`call_indirect` of a typed-scope function are of class `int`**
(integer externs, `sigIntB` signatures; SSA types). -/
theorem callRes_int {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (hs : LowerScopeT f) (hdom : dominatedB f = true) (hb : buildCtx f = .ok (ctx, ranges, st0))
    {j : Nat} {info : IInfo} {c : Clif.Inst} (hj : ctx.insts[j]? = some info)
    (hc : info.clif = some c) (hcall : Cov.CallInst c) :
    ∀ x ∈ info.results, valClassOf ctx x = .int :=
  callRes_intG (ctxInvT_of hs hb) (externsE_of hs.subsetT) hdom hb hj hc hcall

end Backend.Proof.CovT
