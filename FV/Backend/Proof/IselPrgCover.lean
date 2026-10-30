import FV.Backend.Proof.IselPrgCtx

/-!
# Progress of the ISLE lowering (V7): the driver's roots are table roots

The arguments of the driver's ISLE calls are described by the table's roots:

* `stmt_root`: a statement's `lower [.inst ii]` — its form `formOf f c` describes `.inst ii`, is
  one of `stmtForms`, and every output `stmtOut` describes has one single register per result;
* `term_root`: a non-`try_call` terminator's `lower`/`lower_branch` call (`termCall`) in its
  context `termCtx`;
* `try_root`: a `try_call`'s `lower_branch` call in its context `tryCtx`.
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Backend.Proof.Driver Isle Isle.Aarch64

section
variable {f : Clif.Function} {ctx : Ctx}

/-! ## `γ` of the leaves -/

theorem γL_nil' : γL f ctx [] [] := by simp [γL]

theorem γL_cons' {a : PA} {as : List PA} {v : V} {vs : List V} (h1 : γ f ctx a v)
    (h2 : γL f ctx as vs) : γL f ctx (a :: as) (v :: vs) := by
  simp only [γL]; exact ⟨h1, h2⟩

theorem γ_mkVariant {t k : Nat} {n : String} {fs : List PA} {ws : List V}
    (hk : variantIdx t n = some k) (h : γL f ctx fs ws) : γ f ctx (.data t k fs) (mkVariant t n ws) := by
  unfold mkVariant; rw [hk]; simp only [γ]; exact ⟨ws, rfl, h⟩

theorem γ_instDataV {k : Nat} {n : String} {fs : List PA} {ws : List V}
    (hk : variantIdx tyInstData n = some k) (h : γL f ctx fs ws) :
    γ f ctx (idat k fs) (instDataV n ws) := γ_mkVariant hk h

theorem γ_opcodeV {k : Nat} {n : String} (hk : variantIdx tyOpcode n = some k) :
    γ f ctx (opc k) (opcodeV n) := γ_mkVariant hk γL_nil'

theorem γ_aV (hctx : CtxInvW f ctx) {x : Nat} (h : (ctx.valueType? x).isSome) :
    γ f ctx aV (.value x) := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
  simp only [aV, γ]
  exact ⟨x, t, rfl, ht, hctx.valTyE x t ht⟩

theorem γ_vals {as : List PA} {xs : List Nat} (h : γL f ctx as (xs.map .value)) :
    γ f ctx (.vals as) (.values xs) := by
  simp only [γ]; exact ⟨xs, rfl, h⟩

theorem γ_valsMin {lo : Nat} {xs : List Nat} (hl : lo ≤ xs.length)
    (h : ∀ x ∈ xs, (ctx.valueType? x).isSome) : γ f ctx (.valsMin lo) (.values xs) := by
  simp only [γ]; exact ⟨xs, rfl, hl, h⟩

theorem γ_int_any (i : Int) : γ f ctx (.int none none) (.int i) := by
  simp only [γ]; exact ⟨i, rfl, by simp, by simp⟩

theorem γ_ty_mem {t : CTy} {ts : List CTy} (h : t ∈ ts) : γ f ctx (.ty ts) (.ty t) := by
  simp only [γ]; exact ⟨t, h, rfl⟩

theorem γ_op {k : OK} {n : Option Nat} {o : Opnd} (h : OpOk ctx k n o) :
    γ f ctx (.op k n) (.op o) := by
  simp only [γ]; exact ⟨o, rfl, h⟩

theorem γ_memFlags {fl : Clif.MemFlags} (h : ¬(fl.endianness == some .big) = true) :
    γ f ctx (.op .memFlags none) (.op (.memFlags fl)) :=
  γ_op ⟨fl, rfl, by simpa using h⟩

theorem γ_labels {lo : Nat} {n : Option Nat} {ls : List Label} (hl : lo ≤ ls.length)
    (hn : n = none ∨ n = some ls.length) : γ f ctx (.labels lo n) (.labels ls) := by
  simp only [γ]; exact ⟨ls, rfl, hl, hn⟩

theorem γ_blockCalls {bs : List Nat} : γ f ctx (.blockCalls bs.length) (.blockCalls bs) := by
  simp only [γ]; exact ⟨bs, rfl, rfl⟩

theorem γ_tyCall (hctx : CtxInvW f ctx) {ii : Nat} {info : IInfo} (hi : ctx.insts[ii]? = some info) :
    γ f ctx tyCall (.ty (info.resTys.head?.getD .invalid)) := by
  apply γ_ty_mem
  cases h : info.resTys with
  | nil => simp
  | cons t ts =>
    have := hctx.resTysE ii info hi t (by simp [h])
    simp [this]

theorem γ_inst {ii : Nat} {info : IInfo} {t d : PA} (hi : ctx.insts[ii]? = some info)
    (ht : γ f ctx t (.ty (info.resTys.head?.getD .invalid))) (hd : γ f ctx d info.data)
    (hr : ∀ r ∈ info.results, (ctx.valueType? r).isSome) : γ f ctx (.inst t d) (.inst ii) := by
  simp only [γ]; exact ⟨ii, info, rfl, hi, ht, hd, hr⟩

theorem γ_regsVec {n : Option Nat} {rss : List (List Reg)} (h : γ f ctx (.regsVec n) (.regsVec rss)) :
    (∀ rs ∈ rss, rs.length = 1) ∧ (n = none ∨ n = some rss.length) := by
  simp only [γ] at h
  obtain ⟨rss', e, h1, h2⟩ := h
  cases e; exact ⟨h1, h2⟩

end

/-! ## Statement forms in `stmtForms` -/

theorem ofClif_ne (ty : Clif.Ty) : CTy.ofClif ty ≠ .invalid := by cases ty <;> simp [CTy.ofClif]

theorem mem_eTys {ty : Clif.Ty} (h : Compile.tyE ty = true) : ty ∈ eTys := by
  cases ty <;> simp_all [eTys, Compile.tyE, Clif.Ty.isInt]

section
variable {f : Clif.Function}

theorem sf_iconst {ty : Clif.Ty} (h : ty ∈ eTys) (imm : BitVec ty.width) :
    formOf f (.iconst ty imm) ∈ stmtForms := by
  dsimp only [stmtForms]; iterate 20 apply List.mem_append_left
  exact List.mem_map.2 ⟨ty, h, rfl⟩

theorem sf_unary {op : Clif.UnaryOp} {ty : Clif.Ty} (hop : op ∈ eUnary) (h : ty ∈ eTys)
    (hb : ¬(op == .bswap && ty == .i8) = true) (x : Nat) : formOf f (.unary op ty x) ∈ stmtForms := by
  dsimp only [stmtForms]; iterate 19 apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_flatMap.2 ⟨op, hop, List.mem_map.2 ⟨ty, List.mem_filter.2 ⟨h, by
    cases op <;> cases ty <;> simp_all⟩, rfl⟩⟩

theorem sf_binary {op : Clif.BinaryOp} {ty : Clif.Ty} (hop : op ∈ eBinary) (h : ty ∈ eTys)
    (x y : Nat) : formOf f (.binary op ty x y) ∈ stmtForms := by
  dsimp only [stmtForms]; iterate 18 apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_flatMap.2 ⟨op, hop, List.mem_map.2 ⟨ty, h, rfl⟩⟩

theorem sf_div (op : Clif.DivOp) {ty : Clif.Ty} (h : ty ∈ eTys) (x y : Nat) :
    formOf f (.div op ty x y) ∈ stmtForms := by
  dsimp only [stmtForms]; iterate 17 apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_flatMap.2 ⟨op, by cases op <;> simp, List.mem_map.2 ⟨ty, h, rfl⟩⟩

theorem sf_icmp (cc : Clif.IntCC) (ty : Clif.Ty) (x y : Nat) :
    formOf f (.icmp cc ty x y) ∈ stmtForms := by
  dsimp only [stmtForms]; iterate 16 apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.2 ⟨cc, by cases cc <;> simp, rfl⟩

theorem sf_extend (op : Clif.ExtendOp) {ty : Clif.Ty} (h : ty ∈ eTys) (x : Nat) :
    formOf f (.extend op ty x) ∈ stmtForms := by
  dsimp only [stmtForms]; iterate 15 apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_flatMap.2 ⟨op, by cases op <;> simp, List.mem_map.2 ⟨ty, h, rfl⟩⟩

theorem sf_ireduce {ty : Clif.Ty} (h : ty ∈ eTys) (x : Nat) :
    formOf f (.ireduce ty x) ∈ stmtForms := by
  dsimp only [stmtForms]; iterate 14 apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.2 ⟨ty, h, rfl⟩

theorem sf_load (op : Clif.LoadOp) {ty : Clif.Ty} (h : ty ∈ eTys) (fl : Clif.MemFlags) (p : Nat)
    (off : Int) : formOf f (.load op ty fl p off) ∈ stmtForms := by
  dsimp only [stmtForms]; iterate 13 apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_flatMap.2 ⟨op, by cases op <;> simp, List.mem_map.2 ⟨ty, h, rfl⟩⟩

theorem sf_store (op : Clif.StoreOp) (ty : Clif.Ty) (fl : Clif.MemFlags) (x p : Nat) (off : Int) :
    formOf f (.store op ty fl x p off) ∈ stmtForms := by
  dsimp only [stmtForms]; iterate 12 apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.2 ⟨op, by cases op <;> simp, rfl⟩

theorem sf_select {ty : Clif.Ty} (h : ty ∈ eTys) (c x y : Nat) :
    formOf f (.select ty c x y) ∈ stmtForms := by
  dsimp only [stmtForms]; iterate 11 apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.2 ⟨ty, h, rfl⟩

theorem sf_nop : formOf f .nop ∈ stmtForms := by
  dsimp only [stmtForms]; iterate 10 apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_cons_self

theorem sf_symbolValue (gv : Nat) : formOf f (.symbolValue .i64 gv) ∈ stmtForms := by
  dsimp only [stmtForms]; iterate 10 apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_cons_of_mem _ List.mem_cons_self

theorem sf_stackAddr {ty : Clif.Ty} (h : ty ∈ eTys) (s : Nat) (off : Int) :
    formOf f (.stackAddr ty s off) ∈ stmtForms := by
  dsimp only [stmtForms]; iterate 9 apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.2 ⟨ty, h, rfl⟩

theorem sf_call {fn : Nat} (h : retsOf f fn ≤ 8) (args : List Nat) :
    formOf f (.call fn args) ∈ stmtForms := by
  dsimp only [stmtForms]; iterate 8 apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.2 ⟨retsOf f fn, by simp [retCounts]; omega, rfl⟩

theorem sf_callIndirect {sig : Nat} (h : sigRetsOf f sig ≤ 8) (c : Nat) (args : List Nat) :
    formOf f (.callIndirect sig c args) ∈ stmtForms := by
  dsimp only [stmtForms]; iterate 7 apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.2 ⟨sigRetsOf f sig, by simp [retCounts]; omega, rfl⟩

theorem sf_funcAddr (fn : Nat) : formOf f (.funcAddr .i64 fn) ∈ stmtForms := by
  dsimp only [stmtForms]; iterate 6 apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_cons_self

theorem sf_bmask {ty : Clif.Ty} (h : ty ∈ eTys) (x : Nat) : formOf f (.bmask ty x) ∈ stmtForms := by
  dsimp only [stmtForms]; iterate 5 apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.2 ⟨ty, h, rfl⟩

theorem sf_atomicLoad {ty : Clif.Ty} (h : ty ∈ eTys) (fl : Clif.MemFlags) (p : Nat) :
    formOf f (.atomicLoad ty fl p) ∈ stmtForms := by
  dsimp only [stmtForms]; iterate 4 apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.2 ⟨ty, h, rfl⟩

theorem sf_atomicStore (ty : Clif.Ty) (fl : Clif.MemFlags) (x p : Nat) :
    formOf f (.atomicStore ty fl x p) ∈ stmtForms := by
  dsimp only [stmtForms]; iterate 3 apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_cons_self

theorem sf_atomicRmw (op : Clif.AtomicRmwOp) {ty : Clif.Ty} (h : ty ∈ eTys) (fl : Clif.MemFlags)
    (p x : Nat) : formOf f (.atomicRmw op ty fl p x) ∈ stmtForms := by
  dsimp only [stmtForms]; iterate 2 apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_flatMap.2 ⟨op, by cases op <;> simp, List.mem_map.2 ⟨ty, h, rfl⟩⟩

theorem sf_atomicCas {ty : Clif.Ty} (h : ty ∈ eTys) (fl : Clif.MemFlags) (p e x : Nat) :
    formOf f (.atomicCas ty fl p e x) ∈ stmtForms := by
  dsimp only [stmtForms]; apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.2 ⟨ty, h, rfl⟩

theorem sf_fence : formOf f .fence ∈ stmtForms := by
  dsimp only [stmtForms]
  apply List.mem_append_right
  exact List.mem_cons_self

theorem sf_tlsValue (gv : Nat) : formOf f (.tlsValue .i64 gv) ∈ stmtForms := by
  dsimp only [stmtForms]
  apply List.mem_append_right
  exact List.mem_cons_of_mem _ List.mem_cons_self

end

/-! ## Statement roots -/

theorem stmtOut_single {t : CTy} (ht : t ≠ .invalid) {T k : Nat} {fs : List PA}
    (hk1 : k ≠ VIdx.InstructionData.Call) (hk2 : k ≠ VIdx.InstructionData.CallIndirect) :
    stmtOut (.inst (.ty [t]) (.data T k fs)) = .regsVec (some 1) := by
  unfold stmtOut
  split <;> simp_all

theorem sigRets_of_ne {s : Clif.Signature} (h : s.returns ≠ []) : sigRets s = s.returns := by
  unfold sigRets
  split
  · simp [List.isEmpty_iff, h]
  · rfl

section
variable {f : Clif.Function} {ctx : Ctx}

theorem out_n {a : PA} {n : Nat} {info : IInfo} (ha : stmtOut a = .regsVec (some n))
    (hl : info.results ≠ [] → info.results.length = n) :
    info.results ≠ [] → ∀ rss, γ f ctx (stmtOut a) (.regsVec rss) →
      rss.length = info.results.length ∧ ∀ rs ∈ rss, rs.length = 1 := by
  intro hne rss h
  rw [ha] at h
  obtain ⟨h1, h2⟩ := γ_regsVec h
  refine ⟨?_, h1⟩
  rw [hl hne]
  rcases h2 with h2 | h2
  · cases h2
  · exact (Option.some.inj h2).symm

theorem out_none {a : PA} {info : IInfo} (hl : info.results = []) :
    info.results ≠ [] → ∀ rss, γ f ctx (stmtOut a) (.regsVec rss) →
      rss.length = info.results.length ∧ ∀ rs ∈ rss, rs.length = 1 :=
  fun hne => absurd hl hne

end

set_option hygiene false in
/-- Close the `γ` goal of an `InstructionData` value as far as the generic leaves go. -/
macro "prg_data" : tactic => `(tactic| (
  repeat' first
    | exact γL_nil'
    | apply γL_cons'
    | exact γ_int_any _
    | exact γ_memFlags (by assumption)
    | exact hV _ (by simp [Driver.instArgs])
    | (apply γ_vals; simp only [List.map_cons, List.map_nil])
    | exact γ_opcodeV (by rfl)
    | exact γ_mkVariant (by rfl) γL_nil'
    | refine γ_instDataV (by rfl) ?_))

set_option hygiene false in
/-- Split `instData`'s checks, closing the failing branches. -/
macro "prg_split" : tactic => `(tactic| (
  repeat' split at hd
  all_goals try (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at hd)
  all_goals try (simp only [pure, Except.pure, Except.ok.injEq] at hd)))

set_option hygiene false in
/-- The result type of an E instruction is an E type. -/
macro "prg_ety" : tactic => `(tactic|
  exact mem_eTys (by
    revert hE; cases ty <;>
      simp [Compile.instE, Compile.tyE, Compile.unaryTyE, Compile.unaryE, Compile.binaryE]))

set_option maxRecDepth 100000 in
/-- **A statement's root**: the form of its instruction describes `.inst ii`, is a statement
root of the table, and every output `stmtOut` describes has one single register per result. -/
theorem stmt_root {f : Clif.Function} {ctx : Ctx} (hP : PInv f ctx) {ii : Nat} {info : IInfo}
    {c : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some c) :
    γ f ctx (formOf f c) (.inst ii) ∧ formOf f c ∈ stmtForms ∧
      (info.results ≠ [] → ∀ rss, γ f ctx (stmtOut (formOf f c)) (.regsVec rss) →
        rss.length = info.results.length ∧ ∀ rs ∈ rss, rs.length = 1) := by
  have hctx := hP.ctxInv
  have hd := hctx.data ii info c hi hc
  have hE := hctx.instE ii info c hi hc
  obtain ⟨tys, hty, hrt, hlen⟩ := hctx.resTys ii info c hi hc
  have hof := hP.clifOf ii info c hi hc
  have hV : ∀ x ∈ Driver.instArgs c, γ f ctx aV (.value x) := fun x hx =>
    γ_aV hctx (hP.argsTyped c hof x hx)
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
    refine ⟨γ_inst hi (γ_tyCall hctx hi) (by
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
      refine ⟨γ_inst hi (γ_tyCall hctx hi) (by
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

/-! ## Terminator roots -/

theorem exnTableOpnd_inv {f : Clif.Function} {et : Clif.ExnTable} {sig : Clif.Signature}
    {items : List (Option Nat)} (h : exnTableOpnd f et = .ok (sig, items)) :
    f.sigDecls.lookup et.sig = some sig ∧ items.length = et.items.length := by
  unfold exnTableOpnd at h
  cases hs : f.sigDecls.lookup et.sig with
  | none => simp only [hs] at h; cases h
  | some s =>
    simp only [hs, bind, Except.bind] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i items' hit
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨rfl, (Prep.lmapM_ok hit).1⟩

theorem tryCallData_call {f : Clif.Function} {fn : Nat} {args : List Nat} {et : Clif.ExnTable}
    {data : V} {sig : Clif.Signature} {items : List (Option Nat)}
    (hd : tryCallData f (.tryCall fn args et) = .ok data) (hx : exnTableOpnd f et = .ok (sig, items)) :
    ∃ ext, f.extern? fn = some ext ∧ ext.sig = sig ∧ data = instDataV "TryCall"
      [opcodeV "TryCall", .values args, .op (.funcRef fn), .op (.exnTable sig items)] := by
  simp only [tryCallData, hx, bind, Except.bind] at hd
  cases he : f.extern? fn with
  | none => simp only [he] at hd; cases hd
  | some ext =>
    simp only [he] at hd
    split at hd
    · cases hd
    · rename_i hne
      simp only [pure, Except.pure, Except.ok.injEq] at hd
      exact ⟨ext, rfl, by simpa using hne, hd.symm⟩

theorem tryCallData_ind {f : Clif.Function} {callee : Nat} {args : List Nat} {et : Clif.ExnTable}
    {data : V} {sig : Clif.Signature} {items : List (Option Nat)}
    (hd : tryCallData f (.tryCallIndirect callee args et) = .ok data)
    (hx : exnTableOpnd f et = .ok (sig, items)) :
    data = instDataV "TryCallIndirect"
      [opcodeV "TryCallIndirect", .values (callee :: args), .op (.exnTable sig items)] := by
  simp only [tryCallData, hx, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
  exact hd.symm

/-- A `return` of `f` with as many values as the signature returns passes at most 8 values to
the lowering (`sretRet` adds the `sret` pointer only to a signature without returns). -/
theorem ret_len {f : Clif.Function} {vs : List Nat} (hv : vs.length = f.sig.returns.length)
    (h8 : f.sig.returns.length ≤ 8) : (vs ++ sretRet f).length ≤ 8 := by
  unfold sretRet
  split
  · rename_i hne
    have h0 : f.sig.returns = [] := by
      revert hne
      unfold sigRets
      split
      · split
        · rename_i h; intro _; exact List.isEmpty_iff.mp h
        · simp
      · simp
    rw [List.length_append, hv, h0]
    split
    · rename_i b0 i _ _
      cases b0.params[i]? <;> simp
    · simp
  · simpa [hv] using h8

section
variable {f : Clif.Function} {ctx : Ctx}

theorem γL_rep {xs : List Nat} (h : ∀ x ∈ xs, γ f ctx aV (.value x)) :
    γL f ctx (List.replicate xs.length aV) (xs.map .value) := by
  induction xs with
  | nil => exact γL_nil'
  | cons x xs ih =>
    exact γL_cons' (h x List.mem_cons_self) (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- The operands of a terminator of `f` have types in `buildCtx`'s context (dominance). -/
theorem termArgs_typed {ranges : Array (Nat × Nat)} {st0 : LState}
    (hb : buildCtx f = .ok (ctx, ranges, st0)) (hdom : dominatedB f = true) {B : Clif.Block}
    (hB : B ∈ f.blocks) {x : Nat} (hx : x ∈ termArgs (abiTerm f B.term)) :
    (ctx.valueType? x).isSome := by
  obtain ⟨bi, hbi, e⟩ := List.getElem_of_mem hB
  have hB' : f.blocks[bi]? = some B := by rw [List.getElem?_eq_getElem hbi, e]
  exact typed_of_def (ctxSpec_of hb)
    (availOf_defs (((dominated_of hdom).uses ctx ranges st0 hb bi B hB').2 x hx))

set_option maxRecDepth 100000 in
/-- **A terminator's root**: the driver's `lower`/`lower_branch` call on a non-`try_call`
terminator of `f` (at its placeholder slot, in its context `termCtx`, with one target per
successor) is a root of the table whose inputs describe its arguments. -/
theorem term_root {ranges : Array (Nat × Nat)} {st0 : LState} (hP : PInv f ctx)
    (hb : buildCtx f = .ok (ctx, ranges, st0)) (hdom : dominatedB f = true)
    (hin : iselInB f = true) (hdrv : driverInB f = true) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) {t : Clif.Terminator}
    (ht : ∃ B ∈ f.blocks, B.term = t) {data : V} (hd : termData (abiTerm f t) = .ok data)
    {targets : List Label} (hlen : targets.length = (destsOf t).length) :
    ∃ q ∈ termRoots, (∃ T : Term, program.termByName? (termCall t ti targets).1 = some T ∧
      T.id = q.1) ∧ γL f (termCtx ctx ti data) q.2 (termCall t ti targets).2 := by
  obtain ⟨B, hB, rfl⟩ := ht
  have hP' := pinv_termCtx hP hph data
  have hself := termCtx_insts_self hph data
  have hA : ∀ x ∈ termArgs (abiTerm f B.term), γ f (termCtx ctx ti data) aV (.value x) :=
    fun x hx => γ_aV hP'.ctxInv (termArgs_typed hb hdom hB hx)
  have hinst : ∀ k fs, γ f (termCtx ctx ti data) (idat k fs) data →
      γ f (termCtx ctx ti data) (termInst k fs) (.inst ti) :=
    fun k fs h => γ_inst hself (γ_ty_mem (by simp)) h (by simp)
  have hTI := termIsel_of hin hB
  generalize B.term = t at hA hTI hd hlen
  cases t with
  | ret vs =>
    simp only [abiTerm, termData, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    have hv : vs.length = f.sig.returns.length := by simpa [termIselB] using hTI
    have h8 : f.sig.returns.length ≤ 8 := by
      simp only [driverInB, Bool.and_eq_true, decide_eq_true_eq] at hdrv; exact hdrv.1.2
    have hm := ret_len hv h8
    refine ⟨(TId.lower, [termInst VIdx.InstructionData.MultiAry [opc VIdx.Opcode.Return,
      .vals (List.replicate (vs ++ sretRet f).length aV)]]), ?_, ⟨_, program_termByName_lower, rfl⟩,
      γL_cons' (hinst _ _ (γ_instDataV (by rfl) (γL_cons' (γ_opcodeV (by rfl))
        (γL_cons' (γ_vals (γL_rep fun x hx => hA x (by simpa [abiTerm, termArgs] using hx)))
          γL_nil')))) γL_nil'⟩
    dsimp only [termRoots]; iterate 3 apply List.mem_append_left
    exact List.mem_map.2 ⟨_, List.mem_range.2 (by omega), rfl⟩
  | trap c =>
    simp only [abiTerm, termData, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    refine ⟨(TId.lower, [termInst VIdx.InstructionData.Trap [opc VIdx.Opcode.Trap, .op .trapCode none]]),
      ?_, ⟨_, program_termByName_lower, rfl⟩,
      γL_cons' (hinst _ _ (γ_instDataV (by rfl) (γL_cons' (γ_opcodeV (by rfl))
        (γL_cons' (γ_op ⟨c, rfl⟩) γL_nil')))) γL_nil'⟩
    dsimp only [termRoots]; iterate 2 apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_cons_self
  | jump bc =>
    simp only [abiTerm, termData, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    have hl : targets.length = 1 := by simpa [destsOf] using hlen
    refine ⟨(TId.lower_branch, [termInst VIdx.InstructionData.Jump
      [opc VIdx.Opcode.Jump, .blockCalls 1], .labels 1 (some 1)]), ?_,
      ⟨_, program_termByName_lower_branch, rfl⟩,
      γL_cons' (hinst _ _ (γ_instDataV (by rfl) (γL_cons' (γ_opcodeV (by rfl))
        (γL_cons' (γ_blockCalls (bs := [0])) γL_nil'))))
        (γL_cons' (γ_labels (by omega) (.inr (by rw [hl]))) γL_nil')⟩
    dsimp only [termRoots]; iterate 2 apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_cons_of_mem _ List.mem_cons_self
  | brif c th el =>
    simp only [abiTerm, termData, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    have hl : targets.length = 2 := by simpa [destsOf] using hlen
    refine ⟨(TId.lower_branch, [termInst VIdx.InstructionData.Brif
      [opc VIdx.Opcode.Brif, aV, .blockCalls 2], .labels 2 (some 2)]), ?_,
      ⟨_, program_termByName_lower_branch, rfl⟩,
      γL_cons' (hinst _ _ (γ_instDataV (by rfl) (γL_cons' (γ_opcodeV (by rfl))
        (γL_cons' (hA c (by simp [abiTerm, termArgs]))
          (γL_cons' (γ_blockCalls (bs := [0, 1])) γL_nil')))))
        (γL_cons' (γ_labels (by omega) (.inr (by rw [hl]))) γL_nil')⟩
    dsimp only [termRoots]; iterate 2 apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  | brTable x dflt tbl =>
    simp only [abiTerm, termData, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    have hl : targets.length = tbl.length + 1 := by simpa [destsOf] using hlen
    refine ⟨(TId.lower_branch, [termInst VIdx.InstructionData.BranchTable
      [opc VIdx.Opcode.BrTable, aV, .op .jumpTable none], .labels 1 none]), ?_,
      ⟨_, program_termByName_lower_branch, rfl⟩,
      γL_cons' (hinst _ _ (γ_instDataV (by rfl) (γL_cons' (γ_opcodeV (by rfl))
        (γL_cons' (hA x (by simp [abiTerm, termArgs]))
          (γL_cons' (γ_op ⟨0, rfl⟩) γL_nil')))))
        (γL_cons' (γ_labels (by omega) (.inl rfl)) γL_nil')⟩
    dsimp only [termRoots]; iterate 2 apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  | returnCall fn args => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
  | tryCall fn args et => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
  | tryCallIndirect callee args et =>
    simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd

set_option maxRecDepth 100000 in
/-- **A `try_call`'s root**: the driver's `lower_branch` call on a `try_call`/`try_call_indirect`
of `f` (at its placeholder slot, in its context `tryCtx` with the return/payload vregs
`tryRegsOf` allocates, with one target per exception-table item plus the continuation) is a
root of the table whose inputs describe its arguments. -/
theorem try_root {ranges : Array (Nat × Nat)} {st0 : LState} (hP : PInv f ctx)
    (hb : buildCtx f = .ok (ctx, ranges, st0)) (hdom : dominatedB f = true)
    (hin : iselInB f = true) {ti : Nat} (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩)
    {t : Clif.Terminator} (ht : ∃ B ∈ f.blocks, B.term = t) {et : Clif.ExnTable}
    (het : exnOf t = some et) {data : V} (hd : tryCallData f t = .ok data) {sig : Clif.Signature}
    {items : List (Option Nat)} (hx : exnTableOpnd f et = .ok (sig, items))
    {trs : List Reg × List Reg} {st1 st2 : LState} (hr : tryRegsOf sig st1 = some (trs, st2))
    {targets : List Label} (hlen : targets.length = items.length + 1) :
    ∃ q ∈ termRoots, q.1 = TId.lower_branch ∧
      γL f (tryCtx ctx ti data trs) q.2 [.inst ti, .labels targets] := by
  obtain ⟨B, hB, rfl⟩ := ht
  have hP' := pinv_tryCtx hP hph data trs
  have hself : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hA : ∀ x ∈ termArgs (abiTerm f B.term), (ctx.valueType? x).isSome :=
    fun x hx => termArgs_typed hb hdom hB hx
  have hTI := termIsel_of hin hB
  obtain ⟨hsig, hil⟩ := exnTableOpnd_inv hx
  generalize B.term = t at hA hTI het hd
  have hT : et.items.length ≤ maxTryItems ∧ SigOk sig := by
    cases t <;> simp only [exnOf, Option.some.injEq, reduceCtorEq] at het <;> subst het <;>
      simp only [termIselB, hsig, Bool.and_eq_true, decide_eq_true_eq] at hTI <;>
      exact ⟨hTI.1, sigOk_of hTI.2⟩
  have hS := hT.2
  have hinst : ∀ k fs, γ f (tryCtx ctx ti data trs) (idat k fs) data →
      γ f (tryCtx ctx ti data trs) (termInst k fs) (.inst ti) :=
    fun k fs h => γ_inst hself (γ_ty_mem (by simp)) h (by simp)
  have hrl : trs.1.length = (sigRets sig).length := by
    obtain ⟨rets, pays, st', h1, h2, -⟩ :=
      tryRegsOf_ok (s := sig) (Nat.le_trans (returns_le_sigRets sig) hS.2) st1
    rw [hr] at h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, -⟩ := h1
    exact h2
  have hm : items.length ≤ maxTryItems := hil ▸ hT.1
  have hmem : items.length ∈ List.range (maxTryItems + 1) := List.mem_range.2 (by omega)
  have hlab : γ f (tryCtx ctx ti data trs) (.labels (items.length + 1) (some (items.length + 1)))
      (.labels targets) := γ_labels (by omega) (.inr (by rw [hlen]))
  have hexn : γ f (tryCtx ctx ti data trs) (.op .exnTry (some items.length))
      (.op (.exnTable sig items)) := γ_op ⟨sig, items, rfl, hS, hrl, .inr rfl⟩
  cases t with
  | tryCall fn args et' =>
    simp only [exnOf, Option.some.injEq] at het
    subst het
    obtain ⟨ext, he, hes, hdat⟩ := tryCallData_call hd hx
    have hfr : γ f (tryCtx ctx ti data trs) (.op .funcRefTry none) (.op (.funcRef fn)) :=
      γ_op ⟨fn, ext, rfl, by show ctx.func.extern? fn = some ext; rw [hP.ctxInv.func]; exact he,
        hes ▸ hS, by rw [hes]; exact hrl⟩
    refine ⟨(TId.lower_branch, [termInst VIdx.InstructionData.TryCall [opc VIdx.Opcode.TryCall,
      .valsMin 0, .op .funcRefTry none, .op .exnTry (some items.length)],
      .labels (items.length + 1) (some (items.length + 1))]), ?_, rfl,
      γL_cons' (hinst _ _ ?_) (γL_cons' hlab γL_nil')⟩
    · dsimp only [termRoots]; apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map.2 ⟨_, hmem, rfl⟩
    · subst hdat
      refine γ_instDataV (by rfl) (γL_cons' (γ_opcodeV (by rfl)) ?_)
      refine γL_cons' (γ_valsMin (Nat.zero_le _) fun x hx' => hA x (by simp [abiTerm, termArgs, hx'])) ?_
      exact γL_cons' hfr (γL_cons' hexn γL_nil')
  | tryCallIndirect callee args et' =>
    simp only [exnOf, Option.some.injEq] at het
    subst het
    have hdat := tryCallData_ind hd hx
    refine ⟨(TId.lower_branch, [termInst VIdx.InstructionData.TryCallIndirect
      [opc VIdx.Opcode.TryCallIndirect, .valsMin 1, .op .exnTry (some items.length)],
      .labels (items.length + 1) (some (items.length + 1))]), ?_, rfl,
      γL_cons' (hinst _ _ ?_) (γL_cons' hlab γL_nil')⟩
    · dsimp only [termRoots]
      apply List.mem_append_right
      exact List.mem_map.2 ⟨_, hmem, rfl⟩
    · subst hdat
      refine γ_instDataV (by rfl) (γL_cons' (γ_opcodeV (by rfl)) ?_)
      refine γL_cons' (γ_valsMin (by simp) fun x hx' => hA x ?_) (γL_cons' hexn γL_nil')
      simp only [List.mem_cons] at hx'
      rcases hx' with rfl | hx' <;> simp [abiTerm, termArgs, *]
  | _ => simp [exnOf] at het

end

end Backend.Proof.Prg
