import FV.Backend.Proof.StockPolicy
import FV.Isle.InterpProjection

/-!
The stock scheduler changes constructors that track demand, sinking and aliases,
but keeps the existing value operations and DFG extractors. Pattern matching
therefore transports without any restriction on the scheduling state. Full
evaluation transport additionally needs constructor agreement; the sinking and
ABI changes require their own semantic proofs rather than that agreement.
-/

namespace Backend.Stock.Proof

open Isle Isle.Interp Isle.Aarch64

/-- Constructors with scheduler bookkeeping or deliberately revised stock ABI
behavior. All other external helpers retain the old state projection. -/
def revisedCtors : List Nat := [TId.put_in_reg, TId.put_in_regs, TId.mark_value_used,
  TId.put_extended_in_reg, TId.put_in_regs_vec, TId.is_sinkable_inst, TId.sink_inst, TId.opportunistic_def,
  TId.gen_return, TId.gen_call_output, TId.gen_try_call_rets]

theorem stock_ctor_unchanged (ctx : Ctx) (t : Term) (args : List V) (st : State)
    (h : t.id ∉ revisedCtors) :
    projectCtor State.base (Stock.externCtor ctx t args st) =
      Backend.externCtor ctx t args st.base := by
  unfold Stock.externCtor
  split
  all_goals first
    | (exfalso; apply h; simp [revisedCtors, *]; done)
    | (dsimp only; split <;> simp only [projectCtor, *])

/-- An unrevised helper changes only the legacy machine-code state. The full
scheduling state, including aliases, is retained on successful execution. -/
theorem stock_ctor_baseOnly (ctx : Ctx) (t : Term) (args : List V) (st : State)
    (h : t.id ∉ revisedCtors) :
    Stock.externCtor ctx t args st =
      match Backend.externCtor ctx t args st.base with
      | .ok (v, base) => .ok (v, { st with base })
      | .fail => .fail
      | .unmodeled e => .unmodeled e := by
  unfold Stock.externCtor
  split
  all_goals first
    | (exfalso; apply h; simp [revisedCtors, *]; done)
    | rfl

theorem stock_matchPat (p : Program) (ctx : Ctx) (st : State) (pat : Pattern)
    (v : V) (env : Env V) :
    matchPat p (Stock.sem ctx) st pat v env =
      matchPat p (Backend.sem ctx) st.base pat v env :=
  matchPat_restate p (Backend.sem ctx) State.base (Stock.externCtor ctx)
    (fun t v st => Backend.externExtract ctx t v st.base) (fun _ _ _ => rfl) st pat v env

theorem stock_matchAll (p : Program) (ctx : Ctx) (st : State) (ps : List Pattern)
    (v : V) (env : Env V) :
    matchAll p (Stock.sem ctx) st ps v env =
      matchAll p (Backend.sem ctx) st.base ps v env :=
  matchAll_restate p (Backend.sem ctx) State.base (Stock.externCtor ctx)
    (fun t v st => Backend.externExtract ctx t v st.base) (fun _ _ _ => rfl) st ps v env

theorem stock_matchArgs (p : Program) (ctx : Ctx) (st : State) (ps : List Pattern)
    (vs : List V) (env : Env V) :
    matchArgs p (Stock.sem ctx) st ps vs env =
      matchArgs p (Backend.sem ctx) st.base ps vs env :=
  matchArgs_restate p (Backend.sem ctx) State.base (Stock.externCtor ctx)
    (fun t v st => Backend.externExtract ctx t v st.base) (fun _ _ _ => rfl) st ps vs env

/-! A one-term slice uses the real `def_inst` extractor and load context. Only
that exported term is reduced, never the generated AArch64 program. -/

def projectionProgram : Program := { (default : Program) with terms := #[T.def_inst] }

def projectionPat : Pattern := .term 0 0 [.bind 0 0 (.wildcard 0)]

theorem stock_ctor_unchanged_witness :
    T.temp_writable_reg.id ∉ revisedCtors ∧
    projectCtor State.base
      (Stock.externCtor sinkCtx T.temp_writable_reg [.ty (.int 64)] sinkState) =
      Backend.externCtor sinkCtx T.temp_writable_reg [.ty (.int 64)] sinkState.base ∧
    Stock.externCtor sinkCtx T.temp_writable_reg [.ty (.int 64)] sinkState =
      .ok (.reg (.vreg 194 .int),
        { sinkState with base := (sinkState.base.fresh .int).2 }) :=
  ⟨(by decide), stock_ctor_unchanged _ _ _ _ (by decide), rfl⟩

theorem stock_ctor_baseOnly_witness :
    Stock.externCtor sinkCtx T.temp_writable_reg [.ty (.int 64)] sinkState =
      .ok (.reg (.vreg 194 .int),
        { sinkState with base := (sinkState.base.fresh .int).2 }) := by
  rw [stock_ctor_baseOnly _ _ _ _ (by decide)]
  rfl

theorem stock_matchPat_witness :
    matchPat projectionProgram (Stock.sem sinkCtx) sinkState projectionPat (.value 0) #[none] =
      matchPat projectionProgram (Backend.sem sinkCtx) sinkState.base
        projectionPat (.value 0) #[none] ∧
    matchPat projectionProgram (Stock.sem sinkCtx) sinkState projectionPat (.value 0) #[none] =
      .ok (some #[some (.inst 0)]) :=
  ⟨stock_matchPat _ _ _ _ _ _, rfl⟩

theorem stock_matchAll_witness :
    matchAll projectionProgram (Stock.sem sinkCtx) sinkState [projectionPat] (.value 0) #[none] =
      matchAll projectionProgram (Backend.sem sinkCtx) sinkState.base
        [projectionPat] (.value 0) #[none] ∧
    matchAll projectionProgram (Stock.sem sinkCtx) sinkState [projectionPat] (.value 0) #[none] =
      .ok (some #[some (.inst 0)]) :=
  ⟨stock_matchAll _ _ _ _ _ _, rfl⟩

theorem stock_matchArgs_witness :
    matchArgs projectionProgram (Stock.sem sinkCtx) sinkState [projectionPat] [.value 0] #[none] =
      matchArgs projectionProgram (Backend.sem sinkCtx) sinkState.base
        [projectionPat] [.value 0] #[none] ∧
    matchArgs projectionProgram (Stock.sem sinkCtx) sinkState [projectionPat] [.value 0] #[none] =
      .ok (some #[some (.inst 0)]) :=
  ⟨stock_matchArgs _ _ _ _ _ _, rfl⟩

end Backend.Stock.Proof
