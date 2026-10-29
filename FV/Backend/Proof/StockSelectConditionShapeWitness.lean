module

public import FV.Backend.Proof.StockSelectConditionCompanion
public import FV.Backend.Proof.StockSelectZeroConditionShape
public import FV.Backend.Proof.StockSelectScalarDriverRuns

@[expose] public section

namespace Backend.Stock.Proof.ScalarSelect.ConditionShapeWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem int_of_width (ty : Clif.Ty) : ∃ t : Clif.Ty, t.isInt = true ∧ t.width = ty.width := by
  cases ty
  all_goals first
    | exact ⟨.i8,rfl,rfl⟩
    | exact ⟨.i16,rfl,rfl⟩
    | exact ⟨.i32,rfl,rfl⟩
    | exact ⟨.i64,rfl,rfl⟩
    | exact ⟨.i128,rfl,rfl⟩
private theorem safe (ty : Clif.Ty) (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    (int : ty.isInt = true) : LowerScope (scalarSelectFunction ty .i64) :=
  lowerScope_of (by cases ty <;> first | rfl | (simp at int; done) | simp [Clif.Ty.width] at width)
private theorem build (ty : Clif.Ty) (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    (int : ty.isInt = true) : Stock.buildCtx (scalarSelectFunction ty .i64) = .ok (scalarSelectBuilt ty .i64) := by
  cases ty <;> first | rfl | (simp at int; done) | simp [Clif.Ty.width] at width
private def Observed (ty : Clif.Ty) : Prop :=
  (((applyTerm program (Stock.sem (scalarSelectBuilt ty .i64).1) {} 1001 123 651 [.value 7]).run
    ((scalarSelectBuilt ty .i64).2.2,#[])).toOption.bind (fun result => result.1)).isSome = true
section Kernel
attribute [local semireducible] Isle.Aarch64.program
private theorem observed (ty : Clif.Ty)
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64) (int : ty.isInt = true) : Observed ty := by
  cases ty
  all_goals first | (unfold Observed; decide +kernel) | (simp at int; done) | simp [Clif.Ty.width] at width
end Kernel
private theorem nonzero_condition_shape (ty : Clif.Ty)
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64) (int : ty.isInt = true) :
    ∃ f ctx st middle condition trace,LowerScope f ∧ MappedCtxInv f ctx ∧
      ctx.valueType? 7 = some (.int ty.width) ∧
      ApplyInternal program (Stock.sem ctx) {} 1000 123 651 [.value 7] (st,#[]) condition (middle,trace) ∧
      CondShape condition (fun _ => True) ∧
      ∃ producer cc booleanTrace,CondFlag cmpImm0 condition producer cc ∧ vdefs producer = [] ∧
        cc ≠ .al ∧ cc ≠ .nv ∧
        ApplyInternal program (Stock.sem ctx) {} 119 27 715 [condition] (middle,trace)
          (.reg (middle.base.fresh .int).1)
          ({middle with base := (((middle.base.fresh .int).2.emit producer).emit
            (.cset (middle.base.fresh .int).1 cc))},booleanTrace) := by
  let ctx := (scalarSelectBuilt ty .i64).1
  let st := (scalarSelectBuilt ty .i64).2.2
  have inv : MappedCtxInv (scalarSelectFunction ty .i64) ctx := buildCtx_mappedInv (safe ty width int) (build ty width int)
  have typed : ctx.valueType? 7 = some (.int ty.width) := by
    cases ty <;> first | rfl | (simp at int; done) | simp [Clif.Ty.width] at width
  have success := observed ty width int
  obtain ⟨condition,middle,trace,run⟩ : ∃ condition middle trace,
      ApplyInternal program (Stock.sem ctx) {} 1000 123 651 [.value 7] (st,#[]) condition (middle,trace) := by
    unfold Observed at success
    cases actual : (applyTerm program (Stock.sem ctx) {} 1001 123 651 [.value 7]).run (st,#[]) with
    | error e => simp [ctx,st] at actual; rw [actual] at success; cases success
    | ok result =>
      obtain ⟨output,middle,trace⟩ := result
      cases output with
      | none => simp [ctx,st] at actual; rw [actual] at success; cases success
      | some value => exact ⟨value,middle,trace,actual⟩
  have shape := stock_select_nonzero_actual_condition_shape inv width (by decide) typed run
  exact ⟨_,ctx,st,middle,condition,trace,safe ty width int,inv,typed,run,shape,
    stock_select_condition_boolean_companion ctx shape middle trace⟩
/-- Each original scalar condition width inhabits the decoded nonzero and
proof-only boolean-companion contracts in an actual built source context. -/
theorem stock_select_nonzero_condition_shape_witness (ty : Clif.Ty)
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64) :
    ∃ f ctx st middle condition trace,LowerScope f ∧ MappedCtxInv f ctx ∧
      ctx.valueType? 7 = some (.int ty.width) ∧
      ApplyInternal program (Stock.sem ctx) {} 1000 123 651 [.value 7] (st,#[]) condition (middle,trace) ∧
      CondShape condition (fun _ => True) ∧
      ∃ producer cc booleanTrace,CondFlag cmpImm0 condition producer cc ∧ vdefs producer = [] ∧
        cc ≠ .al ∧ cc ≠ .nv ∧
        ApplyInternal program (Stock.sem ctx) {} 119 27 715 [condition] (middle,trace)
          (.reg (middle.base.fresh .int).1)
          ({middle with base := (((middle.base.fresh .int).2.emit producer).emit
            (.cset (middle.base.fresh .int).1 cc))},booleanTrace) := by
  obtain ⟨t,int,same⟩ := int_of_width ty
  rw [← same] at width ⊢
  exact nonzero_condition_shape t width int
/-- Both register-zero forms and both machine widths inhabit actual inversion
and the subsequently constructed boolean companion, with a nonempty trace. -/
theorem stock_select_zero_invert_companion_witness (nonzero : Bool) (sz : OperandSize) :
    ∃ raw out trace,CondShape raw (fun _ => True) ∧
      ApplyInternal program (Stock.sem sinkCtx) {} 119 123 649 [raw]
        (sinkState,#[17]) out (sinkState,trace) ∧ CondShape out (fun _ => True) ∧
      ∃ producer cc booleanTrace,CondFlag cmpImm0 out producer cc ∧ vdefs producer = [] ∧
        cc ≠ .al ∧ cc ≠ .nv ∧
        ApplyInternal program (Stock.sem sinkCtx) {} 119 27 715 [out] (sinkState,trace)
          (.reg (sinkState.base.fresh .int).1)
          ({sinkState with base := (((sinkState.base.fresh .int).2.emit producer).emit
            (.cset (sinkState.base.fresh .int).1 cc))},booleanTrace) := by
  let raw := V.data 123 (if nonzero then 1 else 0)
    [.reg (.vreg 7 .int),.data 93 (if sz = .size32 then 0 else 1) []]
  have shape : CondShape raw (fun _ => True) := by
    cases nonzero <;> cases sz
    all_goals first | exact Or.inl ⟨7,_,_,rfl,rfl,trivial⟩ | exact Or.inr (Or.inl ⟨7,_,_,rfl,rfl,trivial⟩)
  have run := ScalarCmp.stock_cmp_zero_invert data_program sinkCtx (cfg := {}) rfl nonzero (.vreg 7 .int)
    (.data 93 (if sz = .size32 then 0 else 1) []) sinkState #[17] 80
  have inverted := stock_select_condition_invert_shape (by decide : 39 ≤ 119) shape run
  exact ⟨raw,_,_,shape,run,inverted.1,stock_select_condition_boolean_companion sinkCtx inverted.1 _ _⟩
/-- Every source integer comparison condition inhabits real flag inversion
and its subsequent boolean companion; the producer is decoded and has no definitions. -/
theorem stock_select_flags_invert_companion_witness (cc : Clif.IntCC) :
    ∃ raw out trace,CondShape raw (fun _ => True) ∧
      ApplyInternal program (Stock.sem sinkCtx) {} 119 123 649 [raw]
        (sinkState,#[17]) out (sinkState,trace) ∧ CondShape out (fun _ => True) ∧
      ∃ producer condition booleanTrace,CondFlag cmpImm0 out producer condition ∧ vdefs producer = [] ∧
        condition ≠ .al ∧ condition ≠ .nv ∧
        ApplyInternal program (Stock.sem sinkCtx) {} 119 27 715 [out] (sinkState,trace)
          (.reg (sinkState.base.fresh .int).1)
          ({sinkState with base := (((sinkState.base.fresh .int).2.emit producer).emit
            (.cset (sinkState.base.fresh .int).1 condition))},booleanTrace) := by
  let mi := V.data 58 2 [.data 59 10 [],.data 93 1 [],.reg .xzr,.reg (.vreg 7 .int),.reg (.vreg 9 .int)]
  let raw := V.data 123 2 [.data 47 1 [mi],.data 96 (condOf cc).idx []]
  have shape : CondShape raw (fun _ => True) := Or.inr (Or.inr ⟨mi,
    .aluRRR .subS .size64 .xzr (.vreg 7 .int) (.vreg 9 .int),condOf cc,rfl,rfl,
    (condOf_ne_al cc).1,(condOf_ne_al cc).2,rfl,fun _ _ => trivial⟩)
  have run := ScalarCmp.stock_cmp_flag_invert data_program sinkCtx (cfg := {}) rfl
    (.data 47 1 [mi]) (condOf cc) sinkState #[17] 80
  have inverted := stock_select_condition_invert_shape (by decide : 39 ≤ 119) shape run
  exact ⟨raw,_,_,shape,run,inverted.1,stock_select_condition_boolean_companion sinkCtx inverted.1 _ _⟩
private def ZeroRhsObserved (ty : Clif.Ty) (left nonzero : Bool) : Prop :=
  (((evalExpr program (Stock.sem (scalarSelectBuilt ty .i64).1) {} 1000
    (ScalarCmp.cmpZeroRule left nonzero).rhs #[some (.value 7)]).run
      ((scalarSelectBuilt ty .i64).2.2,#[])).toOption.bind (fun result => result.1)).isSome = true
section Kernel
attribute [local semireducible] Isle.Aarch64.program
private theorem zero_rhs_observed (ty : Clif.Ty) (left nonzero : Bool)
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64) (int : ty.isInt = true) :
    ZeroRhsObserved ty left nonzero := by
  cases ty <;> cases left <;> cases nonzero
  all_goals first | (unfold ZeroRhsObserved; decide +kernel) | (simp at int; done) | simp [Clif.Ty.width] at width
end Kernel
private theorem zero_rhs_shape (ty : Clif.Ty) (left nonzero : Bool)
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64) (int : ty.isInt = true) :
    ∃ f ctx st out next trace,LowerScope f ∧ MappedCtxInv f ctx ∧
      ctx.valueType? 7 = some (.int ty.width) ∧
      (evalExpr program (Stock.sem ctx) {} 1000 (ScalarCmp.cmpZeroRule left nonzero).rhs
        #[some (.value 7)]).run (st,#[]) = .ok (some out,next,trace) ∧
      CondShape out (fun _ => True) := by
  let ctx := (scalarSelectBuilt ty .i64).1
  let st := (scalarSelectBuilt ty .i64).2.2
  have inv : MappedCtxInv (scalarSelectFunction ty .i64) ctx := buildCtx_mappedInv (safe ty width int) (build ty width int)
  have typed : ctx.valueType? 7 = some (.int ty.width) := by
    cases ty <;> first | rfl | (simp at int; done) | simp [Clif.Ty.width] at width
  have success := zero_rhs_observed ty left nonzero width int
  obtain ⟨out,next,trace,run⟩ : ∃ out next trace,
      (evalExpr program (Stock.sem ctx) {} 1000 (ScalarCmp.cmpZeroRule left nonzero).rhs
        #[some (.value 7)]).run (st,#[]) = .ok (some out,next,trace) := by
    unfold ZeroRhsObserved at success
    cases actual : (evalExpr program (Stock.sem ctx) {} 1000 (ScalarCmp.cmpZeroRule left nonzero).rhs
        #[some (.value 7)]).run (st,#[]) with
    | error e => simp [ctx,st] at actual; rw [actual] at success; cases success
    | ok result =>
      obtain ⟨output,next,trace⟩ := result
      cases output with
      | none => simp [ctx,st] at actual; rw [actual] at success; cases success
      | some out => exact ⟨out,next,trace,rfl⟩
  have shape := stock_select_zero_rhs_condition_shape (x := 7) (y := 7) (n := 760)
    inv width left nonzero typed typed (by simpa only [ite_self] using run)
  exact ⟨_,ctx,st,out,next,trace,safe ty width int,inv,typed,run,shape⟩
/-- All four scalar widths and both mirrored zero equality/inequality RHSs
inhabit the decoded-condition contract in an accepted original built context. -/
theorem stock_select_zero_rhs_shape_witness (ty : Clif.Ty) (left nonzero : Bool)
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64) :
    ∃ f ctx st out next trace,LowerScope f ∧ MappedCtxInv f ctx ∧
      ctx.valueType? 7 = some (.int ty.width) ∧
      (evalExpr program (Stock.sem ctx) {} 1000 (ScalarCmp.cmpZeroRule left nonzero).rhs
        #[some (.value 7)]).run (st,#[]) = .ok (some out,next,trace) ∧
      CondShape out (fun _ => True) := by
  obtain ⟨t,int,same⟩ := int_of_width ty
  rw [← same] at width ⊢
  exact zero_rhs_shape t left nonzero width int
end Backend.Stock.Proof.ScalarSelect.ConditionShapeWitness
