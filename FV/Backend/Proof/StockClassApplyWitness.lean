import FV.Backend.Proof.StockClassWitness
namespace Backend.Stock.Proof.OperandClassWitnessDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Flow Backend.Proof.Cov Backend.Proof.PerEdgePrep
open Backend.Stock.Proof.OperandClassDraft
open Backend.Stock.Proof.EmissionCoverageFixture
open Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- The generic class analysis and helper contract have nonempty typed arguments,
an actual fresh allocation and a complete original-source/raw/checked/physical
pipeline, using the real allocated context rather than a supplied model. -/
theorem stock_complete_class_apply_witness :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc)
      (ranges : Array (Nat × Nat)) (next : State) (value : Backend.V),
      Stock.lower (function false) = .ok result ∧ LowerScope (function false) ∧
      Dominated (function false) ∧ ArityOk (function false) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      Stock.buildCtx (function false) = .ok (result.ctx,ranges,result.initial) ∧
      Clean result.ctx ∧ ClsIs result.ctx result.initial.base result.initial.base ∧
      Stock.externCtor result.ctx T.temp_writable_reg [.ty (.int 64)] result.initial = .ok (value,next) ∧
      CtorCls result.ctx T.temp_writable_reg.id [.ty (.int 64)] result.initial.base value next.base ∧
      aApplyC program clsTab false T.temp_writable_reg.ret TId.temp_writable_reg [FA.c0] = some FA.c0 ∧
      Holds2 (fun a s v => γC a s.base v) result.initial [FA.c0] [.ty (.int 64)] ∧
      (applyTerm program (Stock.sem result.ctx) {} 1 T.temp_writable_reg.ret TId.temp_writable_reg
        [.ty (.int 64)]).run (result.initial,#[]) = .ok (some value,next,#[]) ∧
      ClsIs result.ctx result.initial.base next.base ∧ GoodV next.base.classes value ∧
      next.base.nextVreg = result.initial.base.nextVreg + 1 := by
  rcases stock_complete_operand_classes_witness false with
    ⟨result,p,rf,af,out,rootAfter,rootTrace,ranges,i,lowered,scope,dominated,arity,prepared,
      fallback,checked,physical,build,mapped,clean,named,initial,rest⟩
  let next : State := {result.initial with base := (result.initial.base.fresh .int).2}
  let value : Backend.V := .reg (result.initial.base.fresh .int).1
  have ctor : Stock.externCtor result.ctx T.temp_writable_reg [.ty (.int 64)] result.initial = .ok (value,next) := by
    rw [stock_ctor_baseOnly _ _ _ _ (by decide)]
    rfl
  have summary : aApplyC program clsTab false T.temp_writable_reg.ret TId.temp_writable_reg [FA.c0] = some FA.c0 := by
    simp (config := {decide := true}) [aApplyC,data_program.t175,T.temp_writable_reg,apreC,Backend.Proof.Flow.actor,joinAll,FA.c0,FA.join]
  have held : Holds2 (fun a s v => γC a s.base v) result.initial [FA.c0] [.ty (.int 64)] :=
    ⟨(by intro _ r hr; simp [V.regsIn] at hr),trivial⟩
  have run : (applyTerm program (Stock.sem result.ctx) {} 1 T.temp_writable_reg.ret TId.temp_writable_reg
      [.ty (.int 64)]).run (result.initial,#[]) = .ok (some value,next,#[]) := by
    simp only [applyTerm.eq_2,data_program.t175,T.temp_writable_reg,isel_monad,Stock.sem]
    simp only [T.temp_writable_reg] at ctor
    rw [ctor]
    rfl
  have classified := stock_apply_classes (ctx := result.ctx) clean rfl summary held initial run
  exact ⟨result,p,rf,af,ranges,next,value,lowered,scope,dominated,arity,prepared,fallback,checked,physical,
    build,clean,initial,ctor,stock_ctor_classes ctor,summary,held,run,classified.1,classified.2 _ rfl (by decide),rfl⟩

end Backend.Stock.Proof.OperandClassWitnessDraft
