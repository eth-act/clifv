import FV.Backend.Proof.StockBindingClassWitness

namespace Backend.Stock.Proof.BindingClassWitnessDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Flow Backend.Proof.Cov Backend.Proof.PerEdgePrep
open Backend.Stock.Proof.BindingClassDraft
open Backend.Stock.Proof.EmissionCoverageFixture
open Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem ordered_context {ctx : Ctx} {seed : State} {x key : Nat}
    (mapped : ∀ x r,ctx.valueReg? x = some r → ∃ n,r = .vreg n .int)
    (size : Sz seed.base) (sourceValues : ∀ x r,ctx.valueReg? x = some r → RegCls seed.base.classes r)
    (lookup : ctx.valueReg? x = some (.vreg key .int)) :
    ∃ (before after : State) (copies : Array MInst) (n : Nat),AliasClasses before ∧
      bindResults ctx [(x,[.vreg n .int]),(x,[.x 1]),(x,[.vreg (n+1) .int])] before = .ok (after,copies) ∧
      copies = #[.mov .size64 (.vreg key .int) (.x 1)] ∧ (after.alias[key]?).join = some (n+1) ∧
      AliasClasses after ∧ RegsFrom (RegCls after.base.classes) (.mov .size64 (.vreg key .int) (.x 1)) ∧
      InstCls after.base.classes ((MInst.mov .size64 (.vreg key .int) (.x 1)).mapRegs
        (Backend.lowerFunction.resolve after.alias (after.alias.size+1))) := by
  let n := seed.base.nextVreg
  let before : State := {seed with base := ((seed.base.fresh .int).2.fresh .int).2,alias := #[]}
  let aliases := aliasStep (aliasStep #[] (key,n)) (key,n+1)
  let after : State := {before with alias := aliases}
  let copies : Array MInst := #[.mov .size64 (.vreg key .int) (.x 1)]
  have run : bindResults ctx [(x,[.vreg n .int]),(x,[.x 1]),(x,[.vreg (n+1) .int])] before =
      .ok (after,copies) := by
    simp only [bindResults,List.foldlM_cons,List.foldlM_nil,lookup,setAlias_virtual,
      bind,Except.bind,pure,Except.pure]
    rfl
  have growth : ClsStep seed.base before.base :=
    clsStep_trans (clsStep_fresh _ .int) (clsStep_fresh _ .int)
  have values : ∀ x r,ctx.valueReg? x = some r → RegCls before.base.classes r :=
    fun x r found => regCls_step growth (sourceValues x r found)
  have first : RegCls before.base.classes (.vreg n .int) :=
    regCls_step (clsStep_fresh _ .int) (fresh_cls size .int)
  have second : RegCls before.base.classes (.vreg (n+1) .int) :=
    fresh_cls (sz_step (clsStep_fresh _ .int) size) .int
  have physicalClass : RegCls before.base.classes (.x 1) := regCls_real (by intro k c eq; cases eq)
  have outputs : ∀ pair ∈ ([(x,[.vreg n .int]),(x,[.x 1]),(x,[.vreg (n+1) .int])] : List (Nat × List Reg)),
      ∀ r ∈ pair.2,RegCls before.base.classes r := by
    intro pair member r inside
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · cases List.mem_singleton.mp inside; exact first
    · cases List.mem_singleton.mp inside; exact physicalClass
    · cases List.mem_singleton.mp inside; exact second
  have old : AliasClasses before := by
    intro key target entry
    change ((#[] : Array (Option Nat))[key]?).join = some target at entry
    simp at entry
  obtain ⟨base,consistent⟩ := stock_bindResults_alias_classes mapped values outputs old run
  have entry : (after.alias[key]?).join = some (n+1) := by
    have finalEntry := aliasStep_get (aliasStep (#[] : Array (Option Nat)) (key,n)) (key,n+1) key
    simp only [ite_true] at finalEntry
    exact finalEntry
  have raw : RegsFrom (RegCls after.base.classes) (.mov .size64 (.vreg key .int) (.x 1)) := by
    intro g held
    have dest := held (.vreg key .int) (by rw [base]; exact values x _ lookup)
    have src := held (.x 1) (by rw [base]; exact physicalClass)
    simp only [MInst.mapRegs,dest,src]
  exact ⟨before,after,copies,n,old,run,rfl,entry,consistent,raw,
    (stock_resolve_alias_classes consistent (after.alias.size+1)).2 _ raw⟩

/-- The ordered binding/resolver contracts have a real allocated source context
and complete original pipeline. This auxiliary binder run overwrites the same
key twice around a retained physical copy; no distinct-key assumption is hidden. -/
theorem stock_complete_ordered_alias_classes_witness :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc) (ranges : Array (Nat × Nat))
      (before after : State) (copies : Array MInst) (n : Nat),
      Stock.lower (function false) = .ok result ∧ LowerScope (function false) ∧
      Dominated (function false) ∧ ArityOk (function false) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      Stock.buildCtx (function false) = .ok (result.ctx,ranges,result.initial) ∧
      result.ctx.valueReg? 7 = some (.vreg 192 .int) ∧ AliasClasses before ∧
      bindResults result.ctx [(7,[.vreg n .int]),(7,[.x 1]),(7,[.vreg (n+1) .int])] before = .ok (after,copies) ∧
      copies = #[.mov .size64 (.vreg 192 .int) (.x 1)] ∧
      (after.alias[192]?).join = some (n+1) ∧ AliasClasses after ∧
      RegsFrom (RegCls after.base.classes) (.mov .size64 (.vreg 192 .int) (.x 1)) ∧
      InstCls after.base.classes ((MInst.mov .size64 (.vreg 192 .int) (.x 1)).mapRegs
        (Backend.lowerFunction.resolve after.alias (after.alias.size+1))) := by
  rcases stock_complete_binding_classes_witness with
    ⟨result,p,rf,af,ranges,emission,info,i,lowered,scope,dominated,arity,prepared,fallback,checked,physical,
      build,mapped,clean,source,clif,results,initial,empty,emitted,nonempty,classes,more⟩
  let known : Ctx × Array (Nat × Nat) × State :=
    (Stock.buildCtx (function false)).toOption.getD (sinkCtx,#[],sinkState)
  have knownBuild : Stock.buildCtx (function false) = .ok known := rfl
  have context : result.ctx = known.1 := congrArg Prod.fst (Except.ok.inj (build.symm.trans knownBuild))
  have lookup : result.ctx.valueReg? 7 = some (.vreg 192 .int) := by rw [context]; rfl
  obtain ⟨before,after,copies,n,old,run,copy,entry,consistent,raw,renamed⟩ :=
    ordered_context mapped.valueReg initial.sz initial.vals lookup
  exact ⟨result,p,rf,af,ranges,before,after,copies,n,lowered,scope,dominated,arity,prepared,fallback,checked,physical,
    build,lookup,old,run,copy,entry,consistent,raw,renamed⟩

end Backend.Stock.Proof.BindingClassWitnessDraft
