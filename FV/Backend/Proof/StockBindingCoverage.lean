import FV.Backend.Proof.StockResultRegisterCoverage
import FV.Backend.Proof.StockResults

namespace Backend.Stock.Proof.Coverage.Result
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Backend.Proof.Spill Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem fold_fields_mem_eq {α β γ : Type} (field : α → γ)
    (step : α → β → Except String α) (xs : List β)
    (keeps : ∀ a x next,x ∈ xs → step a x = .ok next → field next = field a)
    {before after : α} (run : xs.foldlM step before = .ok after) : field after = field before := by
  induction xs generalizing before with
  | nil => cases run; rfl
  | cons x xs ih =>
    rw [List.foldlM_cons] at run
    obtain ⟨middle,first,rest⟩ := Except.bind_ok run
    exact (ih (fun a y next member => keeps a y next (List.mem_cons_of_mem _ member)) rest).trans
      (keeps before x middle (List.mem_cons_self ..) first)

/-- Successful binding of actual integer virtual results changes aliases only:
it preserves the emitted base and adds no physical-result copy instructions.
Neither distinct result keys nor a single-result-vector premise is required. -/
theorem stock_bindResults_virtual_only {ctx : Ctx} {pairs : List (Nat × List Reg)}
    (mapped : ∀ x r,ctx.valueReg? x = some r → ∃ n,r = .vreg n .int)
    (virtual : ∀ pair ∈ pairs,∀ r ∈ pair.2,∃ n,r = .vreg n .int)
    {before after : State} {copies : Array MInst}
    (run : bindResults ctx pairs before = .ok (after,copies)) :
    after.base = before.base ∧ copies = #[] := by
  have fields : (after.base,copies) = (before.base,#[]) := by
    unfold bindResults at run
    apply fold_fields_mem_eq (fun acc : State × Array MInst => (acc.1.base,acc.2)) _ pairs ?_ run
    intro acc pair next member step
    rcases acc with ⟨st,code⟩
    rcases pair with ⟨x,rs⟩
    dsimp only at step
    cases found : ctx.valueReg? x with
    | none => simp only [found] at step; cases step
    | some r =>
      obtain ⟨key,rfl⟩ := mapped x r found
      simp only [found] at step
      cases rs with
      | nil => cases step
      | cons r rs =>
        cases rs with
        | nil =>
          obtain ⟨target,rfl⟩ := virtual (x,[r]) member r (List.mem_singleton_self _)
          simp only [setAlias_virtual,bind,Except.bind,pure,Except.pure] at step
          cases step
          rfl
        | cons r' rs => cases r <;> cases step
  exact Prod.mk.inj fields

private theorem zip_right {α β : Type} {xs : List α} {ys : List β} {x : α} {y : β}
    (member : (x,y) ∈ xs.zip ys) : y ∈ ys := by
  obtain ⟨j,atPair⟩ := List.mem_iff_getElem?.mp member
  exact List.mem_of_getElem? (List.getElem?_zip_eq_some.mp atPair).2

/-- Actual complete statement emission, including real ordered binding, adds
only covered forms. Original scope/context facts derive result classes and
empty binding copies; no copy/coverage certificate is passed by the caller. -/
theorem stock_emitInstruction_form_coverage {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (source : ctx.insts[ii]? = some info) (original : info.clif = some inst)
    {before : State} {emission : Emission} (empty : before.base.emitted = #[])
    (run : emitInstruction ctx ii before = .ok emission) :
    ∀ i ∈ emission.code.toList,Covered i = true ∧ (i.isCtl = false → SpillInstOk i) := by
  unfold emitInstruction at run
  cases lowered : Stock.runTerm ctx "lower" [.inst ii] before with
  | error e => simp only [lowered,bind,Except.bind] at run; cases run
  | ok answer =>
    rcases answer with ⟨out,next,trace⟩
    simp only [lowered,bind,Except.bind] at run
    cases out with
    | none => cases run
    | some out =>
      cases out <;> try (cases run)
      rename_i rss
      dsimp only at run
      split at run
      · cases run
      · cases binding : bindResults ctx (ctx.insts[ii]!.results.zip rss) next with
        | error e => simp only [binding,bind,Except.bind] at run; cases run
        | ok answer =>
          rcases answer with ⟨bound,copies⟩
          simp only [binding,pure,Except.pure] at run
          cases run
          have atInfo : ctx.insts[ii]! = info := by rw [getElem!_def,source]
          rw [atInfo] at binding
          have virtual : ∀ pair ∈ info.results.zip rss,∀ r ∈ pair.2,∃ n,r = .vreg n .int := by
            intro pair member r inside
            by_cases none : info.results = []
            · simp [none] at member
            · exact stock_statement_result_registers mapped clean source original lowered none r (mem_regsVec (zip_right member) inside)
          obtain ⟨sameBase,noCopies⟩ := stock_bindResults_virtual_only mapped.valueReg virtual binding
          obtain ⟨code,since,covered⟩ := Emission.stock_statement_emission_coverage mapped clean source original lowered
          intro i member
          dsimp only at member
          rw [sameBase,noCopies,Array.append_empty,since,empty,Array.empty_append] at member
          have inCode : i ∈ code := by simpa only [List.toList_toArray] using member
          have form := covered i inCode
          refine ⟨form,fun ordinary => spillInstOk_of_formOk (ctx := default) ?_⟩
          simpa only [Covered,ordinary,Bool.false_or] using form

/-- Every successful source-statement scan emits covered forms, including
sunk/omitted/skipped/committed empty-code cases and actual root/binding emission.
The scan itself supplies its empty local emission buffer. -/
theorem stock_scanInstruction_form_coverage {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {block ii ti : Nat} {branch : Bool} {info : IInfo} {inst : Clif.Inst}
    (source : ctx.insts[ii]? = some info) (original : info.clif = some inst)
    {before : State} {scan : Scan} (run : scanInstruction ctx block ii ti branch before = .ok scan) :
    ∀ i ∈ scan.emitted.toList,Covered i = true ∧ (i.isCtl = false → SpillInstOk i) := by
  unfold scanInstruction at run
  dsimp only at run
  repeat' first
    | (solve | cases run; intro i member; cases member)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals first
    | (solve | cases run)
    | (cases run
       exact stock_emitInstruction_form_coverage mapped clean source original (before := scanState before ii)
         (by unfold scanState; dsimp only; split <;> rfl) (by assumption))

end Backend.Stock.Proof.Coverage.Result
