import FV.Backend.Proof.StockEntryAliases

/-! Source successor binding and mapped/final-alias machine parallel copies.
The semantic transfer computes register numbers from the actual context. The
remaining driver obligation is identifying these lists with VCode edge fields. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def edgeValueNum (ctx : Ctx) (x : Nat) : Nat :=
  match ctx.valueReg? x with | some (.vreg n .int) => n | _ => 0

def edgeParamNumbers (result : Result) (b : Clif.Block) : List Nat :=
  (b.params.map (·.1)).map (fun x => aliasNum result.final.alias (edgeValueNum result.ctx x))

def edgeArgumentNumbers (result : Result) (bc : Clif.BlockCall) : List Nat :=
  bc.args.map (fun x => aliasNum result.final.alias (edgeValueNum result.ctx x))

private theorem number_eq {ctx : Ctx} {x n : Nat} (mapped : ctx.valueReg? x = some (.vreg n .int)) :
    edgeValueNum ctx x = n := by simp only [edgeValueNum,mapped]

private theorem built_context {f : Clif.Function} {result : Result} (run : Stock.lower f = .ok result) :
    ∃ ranges,Stock.buildCtx f = .ok (result.ctx,ranges,result.initial) := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  cases run
  exact ⟨_,by assumption⟩

private theorem parameter_mapped {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup)
    {tl : Nat} {b : Clif.Block} (block : f.blocks[tl]? = some b) {x : Nat}
    (parameter : x ∈ b.params.map (·.1)) : ∃ key,result.ctx.valueReg? x = some (.vreg key .int) := by
  obtain ⟨ranges,build⟩ := built_context run
  obtain ⟨original,st0,sourceBuild,spec,view⟩ := buildCtx_source build
  obtain ⟨q,member,rfl⟩ := List.mem_map.mp parameter
  have old := (spec.facts.types ssa).2 b (List.mem_of_getElem? block) q member
  have typed : result.ctx.valueType? q.1 = some (CTy.ofClif q.2) := by
    simpa only [Ctx.valueType?,view.valTy] using old
  exact (buildCtx_mappedInv scope build).typedReg q.1 _ typed

private theorem destinations_nodup {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup)
    {tl : Nat} {b : Clif.Block} (block : f.blocks[tl]? = some b) : (edgeParamNumbers result b).Nodup := by
  obtain ⟨ranges,build⟩ := built_context run
  have original := (List.nodup_append.mp (block_nodup ssa block)).1
  change List.Pairwise (fun a b : Nat => a ≠ b)
    ((b.params.map (·.1)).map (fun x => aliasNum result.final.alias (edgeValueNum result.ctx x)))
  rw [List.pairwise_map]
  apply List.Pairwise.imp_of_mem ?_ original
  intro x y hx hy different equal
  obtain ⟨nx,mx⟩ := parameter_mapped run scope ssa block hx
  obtain ⟨ny,my⟩ := parameter_mapped run scope ssa block hy
  rw [number_eq mx,number_eq my,stock_lower_parameter_resolves run ssa block hx mx,
    stock_lower_parameter_resolves run ssa block hy my] at equal
  subst ny
  exact different ((buildCtx_allocated build).2.1 x y nx mx my)

/-- Actual successful source successor binding agrees with the corresponding
mapped/final-alias machine copy. Original scope/dominance derive destination
injectivity and inherited-value separation; no register-map certificate or
new accepted-program condition is supplied. -/
theorem stock_lower_edge_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {tl : Nat} {b : Clif.Block} (block : f.blocks[tl]? = some b)
    {fr fr' : Clif.Frame} (func : fr.func = f) {bc : Clif.BlockCall}
    (target : f.block? bc.block = some b) (entered : Clif.enterBlock fr bc = .ok fr')
    {needed : Nat → Prop} (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) tl 0)
    {ρ : Nat → CV} (held : ValuesHeld
      (fun x => x ∈ bc.args ∨ (needed x ∧ x ∉ b.params.map (·.1))) result.ctx fr
      (fun key => ρ (aliasNum result.final.alias key))) :
    ValuesHeld needed result.ctx fr' (fun key =>
      parCopyEnv ρ (edgeParamNumbers result b) (edgeArgumentNumbers result bc) (aliasNum result.final.alias key)) := by
  obtain ⟨original,vals,regs,found,read,types,set,frame⟩ := enterBlock_spec entered
  rw [func] at found
  cases Option.some.inj (found.symm.trans target)
  have parameterNodup := (List.nodup_append.mp (block_nodup dominated.ssa block)).1
  have copyNodup := destinations_nodup run scope dominated.ssa block
  have sourceLength := (getMany_spec read).1
  have targetLength := setMany_length set
  have copyLength : (edgeParamNumbers result b).length = (edgeArgumentNumbers result bc).length := by
    simp only [edgeParamNumbers,edgeArgumentNumbers,List.length_map]
    simp only [List.length_map] at targetLength
    omega
  intro x need value lookup
  have actual : regs x = some value := by simpa only [frame] using lookup
  by_cases parameter : x ∈ b.params.map (·.1)
  · obtain ⟨m,v,pm,vm,bound⟩ := setMany_mem set parameterNodup x parameter
    have same := Option.some.inj (bound.symm.trans actual)
    subst v
    have mBound : m < bc.args.length := by
      have present := (List.getElem?_eq_some_iff.mp pm).1
      omega
    let arg := bc.args[m]
    have am : bc.args[m]? = some arg := List.getElem?_eq_getElem mBound
    obtain ⟨v,readArg,valueAt⟩ := (getMany_spec read).2 m arg am
    have same := Option.some.inj (valueAt.symm.trans vm)
    subst v
    obtain ⟨sourceKey,sourceMapped,sourceHeld⟩ := held arg (Or.inl (List.mem_of_getElem? am)) value readArg
    obtain ⟨key,mapped⟩ := parameter_mapped run scope dominated.ssa block parameter
    refine ⟨key,mapped,?_⟩
    have destinationAt : (edgeParamNumbers result b)[m]? = some (aliasNum result.final.alias key) := by
      simp only [edgeParamNumbers,List.getElem?_map,pm,Option.map_some,number_eq mapped]
    have sourceAt : (edgeArgumentNumbers result bc)[m]? = some (aliasNum result.final.alias sourceKey) := by
      simp only [edgeArgumentNumbers,List.getElem?_map,am,Option.map_some,number_eq sourceMapped]
    dsimp only
    rw [parCopyEnv_param (ρ := ρ) copyNodup copyLength m destinationAt sourceAt]
    exact sourceHeld
  · have before : fr.regs x = some value := by
      rw [setMany_other set parameter] at actual
      exact actual
    obtain ⟨key,mapped,sourceHeld⟩ := held x (Or.inr ⟨need,parameter⟩) value before
    refine ⟨key,mapped,?_⟩
    have outside : aliasNum result.final.alias key ∉ edgeParamNumbers result b := by
      intro member
      obtain ⟨y,yp,equals⟩ := List.mem_map.mp member
      obtain ⟨parameterKey,targetMapped⟩ := parameter_mapped run scope dominated.ssa block yp
      have apart := stock_lower_entry_alias_apart run scope dominated block (available x need) parameter mapped yp targetMapped
      apply apart
      rw [number_eq targetMapped] at equals
      exact equals.symm
    dsimp only
    rw [parCopyEnv_other (ρ := ρ) outside]
    exact sourceHeld
end Backend.Stock.Proof
