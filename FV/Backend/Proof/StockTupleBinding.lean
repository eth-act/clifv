import FV.Backend.Proof.StockCallOutputValues
namespace Backend.Stock.Proof.TupleBindingDraft
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

def freshVectors (base count : Nat) : List (List Reg) :=
  (List.range count).map (fun j => [Reg.vreg (base+j) .int])
def sourceNumber (ctx : Ctx) (x : Nat) : Nat :=
  match ctx.valueReg? x with | some (.vreg n .int) => n | _ => 0
private def bindingStep (ctx : Ctx) (acc : State × Array MInst) (pair : Nat × List Reg) : Except String (State × Array MInst) := do
  let (st,extra) := acc
  let (x,rs) := pair
  let some vr := ctx.valueReg? x | throw s!"unknown value v{x}"
  match rs with
  | [r@(.vreg ..)] => pure (← st.setAlias vr r,extra)
  | [r] => pure (st,extra.push (.mov .size64 vr r))
  | _ => throw "multi-register result"
private theorem fold_inputs {α β : Type} (step : α → β → Except String α) (P : β → Prop)
    (holds : ∀ a x next,step a x = .ok next → P x) (xs : List β) {a next : α}
    (run : xs.foldlM step a = .ok next) : ∀ x ∈ xs,P x := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldlM_cons] at run
    obtain ⟨middle,head,tail⟩ := Except.bind_ok run
    intro y member
    rcases List.mem_cons.mp member with rfl | member
    · exact holds _ _ _ head
    · exact ih tail y member
private theorem binding_mappings {ctx : Ctx} {pairs : List (Nat × List Reg)} {st next : State} {copies : Array MInst}
    (run : bindResults ctx pairs st = .ok (next,copies)) :
    ∀ p ∈ pairs,∃ r,ctx.valueReg? p.1 = some r := by
  change pairs.foldlM (bindingStep ctx) (st,#[]) = .ok (next,copies) at run
  apply fold_inputs (bindingStep ctx) (fun p => ∃ r,ctx.valueReg? p.1 = some r) ?_ pairs run
  intro acc pair next call
  rcases pair with ⟨x,rs⟩
  cases mapped : ctx.valueReg? x with
  | none => simp [bindingStep,mapped] at call
  | some r => exact ⟨r,rfl⟩
private theorem alias_frame (xs : List (Nat × Nat)) (a : Array (Option Nat)) (key : Nat)
    (apart : ∀ p ∈ xs,p.1 ≠ key) :
    ((xs.foldl aliasStep a)[key]?).join = (a[key]?).join := by
  induction xs generalizing a with
  | nil => rfl
  | cons p xs ih =>
    rw [List.foldl_cons,ih (aliasStep a p) (fun q h => apart q (List.mem_cons_of_mem _ h)),aliasStep_get]
    simp [Ne.symm (apart p (List.mem_cons_self ..))]
private theorem alias_member (xs : List (Nat × Nat)) (a : Array (Option Nat))
    (distinct : (xs.map (·.1)).Nodup) :
    ∀ p ∈ xs,((xs.foldl aliasStep a)[p.1]?).join = some p.2 := by
  induction xs generalizing a with
  | nil => simp
  | cons p xs ih =>
    simp only [List.map_cons,List.nodup_cons] at distinct
    intro q member
    rcases List.mem_cons.mp member with equal | member
    · subst q
      rw [List.foldl_cons,alias_frame xs (aliasStep a p) p.1 ?_,aliasStep_get]
      · simp
      · intro q present equal
        exact distinct.1 (List.mem_map.mpr ⟨q,present,equal⟩)
    · exact ih (aliasStep a p) distinct.2 q member

/-- Successful real tuple binding installs every indexed fresh result at its
mapped source key, with no copies and unchanged machine state. Mapping
injectivity and the original source-result distinctness prevent overwrites. -/
theorem stock_bindResults_fresh_tuple {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {xs : List Nat} (distinct : xs.Nodup) {base : Nat} {st next : State} {copies : Array MInst}
    (run : bindResults ctx (xs.zip (freshVectors base xs.length)) st = .ok (next,copies)) :
    copies = #[] ∧ next.base = st.base ∧
      (∀ x ∈ xs,∃ key,ctx.valueReg? x = some (.vreg key .int)) ∧
      ∀ (j x key : Nat),xs[j]? = some x → ctx.valueReg? x = some (.vreg key .int) →
        (next.alias[key]?).join = some (base+j) := by
  have mappings := binding_mappings run
  have source : ∀ x ∈ xs,ctx.valueReg? x = some (.vreg (sourceNumber ctx x) .int) := by
    intro x member
    have inKeys : x ∈ (xs.zip (freshVectors base xs.length)).map (·.1) := by
      rw [List.map_fst_zip (by simp [freshVectors])]
      exact member
    obtain ⟨p,present,same⟩ := List.mem_map.mp inKeys
    obtain ⟨r,lookup⟩ := mappings p present
    rw [same] at lookup
    obtain ⟨n,rfl⟩ := mapped.valueReg x r lookup
    simpa only [sourceNumber,lookup] using lookup
  let triples := (xs.zip (List.range xs.length)).map (fun p => (p.1,sourceNumber ctx p.1,base+p.2))
  have packed : xs.zip (freshVectors base xs.length) = triples.map (fun p => (p.1,[Reg.vreg p.2.2 .int])) := by
    simp only [freshVectors,List.zip_map_right,triples,List.map_map,Function.comp_def]
    rfl
  have installed := bindResults_virtual ctx st triples (by
    intro p member
    obtain ⟨q,present,rfl⟩ := List.mem_map.mp member
    exact source q.1 (List.of_mem_zip present).1)
  rw [packed,installed] at run
  cases run
  refine ⟨rfl,rfl,(fun x hx => ⟨sourceNumber ctx x,source x hx⟩),?_⟩
  have keyShape : ((triples.map (·.2)).map (·.1)) = xs.map (sourceNumber ctx) := by
    simp only [triples,List.map_map,Function.comp_def]
    rw [show (fun p : Nat × Nat => sourceNumber ctx p.1) = sourceNumber ctx ∘ Prod.fst from rfl,
      ← List.map_map,List.map_fst_zip (by simp)]
  have keyDistinct : ((triples.map (·.2)).map (·.1)).Nodup := by
    rw [keyShape]
    change List.Pairwise (fun x y => x ≠ y) (xs.map (sourceNumber ctx))
    rw [List.pairwise_map]
    apply distinct.imp_of_mem
    intro x y hx hy different same
    apply different
    exact mapped.injective x y (sourceNumber ctx x) (source x hx) (by rw [same]; exact source y hy)
  intro j x key atValue lookup
  have below : j < xs.length := (List.getElem?_eq_some_iff.mp atValue).1
  have number : sourceNumber ctx x = key := by simp [sourceNumber,lookup]
  have pair : (x,j) ∈ xs.zip (List.range xs.length) := by
    apply List.mem_of_getElem?
    rw [List.getElem?_zip_eq_some]
    exact ⟨atValue,by simp [below]⟩
  have triple : (x,sourceNumber ctx x,base+j) ∈ triples := List.mem_map.mpr ⟨(x,j),pair,rfl⟩
  have result := alias_member (triples.map (·.2)) st.alias keyDistinct
    (sourceNumber ctx x,base+j) (List.mem_map_of_mem triple)
  simpa only [number] using result
end Backend.Stock.Proof.TupleBindingDraft
