import FV.Backend.Proof.StockMemoryLoadStoreClass
import FV.Backend.Proof.StockMemoryStoreRecordFixture
import FV.Backend.StockMemoryLoadStoreCheck

namespace Backend.Stock.Memory.LoadStore.Fixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
open StoreRoots.Fixture
set_option autoImplicit false
set_option Elab.async false

def function (width : IntegerRoots.Width) (kind : StoreRoots.Kind)
    (distinct : Bool) : Clif.Function := {
  name := "stock_integer_load_store"
  sig := {
    params := [⟨.i64,.none,.normal⟩,⟨kind.sourceTy,.none,.normal⟩,⟨.i64,.none,.normal⟩]
    returns := [⟨width.sourceTy,.none,.normal⟩]
    callConv := some .systemV }
  blocks := [{
    id := 0
    params := [(0,.i64),(1,kind.sourceTy),(2,.i64)]
    body := [⟨[3],.load .load width.sourceTy flags 0 0⟩,
      ⟨[],.store kind.sourceOp kind.sourceTy flags 1 (if distinct then 2 else 0) 0⟩]
    term := .ret [3] }] }

theorem scope (width : IntegerRoots.Width) (kind : StoreRoots.Kind) (distinct : Bool) :
    LowerScope (function width kind distinct) := by
  cases width <;> cases kind <;> cases distinct <;> exact lowerScope_of rfl

theorem dominated (width : IntegerRoots.Width) (kind : StoreRoots.Kind) (distinct : Bool) :
    Dominated (function width kind distinct) := by
  constructor
  · change ([0,1,2,3] : List Nat).Nodup; decide
  · intro ctx ranges st build bi b found
    have bound : bi < 1 := by have h := lt_of_getElem? found; simpa [function] using h
    have zero : bi = 0 := by omega
    subst bi
    simp [function] at found
    subst b
    constructor
    · intro j stm present
      cases j with
      | zero =>
        simp [function] at present
        subst stm
        intro x member
        simp only [Driver.instArgs,List.mem_cons,List.not_mem_nil,or_false] at member
        subst x
        simp [availOf,function,defsBefore,defsFrom]
      | succ j =>
        cases j with
        | zero =>
          simp [function] at present
          subst stm
          intro x member
          cases distinct <;> simp [Driver.instArgs] at member <;>
            rcases member with rfl | rfl <;> simp [availOf,function,defsBefore,defsFrom]
        | succ j => simp [function] at present
    · intro x member
      cases width <;> cases kind <;>
        simp [abiTerm,Driver.termArgs,sretRet,sigRets,function] at member <;>
        subst x <;> simp [availOf,function,defsBefore,defsFrom]
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := function width kind distinct) (ctx := ctx) (gn := id)).cand tl x available
    have length : (function width kind distinct).blocks.length = 1 := rfl
    omega

theorem source_class_witness (width : IntegerRoots.Width) (kind : StoreRoots.Kind)
    (distinct : Bool) : SingleClass width kind kind.sourceTy (function width kind distinct) := by
  refine ⟨scope width kind distinct,dominated width kind distinct,
    (by cases width <;> cases kind <;> rfl),rfl,?_,?_⟩
  · intro loc member
    have locations : locsOf (function width kind distinct).sig =
        [ArgLoc.reg (.x 0),ArgLoc.reg (.x 1),ArgLoc.reg (.x 2)] := by
      cases width <;> cases kind <;> rfl
    rw [locations] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> exact ⟨_,rfl⟩
  · exact ⟨(function width kind distinct).blocks[0]!,0,(if distinct then 2 else 0),1,3,
      flags,flags,kind.sourceTy,rfl,rfl,rfl,(by simp [function]),
      (by cases distinct <;> simp [function]),(by simp [function]),
      (by cases kind <;> intro h <;> first | rfl | cases h),rfl,rfl⟩

theorem domain_witness (width : IntegerRoots.Width) (kind : StoreRoots.Kind) (distinct : Bool) :
    Domain (function width kind distinct) :=
  (source_class_witness width kind distinct).domain width kind kind.sourceTy

private theorem dominatedB_of_facts {f : Clif.Function}
    (unique : nodupB (valueDefs f) = true) (dominated : Dominated f) : dominatedB f = true := by
  simp only [dominatedB,unique,Bool.true_and]
  cases built : Backend.buildCtx f with
  | error message => rfl
  | ok output =>
    obtain ⟨ctx,ranges,st⟩ := output
    simp only
    apply List.all_eq_true.mpr
    intro bi member
    cases block : f.blocks[bi]? with
    | none => simp only [block]
    | some b =>
      simp only [block,Bool.and_eq_true,List.all_eq_true]
      have facts := ctxFacts_of built
      have defs : DefsAt ctx b (startOnly (blockStart f bi)).start := fun k stm atStatement r contains =>
        (facts.defs dominated.ssa r _).mpr ⟨bi,b,k,stm,block,atStatement,contains,rfl⟩
      refine ⟨⟨?_,?_⟩,?_⟩
      · intro j member
        cases statement : b.body[j]? with
        | none => simp only [statement]
        | some stm =>
          simp only [statement,List.all_eq_true]
          intro y contains
          exact (mem_avail block defs).mp ((dominated.uses _ _ _ built bi b block).1 j stm statement y contains)
      · intro y contains
        exact (mem_avail block defs).mp ((dominated.uses _ _ _ built bi b block).2 y contains)
      · intro x available
        simp only [Bool.or_eq_true,Std.HashSet.contains_ofList,List.contains_iff_mem,
          List.all_eq_true,Bool.not_eq_true',Bool.eq_false_iff,ne_eq]
        by_cases isLocal : x ∈ defsOf f bi
        · exact .inl isLocal
        · exact .inr (dominated.paramFree _ _ _ built bi x available isLocal)

/-- The executable selector accepts all canonical widths and both pointer forms. -/
theorem source_selector_witness (width : IntegerRoots.Width) (kind : StoreRoots.Kind)
    (distinct : Bool) : Backend.Stock.MemoryLoadStore.sourceOk (function width kind distinct) = true := by
  simp only [Backend.Stock.MemoryLoadStore.sourceOk,Bool.and_eq_true,Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,(source_class_witness width kind distinct).abi⟩,
    (source_class_witness width kind distinct).ordinary⟩,?_⟩
  · cases width <;> cases kind <;> cases distinct <;> rfl
  · cases width <;> cases kind <;> cases distinct <;> decide +kernel
  · apply dominatedB_of_facts ?_ (dominated width kind distinct)
    change nodupB [0,1,2,3] = true
    simp [nodupB]
  · cases width <;> cases kind <;> rfl

end Backend.Stock.Memory.LoadStore.Fixture
