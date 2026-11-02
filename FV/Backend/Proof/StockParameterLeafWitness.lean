import FV.Backend.Proof.StockParameterLeaf
import FV.Backend.Proof.StockScalarCheck

/-! Non-vacuity of the parameter leaf inductions: a real CFG whose entry jumps to a block that
branches on the entry parameter, to a scalar block that ends in `trap` or to a return block,
lowers and meets every premise; its trap leaf has both continuations for every semantics that
meets the usual contracts. -/

namespace Backend.Stock.Proof.ParameterCfg.TrapLeafFixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ForwardSource
set_option autoImplicit false

/-- Entry adds and jumps; block 1 branches on the entry parameter; block 2 multiplies and ends
in `trap`; block 3 returns. -/
def function : Clif.Function := {
  name := "parameter_trap_leaf"
  sig := { params := [⟨.i64,.none,.normal⟩], returns := [⟨.i64,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0,.i64)], body := [⟨[1],.binary .iadd .i64 0 0⟩], term := .jump ⟨1,[]⟩ },
    { id := 1, params := [], body := [], term := .brif 0 ⟨2,[]⟩ ⟨3,[]⟩ },
    { id := 2, params := [], body := [⟨[2],.binary .imul .i64 1 0⟩], term := .trap (.user 4) },
    { id := 3, params := [], body := [], term := .ret [1] }] }

private def checks : Bool :=
  lowerScopeB function && dominatedB function && sigAbiOk function.sig &&
  function.blocks.all (fun b => b.body.all Scalar.maskMixedBodyEligible) &&
  match Stock.lower function with
  | .error _ => false
  | .ok result => (result.order.nodes.findIdx? (· == .original 2)).isSome

-- witness: native_decide (the fixed function's input checks and its lowering only)
private theorem checks_true : checks = true := by native_decide

private theorem four {bi : Nat} {b : Clif.Block} (found : function.blocks[bi]? = some b) :
    (bi = 0 ∧ b = function.blocks[0]!) ∨ (bi = 1 ∧ b = function.blocks[1]!) ∨
      (bi = 2 ∧ b = function.blocks[2]!) ∨ (bi = 3 ∧ b = function.blocks[3]!) := by
  have bound : bi < 4 := by
    have := lt_of_getElem? found
    simpa [function] using this
  have cases : bi = 0 ∨ bi = 1 ∨ bi = 2 ∨ bi = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨rfl,(Option.some.inj found).symm⟩
  · exact Or.inr (Or.inl ⟨rfl,(Option.some.inj found).symm⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl,(Option.some.inj found).symm⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨rfl,(Option.some.inj found).symm⟩))

private theorem index1 : function.blocks.findIdx? (·.id == 1) = some 1 := by decide
private theorem index2 : function.blocks.findIdx? (·.id == 2) = some 2 := by decide
private theorem index3 : function.blocks.findIdx? (·.id == 3) = some 3 := by decide

private theorem ranked : Ranked function (fun bi => bi) := by
  intro bi b ti destination found present target
  change bi < ti
  rcases four found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · simp only [function,List.getElem!_cons_zero,destinations,List.mem_singleton] at present
    subst destination
    have same := Option.some.inj (index1.symm.trans target)
    omega
  · simp only [function,List.getElem!_cons_succ,List.getElem!_cons_zero,destinations,
      List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl | rfl
    · have same := Option.some.inj (index2.symm.trans target)
      omega
    · have same := Option.some.inj (index3.symm.trans target)
      omega
  · simp [function,destinations] at present
  · simp [function,destinations] at present

private theorem leaves : NonentryParameterLeafTerms function := by
  intro bi b found nonentry
  rcases four found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact False.elim (nonentry rfl)
  · exact Or.inr (Or.inr (Or.inl ⟨0,⟨2,[]⟩,⟨3,[]⟩,rfl,rfl,rfl,
      ⟨0,function.blocks[0]!,.i64,by decide,by decide,Or.inr rfl⟩⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨.user 4,rfl⟩))
  · exact Or.inr (Or.inl ⟨[1],rfl⟩)

theorem trap_leaf_witness : ∃ result label,Stock.lower function = .ok result ∧
    result.order.nodes[label]? = some (.original 2) ∧
    LowerScope function ∧ Dominated function ∧ sigAbiOk function.sig = true ∧
    Ranked function (fun bi => bi) ∧ NonentryParameterLeafTerms function ∧
    function.blocks[2]!.term = .trap (.user 4) ∧
    (∀ {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem},Refines F isem → DriverSem isem →
      ∀ {MR : MemRelT},MRStable F MR → ∀ (env : Clif.Env) (cp : Clif.Program),
        (∃ event,event ∈ result.blockScans.toList ∧ event.block = 2 ∧
          TrapsAt function result label 2 function.blocks[2]! event isem MR env cp) ∧
        ∃ event,event ∈ result.blockScans.toList ∧ event.block = 2 ∧
          ReturnsAt function result label 2 function.blocks[2]! event isem MR env cp) := by
  have h := checks_true
  unfold checks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨scope,dominated⟩,abi⟩,bodies⟩,lowered⟩ := h
  have family : ∀ b ∈ function.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst := by
    intro b member stm present
    exact Scalar.maskMixedBodyEligible_sound
      (List.all_eq_true.mp (List.all_eq_true.mp bodies b member) stm present)
  cases run : Stock.lower function with
  | error message => rw [run] at lowered; cases lowered
  | ok result =>
    rw [run] at lowered
    obtain ⟨label,found⟩ := Option.isSome_iff_exists.mp lowered
    have tag : result.order.nodes[label]? = some (.original 2) := by
      have := Array.findIdx?_eq_some_iff_getElem.mp found
      obtain ⟨bound,matched,_⟩ := this
      rw [Array.getElem?_eq_getElem bound]
      simpa using matched
    have block : function.blocks[2]? = some function.blocks[2]! := by decide
    refine ⟨result,label,rfl,tag,lowerScope_of scope,dominated_of dominated,abi,ranked,leaves,rfl,?_⟩
    intro F isem refines driver MR stable env cp
    exact ⟨nonentry_parameter_traps_of_leaf run (lowerScope_of scope) (dominated_of dominated) abi ranked
        leaves family refines driver stable env cp tag block (by decide),
      nonentry_parameter_returns_of_leaf run (lowerScope_of scope) (dominated_of dominated) abi ranked
        leaves family refines driver stable env cp tag block (by decide)⟩

end Backend.Stock.Proof.ParameterCfg.TrapLeafFixture
