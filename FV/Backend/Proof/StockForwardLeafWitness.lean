import FV.Backend.Proof.StockForwardLeaf
import FV.Backend.Proof.StockScalarCheck

/-! Non-vacuity of the forward leaf inductions: a real forward CFG whose entry jumps to a scalar
block that ends in `trap` lowers, meets every premise, and its trap leaf has both
continuations for every semantics that meets the usual contracts. -/

namespace Backend.Stock.Proof.ForwardSource.TrapLeafFixture
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false

/-- Entry adds and jumps; the leaf multiplies and ends in `trap`. -/
def function : Clif.Function := {
  name := "forward_trap_leaf"
  sig := { params := [⟨.i64,.none,.normal⟩], returns := [⟨.i64,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0,.i64)], body := [⟨[1],.binary .iadd .i64 0 0⟩], term := .jump ⟨1,[]⟩ },
    { id := 1, params := [], body := [⟨[2],.binary .imul .i64 1 0⟩], term := .trap (.user 3) }] }

private def checks : Bool :=
  lowerScopeB function && dominatedB function && sigAbiOk function.sig &&
  function.blocks.all (fun b => b.body.all Scalar.maskMixedBodyEligible) &&
  match Stock.lower function with
  | .error _ => false
  | .ok result => decide (result.order.nodes[1]? = some (.original 1))

-- witness: native_decide (the fixed function's input checks and its lowering only)
private theorem checks_true : checks = true := by native_decide

private theorem two {bi : Nat} {b : Clif.Block} (found : function.blocks[bi]? = some b) :
    (bi = 0 ∧ b = function.blocks[0]!) ∨ (bi = 1 ∧ b = function.blocks[1]!) := by
  have bound : bi < 2 := by
    have := lt_of_getElem? found
    simpa [function] using this
  have cases : bi = 0 ∨ bi = 1 := by omega
  rcases cases with rfl | rfl
  · exact Or.inl ⟨rfl,(Option.some.inj found).symm⟩
  · exact Or.inr ⟨rfl,(Option.some.inj found).symm⟩

private theorem ranked : Ranked function (fun bi => bi) := by
  intro bi b ti destination found present target
  change bi < ti
  rcases two found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · simp only [function,List.getElem!_cons_zero,destinations,List.mem_singleton] at present
    subst destination
    have known : function.blocks.findIdx? (·.id == 1) = some 1 := by decide
    have same := Option.some.inj (known.symm.trans target)
    omega
  · simp [function,destinations] at present

private theorem leaves : NonentryJumpLeafBlocks function := by
  intro bi b found nonentry
  rcases two found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact False.elim (nonentry rfl)
  · exact Or.inr (Or.inr ⟨.user 3,rfl⟩)

theorem trap_leaf_witness : ∃ result,Stock.lower function = .ok result ∧
    LowerScope function ∧ Dominated function ∧ sigAbiOk function.sig = true ∧
    Ranked function (fun bi => bi) ∧ NonentryJumpLeafBlocks function ∧
    function.blocks[1]!.term = .trap (.user 3) ∧
    (∀ {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem},Refines F isem → DriverSem isem →
      ∀ {MR : MemRelT},MRStable F MR → ∀ (env : Clif.Env) (cp : Clif.Program),
        (∃ event,event ∈ result.blockScans.toList ∧ event.block = 1 ∧
          TrapsAt function result 1 1 function.blocks[1]! event isem MR env cp) ∧
        ∃ event,event ∈ result.blockScans.toList ∧ event.block = 1 ∧
          ReturnsAt function result 1 1 function.blocks[1]! event isem MR env cp) := by
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
    have tag : result.order.nodes[1]? = some (.original 1) := of_decide_eq_true lowered
    have block : function.blocks[1]? = some function.blocks[1]! := by decide
    refine ⟨result,rfl,lowerScope_of scope,dominated_of dominated,abi,ranked,leaves,rfl,?_⟩
    intro F isem refines driver MR stable env cp
    exact ⟨nonentry_traps_of_leafTerms run (lowerScope_of scope) (dominated_of dominated) abi ranked leaves
        family refines driver stable env cp tag block (by decide),
      nonentry_returns_of_leafTerms run (lowerScope_of scope) (dominated_of dominated) abi ranked leaves
        family refines driver stable env cp tag block (by decide)⟩

end Backend.Stock.Proof.ForwardSource.TrapLeafFixture
