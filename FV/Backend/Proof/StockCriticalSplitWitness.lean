import FV.Backend.Proof.StockCriticalSplitFixture
import FV.Backend.Proof.StockSourceIndegree

namespace Backend.Stock.Proof.CriticalSplitWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgeSpill
open Backend.Stock.Proof.CriticalSplitFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
private def original (indirect : Bool) : Ctx × Array (Nat × Nat) × LState :=
  (Backend.buildCtx (function indirect)).toOption.getD (sinkCtx,#[],default)
private theorem original_build (indirect : Bool) : Backend.buildCtx (function indirect) = .ok (original indirect) := by
  cases indirect <;> rfl
private theorem dominated (indirect : Bool) : Dominated (function indirect) := by
  cases indirect
  all_goals
    constructor
    · simp only [valueDefs,function]; decide +kernel
    · intro ctx ranges st build bi b found
      have bound : bi < 3 := by have h := lt_of_getElem? found; simpa [function] using h
      have choices : bi = 0 ∨ bi = 1 ∨ bi = 2 := by omega
      rcases choices with rfl | rfl | rfl
      all_goals
        simp [function] at found
        subst b
        constructor
        · intro j stm present y member
          cases j <;> simp at present <;> subst stm <;> cases member
        · intro y member
          first
          | (change y ∈ ([] : List Nat) at member; cases member)
          | (change y ∈ [0] at member; simp only [List.mem_singleton] at member; subst y; simp [availOf,function,defsBefore,defsFrom])
          | (change y ∈ [2] at member; simp only [List.mem_singleton] at member; subst y; simp [availOf,function,defsBefore,defsFrom])
          | (change y ∈ [7] at member; simp only [List.mem_singleton] at member; subst y; simp [availOf,function,defsBefore,defsFrom])
    · intro ctx ranges st build tl x available notLocal y member
      have fixed := (inFix_fixOk (ctx := ctx) (gn := id)).cand tl x available
      have context := congrArg Prod.fst (Except.ok.inj (build.symm.trans (original_build _)))
      change ctx = _ at context
      rw [context] at member
      have values := fixed.2.2.2.1
      simp [valueDefs,function] at values
      first | (rcases values with rfl | rfl | rfl) | (rcases values with rfl | rfl)
      all_goals change y ∈ ([] : List Nat) at member; cases member

private theorem source_computed (indirect : Bool) : stockSourceTable (function indirect) = .ok #[#[1],#[],#[1]] := by
  cases indirect <;> cbv
private theorem order_computed (indirect : Bool) : blockOrder (function indirect) = .ok {
    nodes := #[.original 0,.edge 0 0 1,.original 1],successors := #[#[1],#[2],#[]]} := by
  cases indirect <;> cbv

/-- Complete direct/indirect one-successor TryCall programs inhabit actual
critical insertion completeness, including source indegree contributed by an
unreachable block. The original source is retained, and all raw/checked/
physical pipeline stages succeed. -/
theorem stock_single_try_forced_split_witness (indirect : Bool) :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc)
      (source : Array (Array Nat)) (degree : Array Nat),
      Stock.lower (function indirect) = .ok result ∧ LowerScope (function indirect) ∧
      Dominated (function indirect) ∧ ArityOk (function indirect) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      stockSourceTable (function indirect) = .ok source ∧ source = #[#[1],#[],#[1]] ∧
      sourceIndegree source (function indirect).blocks.length = .ok degree ∧ degree = #[0,2,0] ∧
      CriticalSplitComplete (function indirect) source degree result.order.nodes ∧
      source[0]!.size = 1 ∧ degree[1]! = 2 ∧
      Node.original 2 ∉ result.order.nodes.toList ∧ Node.edge 0 0 1 ∈ result.order.nodes.toList ∧
      result.order.nodes[1]? = some (.edge 0 0 1) ∧ result.order.successors[0]? = some #[1] ∧
      result.order.successors[1]? = some #[2] ∧
      degree.size = 3 ∧ (∀ target,target < 3 → degree[target]! = (source.toList.flatMap Array.toList).count target) := by
  obtain ⟨fixture⟩ := single_try_fixture indirect
  rcases fixture with ⟨result,p,rf,af,run,scope,arity,raw,fallback,accepted,physical⟩
  have dominated := dominated indirect
  obtain ⟨source,degree,sourceRun,counted,complete⟩ := stock_lower_critical_split_complete run
  have sourceEq := Except.ok.inj (sourceRun.symm.trans (source_computed indirect))
  have degreeComputed : sourceIndegree source (function indirect).blocks.length = .ok #[0,2,0] := by
    rw [sourceEq]
    cases indirect <;> rfl
  have degreeEq := Except.ok.inj (counted.symm.trans degreeComputed)
  have order := Except.ok.inj ((stock_lower_order run).symm.trans (order_computed indirect))
  have original : Node.original 0 ∈ result.order.nodes.toList := by rw [order]; simp
  have selected : source[0]![0]? = some 1 := by rw [sourceEq]; rfl
  have forced : (forceCritical (function indirect).blocks[0]!.term || decide (1 < source[0]!.size)) = true := by
    cases indirect <;> rfl
  have shared : 1 < degree[1]! := by rw [degreeEq]; decide
  have inserted := complete 0 original 0 1 selected forced shared
  exact ⟨result,p,rf,af,source,degree,run,scope,dominated,arity,raw,fallback,accepted,physical,
    sourceRun,sourceEq,counted,degreeEq,complete,by rw [sourceEq]; rfl,by rw [degreeEq]; rfl,
    by rw [order]; simp,inserted,by rw [order]; rfl,by rw [order]; rfl,by rw [order]; rfl,sourceIndegree_counts counted⟩

end Backend.Stock.Proof.CriticalSplitWitness
