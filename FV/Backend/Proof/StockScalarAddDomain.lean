module

public import FV.Backend.Lowering.StockScalarAdd
public import FV.Backend.Proof.LowerDecide

@[expose] public section

set_option autoImplicit false
namespace Backend.Stock.ScalarAdd
open D0 Backend.Proof.Driver
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option Elab.async false

/-- Finite context fields, without evaluating the dataflow fixed point. -/
theorem context_scope (name : String) (runs : List Clif.RunCommand) (c : Configuration) :
    ((Backend.buildCtx (source name c runs)).toOption.map
      (fun s => decide (s.1.valDef = #[none,none,some 0]))).getD false = true ∧
    lowerScopeB (source name c runs) = true := by
  cases c with
  | defaultI32 =>
    change ((Backend.buildCtx (source "" .defaultI32 [])).toOption.map
      (fun s => decide (s.1.valDef = #[none,none,some 0]))).getD false = true ∧
      lowerScopeB (source "" .defaultI32 []) = true
    decide +kernel
  | systemVI32 =>
    change ((Backend.buildCtx (source "" .systemVI32 [])).toOption.map
      (fun s => decide (s.1.valDef = #[none,none,some 0]))).getD false = true ∧
      lowerScopeB (source "" .systemVI32 []) = true
    decide +kernel
  | fastI32 =>
    change ((Backend.buildCtx (source "" .fastI32 [])).toOption.map
      (fun s => decide (s.1.valDef = #[none,none,some 0]))).getD false = true ∧
      lowerScopeB (source "" .fastI32 []) = true
    decide +kernel
  | defaultI64 =>
    change ((Backend.buildCtx (source "" .defaultI64 [])).toOption.map
      (fun s => decide (s.1.valDef = #[none,none,some 0]))).getD false = true ∧
      lowerScopeB (source "" .defaultI64 []) = true
    decide +kernel
  | systemVI64 =>
    change ((Backend.buildCtx (source "" .systemVI64 [])).toOption.map
      (fun s => decide (s.1.valDef = #[none,none,some 0]))).getD false = true ∧
      lowerScopeB (source "" .systemVI64 []) = true
    decide +kernel
  | fastI64 =>
    change ((Backend.buildCtx (source "" .fastI64 [])).toOption.map
      (fun s => decide (s.1.valDef = #[none,none,some 0]))).getD false = true ∧
      lowerScopeB (source "" .fastI64 []) = true
    decide +kernel

/-- Actual source SSA and operand availability. Parameters and earlier body
results establish every use independently of the computed entry solution. -/
theorem lowering_domain (name : String) (runs : List Clif.RunCommand) (c : Configuration) :
    Dominated (source name c runs) ∧ LowerScope (source name c runs) := by
  let f := source name c runs
  have finite := context_scope name runs c
  have stored : ∀ {ctx ranges st0}, Backend.buildCtx f = .ok (ctx,ranges,st0) →
      ctx.valDef = #[none,none,some 0] := by
    intro ctx ranges st0 hb
    have h := finite.1
    change ((Backend.buildCtx f).toOption.map
      (fun s => decide (s.1.valDef = #[none,none,some 0]))).getD false = true at h
    rw [hb] at h
    change decide (ctx.valDef = #[none,none,some 0]) = true at h
    exact of_decide_eq_true h
  refine ⟨?_,lowerScope_of finite.2⟩
  constructor
  · change ([0,1,2] : List Nat).Nodup
    decide
  · intro ctx ranges st0 hb bi B hB
    cases bi with
    | zero =>
      have same : B = f.blocks[0]! := by simpa [f,source,D0.source] using hB.symm
      subst B
      constructor
      · intro j stm hj y hy
        cases j with
        | zero =>
          have same : stm = ⟨[2],.binary .iadd (valueType c) 0 1⟩ := by
            simpa [f,source,D0.source] using hj.symm
          subst stm
          simp only [Backend.Proof.Driver.instArgs,List.mem_cons,List.not_mem_nil,or_false] at hy
          rcases hy with rfl | rfl <;>
            simp [availOf,f,source,D0.source,defsBefore,defsFrom]
        | succ j => simp [f,source,D0.source] at hj
      · intro y hy
        have same : y = 2 := by simpa [f,source,D0.source,abiTerm,sretRet,sigRets,Backend.Proof.Driver.termArgs] using hy
        subst y
        simp [availOf,f,source,D0.source,defsBefore,defsFrom]
    | succ bi => simp [f,source,D0.source] at hB
  · intro ctx ranges st0 hb tl x hx hndef y hy
    cases tl with
    | zero =>
      have ne : x ≠ 2 := by simpa [defsOf,f,source,D0.source] using hndef
      have nd : Ctx.defInst? ctx x = none := by
        have hv := stored hb
        cases x with
        | zero => simp [Ctx.defInst?,hv]
        | succ x =>
          cases x with
          | zero => simp [Ctx.defInst?,hv]
          | succ x =>
            cases x with
            | zero => exact (ne rfl).elim
            | succ x => simp [Ctx.defInst?,hv]
      simp [defArgs,nd] at hy
    | succ tl => simp [parsOf,f,source,D0.source]

end Backend.Stock.ScalarAdd
