import FV.Backend.Proof.IselExtern
import FV.Backend.Proof.PerEdgeRegallocSound
import FV.Backend.Proof.RegallocCSem
import FV.Backend.Lowering.Stock
import FV.Backend.Proof.LowerDecide
namespace Backend.Stock.Proof.PerEdgeM6DivergenceWitness
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def function : Clif.Function := {
  name := "stock_per_edge_infinite_loop",sig := {callConv := some .systemV}
  blocks := [{id := 0,term := .jump ⟨1,[]⟩},{id := 1,term := .jump ⟨1,[]⟩}] }
private def allocated : RFunc := {spillSlots := 0,saved := [],blocks := #[#[.op 0 #[]],#[.op 0 #[]]]}
local instance {α : Type} [DecidableEq α] : DecidableEq (Except String α) := fun a b =>
  match a,b with
  | .ok a,.ok b =>
    if h : a = b then isTrue (congrArg Except.ok h)
    else isFalse (fun eq => h (Except.ok.inj eq))
  | .error a,.error b =>
    if h : a = b then isTrue (congrArg Except.error h)
    else isFalse (fun eq => h (Except.error.inj eq))
  | .ok _,.error _ => isFalse (fun h => by cases h)
  | .error _,.ok _ => isFalse (fun h => by cases h)
private def Observed : Prop := (Stock.lower function).toOption.map (fun (result : Result) => decide (
  checkAllocAt result.code result.edgeArgs allocated = .ok () ∧ result.code.blocks.size = 2 ∧
  (result.code.blocks[0]!).insts = #[.jump 1] ∧ (result.code.blocks[1]!).insts = #[.jump 1] ∧
  result.code.cfg = .ok (#[#[1],#[1]],#[#[],#[0,1]]))) = some true
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed : Observed := by unfold Observed; decide +kernel
end Kernel
private theorem dominated : Dominated function := by
  constructor
  · change ([] : List Nat).Nodup; decide
  · intro ctx ranges initial build bi block found
    cases bi with
    | zero =>
      simp [function] at found
      subst block
      constructor
      · intro j statement present; simp [function] at present
      · intro y member; simp [function,abiTerm,Driver.termArgs] at member
    | succ bi =>
      cases bi with
      | zero =>
        simp [function] at found
        subst block
        constructor
        · intro j statement present; simp [function] at present
        · intro y member; simp [function,abiTerm,Driver.termArgs] at member
      | succ bi => simp [function] at found
  · intro ctx ranges initial build tl x available notLocal y member
    cases tl with
    | zero => simp [parsOf,function]
    | succ tl => cases tl <;> simp [parsOf,function]
private def trace (m : Loc → CV) (w : Arm.ArmState) (n : Nat) : MConf CV Arm.ArmState :=
  .run ⟨if n = 0 then 0 else 1,[.op 0 #[]],m,w⟩
/-- A complete original-scope/dominated Stock loop has a concrete infinite
allocated execution from function entry. Indexed M6 supplies VCode executions
of every length, with no assumed progress or supplied source/edge certificate. -/
theorem stock_per_edge_m6_divergence_witness : ∃ result : Result,
    Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
    checkAllocAt result.code result.edgeArgs allocated = .ok () ∧
    ∀ (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (w : Arm.ArmState)
        (m : Loc → CV) (ρ : Nat → CV),
      trace m w 0 = MConf.init allocated m w ∧
      (∀ n,MStep result.code (csem F ctx X) ckeep allocated (trace m w n) (trace m w (n+1))) ∧
      ∀ N,∃ v,StepsN (VStepAt result.code result.edgeArgs (csem F ctx X)) N (VConf.init ρ w) v := by
  have actual := observed
  unfold Observed at actual
  cases run : Stock.lower function with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,decide_eq_true_eq] at actual
    obtain ⟨accepted,size,code0,code1,cfg⟩ := actual
    refine ⟨result,rfl,lowerScope_of (by decide +kernel),dominated,accepted,?_⟩
    intro F ctx X w m ρ
    have initial : trace m w 0 = MConf.init allocated m w := rfl
    have steps : ∀ n,MStep result.code (csem F ctx X) ckeep allocated (trace m w n) (trace m w (n+1)) := by
      intro n
      let b := if n = 0 then 0 else 1
      have positions : b = 0 ∨ b = 1 := by unfold b; split <;> simp
      have bound : b < result.code.blocks.size := by omega
      have placed : result.code.blocks[b]? = some result.code.blocks[b]! := by
        simp [getElem!_def,Array.getElem?_eq_getElem bound]
      have code : (result.code.blocks[b]!).insts = #[.jump 1] := by
        rcases positions with h | h <;> simp [h,code0,code1]
      have successor : succOf result.code b 0 = some 1 := by
        rcases positions with h | h <;> simp [succOf,cfg,h]
      change MStep result.code (csem F ctx X) ckeep allocated (.run ⟨b,[.op 0 #[]],m,w⟩) _
      have next : trace m w (n+1) = .run ⟨1,[.op 0 #[]],m,w⟩ := by simp [trace]
      rw [next]
      refine MStep.op (k := 0) (allocs := #[]) (i := .jump 1) (ops := #[])
        (outs := []) (outs' := []) (m2 := m) placed (by rw [code]; rfl) rfl rfl
        (by rfl) (by simp) (HavocOuts.refl _ _ _) ⟨fun _ _ => by simp [writeM],fun _ h => by cases h⟩ ?_
      simp [writeM]
      apply MNext.goto _ successor (show allocated.blocks[1]? = some #[.op 0 #[]] from rfl)
      rw [code]; rfl
    exact ⟨initial,steps,PerEdge.checkAlloc_diverges (sem := csem F ctx X) (keep := ckeep)
      accepted ρ (trace m w) initial steps⟩
end Backend.Stock.Proof.PerEdgeM6DivergenceWitness
