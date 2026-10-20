import FV.Backend.Proof.StockExplicitCallFrames
import FV.E2E.RegLevelCall
namespace Backend.Stock.Proof.ExplicitCallPhysicalDraft
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 ExplicitCallSemDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

private theorem zip_take_subset {α β : Type} (left : List α) (right : List β) (n : Nat) :
    ∀ p ∈ left.zip (right.take n),p ∈ left.zip right := by
  induction left generalizing right n with
  | nil => simp
  | cons a left ih =>
    cases right with
    | nil => simp
    | cons b right =>
      cases n with
      | zero => simp
      | succ n =>
        intro p member
        simp only [List.take_succ_cons,List.zip_cons_cons,List.mem_cons] at member ⊢
        exact member.elim Or.inl (fun h => Or.inr (ih right n p h))
private theorem at_I {F FK : BitVec 64 → Prop} {P : MInst → Prop}
    {exec : MInst → Arm.ArmState → Option Arm.ArmState} {isem : Backend.Proof.Sem}
    {info : CallInfo} {ctl : Ctl} {s : Arm.ArmState}
    (physical : OperandsSoundCtlAtI F FK P exec isem (.call info) ctl s) :
    OperandsSoundCtlAtI F FK P exec (explicitCallSem isem) (.call info) ctl s := by
  intro c wh ops regs i' w outs w' operands checked assigned atPC world aligned valid call
  change (isem (.call info) (useVals ops regs s) w).map
    (fun (full,returned,control) => (full.take info.defs.length,returned,control)) = some (outs,w',ctl) at call
  obtain ⟨⟨full,returned,control⟩,actual,equal⟩ := Option.map_eq_some_iff.mp call
  dsimp only at equal
  cases equal
  obtain ⟨s',run,related,kept,defs,other,saved⟩ :=
    physical c wh ops regs i' w full w' operands checked assigned atPC world aligned valid actual
  refine ⟨s',run,related,kept,?_,other,saved⟩
  intro p member
  exact defs p (zip_take_subset _ full info.defs.length p member)

/-- The original physical callee contract suffices for the adapter. Ignored ABI
outputs remove observations only; the SAME concrete call, world, kept frame,
register-preservation and clobber guarantees prove the result. -/
theorem stock_explicit_call_physical {F : BitVec 64 → Prop} {K : Nat} {X : ExtSem} {H : ArmHooks}
    {S : CallInfo → Prop} (callee : CalleeOk F K X H S) :
    ∀ ctx info,S info → CallSoundCtl F K (callExec H)
      (explicitCallSem (csem F ctx X)) (.call info) .next := by
  intro ctx info member s budget outside
  have old := ((callee.os ctx info member) s budget outside).toI (fun _ => True)
  have fresh := at_I old
  intro c wh ops regs i' w outs w' operands checked assigned world aligned valid call
  exact fresh c wh ops regs i' w outs w' operands checked assigned trivial world aligned valid call

/-- Guarded physical calls retain the original call-site and kept-world
conditions as well. No stronger CalleeOkG contract is introduced. -/
theorem stock_explicit_call_guarded_physical {F G : BitVec 64 → Prop} {K : Nat} {s0 : Arm.ArmState}
    {Pc : BitVec 64 → MInst → Prop} {X : ExtSem} {H : ArmHooks} {S : CallInfo → Prop}
    {gv : Nat → String → Prop} (callee : CalleeOkG F K G s0 Pc X H S gv) :
    ∀ ctx info,S info → CallSoundCtlG F K G s0 Pc (callExec H)
      (explicitCallSem (csemV gv F ctx X)) (.call info) .next := by
  intro ctx info member s budget outside kept
  exact at_I (callee.os ctx info member s budget outside kept)
end Backend.Stock.Proof.ExplicitCallPhysicalDraft
