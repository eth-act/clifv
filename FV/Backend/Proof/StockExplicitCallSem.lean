import FV.E2E.RegLevelDriverSem
import FV.Backend.Proof.StockCallResultValues
namespace Backend.Stock.Proof.ExplicitCallSemDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

/-- Observe only the result registers recorded by a regular call instruction.
The external call and its returned world are unchanged. -/
def explicitCallSem (isem : Backend.Proof.Sem) : Backend.Proof.Sem := fun i uses w =>
  match i with
  | .call info => (isem i uses w).map fun (outs,w',ctl) => (outs.take info.defs.length,w',ctl)
  | _ => isem i uses w

/-- Every old successful call with one value per recorded definition keeps the
same result values, world and control result under the additive adapter. -/
theorem stock_explicit_call_sem_compatible {isem : Backend.Proof.Sem} {info : CallInfo}
    {uses outs : List CV} {w w' : Arm.ArmState} {ctl : Ctl}
    (run : isem (.call info) uses w = some (outs,w',ctl)) (length : outs.length = info.defs.length) :
    explicitCallSem isem (.call info) uses w = some (outs,w',ctl) := by
  simp only [explicitCallSem,run,Option.map_some]
  rw [← length,List.take_length]

private theorem prefix_take {vals : List Clif.Val} {outs : List CV} (held : PrefixHold vals outs) :
    AllHold vals (outs.take vals.length) := by
  refine ⟨by have bound := held.1; simp only [List.length_take]; omega,?_⟩
  intro j v x atVal atOut
  apply held.2 j v x atVal
  have below := (List.getElem?_eq_some_iff.mp atVal).1
  simpa only [List.getElem?_take,below,ite_true] using atOut

private theorem returns_le_abi (sig : Clif.Signature) : sig.returns.length ≤ (sigRets sig).length := by
  unfold sigRets
  split
  · split
    · rename_i empty
      have zero := List.isEmpty_iff.mp empty
      simp [zero]
    · exact Nat.le_refl _
  · exact Nat.le_refl _

/-- The original external contract supplies an actual call, its explicit
source-result values and its returned memory world for both direct and GOT
calls. Extra ABI outputs are ignored by the recorded explicit definitions. -/
theorem stock_explicit_direct_call_return {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {env : Clif.Env} {exts : List Clif.ExtFunc} {MR : MemRelT}
    (external : XCallsOk env exts MR X) {ext : Clif.ExtFunc} (member : ext ∈ exts)
    {g : List Clif.Val → Clif.Mem → Clif.Outcome} {sl : List (Clif.SlotId × Nat)}
    {cm cm' : Clif.Mem} {w : Arm.ArmState} {dest : CallDest} {us ds : List (Reg × Reg)}
    {uses args : List CV} {vals rvals : List Clif.Val}
    (found : env.extern ext.name = some g)
    (target : dest = .sym ext.name ∧ uses = args ∨
      ∃ r,dest = .reg r ∧ ext.colocated = false ∧ uses = ofX (X.sym ext.name 0) :: args)
    (defs : ds.length = ext.sig.returns.length) (arguments : ArgsAt ext.sig vals args w)
    (memory : MR sl cm w) (returned : g vals cm = .returned rvals cm')
    (length : rvals.length = ext.sig.returns.length) :
    ∃ outs w',explicitCallSem (csem F ctx X) (.call ⟨dest,us,ds⟩) uses w = some (outs,w',.next) ∧
      outs.length = ds.length ∧ AllHold rvals outs ∧ MR sl cm' w' := by
  have call : ∃ full w',X.call (match dest with | .sym n => some n | .reg _ => none) uses w = some (full,w') ∧
      full.length = (sigRets ext.sig).length ∧ PrefixHold rvals full ∧ MR sl cm' w' := by
    rcases target with ⟨rfl,rfl⟩ | ⟨r,rfl,far,rfl⟩
    · exact external ext member g sl cm w (some ext.name) _ _ vals rvals cm' found (.inl ⟨rfl,rfl⟩) arguments memory returned length
    · exact external ext member g sl cm w none _ args vals rvals cm' found (.inr ⟨rfl,far,rfl⟩) arguments memory returned length
  obtain ⟨full,w',run,abiLength,held,related⟩ := call
  refine ⟨full.take ds.length,w',?_,?_,?_,related⟩
  · simp [explicitCallSem,csem]
    exact ⟨full,run,rfl⟩
  · have bound := returns_le_abi ext.sig
    simp only [List.length_take]
    omega
  · rw [defs,← length]
    exact prefix_take held

/-- Original indirect-call external semantics likewise supply the actual
explicit results and returned world; no stronger external contract is required. -/
theorem stock_explicit_indirect_call_return {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {env : Clif.Env} {sigs : List Clif.Signature} {MR : MemRelT}
    (external : XCallsIndOk env sigs MR X) {sig : Clif.Signature} (member : sig ∈ sigs)
    {name : String} {g : List Clif.Val → Clif.Mem → Clif.Outcome}
    {sl : List (Clif.SlotId × Nat)} {cm cm' : Clif.Mem} {w : Arm.ArmState}
    {r : Reg} {us ds : List (Reg × Reg)} {u : CV} {args : List CV} {vals rvals : List Clif.Val}
    (found : env.extern name = some g) (signature : ∀ s,env.sigOf name = some s → sig.abiMatch s = true)
    (address : lo64 u = X.sym name 0) (defs : ds.length = sig.returns.length)
    (count : vals.length ≤ 8) (arguments : AllHold vals args) (memory : MR sl cm w)
    (returned : g vals cm = .returned rvals cm') (length : rvals.length = sig.returns.length)
    (typed : vals.map (·.ty) = Clif.AbiParam.tys sig.params) :
    ∃ outs w',explicitCallSem (csem F ctx X) (.call ⟨.reg r,us,ds⟩) (u :: args) w = some (outs,w',.next) ∧
      outs.length = ds.length ∧ AllHold rvals outs ∧ MR sl cm' w' := by
  obtain ⟨full,w',run,abiLength,held,related⟩ := external sig member name g sl cm w u args vals rvals cm'
    found signature address count arguments memory returned length typed
  refine ⟨full.take ds.length,w',?_,?_,?_,related⟩
  · simp [explicitCallSem,csem,run]
  · have bound := returns_le_abi sig
    simp only [List.length_take]
    omega
  · rw [defs,← length]
    exact prefix_take held
end Backend.Stock.Proof.ExplicitCallSemDraft
