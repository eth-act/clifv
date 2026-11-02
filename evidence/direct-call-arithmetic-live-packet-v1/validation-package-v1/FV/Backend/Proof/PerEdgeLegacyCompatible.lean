import FV.Backend.Proof.StockPerEdgeReturnContract

namespace Backend.Proof
open Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Every actual CFG edge selects exactly the arguments retained in the
legacy block field. This supports single-successor classes without changing
the semantics of general per-successor vectors. -/
def EdgeLegacyCompatible (vc : VCode) (edges : Array (Array (Array Reg))) : Prop :=
  ∀ b index target,succOf vc b index = some target →
    ∃ vb,vc.blocks[b]? = some vb ∧ edges[b]?.bind (·[index]?) = some vb.branchArgs

theorem EdgeLegacyCompatible.step {V W : Type} {vc : VCode} {edges : Array (Array (Array Reg))}
    {sem : ISem V W} (compatible : EdgeLegacyCompatible vc edges)
    {a b : VConf V W} (step : VStepAt vc edges sem a b) : VStep vc sem a b := by
  cases step with
  | @step fromLabel k regs world block inst ops outputs final ctl nextConf placed instruction operands semantics length next =>
    refine VStep.step placed instruction operands semantics length ?_
    cases next with
    | next room => exact VNext.next room
    | ret ret => exact VNext.ret ret
    | halt => exact VNext.halt
    | @goto index target nextRegs last successor copied =>
      obtain ⟨vb,found,args⟩ := compatible _ _ _ successor
      have same : ∀ ρ : Nat → V,edgeEnvAt vc edges fromLabel target index ρ = edgeEnv vc fromLabel target ρ := by
        intro ρ
        cases targetFound : vc.blocks[target]? <;> simp [edgeEnvAt,edgeEnv,found,args,targetFound]
      exact VNext.goto last successor (by rwa [same] at copied)

theorem EdgeLegacyCompatible.star {V W : Type} {vc : VCode} {edges : Array (Array (Array Reg))}
    {sem : ISem V W} (compatible : EdgeLegacyCompatible vc edges)
    {a b : VConf V W} (steps : Star (VStepAt vc edges sem) a b) : Star (VStep vc sem) a b := by
  induction steps with
  | refl a => exact .refl a
  | step first rest ih => exact .step (compatible.step first) ih

end Backend.Proof

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false

/-- Actual edge-field equality transports the full ABI-aware observation to
the existing compiler/checker/linker contract, retaining the chosen initial
register file, trap code, return pins and memory deallocation. -/
theorem RunOkABIAt.legacyCompatible {W : Type} {f : Clif.Function} {vc : VCode}
    {edges : Array (Array (Array Reg))} {sem : ISem CV W}
    (compatible : EdgeLegacyCompatible vc edges) {MR : MemRelTW W}
    {slots : List (Clif.SlotId × Nat)} {vs : VState CV W} {o : Clif.Outcome}
    (source : RunOkABIAt f vc edges sem MR slots vs o) : RunOkABI f vc sem MR slots vs o := by
  cases o with
  | returned vals cm =>
    obtain ⟨us,outs,w,cm0,reached,rest⟩ := source
    obtain ⟨b,k,ρ,w₁,vb,ops,outputs,path,tail⟩ := reached
    exact ⟨us,outs,w,cm0,⟨b,k,ρ,w₁,vb,ops,outputs,compatible.star path,tail⟩,rest⟩
  | trapped code =>
    obtain ⟨b,k,ρ,w,vb,i,ops,outs,w',path,tail⟩ := source
    exact ⟨b,k,ρ,w,vb,i,ops,outs,w',compatible.star path,tail⟩
  | _ => trivial

end Backend.Stock.Proof
