import FV.Backend.Proof.IselGeneric
import FV.Backend.Proof.VCodeSem
import FV.Arm.MinTheory

/-! Per-successor VCode execution. The existing single-vector semantics and
all its theorems remain unchanged. Allocation/checker consumers must use the
same per-successor vectors before production Stock cutover. -/
namespace Backend.Proof

/-- The selected outgoing vector copied into the actual successor parameters.
Control/CFG selection is supplied by VNextAt's actual succOf premise. -/
def edgeEnvAt {V : Type} (vc : VCode) (edges : Array (Array (Array Reg)))
    (b s index : Nat) (ρ : Nat → V) : Option (Nat → V) := do
  let sb ← vc.blocks[s]?
  let args ← edges[b]?.bind (·[index]?)
  if args.size = sb.params.size then
    let ps ← (sb.params.toList.mapM vregNum).toOption
    let xs ← (args.toList.mapM vregNum).toOption
    pure (parCopyEnv ρ ps xs)
  else none

/-- Parallel-copy semantics for actual per-successor vectors. -/
theorem edgeEnvAt_eq {V : Type} {vc : VCode} {edges : Array (Array (Array Reg))}
    {b s index : Nat} {sb : VBlock} {ps xs : List Nat}
    (target : vc.blocks[s]? = some sb)
    (args : edges[b]?.bind (·[index]?) = some (xs.map (fun n => Reg.vreg n .int)).toArray)
    (params : sb.params = (ps.map (fun n => Reg.vreg n .int)).toArray)
    (length : ps.length = xs.length) (ρ : Nat → V) :
    edgeEnvAt vc edges b s index ρ = some (parCopyEnv ρ ps xs) := by
  have numbers : ∀ ns : List Nat,List.mapM (vregNum ∘ fun n => Reg.vreg n RegClass.int) ns = .ok ns := by
    intro ns
    induction ns with
    | nil => rfl
    | cons n ns ih => simp [List.mapM_cons,vregNum,ih] <;> rfl
  simp [edgeEnvAt,target,args,params,length,Except.toOption,numbers]

variable {V W : Type} (vc : VCode) (edges : Array (Array (Array Reg))) (sem : ISem V W)

/-- VNext with the actual selected per-successor copy. All nonbranch clauses
retain the existing meaning and register/world update discipline. -/
inductive VNextAt (b k n : Nat) (i : MInst) (uses : List V) (ρ : Nat → V) (w : W) :
    Ctl → VConf V W → Prop
  | next : k + 1 < n → VNextAt b k n i uses ρ w .next (.run ⟨b,k+1,ρ,w⟩)
  | goto {j s ρ'} : k + 1 = n → succOf vc b j = some s → edgeEnvAt vc edges b s j ρ = some ρ' →
      VNextAt b k n i uses ρ w (.goto j) (.run ⟨s,0,ρ',w⟩)
  | ret {us} : i = .rets us → VNextAt b k n i uses ρ w .ret (.ret uses w)
  | halt : VNextAt b k n i uses ρ w .halt (.halt w)

/-- Actual VCode instructions and CFG, with Result.edgeArgs-style per-successor
copies. The instruction semantics, writes and world are unchanged. -/
inductive VStepAt : VConf V W → VConf V W → Prop
  | step {b k ρ w vb i ops outs w' ctl c'} :
      vc.blocks[b]? = some vb → vb.insts[k]? = some i → i.operands = .ok ops →
      sem i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) w = some (outs,w',ctl) →
      outs.length = (ops.toList.filter Operand.isDef).length →
      VNextAt vc edges b k vb.insts.size i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg))
        (writeV (writeV ρ (((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isEarly)))
          (((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isLate))) w' ctl c' →
      VStepAt (.run ⟨b,k,ρ,w⟩) c'
end Backend.Proof
