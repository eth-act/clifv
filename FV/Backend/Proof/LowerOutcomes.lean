import FV.Backend.Proof.LowerLemmas
import FV.Backend.Proof.TryRegs

/-! Stable VCode return/trap outcomes, separate from CLIF simulation proofs. -/
namespace Backend.Proof.Driver
open Backend Backend.Proof

/-- From `vs`, the VCode run reaches an instruction that halts with trap code `c`. -/
def VTrapFrom {W : Type} (vc : VCode) (sem : ISem CV W) (vs : VState CV W) (c : Clif.TrapCode) :
    Prop :=
  ∃ b k ρ w vb i ops outs w', Star (VStep vc sem) (.run vs) (.run ⟨b, k, ρ, w⟩) ∧
    vc.blocks[b]? = some vb ∧ vb.insts[k]? = some i ∧ i.operands = .ok ops ∧
    sem i (vuses ops ρ) w = some (outs, w', .halt) ∧ trapCode? i = some c

/-- From `vs`, the VCode run executes `rets us` with use values `vals`, final world `w`. -/
def VRetFrom {W : Type} (vc : VCode) (sem : ISem CV W) (vs : VState CV W) (us : List (Reg × Reg))
    (vals : List CV) (w : W) : Prop :=
  ∃ b k ρ w₁ vb ops outs, Star (VStep vc sem) (.run vs) (.run ⟨b, k, ρ, w₁⟩) ∧
    vc.blocks[b]? = some vb ∧ vb.insts[k]? = some (.rets us) ∧
    (MInst.rets us).operands = .ok ops ∧ vals = vuses ops ρ ∧
    sem (.rets us) vals w₁ = some (outs, w, .ret)

theorem VTrapFrom.prefix {W : Type} {vc : VCode} {sem : ISem CV W} {vs vs' : VState CV W}
    {c : Clif.TrapCode} (h : Star (VStep vc sem) (.run vs) (.run vs')) (h' : VTrapFrom vc sem vs' c) :
    VTrapFrom vc sem vs c := by
  obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hs, h1⟩ := h'
  exact ⟨b, k, ρ, w, vb, i, ops, outs, w', h.trans hs, h1⟩

theorem VRetFrom.prefix {W : Type} {vc : VCode} {sem : ISem CV W} {vs vs' : VState CV W}
    {us : List (Reg × Reg)} {vals : List CV} {w : W}
    (h : Star (VStep vc sem) (.run vs) (.run vs')) (h' : VRetFrom vc sem vs' us vals w) :
    VRetFrom vc sem vs us vals w := by
  obtain ⟨b, k, ρ, w₁, vb, ops, outs, hs, h1⟩ := h'
  exact ⟨b, k, ρ, w₁, vb, ops, outs, h.trans hs, h1⟩

/-- The arguments in the body-entry world `w` as the entry code reads them (the driver's entry
premise): a register-passed parameter in its argument register (low bits), a stack-passed one
in the caller's outgoing area at `fp + 16 + off` (above the saved fp/lr pair), whose bytes avoid
the frame addresses `F`. -/
def ArgsAtEntry (F : BitVec 64 → Prop) (sig : Clif.Signature) (args : List Clif.Val)
    (w : Arm.ArmState) : Prop :=
  ∀ loc v, (loc, v) ∈ (locsOf sig).zip args → match loc with
    | .reg r => VHolds v (regVal w r)
    | .stack off =>
      Avoids F v.ty.bytes (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int))) ∧
      (Arm.read_mem_bytes v.ty.bytes (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int)))
        w).setWidth v.ty.width = v.bits


/-- `s'` is reachable from `s` by CLIF steps that continue. -/
inductive Reach (env : Clif.Env) (p : Clif.Program) : Clif.State → Clif.State → Prop
  | refl (s : Clif.State) : Reach env p s s
  | step {s s' s'' : Clif.State} : Clif.step env p s = .next s' → Reach env p s' s'' →
      Reach env p s s''


end Backend.Proof.Driver
