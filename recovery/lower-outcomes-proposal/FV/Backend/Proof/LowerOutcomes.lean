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

end Backend.Proof.Driver
