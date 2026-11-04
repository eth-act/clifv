import FV.Backend.Proof.LoadConstant
import FV.Backend.Proof.RegallocCover
import FV.Backend.Proof.RelocProvEmit
import FV.Backend.Proof.UnwindTables
import FV.Concurrency.ArmAllocMem
import FV.Concurrency.ArmAllocLSX
import FV.Concurrency.Code
import FV.E2E.EmitEnc
import FV.E2E.EmitLabels
import FV.E2E.EmitNear
import FV.E2E.ExecReads
import FV.E2E.PairLines
import FV.E2E.RegLevelGoodX
import FV.E2E.RegLevelMove
import FV.Link.RelocShapeProof
import FV.E2E.ExecWrites
import FV.E2E.RegLevelFRFree
import FV.E2E.LinkArmX30Check

/-!
# The `loadConst64` line lemmas, for `loadConstLines`

Phase 1 of AG-2j (#554): one twin per per-line lemma about `loadConst64`, with the same
statement shape, so that phase 2 can make `loadConst64` equal to `loadConstLines`
(Cranelift's `Inst::load_constant`) and replace each proof by its twin. Each twin follows from
the shape lemma `mem_loadConstLines` (every line is `.ins i none` with `i` a
`movz`/`movn`/`movk`/`orr _, xzr, #_` of the destination register); `loadConstLines_enc` also
uses `loadConstLines_toArmInst`. The semantic twin `steps_loadConstLines` and the length twin
`loadConstLines_length` are in `FV/Backend/Proof/LoadConstant.lean`, with
`loadConstLines_ne_nil` (for the users of `loadConst64_eq` that need only a nonempty list).
Beyond the per-line lemmas of the brief: `loadConstLines_noStores` (`ExecWrites`),
`frLine_loadConstLines` (`RegLevelFRFree`) and `loadConstLines_x30` (for `spAdjLines_x30`).

This leaf module imports the modules that define the predicates; it is not imported by them.
-/

namespace Backend.Proof

open Backend

/-- Twin of `mem_loadConst64` (`FV/Backend/Proof/RegallocCover.lean`). -/
theorem mem_loadConstLines' {r : Reg} {v : Nat} {ln : Line} (h : ln ∈ loadConstLines r v) :
    ∃ x, ln = .ins x none ∧ x.hooked = false ∧ (Line.ins x none).plain = true := by
  obtain ⟨i, rfl, hf⟩ := mem_loadConstLines h
  rcases hf with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> exact ⟨_, rfl, rfl, rfl⟩

/-- Twin of `loadConst64_ins` (`FV/E2E/RegLevelMove.lean`). -/
theorem loadConstLines_ins (rd : Reg) (v : Nat) :
    ∀ ln ∈ loadConstLines rd v, ∃ i t, ln = .ins i t := by
  intro ln h
  obtain ⟨i, rfl, -⟩ := mem_loadConstLines h
  exact ⟨_, _, rfl⟩

/-- Twin of `loadConst64_noSecond` (`FV/E2E/PairLines.lean`). -/
theorem loadConstLines_noSecond (rd : Reg) (v : Nat) :
    ∀ ln ∈ loadConstLines rd v, lnSecond ln = false := by
  intro ln h
  obtain ⟨i, rfl, hf⟩ := mem_loadConstLines h
  rcases hf with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> rfl

/-- Twin of `loadConst64_tailFree` (`FV/E2E/RegLevelGoodX.lean`). -/
theorem loadConstLines_tailFree (rd : Reg) (v : Nat) :
    ∀ ln ∈ loadConstLines rd v, ln.tailFree = true := by
  intro ln h
  obtain ⟨i, rfl, hf⟩ := mem_loadConstLines h
  rcases hf with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> rfl

/-- Twin of `loadConst64_noLoads` (`FV/E2E/ExecReads.lean`). -/
theorem loadConstLines_noLoads (rd : Reg) (v : Nat) :
    ∀ x t, Line.ins x t ∈ loadConstLines rd v → x.loads = false := by
  intro x t h
  obtain ⟨i, e, hf⟩ := mem_loadConstLines h
  cases e
  rcases hf with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> rfl

/-- Twin of `loadConst64_free` (`FV/Link/RelocShapeProof.lean`). -/
theorem loadConstLines_lnFree (rd : Reg) (v : Nat) :
    ∀ ln ∈ loadConstLines rd v, lnFree ln = true := by
  intro ln h
  obtain ⟨i, rfl, hf⟩ := mem_loadConstLines h
  rcases hf with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> rfl

/-- Twin of `loadConst64_noStores` (`FV/E2E/ExecWrites.lean`). -/
theorem loadConstLines_noStores (rd : Reg) (v : Nat) :
    ∀ x t, Line.ins x t ∈ loadConstLines rd v → x.stores = false := by
  intro x t h
  obtain ⟨i, e, hf⟩ := mem_loadConstLines h
  cases e
  rcases hf with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> rfl

/-- Twin of `frLine_loadConst64` (`FV/E2E/RegLevelFRFree.lean`). -/
theorem frLine_loadConstLines (rd : Reg) (v : Nat) :
    ∀ x t, Line.ins x t ∈ loadConstLines rd v → x.frLine = false := by
  intro x t h
  obtain ⟨i, e, hf⟩ := mem_loadConstLines h
  cases e
  rcases hf with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> rfl

/-- No line is `x30`-exempt (for `E2E.spAdjLines_x30`, `FV/E2E/BackendTwoRunLE.lean`, which
case-splits `loadConst64_eq`). -/
theorem loadConstLines_x30 (rd : Reg) (v : Nat) :
    ∀ x t, Line.ins x t ∈ loadConstLines rd v → x.x30Exempt = false := by
  intro x t h
  obtain ⟨i, e, hf⟩ := mem_loadConstLines h
  cases e
  rcases hf with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> simp [Insn.x30Exempt]

namespace RelocProv

/-- Twin of `RelocProv.loadConst64_free` (`FV/Backend/Proof/RelocProvEmit.lean`). -/
theorem loadConstLines_free (rd : Reg) (v : Nat) :
    ∀ ln ∈ loadConstLines rd v, refFreeL ln = true := by
  intro ln h
  obtain ⟨i, rfl, hf⟩ := mem_loadConstLines h
  rcases hf with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> rfl

end RelocProv

namespace UnwindTables

/-- Twin of `UnwindTables.loadConst64_noCall` (`FV/Backend/Proof/UnwindTables.lean`). -/
theorem loadConstLines_noCall (rd : Reg) (v : Nat) :
    ∀ l ∈ loadConstLines rd v, l.isCall = false := by
  intro ln h
  obtain ⟨i, rfl, hf⟩ := mem_loadConstLines h
  rcases hf with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> rfl

end UnwindTables

end Backend.Proof

namespace E2E

open Backend Backend.Proof

/-- Twin of `E2E.loadConst64_enc` (`FV/E2E/EmitEnc.lean`). -/
theorem loadConstLines_enc {n : Nat} (hn : n ≤ 30) (v : Nat) :
    ∀ i t, Line.ins i t ∈ loadConstLines (.x n) v → i.encodable = true := by
  intro i t h
  obtain ⟨ai, ha⟩ := loadConstLines_toArmInst hn v ⟨0, fun _ => some 0⟩ i t h
  simp [Insn.encodable, Insn.encode, ha, Functor.map, Except.map]

namespace EmitLabels

/-- Twin of `EmitLabels.loadConst64_plain` (`FV/E2E/EmitLabels.lean`). -/
theorem loadConstLines_plain (rd : Reg) (v : Nat) : Plain (loadConstLines rd v) := by
  intro ln h
  obtain ⟨i, rfl, hf⟩ := mem_loadConstLines h
  rcases hf with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;>
    simp [lineDef, Line.labelsUsed, Insn.pcRelSpec?]

end EmitLabels

namespace EmitNear

/-- Twin of `EmitNear.loadConst64_nearOkB` (`FV/E2E/EmitNear.lean`). -/
theorem loadConstLines_nearOkB (rd : Reg) (v : Nat) :
    ∀ ln ∈ loadConstLines rd v, ln.nearOkB = true := by
  intro ln h
  obtain ⟨i, rfl, hf⟩ := mem_loadConstLines h
  rcases hf with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;>
    simp [Line.nearOkB, Line.nearTgt, Line.bOk, Insn.pcRelSpec?]

end EmitNear

end E2E

namespace Concurrency.Code

open Backend Backend.Proof

/-- Twin of `Code.kinds_loadConst64` (`FV/Concurrency/Code.lean`). -/
theorem kinds_loadConstLines (rd : Reg) (v : Nat) : kinds (loadConstLines rd v) = [] := by
  unfold kinds
  rw [List.filterMap_eq_nil_iff]
  intro ln h
  obtain ⟨i, rfl, hf⟩ := mem_loadConstLines h
  rcases hf with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> rfl

end Concurrency.Code

namespace Concurrency.ArmAllocThread

open Backend Backend.Proof

/-- Twin of `ArmAllocThread.noRet_loadConst64` (`FV/Concurrency/ArmAllocMem.lean`). -/
theorem noRet_loadConstLines (rd : Reg) (v : Nat) : NoRet (loadConstLines rd v) := by
  intro x t h
  obtain ⟨i, e, hf⟩ := mem_loadConstLines h
  cases e
  rcases hf with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> (intro h; cases h)

/-- Twin of `ArmAllocThread.preLines_loadConst64` (`FV/Concurrency/ArmAllocLSX.lean`). -/
theorem preLines_loadConstLines (rd : Reg) (v : Nat) : PreLines (loadConstLines rd v) := by
  intro ln h
  obtain ⟨i, rfl, hf⟩ := mem_loadConstLines h
  rcases hf with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> exact ⟨_, _, rfl, rfl⟩

end Concurrency.ArmAllocThread
