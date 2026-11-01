import FV.Backend.EdgeSplit
import FV.Backend.Proof.PerEdgeLegacyCompatible

/-! A successful edge split transports every per-successor observation from the initial
state to the legacy observation of the split code. The indexed preparation relation carries
the runs; the legacy compatibility check turns them into legacy runs. -/
namespace Backend.Proof
open Backend Backend.Proof.Driver
set_option autoImplicit false

theorem splitEdgesChecked_ok {vc : VCode} {edges : Array (Array (Array Reg))} {split : EdgeVCode}
    (h : splitEdgesChecked vc edges = .ok split) :
    splitEdges vc edges = .ok split ∧ PerEdgePrep.prepCheckAt vc edges split = true ∧
      edgeLegacyCompatibleB split.code split.edges = true := by
  unfold splitEdgesChecked at h
  obtain ⟨p,run,h⟩ := Except.bind_ok h
  cases checked : (PerEdgePrep.prepCheckAt vc edges p && edgeLegacyCompatibleB p.code p.edges) with
  | false => simp [checked,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at h
  | true =>
    simp only [checked,Bool.not_true,ite_false,pure,Except.pure,Except.ok.injEq] at h
    cases h
    exact ⟨run,(Bool.and_eq_true _ _).mp checked⟩

theorem edgeLegacyCompatibleB_sound {vc : VCode} {edges : Array (Array (Array Reg))}
    (h : edgeLegacyCompatibleB vc edges = true) : EdgeLegacyCompatible vc edges := by
  intro b index target successor
  unfold edgeLegacyCompatibleB at h
  unfold succOf at successor
  split at h
  · rename_i ss ps cfg
    rw [cfg] at successor
    change ss[b]?.bind (·[index]?) = some target at successor
    cases row : ss[b]? with
    | none => rw [row] at successor; cases successor
    | some sb =>
      rw [row,Option.bind_some] at successor
      have rowBound : b < ss.size := (Array.getElem?_eq_some_iff.mp row).1
      have indexBound : index < sb.size := (Array.getElem?_eq_some_iff.mp successor).1
      have entry := all_range h rowBound
      cases block : vc.blocks[b]? with
      | none => simp [row,block] at entry
      | some vb =>
        simp only [row,block] at entry
        exact ⟨vb,rfl,of_decide_eq_true (all_range entry indexBound)⟩
  · cases h

end Backend.Proof

namespace Backend.Stock.Proof
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false

/-- A successful edge split turns the per-successor ABI observation from the entry into the
legacy one on the split code, for every outcome, initial register file and world. -/
theorem RunOkABIAt.split {W : Type} {f : Clif.Function} {vc : VCode}
    {edges : Array (Array (Array Reg))} {split : EdgeVCode} {sem : ISem CV W}
    (driver : DriverSemG sem) (h : splitEdgesChecked vc edges = .ok split) {MR : MemRelTW W}
    {slots : List (Clif.SlotId × Nat)} {ρ : Nat → CV} {w : W} {o : Clif.Outcome}
    (source : RunOkABIAt f vc edges sem MR slots ⟨0,0,ρ,w⟩ o) :
    RunOkABI f split.code sem MR slots ⟨0,0,ρ,w⟩ o := by
  obtain ⟨-,checked,legacy⟩ := splitEdgesChecked_ok h
  obtain ⟨returns,traps⟩ := PerEdgePrep.prep_sound driver checked ρ w
  apply RunOkABIAt.legacyCompatible (edgeLegacyCompatibleB_sound legacy)
  cases o with
  | returned vals cm =>
    obtain ⟨us,outs,w',cm0,reached,rest⟩ := source
    exact ⟨us,outs,w',cm0,returns us outs w' reached,rest⟩
  | trapped code => exact traps code source
  | _ => trivial

end Backend.Stock.Proof
