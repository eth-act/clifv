import FV.Arm.MinTheory
import FV.Backend.Proof.IselInterp
import FV.Backend.Proof.PerEdgeSpillStateAt

namespace Backend.Proof.PerEdgeSpill
open Backend Backend.Proof.Spill
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def entryFold (rs : List Reg) (a : AState) : AState :=
  rs.foldl (fun a r => AState.put a (.reg r) [.entry r]) a
private theorem entryFold_size (rs : List Reg) (a : AState) : (entryFold rs a).size = a.size := by
  induction rs generalizing a with
  | nil => rfl
  | cons r rs ih => exact (ih _).trans (size_put _ _ _)
private theorem entryFold_keeps (rs : List Reg) (a : AState) (r : Reg)
    (valid : ∃ i,(Loc.reg r).index = some i ∧ i < a.size)
    (held : Sym.entry r ∈ a.get (.reg r)) : Sym.entry r ∈ (entryFold rs a).get (.reg r) := by
  induction rs generalizing a with
  | nil => exact held
  | cons x rs ih =>
    change Sym.entry r ∈ (entryFold rs (AState.put a (.reg x) [.entry x])).get (.reg r)
    apply ih
    · obtain ⟨i,index,bound⟩ := valid
      exact ⟨i,index,by rw [size_put]; exact bound⟩
    · by_cases same : x = r
      · subst x
        obtain ⟨i,index,bound⟩ := valid
        rw [get_put_self index bound]
        exact List.mem_singleton_self _
      · rw [get_put_ne (by intro eq; injection eq with same'; exact same same')]
        exact held
private theorem entryFold_has (rs : List Reg) (a : AState) (r : Reg)
    (valid : ∃ i,(Loc.reg r).index = some i ∧ i < a.size) (member : r ∈ rs) :
    Sym.entry r ∈ (entryFold rs a).get (.reg r) := by
  induction rs generalizing a with
  | nil => cases member
  | cons x rs ih =>
    change Sym.entry r ∈ (entryFold rs (AState.put a (.reg x) [.entry x])).get (.reg r)
    rcases List.mem_cons.mp member with rfl | member
    · apply entryFold_keeps (a := AState.put a (.reg r) [.entry r])
      · obtain ⟨i,index,bound⟩ := valid
        exact ⟨i,index,by rw [size_put]; exact bound⟩
      · obtain ⟨i,index,bound⟩ := valid
        rw [get_put_self index bound]
        exact List.mem_singleton_self _
    · apply ih _ _ member
      obtain ⟨i,index,bound⟩ := valid
      exact ⟨i,index,by rw [size_put]; exact bound⟩

/-- The actual function entry state contains each callee-saved entry symbol in
its physical register. This is a lower bound, complementary to soundness's
upper-bound entry-state lemma. -/
theorem entryState_saved {n : Nat} (large : 64 ≤ n) {r : Reg} (member : r ∈ calleeSaved) :
    Sym.entry r ∈ (entryState n).get (.reg r) := by
  obtain ⟨i,index,bound⟩ := reg_index (calleeSaved_ok r member).1
  exact entryFold_has calleeSaved (Array.replicate n []) r ⟨i,index,by simp; omega⟩ member

/-- Function entry executes the actual spill-save prefix and establishes the
canonical empty-availability body invariant. In particular the saved entry
values are derived from entryState, not supplied as an invariant premise. -/
theorem spill_entry_saves_runs {vc : VCode} {edges : Array (Array (Array Reg))} {c : CheckCtx}
    (saved : c.rf.saved = calleeSaved) {vb : VBlock} (nonempty : vb.insts.size ≠ 0) :
    Spill.Runs c vb 0 spillSaves (entryState (stateSizeAt vc edges))
      (fun k a => k = 0 ∧ GoodAt vc edges (fun _ => false) a ∧
        (bodyStateAt vc edges (fun _ => false)).le a = true) := by
  have size : (entryState (stateSizeAt vc edges)).size = stateSizeAt vc edges := by
    exact (entryFold_size calleeSaved _).trans (by simp)
  rw [spillSaves_eq]
  have run := Spill.Runs.moves (c := c) (vb := vb) (k := 0) (Ne.symm nonempty)
    (calleeSaved.map fun r => (Loc.reg r,Loc.save r)) (entryState (stateSizeAt vc edges))
    (by
      intro m member
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp member
      exact (checkMove_saves c saved _ hr).1)
    (by
      intro m member m' member'
      obtain ⟨r,_,rfl⟩ := List.mem_map.mp member
      obtain ⟨r',_,rfl⟩ := List.mem_map.mp member'
      intro eq; cases eq)
    (by
      simp only [List.map_map]
      exact nodup_map_of_inj (f := fun r => Loc.save r) (g := id) calleeSaved_nodup
        (fun _ _ _ _ same => by injection same))
    (by
      intro m member
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp member
      obtain ⟨i,index,bound⟩ := save_index hr
      exact ⟨i,index,by rw [size]; unfold stateSizeAt; omega⟩)
  apply run.mono
  intro k a result
  have good : GoodAt vc edges (fun _ => false) a := by
    constructor
    · exact result.2.1.trans size
    · intro v cl n available; cases available
    · intro r member
      rw [result.2.2.1 (.reg r,Loc.save r) (List.mem_map.mpr ⟨r,member,rfl⟩)]
      exact entryState_saved (by unfold stateSizeAt; omega) member
  exact ⟨result.1,good,bodyStateAt_le good⟩

end Backend.Proof.PerEdgeSpill
