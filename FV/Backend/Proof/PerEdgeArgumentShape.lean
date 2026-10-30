import FV.Backend.Proof.PerEdgePrepareFilterFacts
import FV.Backend.Proof.StockOutgoingShape

namespace Backend.Proof.PerEdgePrep
open Backend Backend.Proof Backend.Stock.Proof
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def AllArguments (rows : Array EdgeRow) : Prop :=
  ∀ row ∈ rows.toList,RowArgumentShape row
private theorem empty_row : RowArgumentShape #[] := by simp [RowArgumentShape]
private theorem empty_rows : AllArguments #[] := by simp [AllArguments]
private theorem row_get {row : EdgeRow} (shape : RowArgumentShape row) (j : Nat) : ArgumentShape row[j]! := by
  cases found : row[j]? with
  | none => rw [getElem!_def,found]; exact (by intro r h; cases h)
  | some args =>
    rw [getElem!_def,found]
    exact shape args (Array.mem_toList_iff.mpr (Array.mem_of_getElem? found))
private theorem rows_get {rows : Array EdgeRow} (shape : AllArguments rows) (j : Nat) : RowArgumentShape rows[j]! := by
  cases found : rows[j]? with
  | none => rw [getElem!_def,found]; exact empty_row
  | some row =>
    rw [getElem!_def,found]
    exact shape row (Array.mem_toList_iff.mpr (Array.mem_of_getElem? found))
private theorem rows_push {rows : Array EdgeRow} (shape : AllArguments rows) {row : EdgeRow}
    (shaped : RowArgumentShape row) : AllArguments (rows.push row) := by
  intro rs member
  simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
  rcases member with old | same
  · exact shape rs old
  · subst rs; exact shaped
private theorem singleton_row {args : Array Reg} (shape : ArgumentShape args) : RowArgumentShape #[args] := by
  simpa [RowArgumentShape] using shape
private theorem row_empty_at {row : EdgeRow} (shape : RowArgumentShape row) (j : Nat) :
    RowArgumentShape (row.set! j #[]) := by
  intro args member
  obtain ⟨k,found⟩ := List.mem_iff_getElem?.mp member
  rw [Array.getElem?_toList,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds] at found
  split at found
  · split at found
    · cases found; exact (by intro r h; cases h)
    · cases found
  · exact shape args (Array.mem_toList_iff.mpr (Array.mem_of_getElem? found))

private theorem inner_shape (preds : Array (Array Nat)) (xs : List ((Nat × Label) × Nat))
    (st : InnerState) (generated : AllArguments st.2.2.1) (current : RowArgumentShape st.2.2.2.1) :
    AllArguments (xs.foldl (innerStepAt preds) st).2.2.1 ∧
    RowArgumentShape (xs.foldl (innerStepAt preds) st).2.2.2.1 := by
  induction xs generalizing st with
  | nil => exact ⟨generated,current⟩
  | cons x xs ih =>
    rw [List.foldl_cons]
    apply ih
    · unfold innerStepAt
      split
      · exact rows_push generated (singleton_row (row_get current x.2))
      · exact generated
    · unfold innerStepAt
      split
      · exact row_empty_at current x.2
      · exact current

private def OuterShape (st : OuterState) : Prop := AllArguments st.2.2.1 ∧ AllArguments st.2.2.2.2
private theorem outer_step_shape {succs preds : Array (Array Nat)} {outgoing : Array EdgeRow}
    (source : AllArguments outgoing) {x : VBlock × Nat} {st next : OuterState}
    (before : OuterShape st) (run : outerStepAt succs preds outgoing x st = .ok (.yield next)) : OuterShape next := by
  unfold outerStepAt at run
  dsimp only at run
  split at run
  · cases run
    exact ⟨rows_push before.1 (rows_get source x.2),before.2⟩
  · split at run
    · rename_i t last
      split at run
      · rename_i t' targets
        cases run
        have result := inner_shape preds ((succs[x.2]!.zip t.targets.toArray).zipIdx).toList (st.1,st.2.2.2.1,st.2.2.2.2,outgoing[x.2]!,#[])
          before.2 (rows_get source x.2)
        exact ⟨rows_push before.1 result.2,result.1⟩
      · cases run
    · cases run
private theorem outer_not_done (succs preds : Array (Array Nat)) (outgoing : Array EdgeRow)
    (x : VBlock × Nat) (st next : OuterState) : outerStepAt succs preds outgoing x st ≠ .ok (.done next) := by
  unfold outerStepAt
  dsimp only
  repeat' split
  all_goals simp [bind,Except.bind,pure,Except.pure]

/-- Actual indexed preparation preserves virtual-int class for every outgoing
vector, including vectors moved onto inserted critical-edge blocks. The proof
follows executable filtering, splitting folds, row edits and final RPO. -/
theorem prepareAt_argument_shape {vc : VCode} {edges : Array EdgeRow} {p : EdgeVCode}
    (run : prepareAt vc edges = .ok p)
    (original : ∀ (b j : Nat) (row : EdgeRow) (args : Array Reg),
      edges[b]? = some row → row[j]? = some args → ArgumentShape args) :
    ∀ (b j : Nat) (row : EdgeRow) (args : Array Reg),
      p.edges[b]? = some row → row[j]? = some args → ArgumentShape args := by
  obtain ⟨ss0,ps0,ss1,ps1,ss2,ps2,st,cfg0,cfg1,loop,cfg2,result⟩ := prepareAt_stages run
  have keptShape : AllArguments ((keptAt vc edges ss0).map Prod.snd) := by
    intro row member
    obtain ⟨j,found⟩ := List.mem_iff_getElem?.mp member
    rw [Array.getElem?_toList,Array.getElem?_map] at found
    obtain ⟨pair,atPair,same⟩ := Option.map_eq_some_iff.mp found
    subst row
    obtain ⟨bound,equal⟩ := Array.getElem?_eq_some_iff.mp atPair
    have origin := keptAt_source (vc := vc) (edges := edges) (ss := ss0) bound
    rw [equal] at origin
    obtain ⟨b,sourceBlock,sourceRow,_⟩ := origin
    intro args inside
    obtain ⟨k,atArgs⟩ := List.mem_iff_getElem?.mp inside
    exact original b k _ args sourceRow (by simpa only [Array.getElem?_toList] using atArgs)
  have shaped : OuterShape st := by
    rw [← Array.forIn_toList] at loop
    exact Prep.forIn_inv (outerStepAt ss1 ps1 ((keptAt vc edges ss0).map Prod.snd)) _
      (fun _ st => OuterShape st) (fun _ _ _ _ _ before step => outer_step_shape keptShape before step)
      (outer_not_done _ _ _) _ st ⟨empty_rows,empty_rows⟩ loop
  have combined : AllArguments (st.2.2.1 ++ st.2.2.2.2) := by
    intro row member
    rw [Array.toList_append,List.mem_append] at member
    exact member.elim (shaped.1 row) (shaped.2 row)
  intro b j row args atRow atArgs
  rw [result] at atRow
  dsimp only at atRow
  rw [Array.getElem?_map] at atRow
  obtain ⟨i,_,same⟩ := Option.map_eq_some_iff.mp atRow
  subst row
  exact rows_get combined i args (Array.mem_toList_iff.mpr (Array.mem_of_getElem? atArgs))

end Backend.Proof.PerEdgePrep
