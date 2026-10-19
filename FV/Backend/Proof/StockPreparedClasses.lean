import FV.Backend.Proof.StockWholeClasses
import FV.Backend.Proof.StockPreparedInstructionClasses
namespace Backend.Stock.Proof.PreparedClassesDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgePrep
open Backend.Stock.Proof.WholeClassesDraft Backend.Stock.Proof.PreparedInstructionClassDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

private def GA (cls : Array RegClass) (rs : Array Reg) : Prop := ∀ r ∈ rs.toList,IntCls cls r
private def GR (cls : Array RegClass) (row : EdgeRow) : Prop := ∀ rs ∈ row.toList,GA cls rs
private def GE (cls : Array RegClass) (rows : Array EdgeRow) : Prop := ∀ row ∈ rows.toList,GR cls row
private def GB (cls : Array RegClass) (bs : Array VBlock) : Prop :=
  ∀ b ∈ bs.toList,∀ r ∈ b.params.toList ++ b.branchArgs.toList,IntCls cls r
private theorem get_row {cls : Array RegClass} {rows : Array EdgeRow} (held : GE cls rows) (i : Nat) : GR cls rows[i]! := by
  cases found : rows[i]? with
  | none =>
    simp only [getElem!_def,found,Option.getD_none]
    change GR cls (#[] : EdgeRow)
    simp [GR]
  | some row =>
    simp only [getElem!_def,found,Option.getD_some]
    exact held row (Array.mem_toList_iff.mpr (Array.mem_of_getElem? found))
private theorem get_args {cls : Array RegClass} {row : EdgeRow} (held : GR cls row) (i : Nat) : GA cls row[i]! := by
  cases found : row[i]? with
  | none =>
    simp only [getElem!_def,found,Option.getD_none]
    change GA cls (#[] : Array Reg)
    simp [GA]
  | some rs =>
    simp only [getElem!_def,found,Option.getD_some]
    exact held rs (Array.mem_toList_iff.mpr (Array.mem_of_getElem? found))
private theorem get_block {cls : Array RegClass} {bs : Array VBlock} (held : GB cls bs) (i : Nat) :
    ∀ r ∈ bs[i]!.params.toList ++ bs[i]!.branchArgs.toList,IntCls cls r := by
  cases found : bs[i]? with
  | none =>
    simp only [getElem!_def,found,Option.getD_none]
    change ∀ r ∈ ([] : List Reg),IntCls cls r
    simp
  | some b =>
    simp only [getElem!_def,found,Option.getD_some]
    exact held b (Array.mem_toList_iff.mpr (Array.mem_of_getElem? found))
private theorem push_good {α : Type} {P : α → Prop} {xs : Array α} {x : α}
    (held : ∀ a ∈ xs.toList,P a) (fresh : P x) : ∀ a ∈ (xs.push x).toList,P a := by
  intro a member
  simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
  rcases member with old | rfl
  · exact held a old
  · exact fresh
private theorem set_good {α : Type} {P : α → Prop} {xs : Array α} {x : α} {i : Nat}
    (held : ∀ a ∈ xs.toList,P a) (fresh : P x) : ∀ a ∈ (xs.set! i x).toList,P a := by
  intro a member
  obtain ⟨j,found⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
  rw [Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds] at found
  split at found
  · split at found
    · cases found; exact fresh
    · cases found
  · exact held a (Array.mem_toList_iff.mpr (Array.mem_of_getElem? found))
private def InnerGood (cls : Array RegClass) (st : InnerState) : Prop :=
  GB cls st.2.1 ∧ GE cls st.2.2.1 ∧ GR cls st.2.2.2.1
private theorem inner_good (preds : Array (Array Nat)) (x : (Nat × Label) × Nat)
    {cls : Array RegClass} {st : InnerState} (old : InnerGood cls st) : InnerGood cls (innerStepAt preds st x) := by
  unfold innerStepAt
  split
  · have typed := get_args old.2.2 x.2
    refine ⟨?_,?_,?_⟩
    · apply push_good (P := fun b : VBlock => ∀ r ∈ b.params.toList ++ b.branchArgs.toList,IntCls cls r) old.1
      simpa only [GA,Array.toList_empty,List.nil_append] using typed
    · apply push_good (P := GR cls) old.2.1
      intro rs member
      simp only [Array.toList_push,Array.toList_empty,List.mem_singleton] at member
      subst rs
      exact typed
    · exact set_good (P := GA cls) old.2.2 (by simp [GA])
  · exact old
private theorem inner_fold_good (preds : Array (Array Nat)) (xs : List ((Nat × Label) × Nat))
    {cls : Array RegClass} {st : InnerState} (old : InnerGood cls st) :
    InnerGood cls (xs.foldl (innerStepAt preds) st) := by
  induction xs generalizing st with
  | nil => exact old
  | cons x xs ih => exact ih (inner_good preds x old)
private def OuterGood (cls : Array RegClass) (st : OuterState) : Prop :=
  GB cls st.2.1 ∧ GE cls st.2.2.1 ∧ GB cls st.2.2.2.1 ∧ GE cls st.2.2.2.2
private theorem outer_good {succs preds : Array (Array Nat)} {rows : Array EdgeRow}
    {cls : Array RegClass} (outgoing : GE cls rows) {x : VBlock × Nat} {st next : OuterState}
    (block : ∀ r ∈ x.1.params.toList ++ x.1.branchArgs.toList,IntCls cls r)
    (old : OuterGood cls st) (run : outerStepAt succs preds rows x st = .ok (.yield next)) : OuterGood cls next := by
  unfold outerStepAt at run
  dsimp only at run
  split at run
  · cases run
    exact ⟨push_good (P := fun b : VBlock => ∀ r ∈ b.params.toList ++ b.branchArgs.toList,IntCls cls r) old.1 block,
      push_good (P := GR cls) old.2.1 (get_row outgoing x.2),old.2.2⟩
  · split at run
    · rename_i t last
      let initial : InnerState := (st.1,st.2.2.2.1,st.2.2.2.2,rows[x.2]!,#[])
      let inner := ((succs[x.2]!.zip t.targets.toArray).zipIdx).toList.foldl (innerStepAt preds) initial
      have innerInv : InnerGood cls inner := inner_fold_good preds _ ⟨old.2.2.1,old.2.2.2,get_row outgoing x.2⟩
      split at run
      · cases run
        refine ⟨?_,push_good (P := GR cls) old.2.1 innerInv.2.2,innerInv.1,innerInv.2.1⟩
        exact push_good (P := fun b : VBlock => ∀ r ∈ b.params.toList ++ b.branchArgs.toList,IntCls cls r) old.1 block
      · cases run
    · cases run
private theorem outer_no_done (succs preds : Array (Array Nat)) (rows : Array EdgeRow)
    (x : VBlock × Nat) (st next : OuterState) : outerStepAt succs preds rows x st ≠ .ok (.done next) := by
  intro run
  unfold outerStepAt at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals cases run
private theorem outer_loop_good {V : Array VBlock} {rows : Array EdgeRow}
    {succs preds : Array (Array Nat)} {cls : Array RegClass} {st : OuterState}
    (blocks : GB cls V) (outgoing : GE cls rows)
    (run : forIn V.zipIdx (Prep.next0Of V,#[],#[],#[],#[]) (outerStepAt succs preds rows) = .ok st) :
    OuterGood cls st := by
  rw [← Array.forIn_toList] at run
  apply Prep.forIn_inv (outerStepAt succs preds rows) V.zipIdx.toList (fun _ st => OuterGood cls st) ?_
    (outer_no_done succs preds rows) (Prep.next0Of V,#[],#[],#[],#[]) st (by simp [OuterGood,GB,GE]) run
  intro k x before after found held step
  rw [Array.toList_zipIdx,List.getElem?_zipIdx] at found
  have input : ∃ vb,V.toList[k]? = some vb ∧ x = (vb,k) := by
    cases lookup : V.toList[k]? with
    | none => rw [lookup] at found; cases found
    | some vb =>
      rw [lookup] at found
      simp only [Option.map_some,Option.some.injEq,Nat.zero_add] at found
      exact ⟨vb,rfl,found.symm⟩
  obtain ⟨vb,lookup,rfl⟩ := input
  exact outer_good outgoing (blocks vb (List.mem_of_getElem? lookup)) held step

/-- Indexed preparation preserves the complete ClassesOk interfaces and the
virtual integer classes of ALL executable successor vectors, including new
synthetic blocks and their copied arguments. Original source conditions and
actual successful Stock/prepare runs supply every invariant internally. -/
theorem stock_prepared_classes {f : Clif.Function} {result : Result}
    (scope : LowerScope f) (lowered : Stock.lower f = .ok result) {p : EdgeVCode}
    (prepared : prepareAt result.code result.edgeArgs = .ok p) :
    ClassesOkM p.code ∧ ClassesOk p.code ∧
      ∀ row ∈ p.edges.toList,∀ args ∈ row.toList,∀ r ∈ args.toList,IntCls p.code.classes r := by
  have original := stock_lower_classes scope lowered
  have instructions := stock_prepared_instruction_classes scope lowered prepared
  obtain ⟨ss0,ps0,ss1,ps1,ss2,ps2,st,cfg0,cfg1,loop,cfg2,resultEq⟩ := prepareAt_stages prepared
  have originalBlocks : GB result.code.classes result.code.blocks := stock_lower_integer_block_classes scope lowered
  have retainedBlocks : GB result.code.classes ((keptAt result.code result.edgeArgs ss0).map Prod.fst) := by
    intro b member
    obtain ⟨pair,present,rfl⟩ := Array.mem_map.mp (Array.mem_toList_iff.mp member)
    obtain ⟨k,lookup⟩ := Array.mem_iff_getElem?.mp present
    have found := keptAt_source (Array.getElem?_eq_some_iff.mp lookup).1
    obtain ⟨index,source,edge,live⟩ := found
    obtain ⟨bound,same⟩ := Array.getElem_of_getElem? lookup
    rw [same] at source
    exact originalBlocks _ (Array.mem_toList_iff.mpr (Array.mem_of_getElem? source))
  have retainedEdges : GE result.code.classes ((keptAt result.code result.edgeArgs ss0).map Prod.snd) := by
    intro row member
    obtain ⟨pair,present,rfl⟩ := Array.mem_map.mp (Array.mem_toList_iff.mp member)
    obtain ⟨k,lookup⟩ := Array.mem_iff_getElem?.mp present
    obtain ⟨index,source,edge,live⟩ := keptAt_source (Array.getElem?_eq_some_iff.mp lookup).1
    obtain ⟨bound,same⟩ := Array.getElem_of_getElem? lookup
    rw [same] at edge
    exact original.2.2 _ (Array.mem_toList_iff.mpr (Array.mem_of_getElem? edge))
  have final := outer_loop_good retainedBlocks retainedEdges loop
  have blocksAll : GB result.code.classes (st.2.1 ++ st.2.2.2.1) := by
    intro b member
    rcases (show b ∈ st.2.1.toList ∨ b ∈ st.2.2.2.1.toList from by simpa using member) with left | right
    · exact final.1 b left
    · exact final.2.2.1 b right
  have edgesAll : GE result.code.classes (st.2.2.1 ++ st.2.2.2.2) := by
    intro row member
    rcases (show row ∈ st.2.2.1.toList ∨ row ∈ st.2.2.2.2.toList from by simpa using member) with left | right
    · exact final.2.1 row left
    · exact final.2.2.2 row right
  have full : ClassesOkM p.code := by
    refine ⟨instructions,?_⟩
    intro b member r inside
    rw [resultEq] at member
    obtain ⟨i,present,rfl⟩ := Array.mem_map.mp (Array.mem_toList_iff.mp member)
    obtain ⟨typed,n,shape⟩ := get_block blocksAll i r inside
    have classes := (prepareAt_fields prepared).2.1
    exact ⟨n,.int,shape,by rw [classes]; exact regCls_vreg.mp (by rw [← shape]; exact typed)⟩
  refine ⟨full,classesOk_of full,?_⟩
  intro row member args present r inside
  rw [resultEq] at member
  obtain ⟨i,atRow,rfl⟩ := Array.mem_map.mp (Array.mem_toList_iff.mp member)
  have classes := (prepareAt_fields prepared).2.1
  rw [classes]
  exact get_row edgesAll i args present r inside
end Backend.Stock.Proof.PreparedClassesDraft
