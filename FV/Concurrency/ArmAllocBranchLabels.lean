import FV.Concurrency.ArmAllocBranch

/-!
# The allocated function's block labels are distinct (#553)

`af_nodup` and `succ_of_label` (formerly in `ArmAllocBranch`), on the `MachBuffer` emitter: every
block is a segment of the emission plan (`emitOrder` lists every block once, `emitOrder_perm`;
segment `i` is block `emitOrder[i]`'s, `segsOf_spec`), each segment's lines start with its block's
label line (`segLines`), branch relaxation keeps the defined labels (`relaxLines_spec`) and
`labelOffsets` defines every label once (`labelOffsets_go_nodup`).
-/

namespace Concurrency.ArmAllocThread

open Arm Backend Backend.Proof

/-- The segments' block labels are among the labels their lines define, in order. -/
theorem segLines_defs : ∀ (ss : List Seg) (os : List (List Line)), os.length = ss.length →
    (ss.map fun s => Lbl.block s.label).Sublist (E2E.EmitLabels.defs (segLines ss os))
  | [], _, _ => List.nil_sublist _
  | _ :: _, [], h => by simp at h
  | s :: ss, o :: os, h => by
    have ih := segLines_defs ss os (by simpa using h)
    simp only [segLines, List.map_cons, List.cons_append, E2E.EmitLabels.defs_cons,
      E2E.EmitLabels.lineDef, Option.toList_some, List.singleton_append,
      E2E.EmitLabels.defs_append]
    exact ih.trans (List.sublist_append_right _ _) |>.trans (List.sublist_append_right _ _)
      |>.cons_cons _

/-- **The allocated function's block labels are distinct** (as lines: `labelOffsets` defines
every label once). -/
theorem af_nodup {R : RL} (hR : R.Wf) : (R.af.blocks.toList.map fun p => Lbl.block p.1).Nodup := by
  obtain ⟨p, hp, hL, -⟩ := Backend.emitFunc_ok hR.emit
  obtain ⟨hseg, hlen, -⟩ := Backend.emitPlan_spec hp
  obtain ⟨hl, -, hss⟩ := Backend.segsOf_spec hseg
  have hn := (labelOffsets_go_nodup (show labelOffsets.go R.fa.lines.toList 0 {} = .ok R.lm
    from hR.lm)).1
  rw [hL, E2E.EmitLabels.defs_append, (E2E.EmitLabels.relaxLines_spec _ _).1, Plan.lines,
    E2E.EmitLabels.defs_append] at hn
  have hs := (segLines_defs _ _ hlen).nodup (List.nodup_append.1 (List.nodup_append.1 hn).1).1
  -- the segments' labels are the blocks' in `emitOrder`
  have he : (p.segs.map fun s => Lbl.block s.label) =
      (emitOrder R.af).map fun x => Lbl.block x.1.1 := by
    apply List.ext_getElem?
    intro n
    simp only [List.getElem?_map]
    cases hk : p.segs[n]? with
    | none =>
      have : (emitOrder R.af).length ≤ n := by
        rw [← hl]; exact List.getElem?_eq_none_iff.mp hk
      simp [List.getElem?_eq_none_iff.mpr this]
    | some s =>
      obtain ⟨code, -, -, -, hb, -⟩ := hss n s hk
      simp [hb]
  rw [he] at hs
  have hz : (R.af.blocks.toList.zipIdx.map fun x => Lbl.block x.1.1) =
      R.af.blocks.toList.map fun p => Lbl.block p.1 := by
    have : R.af.blocks.toList.zipIdx.map (·.1) = R.af.blocks.toList := by
      rw [List.zipIdx_eq_zip_range', List.map_fst_zip (by simp)]
    conv => rhs; rw [← this]
    rw [List.map_map]; rfl
  rw [← hz]
  exact ((emitOrder_perm R.af).map fun x => Lbl.block x.1.1).nodup_iff.mp hs

/-- **The block with the label of block `b + 1`** is block `b + 1`. -/
theorem succ_of_label {R : RL} (hR : R.Wf) {st b : Nat} {vs : VBlock} {items : Array RItem}
    (hvs : R.vc.blocks[st]? = some vs) (hit : R.rf.blocks[st]? = some items)
    {p : Label × Array AInst} (hp : R.af.blocks[b + 1]? = some p) (hl : p.1 = vs.label) :
    st = b + 1 := by
  obtain ⟨⟨-, -, -, hbl⟩, -⟩ := hR.alloc.ok
  obtain ⟨code, -, haf⟩ := hbl st vs items hvs hit
  refine nodup_idx (af_nodup hR) (x := Lbl.block vs.label) ?_ ?_
  · simp [haf]
  · simp [hp, hl]

end Concurrency.ArmAllocThread
