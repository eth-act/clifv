import FV.Link.UnwFnsComplete
import FV.E2E.RegLevelFrameSaved
import FV.E2E.DeadCleanupLinkCheck
import FV.E2E.SpillLower

/-!
# The frame check `savedCheck` on the allocations the pipeline lowers (S10g, #404)

`savedCheck vc rf = savedCheckRF vc rf && savedCheckAF vc rf af` (`FV/E2E/RegLevelFrameSaved.lean`)
is one of the per-function unwinding checks (`unwFnsB`). Here:

* **the allocation part `savedCheckRF` by construction**: `savedCheckRF_spill` for the spill
  allocation (`spillAlloc`: it saves every callee-saved register and writes no save slot after
  the saves) and `savedCheckRF_build` for regalloc2's answer as the backend reads it
  (`buildRFunc`: it saves every callee-saved register its allocation mentions, `used`, and
  regalloc2's locations are registers and spill slots); with `ctlCheck` (which `lowerRFunc`
  checks) for "no edge enters block 0". So `savedCheckRF_pipe`: the allocation the pipeline
  lowers (`allocResult vcp (readyAnswer vcp (raAnswer vcp o))`) passes it, for every allocator
  answer `o`.
* **the frame part `savedCheckAF`** (`savedCheckAF_of`): the save moves of block 0 become one
  `str` each at their save slots when the slots are below 32 KiB (`saveFrameB`). Since #479 the
  save slots come first in the frame, so `saveFrameB_always` proves it for every allocation of a
  function whose outgoing argument area is below 32560 bytes (`savedCheck_pipe_out`,
  `unwindRows_complete_frame_out` take that bound instead). The code after the saves must not
  start with another callee-save store (`leadOkB`: an allocator answer may store a callee-saved
  register into a spill slot right after the saves, which `checkAlloc` accepts and which
  `savedCheckAF` rightly rejects; a store through x16 counts too, `farSave`, on which
  `unwindRows` fails).
-/

namespace Link.EhCheck.Complete

set_option autoImplicit false

open Backend Backend.Proof E2E

/-! ## Items that write no save slot -/

/-- Item `it` writes no save slot. -/
def WNS : RItem → Prop
  | .move _ d => ∀ r, d ≠ .save r
  | .op _ ls => ∀ l ∈ ls.toList, ∀ r, l ≠ .save r

theorem wns_saveReg {it : RItem} (h : WNS it) : it.saveReg? = none := by
  cases it with
  | op k a => rfl
  | move s d =>
    cases s <;> cases d <;> simp only [RItem.saveReg?]
    rename_i r r'
    exact absurd rfl (h r')

/-- An item writing no save slot is `bodyOk` when every callee-saved register is saved. -/
theorem wns_bodyOk_all {it : RItem} (h : WNS it) : it.bodyOk calleeSaved = true := by
  have hw : ∀ l : Loc, (∀ r, l ≠ .save r) → bodyWritable calleeSaved l = true := by
    intro l hl
    cases l with
    | reg r => by_cases hr : r ∈ calleeSaved <;> simp [bodyWritable]
    | stack _ _ => rfl
    | save r => exact absurd rfl (hl r)
  cases it with
  | move s d => exact hw d h
  | op k ls =>
    simp only [RItem.bodyOk, Array.all_eq_true]
    intro i hi
    exact hw _ (h _ (Array.getElem_mem_toList hi))

/-- The save moves of the registers `rs`. -/
def saveMoves (rs : List Reg) : List RItem := rs.map fun r => .move (.reg r) (.save r)

theorem saveReg?_save (r : Reg) : (RItem.move (.reg r) (.save r)).saveReg? = some r := by
  simp [RItem.saveReg?]

theorem leadSaves_moves (rs : List Reg) {R : List RItem}
    (hR : ∀ it, R.head? = some it → it.saveReg? = none) :
    RItem.leadSaves (saveMoves rs ++ R) = rs := by
  induction rs with
  | nil =>
    cases R with
    | nil => rfl
    | cons it R => simp [saveMoves, RItem.leadSaves, hR it rfl]
  | cons r rs ih =>
    simp only [saveMoves, List.map_cons, List.cons_append, RItem.leadSaves, saveReg?_save] at ih ⊢
    rw [ih]

theorem dropWhile_moves (rs : List Reg) {R : List RItem}
    (hR : ∀ it, R.head? = some it → it.saveReg? = none) :
    (saveMoves rs ++ R).dropWhile (·.saveReg?.isSome) = R := by
  induction rs with
  | nil =>
    cases R with
    | nil => rfl
    | cons it R => simp [saveMoves, hR it rfl]
  | cons r rs ih =>
    simp only [saveMoves, List.map_cons, List.cons_append, List.dropWhile, saveReg?_save,
      Option.isSome_some] at ih ⊢
    exact ih

/-! ## `savedCheckRF` from its parts -/

theorem savedCheckRF_of {vc : VCode} {rf : RFunc} (hctl : ctlCheck vc rf = true)
    (hbody : ∀ b items, rf.blocks[b]? = some items →
      ∀ it ∈ Backend.bodyOf b items.toList, it.bodyOk rf.saveRegs = true)
    (hcs : ∀ r ∈ rf.saveRegs, r ∈ calleeSaved) : savedCheckRF vc rf = true := by
  simp only [ctlCheck, Bool.and_eq_true] at hctl
  obtain ⟨-, hcfg⟩ := hctl
  simp only [savedCheckRF, Bool.and_eq_true, List.all_eq_true, List.mem_range, memB_iff]
  refine ⟨⟨?_, fun b hb => ?_⟩, hcs⟩
  · cases h : vc.cfg with
    | error _ => rfl
    | ok p =>
      obtain ⟨ss, ps⟩ := p
      rw [h] at hcfg
      simpa [Array.all_eq_true] using hcfg
  · rw [Array.getElem?_eq_getElem hb, Option.getD_some]
    exact fun it hit => hbody b _ (Array.getElem?_eq_getElem hb) it hit

/-! ## The spill allocation -/

theorem wns_home (l : Loc) (h : Homes) (v : Nat) (c : RegClass) :
    WNS (.move l (spillHome h v c)) := fun r e => by simp [spillHome] at e

theorem wns_spillInst (h : Homes) (k : Nat) (i : MInst) : ∀ it ∈ spillInst h k i, WNS it := by
  intro it hit
  unfold spillInst at hit
  split at hit
  · simp only [List.mem_singleton] at hit
    subst hit
    intro l hl; simp at hl
  · rename_i ops hops
    have hreg : ∀ l ∈ (spillLocs ops i.clobbers).toList, ∃ r, l = .reg r :=
      fun l hl => E2E.spillLocs_reg hl
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hit
    rcases hit with ((hit | ⟨⟨o, l⟩, hp, rfl⟩) | rfl) | hit
    · split at hit
      · simp only [spillRestores, List.mem_map] at hit
        obtain ⟨r, -, rfl⟩ := hit
        intro r' e; cases e
      · simp at hit
    · have hl : l ∈ (spillLocs ops i.clobbers).toList := by
        have h1 := (List.mem_filter.1 hp).1
        rw [Array.toList_zip] at h1
        simpa using (List.of_mem_zip h1).2
      obtain ⟨r, rfl⟩ := hreg l hl
      intro r' e; cases e
    · intro l hl r e
      obtain ⟨r', rfl⟩ := hreg l hl
      cases e
    · split at hit
      · simp at hit
      · simp only [List.mem_map] at hit
        obtain ⟨⟨o, l⟩, -, rfl⟩ := hit
        exact wns_home _ _ _ _

theorem wns_argMoves (h : Homes) (vb tb : VBlock) : ∀ it ∈ spillArgMoves h vb tb, WNS it := by
  intro it hit
  simp only [spillArgMoves, List.mem_append, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false] at hit
  rcases hit with ⟨_, -, rfl | rfl⟩ | ⟨_, -, rfl | rfl⟩
  · intro r e; cases e
  · intro r e; cases e
  · intro r e; cases e
  · exact wns_home _ _ _ _

theorem wns_entryStores (vc : VCode) (succs preds : Array (Array Nat)) (s : Nat) :
    ∀ it ∈ spillEntryStores (spillHomes vc) vc succs preds s, WNS it := by
  intro it hit
  rw [Spill.spillEntryStores_eq (vc := vc) (succs := succs) (preds := preds) s] at hit
  simp only [List.map_map, List.mem_map] at hit
  obtain ⟨x, -, rfl⟩ := hit
  exact wns_home _ _ _ _

theorem wns_bodyItem (vc : VCode) (succs : Array (Array Nat)) (bi : Nat) (vb : VBlock)
    (x : MInst × Nat) : ∀ it ∈ Spill.bodyItem vc succs bi vb x, WNS it := by
  intro it hit
  unfold Spill.bodyItem at hit
  rcases List.mem_append.1 hit with hit | hit
  · split at hit
    · obtain ⟨tb, htb⟩ := argMovesOf_sub hit
      exact wns_argMoves _ _ _ it htb
    · simp at hit
  · exact wns_spillInst _ _ _ it hit

/-- **`savedCheckRF` of the spill allocation** of a VCode with a CFG (with `ctlCheck`, which
`lowerRFunc` checks). -/
theorem savedCheckRF_spill {vc : VCode} {succs preds : Array (Array Nat)}
    (hcfg : vc.cfg = .ok (succs, preds)) (hctl : ctlCheck vc (spillAlloc vc) = true) :
    savedCheckRF vc (spillAlloc vc) = true := by
  -- the blocks
  have hblk : ∀ b items, (spillAlloc vc).blocks[b]? = some items → ∃ E Bd,
      items.toList = (if b = 0 then saveMoves calleeSaved else []) ++ E ++ Bd ∧
      (∀ it ∈ E ++ Bd, WNS it) := by
    intro b items hb
    have hlt : b < vc.blocks.size := by
      have := (Array.getElem?_eq_some_iff.1 hb).1
      rwa [Spill.spillAlloc_size] at this
    obtain ⟨vb, hvb⟩ : ∃ vb, vc.blocks[b]? = some vb := ⟨_, Array.getElem?_eq_getElem hlt⟩
    rw [Spill.spillAlloc_block hcfg hvb, Option.some.injEq] at hb
    subst hb
    refine ⟨spillEntryStores (spillHomes vc) vc succs preds b,
      vb.insts.toList.zipIdx.flatMap (Spill.bodyItem vc succs b vb), ?_, ?_⟩
    · simp only [List.toList_toArray, List.append_assoc, beq_iff_eq]
      by_cases h0 : b = 0
      · simp [h0, spillSaves, saveMoves]
      · simp [h0]
    · intro it hit
      rcases List.mem_append.1 hit with hit | hit
      · exact wns_entryStores _ _ _ _ it hit
      · simp only [List.mem_flatMap] at hit
        obtain ⟨x, -, hx⟩ := hit
        exact wns_bodyItem _ _ _ _ x it hx
  -- the saved registers
  have hsv : vc.blocks.size ≠ 0 → (spillAlloc vc).saveRegs = calleeSaved := by
    intro hne
    obtain ⟨items, hit⟩ : ∃ items, (spillAlloc vc).blocks[0]? = some items :=
      ⟨_, Array.getElem?_eq_getElem (by rw [Spill.spillAlloc_size]; omega)⟩
    obtain ⟨E, Bd, he, hw⟩ := hblk 0 items hit
    simp only [ite_true] at he
    unfold RFunc.saveRegs
    rw [hit, Option.getD_some, he, List.append_assoc]
    apply leadSaves_moves
    intro it h1
    exact wns_saveReg (hw it (List.mem_of_mem_head? h1))
  refine savedCheckRF_of hctl (fun b items hb it hit => ?_) (fun r hr => ?_)
  · obtain ⟨E, Bd, he, hw⟩ := hblk b items hb
    have hne : vc.blocks.size ≠ 0 := by
      have := (Array.getElem?_eq_some_iff.1 hb).1
      rw [Spill.spillAlloc_size] at this; omega
    rw [hsv hne]
    have hbody : Backend.bodyOf b items.toList = E ++ Bd := by
      unfold Backend.bodyOf
      rw [he]
      by_cases h0 : b = 0
      · simp only [h0, ite_true, List.append_assoc]
        exact dropWhile_moves calleeSaved
          (fun it h1 => wns_saveReg (hw it (List.mem_of_mem_head? h1)))
      · simp [h0]
    rw [hbody] at hit
    exact wns_bodyOk_all (hw it hit)
  · by_cases hne : vc.blocks.size = 0
    · have h0 : (spillAlloc vc).blocks[0]? = none := by
        rw [Array.getElem?_eq_none]; rw [Spill.spillAlloc_size]; omega
      simp [RFunc.saveRegs, h0, RItem.leadSaves] at hr
    · rw [hsv hne] at hr; exact hr

/-! ## regalloc2's answer (`buildRFunc`) -/

/-- No location of `it` is a save slot. -/
def NoSave (it : RItem) : Prop := ∀ l ∈ it.locs, ∀ r, l ≠ .save r

theorem parseLoc_ne_save {s : String} {cls : RegClass} {l : Loc} (h : parseLoc s cls = .ok l)
    (r : Reg) : l ≠ .save r := by
  rintro rfl
  unfold parseLoc at h
  split at h
  · split at h <;> simp [pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  · split at h <;> simp [pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h

theorem parseMove_spec {src dst : String} {m : RItem} (h : parseMove src dst = .ok m) :
    ∃ cls a b, parseLoc src cls = .ok a ∧ parseLoc dst cls = .ok b ∧ m = .move a b := by
  have key : ∀ (e : Except String RegClass), (do let cls ← e; pure (RItem.move (← parseLoc src cls)
      (← parseLoc dst cls))) = Except.ok m →
      ∃ cls a b, parseLoc src cls = .ok a ∧ parseLoc dst cls = .ok b ∧ m = .move a b := by
    intro e he
    cases e with
    | error _ => cases he
    | ok cls =>
      simp only [bind, Except.bind] at he
      cases ha : parseLoc src cls with
      | error _ => rw [ha] at he; cases he
      | ok a =>
        rw [ha] at he
        cases hb : parseLoc dst cls with
        | error _ => rw [hb] at he; cases he
        | ok b =>
          rw [hb] at he
          simp only [pure, Except.pure, Except.ok.injEq] at he
          exact ⟨cls, a, b, ha, hb, he.symm⟩
  unfold parseMove at h
  simp only at h
  split at h <;> (try split at h) <;> exact key _ h

theorem parseMove_noSave {src dst : String} {m : RItem} (h : parseMove src dst = .ok m) :
    NoSave m := by
  obtain ⟨cls, a, b, ha, hb, rfl⟩ := parseMove_spec h
  intro l hl r
  simp only [RItem.locs, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · exact parseLoc_ne_save ha r
  · exact parseLoc_ne_save hb r

theorem forIn_list_inv {α σ ε : Type} (P : σ → Prop) (f : α → σ → Except ε (ForInStep σ))
    (hf : ∀ a s r, P s → f a s = .ok r → P r.value) :
    ∀ (xs : List α) (s r : σ), P s → forIn xs s f = .ok r → P r
  | [], s, r, hs, h => by
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact hs
  | a :: xs, s, r, hs, h => by
    rw [List.forIn_cons] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i st hst
      have := hf a s st hs hst
      cases st with
      | done b =>
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h; exact this
      | yield b => exact forIn_list_inv P f hf xs b r this h

theorem forIn_array_inv {α σ ε : Type} (P : σ → Prop) (f : α → σ → Except ε (ForInStep σ))
    (hf : ∀ a s r, P s → f a s = .ok r → P r.value) (xs : Array α) (s r : σ) (hs : P s)
    (h : forIn xs s f = .ok r) : P r := by
  rw [← Array.forIn_toList] at h
  exact forIn_list_inv P f hf xs.toList s r hs h

theorem list_mapM_mem {α β ε : Type} (f : α → Except ε β) :
    ∀ (as : List α) (bs : List β), as.mapM f = .ok bs → ∀ b ∈ bs, ∃ a ∈ as, f a = .ok b
  | [], bs, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp
  | a :: as, bs, h => by
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i b hb
      split at h
      · cases h
      · rename_i bs' hbs
        simp only [Except.ok.injEq] at h
        subst h
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨a, by simp, hb⟩
        · obtain ⟨a', ha', h'⟩ := list_mapM_mem f as bs' hbs x hx
          exact ⟨a', by simp [ha'], h'⟩

/-- All items of the arrays of `A` meet `NoSave`. -/
def AllNS (A : Array (Array RItem)) : Prop := ∀ arr ∈ A.toList, ∀ it ∈ arr.toList, NoSave it

theorem allNS_modify {A : Array (Array RItem)} (h : AllNS A) (g : Nat) {m : RItem} (hm : NoSave m) :
    AllNS (A.modify g fun x => x.push m) := by
  intro arr harr it hit
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.1 harr)
  rw [Array.getElem_modify] at hit
  have hi' : i < A.size := by simpa using hi
  split at hit
  · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hit
    rcases hit with hit | rfl
    · exact h _ (Array.getElem_mem_toList hi') it hit
    · exact hm
  · exact h _ (Array.getElem_mem_toList hi') it hit

theorem allNS_get! {A : Array (Array RItem)} (h : AllNS A) (g : Nat) :
    ∀ it ∈ A[g]!.toList, NoSave it := by
  intro it hit
  by_cases hg : g < A.size
  · rw [getElem!_pos A g hg] at hit
    exact h _ (Array.getElem_mem_toList hg) it hit
  · rw [getElem!_neg A g hg] at hit
    exact absurd hit (by show it ∉ ([] : List RItem); simp)

theorem allNS_push {A : Array (Array RItem)} (h : AllNS A) {items : Array RItem}
    (hi : ∀ it ∈ items.toList, NoSave it) : AllNS (A.push items) := by
  intro arr harr it hit
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at harr
  rcases harr with harr | rfl
  · exact h arr harr it hit
  · exact hi it hit

theorem foldl_locs (L : List RItem) (acc : List Loc) :
    L.foldl (fun acc it => acc ++ it.locs) acc = acc ++ L.flatMap RItem.locs := by
  induction L generalizing acc with
  | nil => simp
  | cons it L ih => simp [ih]

theorem foldl_blocks_locs (B : List (Array RItem)) (acc : List Loc) :
    B.foldl (fun acc items => items.foldl (fun acc it => acc ++ it.locs) acc) acc =
      acc ++ B.flatMap (fun items => items.toList.flatMap RItem.locs) := by
  induction B generalizing acc with
  | nil => simp
  | cons items B ih =>
    simp only [List.foldl_cons, List.flatMap_cons]
    rw [ih, ← Array.foldl_toList, foldl_locs, List.append_assoc]

theorem mapIdx_shape {S : Array RItem} {F : Nat → RItem → Array RItem} {W : Array (Array RItem)}
    {b : Nat} {items : Array RItem}
    (hb : (W.mapIdx fun bi items => if (bi == 0) = true then S ++ items.flatMap (F bi)
      else items.flatMap (F bi))[b]? = some items) :
    ∃ items0, W[b]? = some items0 ∧
      items.toList = (if b = 0 then S.toList else []) ++ (items0.flatMap (F b)).toList := by
  simp only [Array.getElem?_mapIdx] at hb
  cases hwb : W[b]? with
  | none => rw [hwb] at hb; cases hb
  | some items0 =>
    rw [hwb] at hb
    simp only [Option.map_some, Option.some.injEq] at hb
    subst hb
    refine ⟨items0, rfl, ?_⟩
    by_cases h0 : b = 0 <;> simp [h0]

/-- **What `buildRFunc` builds**: each block is (block 0: the save moves of `rf.saved`, then)
items each of which writes no save slot and no callee-saved register outside `rf.saved`, or is
the restore of a register of `rf.saved`; `rf.saved` are callee-saved. -/
theorem buildRFunc_blocks {vc : VCode} {o : RAOut} {rf : RFunc} (h : buildRFunc vc o = .ok rf) :
    (∀ r ∈ rf.saved, r ∈ calleeSaved) ∧
    ∀ b items, rf.blocks[b]? = some items → ∃ R,
      items.toList = (if b = 0 then saveMoves rf.saved else []) ++ R ∧
      ∀ it ∈ R, it.saveReg? = none ∧ it.bodyOk rf.saved = true := by
  unfold buildRFunc at h
  simp only [bind, Except.bind] at h
  split at h
  · split at h
    · cases h
    · simp [throw, throwThe, MonadExceptOf.throw] at *
  · split at h
    · cases h
    · rename_i v hv
      split at h
      · cases h
      · rename_i w hw
        simp only [pure, Except.pure, Except.ok.injEq] at h
        -- the edits: `NoSave`
        have hv' : AllNS v.1 ∧ AllNS v.2 := by
          refine forIn_array_inv (fun s : Array (Array RItem) × Array (Array RItem) =>
            AllNS s.1 ∧ AllNS s.2) _ ?_ _ _ _ ⟨?_, ?_⟩ hv
          · intro a s r hs hr
            split at hr
            · simp [throw, throwThe, MonadExceptOf.throw] at hr
            · split at hr
              · cases hr
              · rename_i m hm
                have hns := parseMove_noSave hm
                split at hr <;> simp only [pure, Except.pure, Except.ok.injEq] at hr <;> subst hr
                · exact ⟨hs.1, allNS_modify hs.2 _ hns⟩
                · exact ⟨allNS_modify hs.1 _ hns, hs.2⟩
          · intro arr harr it hit
            simp only [Array.toList_replicate, List.mem_replicate] at harr
            rw [harr.2] at hit; simp at hit
          · intro arr harr it hit
            simp only [Array.toList_replicate, List.mem_replicate] at harr
            rw [harr.2] at hit; simp at hit
        -- the blocks: `NoSave`
        have hw' : AllNS w.2 := by
          refine forIn_array_inv (fun s : Nat × Array (Array RItem) => AllNS s.2) _ ?_ _ _ _ ?_ hw
          · intro b s r hs hr
            split at hr
            · cases hr
            · rename_i u hu
              simp only [pure, Except.pure, Except.ok.injEq] at hr
              subst hr
              refine allNS_push hs ?_
              refine forIn_array_inv (fun s : Nat × Array RItem => ∀ it ∈ s.2.toList, NoSave it)
                _ ?_ _ _ _ (by simp) hu
              intro x s' r' hs' hr'
              split at hr'
              · cases hr'
              · rename_i ops _
                have hstep : ∀ (locs : Array Loc), (∀ l ∈ locs.toList, ∀ r, l ≠ .save r) →
                    ∀ it ∈ (((s'.2 ++ v.1[s'.1]!).push (RItem.op x.2 locs)).append v.2[s'.1]!).toList,
                      NoSave it := by
                  intro locs hl it hit
                  rw [show ∀ a b : Array RItem, a.append b = a ++ b from fun _ _ => rfl] at hit
                  simp only [Array.toList_append, Array.toList_push, List.mem_append,
                    List.mem_singleton] at hit
                  rcases hit with ((hit | hit) | rfl) | hit
                  · exact hs' it hit
                  · exact allNS_get! hv'.1 _ it hit
                  · intro l hl' r; exact hl l (by simpa [RItem.locs] using hl') r
                  · exact allNS_get! hv'.2 _ it hit
                have hmap : ∀ (locs : Array Loc), Array.mapM (fun x => parseLoc x.2 x.1.cls)
                    (ops.zip o.allocs[s'.1]!) = .ok locs → ∀ l ∈ locs.toList, ∀ r, l ≠ .save r := by
                  intro locs hm l hl r
                  rw [Array.mapM_eq_mapM_toList] at hm
                  cases hm' : List.mapM (fun x => parseLoc x.2 x.1.cls) (ops.zip o.allocs[s'.1]!).toList with
                  | error e => rw [hm'] at hm; cases hm
                  | ok ls =>
                    rw [hm'] at hm
                    simp only [Functor.map, Except.map, Except.ok.injEq] at hm
                    subst hm
                    obtain ⟨⟨op, st⟩, -, hp⟩ := list_mapM_mem _ _ _ hm' l (by simpa using hl)
                    exact parseLoc_ne_save hp r
                split at hr'
                · split at hr'
                  · cases hr'
                  · simp [throw, throwThe, MonadExceptOf.throw] at *
                · split at hr'
                  · cases hr'
                  · rename_i locs hlocs
                    simp only [pure, Except.pure, Except.ok.injEq] at hr'
                    subst hr'
                    exact hstep locs (hmap locs hlocs)
          · intro arr harr; simp at harr
        subst h
        have hused : ∀ items ∈ w.2.toList, ∀ it ∈ items.toList, ∀ r ∈ calleeSaved,
            Loc.reg r ∈ it.locs → (Array.foldl (fun acc items =>
              Array.foldl (fun acc it => acc ++ it.locs) acc items) [] w.2).contains (Loc.reg r) = true := by
          intro items hitems it hit r hr hl
          rw [List.contains_iff_mem, ← Array.foldl_toList, foldl_blocks_locs]
          simp only [List.nil_append, List.mem_flatMap]
          exact ⟨items, hitems, it, hit, hl⟩
        refine ⟨fun r hr => (List.mem_filter.1 hr).1, fun b items hb => ?_⟩
        obtain ⟨items0, hwb, he⟩ := mapIdx_shape hb
        have hmem : items0 ∈ w.2.toList := Array.mem_toList_iff.2 (Array.mem_of_getElem? hwb)
        have hns : ∀ it ∈ items0.toList, NoSave it := hw' items0 hmem
        refine ⟨_, he.trans (congrArg (· ++ _) ?_), ?_⟩
        · by_cases h0 : b = 0 <;> simp [h0, saveMoves]
        · intro it hit
          simp only [Array.toList_flatMap, List.mem_flatMap] at hit
          obtain ⟨x, hx, hit⟩ := hit
          have hxns := hns x hx
          have hbody : ∀ l ∈ x.locs, bodyWritable (calleeSaved.filter fun r =>
              (vc.blocks.any fun b => b.insts.any fun x => match x with
                | MInst.tryCall _ ti => ti.clobberAll
                | _ => false) ||
              (Array.foldl (fun acc items => Array.foldl (fun acc it => acc ++ it.locs) acc items) []
                w.2).contains (Loc.reg r)) l = true := by
            intro l hl
            cases l with
            | save r => exact absurd rfl (hxns _ hl r)
            | stack _ _ => rfl
            | reg r =>
              simp only [bodyWritable, Bool.or_eq_true, Bool.not_eq_true']
              by_cases hr : r ∈ calleeSaved
              · refine .inr (memB_iff.2 ?_)
                simp only [List.mem_filter, hr, true_and, Bool.or_eq_true]
                exact .inr (hused items0 hmem x hx r hr hl)
              · refine .inl ?_
                cases hm : memB r calleeSaved
                · rfl
                · exact absurd (memB_iff.1 hm) hr
          have hx' : x.saveReg? = none ∧ x.bodyOk (calleeSaved.filter fun r =>
              (vc.blocks.any fun b => b.insts.any fun x => match x with
                | MInst.tryCall _ ti => ti.clobberAll
                | _ => false) ||
              (Array.foldl (fun acc items => Array.foldl (fun acc it => acc ++ it.locs) acc items) []
                w.2).contains (Loc.reg r)) = true := by
            refine ⟨?_, ?_⟩
            · cases x with
              | op k a => rfl
              | move s d =>
                cases s <;> cases d <;> simp only [RItem.saveReg?]
                rename_i r r'
                exact absurd rfl (hxns _ (by simp [RItem.locs]) r')
            · cases x with
              | move s d => exact hbody d (by simp [RItem.locs])
              | op k a =>
                simp only [RItem.bodyOk, Array.all_eq_true]
                intro i hi
                exact hbody _ (by simp [RItem.locs, Array.getElem_mem_toList hi])
          split at hit
          · split at hit
            · simp only [↓reduceIte] at hit
              simp only [Array.toList_push, List.mem_append, Array.toList_map,
                List.mem_map, List.mem_singleton] at hit
              rcases hit with ⟨r, hr, rfl⟩ | rfl
              · refine ⟨rfl, ?_⟩
                simp only [RItem.bodyOk, bodyWritable, Bool.or_eq_true, Bool.not_eq_true']
                exact .inr (memB_iff.2 (by simpa using hr))
              · exact hx'
            · simp only [Bool.false_eq_true, ↓reduceIte] at hit
              simp at hit; subst hit; exact hx'
          · simp at hit; subst hit; exact hx'

/-- **`savedCheckRF` of regalloc2's answer as the backend reads it** (with `ctlCheck`). -/
theorem savedCheckRF_build {vc : VCode} {o : RAOut} {rf : RFunc} (h : buildRFunc vc o = .ok rf)
    (hctl : ctlCheck vc rf = true) : savedCheckRF vc rf = true := by
  obtain ⟨hcs, hblk⟩ := buildRFunc_blocks h
  have hsv : ∀ items, rf.blocks[0]? = some items → rf.saveRegs = rf.saved := by
    intro items h0
    obtain ⟨R, he, hR⟩ := hblk 0 items h0
    simp only [ite_true] at he
    unfold RFunc.saveRegs
    rw [h0, Option.getD_some, he]
    exact leadSaves_moves _ (fun it h1 => (hR it (List.mem_of_mem_head? h1)).1)
  refine savedCheckRF_of hctl (fun b items hb it hit => ?_) (fun r hr => ?_)
  · obtain ⟨items0, h0⟩ : ∃ items0, rf.blocks[0]? = some items0 :=
      ⟨_, Array.getElem?_eq_getElem (by have := (Array.getElem?_eq_some_iff.1 hb).1; omega)⟩
    rw [hsv items0 h0]
    obtain ⟨R, he, hR⟩ := hblk b items hb
    have hbody : Backend.bodyOf b items.toList = R := by
      unfold Backend.bodyOf
      rw [he]
      by_cases h0 : b = 0
      · simp only [h0, ite_true]
        exact dropWhile_moves _ (fun it h1 => (hR it (List.mem_of_mem_head? h1)).1)
      · simp [h0]
    rw [hbody] at hit
    exact (hR it hit).2
  · cases h0 : rf.blocks[0]? with
    | none => simp [RFunc.saveRegs, h0, RItem.leadSaves] at hr
    | some items0 => rw [hsv items0 h0] at hr; exact hcs r hr

/-! ## The allocation the pipeline lowers -/

theorem readyAnswer_cases (vcp : VCode) (ra : Except String RFunc) :
    readyAnswer vcp ra = ra ∨ ∃ e, readyAnswer vcp ra = .error e := by
  unfold readyAnswer
  split
  · split
    · exact .inl rfl
    · exact .inr ⟨_, rfl⟩
  · exact .inr ⟨_, rfl⟩

theorem checkAlloc_size {vc : VCode} {rf : RFunc} (h : (checkAlloc vc rf).isOk = true) :
    rf.blocks.size = vc.blocks.size ∧ vc.blocks.size ≠ 0 := by
  unfold checkAlloc at h
  simp only [bind, Except.bind, ensure] at h
  split at h
  · simp [Except.isOk, Except.toBool] at h
  · by_cases h1 : vc.blocks.size = 0
    · simp [h1, throw, throwThe, MonadExceptOf.throw, Except.isOk, Except.toBool] at h
    · by_cases h2 : rf.blocks.size = vc.blocks.size
      · exact ⟨h2, h1⟩
      · simp [h1, h2, throw, throwThe, MonadExceptOf.throw, Except.isOk, Except.toBool, pure,
          Except.pure] at h

/-- The allocation `pipeCleanupT` lowers is the spill allocation or regalloc2's answer as
`buildRFunc` reads it, accepted by `checkAlloc`. -/
theorem pipeAlloc_cases (vcp : VCode) (o : Lean.Json) :
    allocResult vcp (readyAnswer vcp (LinkCheck.raAnswer vcp o)) = spillAlloc vcp ∨
      ∃ o', buildRFunc vcp o' = .ok (allocResult vcp (readyAnswer vcp (LinkCheck.raAnswer vcp o))) ∧
        (checkAlloc vcp (allocResult vcp (readyAnswer vcp (LinkCheck.raAnswer vcp o)))).isOk = true := by
  have hspill : ∀ ra : Except String RFunc, (∀ rf, ra = .ok rf → ∃ o', buildRFunc vcp o' = .ok rf) →
      allocResult vcp ra = spillAlloc vcp ∨ ∃ o', buildRFunc vcp o' = .ok (allocResult vcp ra) ∧
        (checkAlloc vcp (allocResult vcp ra)).isOk = true := by
    intro ra hra
    cases ra with
    | error e => exact .inl rfl
    | ok rf =>
      by_cases hc : (checkAlloc vcp rf).isOk = true
      · cases hl : lowerRFunc vcp rf with
        | ok af =>
          have e : allocResult vcp (.ok rf) = rf := by simp [allocResult, hc, hl]
          rw [e]
          obtain ⟨o', ho'⟩ := hra rf rfl
          exact .inr ⟨o', ho', hc⟩
        | error _ => exact .inl (by simp [allocResult, hc, hl])
      · exact .inl (by simp [allocResult, hc])
  apply hspill
  intro rf hrf
  rcases readyAnswer_cases vcp (LinkCheck.raAnswer vcp o) with h | ⟨e, h⟩
  · rw [h] at hrf
    unfold LinkCheck.raAnswer at hrf
    simp only [bind, Except.bind] at hrf
    split at hrf
    · cases hrf
    · exact ⟨_, hrf⟩
  · rw [h] at hrf; cases hrf

/-- **`savedCheckRF` of the allocation the pipeline lowers**, for every allocator answer `o`
(the prepared code has a CFG; `ctlCheck` from `lowerRFunc`). -/
theorem savedCheckRF_pipe {vcp : VCode} {o : Lean.Json} {af : AFunc} {ss ps : Array (Array Nat)}
    (hcfg : vcp.cfg = .ok (ss, ps))
    (halloc : lowerRFunc vcp (allocResult vcp (readyAnswer vcp (LinkCheck.raAnswer vcp o))) = .ok af) :
    savedCheckRF vcp (allocResult vcp (readyAnswer vcp (LinkCheck.raAnswer vcp o))) = true := by
  have hctl := (lowerRFunc_ok halloc).2.2
  rcases pipeAlloc_cases vcp o with h | ⟨o', h, -⟩
  · rw [h] at hctl ⊢
    exact savedCheckRF_spill hcfg hctl
  · exact savedCheckRF_build h hctl

/-- The allocation the pipeline lowers has one item list per block of the prepared code. -/
theorem pipeAlloc_size {vcp : VCode} (hne : vcp.blocks.size ≠ 0) (o : Lean.Json) :
    (allocResult vcp (readyAnswer vcp (LinkCheck.raAnswer vcp o))).blocks.size = vcp.blocks.size := by
  rcases pipeAlloc_cases vcp o with h | ⟨o', -, hc⟩
  · rw [h]; exact Spill.spillAlloc_size vcp
  · exact (checkAlloc_size hc).1

/-! ## The frame part -/

/-- A block is its leading save moves, then the rest. -/
theorem leadSaves_split : ∀ l : List RItem,
    l = saveMoves (RItem.leadSaves l) ++ l.dropWhile (·.saveReg?.isSome)
  | [] => rfl
  | it :: l => by
    cases h : it.saveReg? with
    | none => simp [RItem.leadSaves, h, saveMoves]
    | some r =>
      have e := saveReg?_some h
      subst e
      simp only [RItem.leadSaves, saveReg?_save, saveMoves, List.map_cons, List.cons_append,
        List.dropWhile, Option.isSome_some]
      exact congrArg _ (leadSaves_split l)

/-- **The save slots are below 32 KiB**: every save move becomes one `str` at `[sp, #off]`.
Since #479 a theorem whenever the outgoing area is below 32560 bytes (`saveFrameB_always`). -/
def saveFrameB (vc : VCode) (rf : RFunc) : Bool :=
  rf.saveRegs.all fun r => match (RAFrame.compute vc rf).saveOff.lookup r with
    | some o => decide (o < 32768)
    | none => true

/-- **The code of block 0 after the prologue and the saves' stores does not start with
another callee-save store**: neither one at `[sp, #off]` (`calleeSave?`) nor one through x16
(`farSave`). -/
def leadOkB (rf : RFunc) (af : AFunc) : Bool :=
  match af.blocks[0]? with
  | some (_, code) => ((code.toList.drop (1 + rf.saveRegs.length)).head?.bind AInst.calleeSave?).isNone &&
      !farSave (code.toList.drop (1 + rf.saveRegs.length))
  | none => true

/-- **`saveFrameB` holds for every allocation** of a function whose outgoing argument area is
below 32560 bytes (#479): the save slots come first in the frame (`RAFrame.compute`), right
above the outgoing area, so they end by `intBase + 208` whatever the number of spill slots. -/
theorem saveFrameB_always (vc : VCode) (rf : RFunc) (hout : vc.outgoing ≤ 32560) :
    saveFrameB vc rf = true := by
  unfold saveFrameB
  refine List.all_eq_true.2 fun r _ => ?_
  split
  · rename_i o h
    have h1 := save_lt h
    have h2 : (RAFrame.compute vc rf).intBase = alignTo vc.outgoing 16 := rfl
    rw [h2] at h1
    unfold alignTo at h1
    simp only [decide_eq_true_eq]
    omega
  · rfl

/-- The save moves' code: one `str` per saved register at its save slot. -/
theorem saves_code {fr : RAFrame} {vb : VBlock} :
    ∀ (rs : List Reg) {code : List AInst}, itemsCode fr vb (saveMoves rs) = .ok code →
      (∀ r ∈ rs, ∀ o, fr.saveOff.lookup r = some o → o < 32768) →
      ∃ offs : List Nat, offs.length = rs.length ∧
        (∀ (i : Nat) r o, rs[i]? = some r → offs[i]? = some o → fr.saveOff.lookup r = some o) ∧
        code = (rs.zip offs).map fun (r, o) => AInst.inst (slotStore ((r.realClass?).getD .int) r o)
  | [], code, h, _ => by
    simp only [saveMoves, List.map_nil, itemsCode, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨[], rfl, by simp, rfl⟩
  | r :: rs, code, h, hb => by
    simp only [saveMoves, List.map_cons] at h
    obtain ⟨c1, c2, h1, h2, rfl⟩ := itemsCode_cons h
    obtain ⟨offs, hlen, hoff, rfl⟩ := saves_code rs h2 (fun r' hr' => hb r' (by simp [hr']))
    rw [itemCode_move] at h1
    simp only [RAFrame.moveInsts, RAFrame.offset, bind, Except.bind] at h1
    cases hl : fr.saveOff.lookup r with
    | none => rw [hl] at h1; cases h1
    | some o =>
      rw [hl] at h1
      simp only [pure, Except.pure, Except.ok.injEq] at h1
      subst h1
      have ho := hb r (by simp) o hl
      refine ⟨o :: offs, by simp [hlen], fun i r' o' hr' ho' => ?_, ?_⟩
      · cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hr' ho'
          subst hr' ho'; exact hl
        | succ i => exact hoff i r' o' (by simpa using hr') (by simpa using ho')
      · simp [slotStoreAt, ho]

theorem calleeSave_slotStore {r : Reg} (hr : r ∈ calleeSaved) (o : Nat) :
    (AInst.inst (slotStore ((r.realClass?).getD .int) r o)).calleeSave? = some (r, (o : Int)) := by
  have hc : calleeSaved.contains r = true := List.contains_iff_mem.2 hr
  cases h : (r.realClass?).getD RegClass.int <;> simp [slotStore, AInst.calleeSave?, hr]

/-- The rows of the saves' stores are those of their slots. -/
theorem saveRows_eq {fr : RAFrame} {fs : Nat} :
    ∀ (rs : List Reg) (offs : List Nat), offs.length = rs.length → (∀ r ∈ rs, r ∈ calleeSaved) →
      (∀ (i : Nat) r o, rs[i]? = some r → offs[i]? = some o → fr.saveOff.lookup r = some o) →
      ((rs.zip offs).map fun (r, o) => AInst.inst (slotStore ((r.realClass?).getD .int) r o)).mapM
        (UnwindTables.saveRow fs) = saveRowsOf fr fs rs
  | [], [], _, _, _ => rfl
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | r :: rs, o :: offs, hlen, hcs, hoff => by
    have hr := hcs r (by simp)
    have hl := hoff 0 r o rfl rfl
    have ih := saveRows_eq (fs := fs) rs offs (by simpa using hlen) (fun r' h' => hcs r' (by simp [h']))
      (fun i r' o' h1 h2 => hoff (i + 1) r' o' (by simpa using h1) (by simpa using h2))
    obtain ⟨d, hd⟩ := calleeSave_dwarf (calleeSave_slotStore hr o)
    simp only [List.zip_cons_cons, List.map_cons, List.mapM_cons, saveRowsOf] at ih ⊢
    rw [ih]
    simp only [UnwindTables.saveRow, calleeSave_slotStore hr o, Option.bind_some, hd,
      Option.map_some, hl, bind, Option.bind, pure]

/-- The saves' code: callee-save stores of the saved registers at their slots, whose rows are
the saved registers' slots. -/
theorem saves_code' {fr : RAFrame} {vb : VBlock} {fs : Nat} (rs : List Reg) {code : List AInst}
    (h : itemsCode fr vb (saveMoves rs) = .ok code)
    (hb : ∀ r ∈ rs, ∀ o, fr.saveOff.lookup r = some o → o < 32768)
    (hcs : ∀ r ∈ rs, r ∈ calleeSaved) :
    code.length = rs.length ∧
      (∀ a ∈ code, ∃ (r : Reg) (o : Nat), a.calleeSave? = some (r, (o : Int)) ∧
        fr.saveOff.lookup r = some o) ∧
      code.mapM (UnwindTables.saveRow fs) = saveRowsOf fr fs rs := by
  obtain ⟨offs, hlen, hoff, rfl⟩ := saves_code rs h hb
  refine ⟨by simp [hlen], fun a ha => ?_, saveRows_eq rs offs hlen hcs hoff⟩
  simp only [List.mem_map] at ha
  obtain ⟨⟨r, o⟩, hp, rfl⟩ := ha
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hp
  rw [List.getElem?_zip_eq_some] at hi
  exact ⟨r, o, calleeSave_slotStore (hcs r (List.of_mem_zip hp).1) o, hoff i r o hi.1 hi.2⟩

/-- **Block 0's leading callee-save stores** (`savesOf`, what `unwindRows` and `savedCheckAF`
read) on an allocation passing `savedCheckRF`, with save slots below 32 KiB (`saveFrameB`) and
no further callee-save store right after the saves' (`leadOkB`): the saves' stores, at the
saved registers' slots, with their rows; and the code after them does not start with a
callee-saved register's store through x16 (`farSave`). -/
theorem frame_saves_far {vc : VCode} {rf : RFunc} {af : AFunc} (hRF : savedCheckRF vc rf = true)
    (halloc : lowerRFunc vc rf = .ok af) (hsz : rf.blocks.size = vc.blocks.size)
    (hne : vc.blocks.size ≠ 0) (hframe : saveFrameB vc rf = true)
    (hlead : leadOkB rf af = true) :
    (∃ code, af.blocks[0]?.map (·.2) = some (AInst.prologue :: code).toArray ∧
      (code.takeWhile (·.calleeSave?.isSome)).mapM (UnwindTables.saveRow af.frameSize) =
        saveRowsOf (RAFrame.compute vc rf) af.frameSize rf.saveRegs ∧
      ∀ a ∈ code.takeWhile (·.calleeSave?.isSome), ∃ (r : Reg) (o : Nat),
        a.calleeSave? = some (r, (o : Int)) ∧
        (RAFrame.compute vc rf).saveOff.lookup r = some o) ∧
    farSave (afterSavesOf af) = false := by
  obtain ⟨⟨-, -, -, hbl⟩, -⟩ := lowerRFunc_ok halloc
  have hcs := savedCheckRF_cs hRF
  obtain ⟨vb, hvb⟩ : ∃ vb, vc.blocks[0]? = some vb := ⟨_, Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨items0, hit⟩ : ∃ items0, rf.blocks[0]? = some items0 :=
    ⟨_, Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨code, hcode, haf0⟩ := hbl 0 vb items0 hvb hit
  simp only [ite_true] at haf0
  have hsv : rf.saveRegs = RItem.leadSaves items0.toList := by
    simp [RFunc.saveRegs, hit]
  have hsplit := leadSaves_split items0.toList
  rw [← hsv] at hsplit
  rw [hsplit] at hcode
  obtain ⟨cS, cR, hS, hR, rfl⟩ := itemsCode_append hcode
  have hfb : ∀ r ∈ rf.saveRegs, ∀ o, (RAFrame.compute vc rf).saveOff.lookup r = some o → o < 32768 := by
    intro r hr o ho
    have := List.all_eq_true.1 hframe r hr
    rw [ho] at this
    simpa using this
  obtain ⟨hlenS, hallS, hrowS⟩ := saves_code' (fs := af.frameSize) rf.saveRegs hS hfb hcs
  have hallS' : ∀ a ∈ cS, a.calleeSave?.isSome = true := by
    intro a ha
    obtain ⟨r, o, h1, -⟩ := hallS a ha
    simp [h1]
  unfold leadOkB at hlead
  rw [haf0] at hlead
  simp only [List.toList_toArray, List.singleton_append] at hlead
  rw [show 1 + rf.saveRegs.length = (AInst.prologue :: cS).length by simp [hlenS]; omega,
    ← List.cons_append, List.drop_left] at hlead
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hlead
  obtain ⟨hlead, hlf⟩ := hlead
  have hR0 : cR.takeWhile (·.calleeSave?.isSome) = [] := by
    cases cR with
    | nil => rfl
    | cons a cR =>
      simp only [List.head?_cons, Option.bind_some, Option.isNone_iff_eq_none] at hlead
      simp [hlead]
  have hRd : cR.dropWhile (·.calleeSave?.isSome) = cR := by
    cases cR with
    | nil => rfl
    | cons a cR =>
      simp only [List.head?_cons, Option.bind_some, Option.isNone_iff_eq_none] at hlead
      simp [List.dropWhile_cons, hlead]
  have htw : (cS ++ cR).takeWhile (·.calleeSave?.isSome) = cS := by
    rw [List.takeWhile_append_of_pos hallS', hR0, List.append_nil]
  have hdw : (cS ++ cR).dropWhile (·.calleeSave?.isSome) = cR := by
    rw [List.dropWhile_append_of_pos hallS', hRd]
  refine ⟨⟨cS ++ cR, by rw [haf0]; rfl, by rw [htw]; exact hrowS, fun a ha => ?_⟩, ?_⟩
  · rw [htw] at ha
    exact hallS a ha
  · unfold afterSavesOf
    rw [haf0]
    simp only [List.toList_toArray, List.drop_one, List.singleton_append, List.tail_cons]
    rw [hdw]
    exact hlf

/-- **Block 0's leading callee-save stores** (`frame_saves_far` without the `farSave` part). -/
theorem frame_saves {vc : VCode} {rf : RFunc} {af : AFunc} (hRF : savedCheckRF vc rf = true)
    (halloc : lowerRFunc vc rf = .ok af) (hsz : rf.blocks.size = vc.blocks.size)
    (hne : vc.blocks.size ≠ 0) (hframe : saveFrameB vc rf = true)
    (hlead : leadOkB rf af = true) :
    ∃ code, af.blocks[0]?.map (·.2) = some (AInst.prologue :: code).toArray ∧
      (code.takeWhile (·.calleeSave?.isSome)).mapM (UnwindTables.saveRow af.frameSize) =
        saveRowsOf (RAFrame.compute vc rf) af.frameSize rf.saveRegs ∧
      ∀ a ∈ code.takeWhile (·.calleeSave?.isSome), ∃ (r : Reg) (o : Nat),
        a.calleeSave? = some (r, (o : Int)) ∧
        (RAFrame.compute vc rf).saveOff.lookup r = some o :=
  (frame_saves_far hRF halloc hsz hne hframe hlead).1

/-- **`savedCheckAF` from the frame conditions** (`frame_saves`). -/
theorem savedCheckAF_of {vc : VCode} {rf : RFunc} {af : AFunc} (hRF : savedCheckRF vc rf = true)
    (halloc : lowerRFunc vc rf = .ok af) (hsz : rf.blocks.size = vc.blocks.size)
    (hne : vc.blocks.size ≠ 0) (hframe : saveFrameB vc rf = true)
    (hlead : leadOkB rf af = true) : savedCheckAF vc rf af = true := by
  obtain ⟨code, h0, hrow, -⟩ := frame_saves hRF halloc hsz hne hframe hlead
  unfold savedCheckAF
  cases h : af.blocks[0]? with
  | none => rw [h] at h0; cases h0
  | some p =>
    rw [h] at h0
    simp only [Option.map_some, Option.some.injEq] at h0
    obtain ⟨l, c⟩ := p
    simp only at h0
    subst h0
    simp only [List.toList_toArray, List.drop_one, List.tail_cons, decide_eq_true_eq]
    exact hrow

/-- **`savedCheck` from the frame conditions.** -/
theorem savedCheck_of {vc : VCode} {rf : RFunc} {af : AFunc} (hRF : savedCheckRF vc rf = true)
    (halloc : lowerRFunc vc rf = .ok af) (hsz : rf.blocks.size = vc.blocks.size)
    (hne : vc.blocks.size ≠ 0) (hframe : saveFrameB vc rf = true)
    (hlead : leadOkB rf af = true) : savedCheck vc rf = true := by
  unfold savedCheck
  rw [hRF, halloc]
  simp only [Bool.true_and]
  exact savedCheckAF_of hRF halloc hsz hne hframe hlead

/-- **`savedCheck` of the allocation the pipeline lowers**, for every allocator answer `o`, from
the frame conditions. -/
theorem savedCheck_pipe {vcp : VCode} {o : Lean.Json} {af : AFunc} {ss ps : Array (Array Nat)}
    (hcfg : vcp.cfg = .ok (ss, ps)) (hne : vcp.blocks.size ≠ 0)
    (halloc : lowerRFunc vcp (allocResult vcp (readyAnswer vcp (LinkCheck.raAnswer vcp o))) = .ok af)
    (hframe : saveFrameB vcp (allocResult vcp (readyAnswer vcp (LinkCheck.raAnswer vcp o))) = true)
    (hlead : leadOkB (allocResult vcp (readyAnswer vcp (LinkCheck.raAnswer vcp o))) af = true) :
    savedCheck vcp (allocResult vcp (readyAnswer vcp (LinkCheck.raAnswer vcp o))) = true :=
  savedCheck_of (savedCheckRF_pipe hcfg halloc) halloc (pipeAlloc_size hne o) hne hframe hlead

/-! ## `SaveOk` and `unwindRows` -/

theorem save_off {vc : VCode} {rf : RFunc} {r : Reg} {o : Nat}
    (h : (RAFrame.compute vc rf).saveOff.lookup r = some o) :
    o % 8 = 0 ∧ o < (RAFrame.compute vc rf).total := by
  have ho : (RAFrame.compute vc rf).offset (.save r) = .ok o := by
    simp [RAFrame.offset, h, pure, Except.pure]
  obtain ⟨h1, h2⟩ := live_align (vc := vc) (rf := rf) (l := .save r) trivial ho
  have h3 := compute_size_le_total vc rf
  have hb : slotBytes (.save r) = 8 ∨ slotBytes (.save r) = 16 := by
    cases r <;> simp [slotBytes]
  rcases hb with hb | hb <;> rw [hb] at h1 h2 <;> omega

/-- **`SaveOk` of block 0's leading stores** from the frame conditions. -/
theorem saveOk_of {vc : VCode} {rf : RFunc} {af : AFunc} (hRF : savedCheckRF vc rf = true)
    (halloc : lowerRFunc vc rf = .ok af) (hsz : rf.blocks.size = vc.blocks.size)
    (hne : vc.blocks.size ≠ 0) (hframe : saveFrameB vc rf = true)
    (hlead : leadOkB rf af = true) : ∀ a ∈ savesOf af, SaveOk af.frameSize a := by
  obtain ⟨code, h0, -, hall⟩ := frame_saves hRF halloc hsz hne hframe hlead
  have hfs := (lowerRFunc_ok halloc).1.1
  have hal : (RAFrame.compute vc rf).total % 16 = 0 := alignTo16_mod _
  intro a ha
  unfold savesOf at ha
  cases h : af.blocks[0]? with
  | none => rw [h] at h0; cases h0
  | some p =>
    rw [h] at h0 ha
    simp only [Option.map_some, Option.some.injEq] at h0
    obtain ⟨l, c⟩ := p
    simp only at h0 ha
    subst h0
    simp only [List.toList_toArray, List.drop_one, List.tail_cons] at ha
    obtain ⟨r, o, h1, h2⟩ := hall a ha
    obtain ⟨h3, h4⟩ := save_off h2
    refine ⟨r, o, h1, ?_, ?_⟩ <;> rw [hfs] <;> omega

/-- **`unwindRows` succeeds on the emitted code from the frame conditions**
(`unwindRows_complete` with `saveOk_of`). -/
theorem unwindRows_complete_frame {vc : VCode} {rf : RFunc} {af : AFunc} {k : Nat} {fa : FnAsm}
    {fb : FnBin} (hRF : savedCheckRF vc rf = true) (halloc : lowerRFunc vc rf = .ok af)
    (hsz : rf.blocks.size = vc.blocks.size) (hne : vc.blocks.size ≠ 0)
    (hframe : saveFrameB vc rf = true) (hlead : leadOkB rf af = true)
    (hemit : emitFunc k af = .ok fa) (hlay : fa.layout = .ok fb)
    (hcode : 4 * fb.words.size < 2 ^ 32) : ∃ rows, unwindRows af fa = .ok rows := by
  obtain ⟨vb, hvb⟩ : ∃ vb, vc.blocks[0]? = some vb := ⟨_, Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨items0, hit⟩ : ∃ items0, rf.blocks[0]? = some items0 :=
    ⟨_, Array.getElem?_eq_getElem (by omega)⟩
  exact unwindRows_complete halloc hemit hlay hcode hvb hit
    (saveOk_of hRF halloc hsz hne hframe hlead) (frame_saves_far hRF halloc hsz hne hframe hlead).2

/-! ## Without `saveFrameB` (#479): an outgoing area below 32560 bytes suffices -/

/-- `savedCheck_pipe` with the input-side bound on the outgoing area (`saveFrameB_always`)
instead of the output condition `saveFrameB`. -/
theorem savedCheck_pipe_out {vcp : VCode} {o : Lean.Json} {af : AFunc} {ss ps : Array (Array Nat)}
    (hcfg : vcp.cfg = .ok (ss, ps)) (hne : vcp.blocks.size ≠ 0)
    (halloc : lowerRFunc vcp (allocResult vcp (readyAnswer vcp (LinkCheck.raAnswer vcp o))) = .ok af)
    (hout : vcp.outgoing ≤ 32560)
    (hlead : leadOkB (allocResult vcp (readyAnswer vcp (LinkCheck.raAnswer vcp o))) af = true) :
    savedCheck vcp (allocResult vcp (readyAnswer vcp (LinkCheck.raAnswer vcp o))) = true :=
  savedCheck_pipe hcfg hne halloc (saveFrameB_always _ _ hout) hlead

/-- `unwindRows_complete_frame` with the bound on the outgoing area instead of `saveFrameB`. -/
theorem unwindRows_complete_frame_out {vc : VCode} {rf : RFunc} {af : AFunc} {k : Nat}
    {fa : FnAsm} {fb : FnBin} (hRF : savedCheckRF vc rf = true) (halloc : lowerRFunc vc rf = .ok af)
    (hsz : rf.blocks.size = vc.blocks.size) (hne : vc.blocks.size ≠ 0)
    (hout : vc.outgoing ≤ 32560) (hlead : leadOkB rf af = true)
    (hemit : emitFunc k af = .ok fa) (hlay : fa.layout = .ok fb)
    (hcode : 4 * fb.words.size < 2 ^ 32) : ∃ rows, unwindRows af fa = .ok rows :=
  unwindRows_complete_frame hRF halloc hsz hne (saveFrameB_always _ _ hout) hlead hemit hlay hcode

end Link.EhCheck.Complete
