import FV.E2E.RegLevelEmit
import FV.Backend.Proof.AssignOk
import FV.Backend.Proof.SpillLocalCheck
import FV.Backend.Proof.SpillStep4Cfg
import FV.Backend.Proof.SpillStep4
import FV.Backend.Proof.KillOfV

/-!
# `lowerRFunc` lowers the spill allocation (V5)

`lowerRFunc_spill_of`: `lowerRFunc vc (spillAlloc vc)` succeeds when the VCode meets the spill
allocator's local facts (`Spill.SpillLocalOk`), every instruction meets `ctlInstOk` at its place,
and block 0 starts with `Args` followed by more instructions (the frame has no size limit: slots
beyond 32 KiB are addressed through x16). The parts:

* `lowerRFunc_of`: the converse of `lowerRFunc_ok` — `lowerRFunc` succeeds when `ctlCheck`
  accepts and every item of every block has code (`itemCode`);
* every item the spill allocation emits is a move between a register and a register or a frame
  slot the frame has an offset for (`MoveOk`: spill homes, temporaries, the callee-save slots of
  `calleeSaved`, all of which `RAFrame.compute` lays out), or an instruction whose operand
  locations are `spillLocs` (all registers, as many as operands: `MInst.assign` succeeds,
  `assign_ok_of_operands`);
* `ctlCheck_spill`: block 0 is the saves (moves into memory), then `Args` (no uses, so no loads in
  front of it), and no `op 0` after it; no edge enters block 0 (`EdgesOk.entry`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Spill

/-! ## `lowerRFunc`'s success, structurally -/

theorem mapIdxM_go_ok_of {α β ε : Type} {f : Nat → α → Except ε β} :
    ∀ (l : List α) (acc : Array β), (∀ j a, l[j]? = some a → ∃ b, f (acc.size + j) a = .ok b) →
      ∃ out, List.mapIdxM.go f l acc = .ok out
  | [], acc, _ => ⟨acc.toList, rfl⟩
  | a :: l, acc, h => by
    obtain ⟨b, hb⟩ := h 0 a rfl
    rw [Nat.add_zero] at hb
    obtain ⟨out, hout⟩ := mapIdxM_go_ok_of l (acc.push b) fun j a' hj => by
      obtain ⟨b', hb'⟩ := h (j + 1) a' (by simpa using hj)
      exact ⟨b', by rw [Array.size_push, Nat.add_assoc, Nat.add_comm 1 j]; exact hb'⟩
    refine ⟨out, ?_⟩
    simp only [List.mapIdxM.go, bind, Except.bind, hb]
    exact hout

theorem array_mapIdxM_ok_of {α β ε : Type} {f : Nat → α → Except ε β} {as : Array α}
    (h : ∀ i a, as[i]? = some a → ∃ b, f i a = .ok b) : ∃ bs, as.mapIdxM f = .ok bs := by
  have e := Array.toList_mapIdxM (xs := as) (f := f)
  obtain ⟨out, hout⟩ := mapIdxM_go_ok_of (f := f) as.toList #[]
    (fun j a hj => by simpa using h j a (by simpa using hj))
  cases hm : as.mapIdxM f with
  | ok bs => exact ⟨bs, rfl⟩
  | error x =>
    rw [hm] at e
    simp only [Functor.map, Except.map, List.mapIdxM, hout] at e
    cases e

theorem itemsCode_ok_of {fr : RAFrame} {vb : VBlock} : ∀ {its : List RItem},
    (∀ it ∈ its, ∃ c, itemCode fr vb it = .ok c) → ∃ code, itemsCode fr vb its = .ok code
  | [], _ => ⟨[], rfl⟩
  | it :: its, h => by
    obtain ⟨c1, h1⟩ := h it (List.mem_cons_self ..)
    obtain ⟨c2, h2⟩ := itemsCode_ok_of (its := its) (fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact ⟨c1 ++ c2, by simp [itemsCode, h1, h2, bind, Except.bind, pure, Except.pure]⟩

theorem array_mapIdxM_ne_error {α β ε : Type} {f : Nat → α → Except ε β} {as : Array α}
    (h : ∀ i a, as[i]? = some a → ∃ b, f i a = .ok b) {e : ε} : as.mapIdxM f ≠ .error e := by
  obtain ⟨bs, hbs⟩ := array_mapIdxM_ok_of h
  rw [hbs]; intro c; cases c

/-- **`lowerRFunc` succeeds** when `ctlCheck` and `saveShapeOk` accept and every item has code
(the converse of `lowerRFunc_ok`). -/
theorem lowerRFunc_of {vc : VCode} {rf : RFunc} (hck : ctlCheck vc rf = true)
    (hss : saveShapeOk vc rf = true)
    (hit : ∀ (b : Nat) (vb : VBlock) (items : Array RItem), vc.blocks[b]? = some vb →
      rf.blocks[b]? = some items →
      ∀ it ∈ items.toList, ∃ c, itemCode (RAFrame.compute vc rf) vb it = .ok c) :
    ∃ af, lowerRFunc vc rf = .ok af := by
  cases hl : lowerRFunc vc rf with
  | ok af => exact ⟨af, rfl⟩
  | error err =>
  exfalso
  unfold lowerRFunc at hl
  simp only [bind, Except.bind] at hl
  -- `ctlCheck`
  rw [ite_eq_right (by simp [hck])] at hl
  rw [ite_eq_right (by simp [hss])] at hl
  split at hl
  · rename_i e hm
    refine array_mapIdxM_ne_error (fun bi x hx => ?_) hm
    obtain ⟨vb, items⟩ := x
    obtain ⟨hvb, hitm⟩ := Array.getElem?_zip_eq_some.mp hx
    simp only
    rw [← Array.forIn_toList, forIn_except_yield _ _ _ (fun it c => itemStep (RAFrame.compute vc rf) vb c it)]
    · rw [itemsCode_foldl]
      obtain ⟨code, hc⟩ := itemsCode_ok_of (hit bi vb items hvb hitm)
      rw [hc]
      exact ⟨_, rfl⟩
    · intro it c
      cases it with
      | move src dst =>
        simp only [itemStep]
        cases (RAFrame.compute vc rf).moveInsts src dst <;> rfl
      | op k allocs =>
        simp only [itemStep, bind, Except.bind]
        generalize (Array.mapM (fun x => match x with
          | Loc.reg r => (pure r : Except String Reg)
          | l => throw (toString "operand in " ++ toString (repr l))) allocs) = M
        cases M with
        | error e => rfl
        | ok regs =>
          simp only
          cases vb.insts[k]? with
          | none => rfl
          | some i =>
            simp only
            cases i.assign regs with
            | error e => rfl
            | ok m => cases m <;> rfl
  · simp [pure, Except.pure] at hl

/-! ## The items of the spill allocation -/

/-- A location the frame has an offset for, or a register. -/
def SlotOk : Loc → Prop
  | .save r => r ∈ calleeSaved
  | _ => True

/-- A move between a register and a register or a slot with an offset. -/
def MoveOk (a b : Loc) : Prop := (∃ r, a = .reg r ∧ SlotOk b) ∨ (∃ r, b = .reg r ∧ SlotOk a)

/-- The items of the spill allocation of block `vb`: such moves, and instructions of the block
with the operand locations `spillLocs`. -/
def ItemOk (vb : VBlock) : RItem → Prop
  | .move a b => MoveOk a b
  | .op k locs => ∃ i, vb.insts[k]? = some i ∧
      ∀ ops, i.operands = .ok ops → locs = spillLocs ops i.clobbers

theorem baseLoc_reg (is fs : List Reg) (pre : List Operand) (o : Operand) :
    ∃ r, baseLoc is fs pre o = .reg r := by
  unfold baseLoc
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · split <;> exact ⟨_, rfl⟩

/-- Every location `spillLocs` computes is a register. -/
theorem spillLocs_reg {ops : Array Operand} {clob : List Reg} {l : Loc}
    (h : l ∈ (spillLocs ops clob).toList) : ∃ r, l = .reg r := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp h
  rw [Array.getElem?_toList, spillLocs_get] at hj
  cases ho : ops.toList[j]? with
  | none => rw [ho] at hj; cases hj
  | some o =>
    rw [ho] at hj
    simp only [Option.map_some, Option.some.injEq] at hj
    subst hj
    unfold locOf
    split
    · rename_i i _
      cases ops.toList[i]? with
      | none => exact ⟨_, rfl⟩
      | some oi => exact baseLoc_reg _ _ _ _
    · exact baseLoc_reg _ _ _ _

theorem mem_pairs_reg {ops : Array Operand} {clob : List Reg} {x : Operand × Loc}
    (h : x ∈ (ops.zip (spillLocs ops clob)).toList) : ∃ r, x.2 = .reg r := by
  rw [Array.toList_zip] at h
  exact spillLocs_reg (List.of_mem_zip h).2

theorem keptPairs_sub {i : MInst} {pairs : List (Operand × Loc)} {x : Operand × Loc}
    (h : x ∈ keptPairs i pairs) : x ∈ pairs := by
  unfold keptPairs at h
  split at h
  · exact (List.mem_filter.mp h).1
  · exact (List.mem_filter.mp (List.mem_of_mem_take h)).1

theorem slotOk_home (h : Homes) (v : Nat) (c : RegClass) : SlotOk (spillHome h v c) := trivial

theorem itemOk_spillInst {h : Homes} {vb : VBlock} {k : Nat} {i : MInst}
    (hi : vb.insts[k]? = some i) {it : RItem} (hit : it ∈ spillInst h k i) : ItemOk vb it := by
  unfold spillInst at hit
  split at hit
  · rename_i e he
    simp only [List.mem_singleton] at hit
    subst hit
    exact ⟨i, hi, fun ops hops => by rw [hops] at he; cases he⟩
  · rename_i ops hops
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hit
    rcases hit with ((hr | ⟨⟨o, l⟩, hx, rfl⟩) | rfl) | hs
    · split at hr
      · simp only [spillRestores, List.mem_map] at hr
        obtain ⟨r, hr, rfl⟩ := hr
        exact .inr ⟨r, rfl, hr⟩
      · cases hr
    · obtain ⟨r, rfl⟩ := mem_pairs_reg ((List.mem_filter.mp hx).1)
      exact .inr ⟨r, rfl, slotOk_home _ _ _⟩
    · exact ⟨i, hi, fun ops' hops' => by rw [hops] at hops'; cases hops'; rfl⟩
    · split at hs
      · cases hs
      · simp only [List.mem_map] at hs
        obtain ⟨⟨o, l⟩, hx, rfl⟩ := hs
        obtain ⟨r, hr⟩ := mem_pairs_reg (keptPairs_sub hx)
        simp only at hr; subst hr
        exact .inl ⟨r, rfl, slotOk_home _ _ _⟩

theorem itemOk_argMoves {h : Homes} {vb tb : VBlock} {it : RItem}
    (hit : it ∈ spillArgMoves h vb tb) : ItemOk vb it := by
  unfold spillArgMoves at hit
  simp only [List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hit
  rcases hit with ⟨_, _, rfl | rfl⟩ | ⟨_, _, rfl | rfl⟩
  · exact .inr ⟨_, rfl, trivial⟩
  · exact .inl ⟨_, rfl, trivial⟩
  · exact .inr ⟨_, rfl, trivial⟩
  · exact .inl ⟨_, rfl, trivial⟩

theorem termEdgeDefs_reg {vb : VBlock} {j : Nat} {x : Operand × Loc}
    (h : x ∈ termEdgeDefs vb j) : ∃ r, x.2 = .reg r := by
  unfold termEdgeDefs at h
  cases hb : vb.insts.back? with
  | none => rw [hb] at h; cases h
  | some i =>
    rw [hb] at h
    simp only at h
    split at h
    · cases h
    · cases hop : i.operands with
      | error e => rw [hop] at h; cases h
      | ok ops =>
        rw [hop] at h
        have hk : ∀ y ∈ keptPairs i (ops.zip (spillLocs ops i.clobbers)).toList, ∃ r, y.2 = .reg r :=
          fun y hy => mem_pairs_reg (keptPairs_sub hy)
        simp only at h
        split at h
        · split at h
          · exact hk x (List.mem_of_mem_take h)
          · exact hk x h
        · exact hk x h

theorem itemOk_entryStores {vc : VCode} {succs preds : Array (Array Nat)} {s : Nat}
    {vb : VBlock} {it : RItem} (hit : it ∈ spillEntryStores (spillHomes vc) vc succs preds s) :
    ItemOk vb it := by
  rw [Spill.spillEntryStores_eq (vc := vc) (succs := succs) (preds := preds) s] at hit
  simp only [List.map_map, List.mem_map] at hit
  obtain ⟨x, hx, rfl⟩ := hit
  obtain ⟨_, _, _, _, -, -, -, -, hx'⟩ := Spill.entryPairs_spec (vc := vc) (succs := succs) (preds := preds) hx
  obtain ⟨r, hr⟩ := termEdgeDefs_reg hx'
  exact .inl ⟨r, hr, trivial⟩

theorem argMovesOf_sub {vc : VCode} {succs : Array (Array Nat)} {b : Nat} {vb : VBlock} {it : RItem}
    (h : it ∈ argMovesOf vc succs b vb) : ∃ tb, it ∈ spillArgMoves (spillHomes vc) vb tb := by
  rcases hs : succs[b]? with _ | ⟨_ | ⟨t, _ | ⟨c, l⟩⟩⟩
  · unfold argMovesOf at h; rw [hs] at h; cases h
  · unfold argMovesOf at h; rw [hs] at h; cases h
  · cases ht : vc.blocks[t]? with
    | none =>
      unfold argMovesOf at h; rw [hs] at h
      change it ∈ (match vc.blocks[t]? with
        | some tb => spillArgMoves (spillHomes vc) vb tb
        | none => []) at h
      rw [ht] at h; cases h
    | some tb => rw [argMovesOf_eq hs ht] at h; exact ⟨tb, h⟩
  · unfold argMovesOf at h; rw [hs] at h; cases h

theorem argMoves_isMove {h : Homes} {vb tb : VBlock} {it : RItem}
    (hit : it ∈ spillArgMoves h vb tb) : it.isMove = true := by
  unfold spillArgMoves at hit
  simp only [List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hit
  rcases hit with ⟨_, _, rfl | rfl⟩ | ⟨_, _, rfl | rfl⟩ <;> rfl

/-- **Every item of the spill allocation is `ItemOk`.** -/
theorem itemOk_spillAlloc {vc : VCode} {ss ps : Array (Array Nat)} (hcfg : vc.cfg = .ok (ss, ps))
    {b : Nat} {vb : VBlock} {items : Array RItem}
    (hvb : vc.blocks[b]? = some vb) (hit : (spillAlloc vc).blocks[b]? = some items) :
    ∀ it ∈ items.toList, ItemOk vb it := by
  rw [Spill.spillAlloc_block hcfg hvb] at hit
  obtain rfl := Option.some.inj hit
  intro it hm
  simp only [List.mem_append, List.mem_flatMap] at hm
  rcases hm with (hs | he) | ⟨⟨i, k⟩, hik, hm⟩
  · split at hs
    · simp only [spillSaves, List.mem_map] at hs
      obtain ⟨r, hr, rfl⟩ := hs
      exact .inl ⟨r, rfl, hr⟩
    · cases hs
  · exact itemOk_entryStores he
  · have hi : vb.insts[k]? = some i := by
      have := List.mem_zipIdx_iff_getElem?.mp hik
      simpa using this
    unfold bodyItem at hm
    rcases List.mem_append.mp hm with hm | hm
    · split at hm
      · obtain ⟨tb, htb⟩ := argMovesOf_sub hm
        exact itemOk_argMoves htb
      · cases hm
    · exact itemOk_spillInst hi hm

/-! ## The frame and the code of each item -/

theorem calleeSaved_cls : ∀ r ∈ calleeSaved, r.realClass? = some .float ∨ r.realClass? = some .int := by
  decide

theorem fold_keys {α : Type} (step : Nat) : ∀ (rs : List α) (acc : List (α × Nat)) (o : Nat),
    ((rs.foldl (fun (x : List (α × Nat) × Nat) r => match x with
      | (acc, o) => (acc ++ [(r, o)], o + step)) (acc, o)).1).map Prod.fst = acc.map Prod.fst ++ rs
  | [], acc, o => by simp
  | r :: rs, acc, o => by
    rw [List.foldl_cons, fold_keys step rs]
    simp

theorem lookup_some_of_mem {l : List (Reg × Nat)} {r : Reg} (h : r ∈ l.map Prod.fst) :
    ∃ o, l.lookup r = some o := by
  induction l with
  | nil => cases h
  | cons p l ih =>
    obtain ⟨q, o⟩ := p
    simp only [List.lookup_cons]
    by_cases e : r = q
    · subst e; exact ⟨o, by simp⟩
    · have : (r == q) = false := by simpa using e
      rw [this]
      simp only [List.map_cons, List.mem_cons] at h
      exact ih (h.resolve_left e)

/-- The spill allocation's frame has a save slot for every callee-saved register. -/
theorem saveOff_spill (vc : VCode) {r : Reg} (hr : r ∈ calleeSaved) :
    ∃ o, (RAFrame.compute vc (spillAlloc vc)).saveOff.lookup r = some o := by
  apply lookup_some_of_mem
  have hsv : (spillAlloc vc).saved = calleeSaved := rfl
  simp only [RAFrame.compute, hsv, List.map_map]
  simpa [Function.comp_def] using hr

theorem offset_ok (vc : VCode) {l : Loc} (hl : SlotOk l) (hr : ∀ r, l ≠ .reg r) :
    ∃ o, (RAFrame.compute vc (spillAlloc vc)).offset l = .ok o := by
  cases l with
  | reg r => exact absurd rfl (hr r)
  | stack s c => cases c <;> exact ⟨_, rfl⟩
  | save r =>
    obtain ⟨o, ho⟩ := saveOff_spill vc hl
    exact ⟨o, by simp [RAFrame.offset, ho, pure, Except.pure]⟩

theorem moveInsts_ok (vc : VCode) {a b : Loc} (h : MoveOk a b) :
    ∃ l, (RAFrame.compute vc (spillAlloc vc)).moveInsts a b = .ok l := by
  rcases h with ⟨r, rfl, hb⟩ | ⟨r, rfl, ha⟩
  · cases b with
    | reg q =>
      unfold RAFrame.moveInsts
      split <;> first | exact ⟨_, rfl⟩ | (split <;> exact ⟨_, rfl⟩)
    | _ =>
      obtain ⟨o, ho⟩ := offset_ok vc hb (fun _ e => by cases e)
      simp only [RAFrame.moveInsts, ho, bind, Except.bind]
      exact ⟨_, rfl⟩
  · cases a with
    | reg q =>
      unfold RAFrame.moveInsts
      split <;> first | exact ⟨_, rfl⟩ | (split <;> exact ⟨_, rfl⟩)
    | _ =>
      obtain ⟨o, ho⟩ := offset_ok vc ha (fun _ e => by cases e)
      simp only [RAFrame.moveInsts, ho, bind, Except.bind]
      exact ⟨_, rfl⟩

theorem mapM_regs_ok {g : Loc → Except String Reg} (hg : ∀ r, g (.reg r) = .ok r) :
    ∀ (locs : List Loc), (∀ l ∈ locs, ∃ r, l = .reg r) →
      ∃ regs : List Reg, locs.mapM g = .ok regs ∧ regs.length = locs.length
  | [], _ => ⟨[], rfl, rfl⟩
  | l :: ls, h => by
    obtain ⟨r, rfl⟩ := h l (List.mem_cons_self ..)
    obtain ⟨regs, hm, hn⟩ := mapM_regs_ok hg ls (fun x hx => h x (List.mem_cons_of_mem _ hx))
    refine ⟨r :: regs, ?_, by simp [hn]⟩
    simp only [List.mapM_cons, hm, hg]
    rfl

theorem mapM_regs_of {g : Loc → Except String Reg} (hg : ∀ r, g (.reg r) = .ok r)
    {locs : Array Loc} {res : Except String (Array Reg)}
    (h : ∀ l ∈ locs.toList, ∃ r, l = .reg r) (hres : locs.mapM g = res) :
    ∃ regs, res = .ok regs ∧ regs.size = locs.size := by
  obtain ⟨regs, hm, hn⟩ := mapM_regs_ok hg locs.toList h
  refine ⟨regs.toArray, ?_, by simp [hn]⟩
  rw [← hres, Array.mapM_eq_mapM_toList, hm]
  rfl

/-- **Every item of the spill allocation has code**, given the instructions' operand views. -/
theorem itemCode_spill (vc : VCode) {vb : VBlock} {it : RItem} (hit : ItemOk vb it)
    (hops : ∀ (k : Nat) (i : MInst), vb.insts[k]? = some i → ∃ ops, i.operands = .ok ops) :
    ∃ c, itemCode (RAFrame.compute vc (spillAlloc vc)) vb it = .ok c := by
  cases it with
  | move a b =>
    obtain ⟨l, hl⟩ := moveInsts_ok vc hit
    simp only [itemCode, itemStep, hl, bind, Except.bind]
    exact ⟨_, rfl⟩
  | op k locs =>
    obtain ⟨i, hi, hloc⟩ := hit
    obtain ⟨ops, hop⟩ := hops k i hi
    have hl := hloc ops hop
    subst hl
    unfold itemCode itemStep
    simp only [bind, Except.bind]
    split
    · rename_i e heq
      obtain ⟨regs, hr, -⟩ := mapM_regs_of (by intro r; rfl) (fun l hl => spillLocs_reg hl) heq
      cases hr
    · rename_i regs heq
      obtain ⟨regs', hr, hn⟩ := mapM_regs_of (by intro r; rfl) (fun l hl => spillLocs_reg hl) heq
      have hn' : regs.size = ops.size := by
        cases hr; rw [hn, spillLocs_size]
      obtain ⟨i', hi'⟩ := assign_ok_of_operands (regs := regs) hop hn'
      rw [hi]
      simp only [hi']
      cases i' <;> exact ⟨_, rfl⟩

/-! ## `ctlCheck` -/

theorem takeWhile_append_cons {α : Type} {p : α → Bool} {x : α} (hx : p x = false) :
    ∀ {l1 : List α} (l2 : List α), (∀ a ∈ l1, p a = true) →
      (l1 ++ x :: l2).takeWhile p = l1 ∧ (l1 ++ x :: l2).dropWhile p = x :: l2
  | [], l2, _ => by simp [hx]
  | a :: l1, l2, h => by
    have ha := h a (List.mem_cons_self ..)
    obtain ⟨h1, h2⟩ := takeWhile_append_cons hx (l1 := l1) l2 (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp [ha, h1, h2]

theorem spillInst_op {h : Homes} {k : Nat} {i : MInst} {it : RItem} (hit : it ∈ spillInst h k i)
    (h0 : it.isOp0 = true) : k = 0 := by
  unfold spillInst at hit
  split at hit
  · simp only [List.mem_singleton] at hit; subst hit
    cases k <;> simp_all [RItem.isOp0]
  · simp only [List.mem_append, List.mem_map, List.mem_singleton] at hit
    rcases hit with ((hr | ⟨_, _, rfl⟩) | rfl) | hs
    · split at hr
      · simp only [spillRestores, List.mem_map] at hr
        obtain ⟨r, -, rfl⟩ := hr; cases h0
      · cases hr
    · cases h0
    · cases k <;> simp_all [RItem.isOp0]
    · split at hs
      · cases hs
      · simp only [List.mem_map] at hs
        obtain ⟨_, _, rfl⟩ := hs; cases h0

/-- The items of an instruction: some before it, the instruction, moves after it; nothing before
it when it has no uses and is no `Rets`. -/
theorem spillInst_shape {h : Homes} {k : Nat} {i : MInst} {ops : Array Operand}
    (hops : i.operands = .ok ops) :
    ∃ pre post, spillInst h k i = pre ++ RItem.op k (spillLocs ops i.clobbers) :: post ∧
      (∀ it ∈ post, it.isMove = true) ∧
      ((∀ o ∈ ops.toList, o.kind ≠ .use) → (∀ us, i ≠ .rets us) → pre = []) := by
  unfold spillInst
  rw [hops]
  dsimp only
  refine ⟨_, _, List.append_assoc _ _ _, ?_, ?_⟩
  · intro it hit
    split at hit
    · cases hit
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hit; rfl
  · intro hu hr
    have hf : ((ops.zip (spillLocs ops i.clobbers)).toList.filter (fun x => x.1.kind == .use)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx
      rw [Array.toList_zip] at hx
      simpa using hu x.1 (List.of_mem_zip hx).1
    rw [hf, List.map_nil, List.append_nil]
    split
    · rename_i us; exact absurd rfl (hr us)
    · rfl

theorem args_noUse {ds : List (Reg × Reg)} {ops : Array Operand}
    (hops : (MInst.args ds).operands = .ok ops) : ∀ o ∈ ops.toList, o.kind ≠ .use := by
  intro o ho hu
  have := ((Kill.operands_kinds hops) o ho).1 hu
  simp [Kill.useRegsK, MInst.uses, Kill.pairUses] at this

/-- **`ctlCheck` accepts the spill allocation** of a VCode whose instructions meet `ctlInstOk`
at their places, whose block 0 starts with `Args` and has more instructions, and which meets
the local facts (no edge into block 0, operand views). -/
theorem ctlCheck_spill {vc : VCode} {ss ps : Array (Array Nat)} (hcfg : vc.cfg = .ok (ss, ps))
    (hloc : SpillLocalOk vc)
    (hins : ∀ (b : Nat) (vb : VBlock) (k : Nat) (i : MInst), vc.blocks[b]? = some vb →
      vb.insts[k]? = some i → ctlInstOk b k i = true)
    (h0 : ∃ vb0 ds, vc.blocks[0]? = some vb0 ∧ vb0.insts[0]? = some (.args ds) ∧ 1 < vb0.insts.size) :
    ctlCheck vc (spillAlloc vc) = true := by
  have hp0 : ps[0]? = some #[] := (hloc.2.2 ss ps hcfg).entry.2.1
  obtain ⟨vb0, ds, hvb0, hi0, hn0⟩ := h0
  unfold ctlCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- the instructions
    simp only [List.all_eq_true]
    intro x hx y hy
    have hb := List.mem_zipIdx_iff_getElem?.mp hx
    have hk := List.mem_zipIdx_iff_getElem?.mp hy
    exact hins x.2 x.1 y.2 y.1 (by simpa using hb) (by simpa using hk)
  · -- block 0: the saves, then `Args`, then no `op 0`
    obtain ⟨ops, hops, -, -⟩ := hloc.1 0 vb0 0 (.args ds) hvb0 hi0
    obtain ⟨pre, post, hsi, hpost, hpre⟩ := spillInst_shape (h := spillHomes vc) (k := 0) hops
    rw [hpre (args_noUse hops) (fun us e => by cases e), List.nil_append] at hsi
    obtain ⟨rest, hrest⟩ : ∃ rest, vb0.insts.toList = .args ds :: rest := by
      cases e : vb0.insts.toList with
      | nil => rw [← Array.getElem?_toList, e] at hi0; cases hi0
      | cons a rest =>
        rw [← Array.getElem?_toList, e] at hi0
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi0
        exact ⟨rest, by rw [hi0]⟩
    have hes : spillEntryStores (spillHomes vc) vc ss ps 0 = [] :=
      Spill.spillEntryStores_ne (vc := vc) (succs := ss) (preds := ps) (fun b hb => by rw [hp0] at hb; cases hb)
    have hbi : bodyItem vc ss 0 vb0 (.args ds, 0) =
        RItem.op 0 (spillLocs ops (MInst.args ds).clobbers) :: post := by
      unfold bodyItem
      rw [ite_eq_right (by simp only [Bool.and_eq_true, beq_iff_eq]; omega), hsi, List.nil_append]
    rw [Spill.spillAlloc_block hcfg hvb0, Option.getD_some, List.toList_toArray, hes, hrest,
      List.zipIdx_cons, List.flatMap_cons, hbi]
    simp only [beq_self_eq_true, ite_true, List.append_nil, List.cons_append]
    obtain ⟨h1, h2⟩ := takeWhile_append_cons (p := RItem.isMove)
      (x := RItem.op 0 (spillLocs ops (MInst.args ds).clobbers)) rfl
      (l1 := spillSaves) (post ++ (rest.zipIdx (0 + 1)).flatMap (bodyItem vc ss 0 vb0))
      (by intro a ha; simp only [spillSaves, List.mem_map] at ha; obtain ⟨_, _, rfl⟩ := ha; rfl)
    rw [h1, h2]
    refine ⟨by decide, ?_⟩
    simp only [List.drop_succ_cons, List.drop_zero, List.all_eq_true, List.mem_append,
      List.mem_flatMap, Bool.not_eq_eq_eq_not, Bool.not_true]
    rintro it (hit | ⟨⟨i, k⟩, hik, hit⟩)
    · have := hpost it hit
      cases it <;> simp_all [RItem.isMove, RItem.isOp0]
    · have hk : 1 ≤ k := List.le_snd_of_mem_zipIdx hik
      unfold bodyItem at hit
      rcases List.mem_append.mp hit with hit | hit
      · split at hit
        · obtain ⟨tb, htb⟩ := argMovesOf_sub hit
          have := argMoves_isMove htb
          cases it <;> simp_all [RItem.isMove, RItem.isOp0]
        · cases hit
      · cases e : it.isOp0
        · rfl
        · exact absurd (spillInst_op hit e) (by omega)
  · -- no edge into block 0
    rw [hcfg]
    simp only [Array.all_eq_true', bne_iff_ne, ne_eq]
    intro sb hsb s hs e
    subst e
    obtain ⟨b, hb⟩ := Array.getElem?_of_mem hsb
    exact preds_empty hcfg hp0 hb (by simpa using hs)

/-! ## The callee-save shape of the spill allocation (`saveShapeOk`) -/

/-- A move that touches no save slot and none of the registers `rs`. -/
def PlainMv (rs : List Reg) (it : RItem) : Prop :=
  ∃ a b, it = .move a b ∧ a.isSave = false ∧ b.isSave = false ∧ ∀ r ∈ rs, a ≠ .reg r ∧ b ≠ .reg r

theorem PlainMv.isMove {rs : List Reg} {it : RItem} (h : PlainMv rs it) : it.isMove = true := by
  obtain ⟨a, b, rfl, -⟩ := h; rfl

theorem PlainMv.noSave {rs : List Reg} {it : RItem} (h : PlainMv rs it) : it.noSave = true := by
  obtain ⟨a, b, rfl, ha, hb, -⟩ := h; simp [RItem.noSave, ha, hb]

theorem PlainMv.restoreReg {rs : List Reg} {it : RItem} (h : PlainMv rs it) : it.restoreReg = none := by
  obtain ⟨a, b, rfl, ha, -⟩ := h; cases a <;> simp_all [RItem.restoreReg, Loc.isSave]

theorem saveSegsOk_moves (vb : VBlock) (saved : List Reg) : ∀ (xs pend ys : List RItem),
    (∀ x ∈ xs, x.isMove = true) →
    saveSegsOk vb saved pend (xs ++ ys) = saveSegsOk vb saved (pend ++ xs) ys
  | [], pend, ys, _ => by simp
  | x :: xs, pend, ys, h => by
    obtain ⟨a, b, rfl⟩ : ∃ a b, x = .move a b := by
      have := h x (List.mem_cons_self ..); cases x <;> simp_all [RItem.isMove]
    simp only [List.cons_append, saveSegsOk]
    rw [saveSegsOk_moves vb saved xs _ ys (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    simp

theorem retTailOk_plain (saved : List Reg) : ∀ (P L : List RItem), (∀ x ∈ P, PlainMv [] x) →
    retTailOk saved [] (P ++ L) = retTailOk saved [] L
  | [], L, _ => rfl
  | x :: P, L, h => by
    have hx := h x (List.mem_cons_self ..)
    have hr := hx.restoreReg
    obtain ⟨a, b, rfl, ha, hb, -⟩ := hx
    simp only [List.cons_append, retTailOk, hr]
    simp [RItem.avoids, ha, hb, retTailOk_plain saved P L (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem retTailOk_tail (saved : List Reg) : ∀ L : List RItem, (∀ x ∈ L, PlainMv saved x) →
    retTailOk saved saved L = true
  | [], _ => by simp [retTailOk]
  | x :: L, h => by
    have hx := h x (List.mem_cons_self ..)
    have hr := hx.restoreReg
    obtain ⟨a, b, rfl, ha, hb, hab⟩ := hx
    have ih := retTailOk_tail saved L (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [retTailOk, hr, RItem.avoids, ha, hb, ih, Bool.not_false, Bool.true_and, Bool.and_true]
    simp only [Bool.not_eq_true', List.any_eq_false]
    intro r hr'
    simp [(hab r hr').1, (hab r hr').2]

theorem retTailOk_restores (saved : List Reg) (L : List RItem) (hL : ∀ x ∈ L, PlainMv saved x) :
    ∀ (done rs : List Reg), done ++ rs = saved →
    retTailOk saved done (rs.map (fun r => RItem.move (.save r) (.reg r)) ++ L) = true
  | done, [], h => by
    simp only [List.append_nil] at h; subst h
    simpa using retTailOk_tail done L hL
  | done, r :: rs, h => by
    have hget : saved[done.length]? = some r := by rw [← h]; simp
    simp only [List.map_cons, List.cons_append, retTailOk, RItem.restoreReg, RItem.isRestore,
      beq_self_eq_true, hget, Bool.true_and]
    exact retTailOk_restores saved L hL (done ++ [r]) rs (by rw [← h]; simp)

/-- The location `spillLocs` gives a fixed operand is its register. -/
theorem pair_fixed {ops : Array Operand} {clob : List Reg} {o : Operand} {l : Loc} {p : Reg}
    (h : (o, l) ∈ (ops.zip (spillLocs ops clob)).toList) (hc : o.con = .fixed p) : l = .reg p := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp h
  rw [Array.getElem?_toList, Array.getElem?_zip_eq_some] at hj
  obtain ⟨h1, h2⟩ := hj
  rw [← Array.getElem?_toList] at h1
  rw [spillLocs_get, h1] at h2
  simp only [Option.map_some, Option.some.injEq] at h2
  subst h2
  unfold locOf
  rw [hc]
  simp [baseLoc, hc]

theorem rets_or (i : MInst) : (∃ us, i = .rets us) ∨
    ((match i with | .rets _ => spillRestores | _ => []) = [] ∧ ∀ us, i ≠ .rets us) := by
  cases i <;> simp

/-- The items of one instruction of the spill allocation: save-free moves, the restores before
a `Rets` (whose loads avoid the callee-saved registers), the instruction, save-free moves. -/
theorem saveSegs_body (vc : VCode) (succs : Array (Array Nat)) (bi : Nat) (vb : VBlock)
    (hinst : ∀ (k : Nat) (i : MInst), vb.insts[k]? = some i → SpillInstOk i) :
    ∀ (xs : List (MInst × Nat)) (C : List RItem), (∀ x ∈ xs, vb.insts[x.2]? = some x.1) →
      (∀ c ∈ C, PlainMv [] c) →
      saveSegsOk vb calleeSaved C (xs.flatMap (bodyItem vc succs bi vb)) = true
  | [], C, _, hC => by
    simp only [List.flatMap_nil, saveSegsOk, List.all_eq_true]
    exact fun c hc => (hC c hc).noSave
  | (i, k) :: xs, C, hxs, hC => by
    have hk : vb.insts[k]? = some i := hxs (i, k) (List.mem_cons_self ..)
    obtain ⟨ops, hops, -, hrets⟩ := hinst k i hk
    -- the argument copies
    have hM : ∀ x ∈ (if k + 1 == vb.insts.size && !vb.branchArgs.isEmpty then
        argMovesOf vc succs bi vb else []), PlainMv [] x := by
      intro x hx
      split at hx
      · obtain ⟨tb, htb⟩ := argMovesOf_sub hx
        unfold spillArgMoves at htb
        simp only [List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at htb
        rcases htb with ⟨_, _, rfl | rfl⟩ | ⟨_, _, rfl | rfl⟩ <;>
          exact ⟨_, _, rfl, by simp [spillHome, Loc.isSave], by simp [spillHome, Loc.isSave], by simp⟩
      · cases hx
    -- the loads and the stores
    have hpair : ∀ x ∈ (ops.zip (spillLocs ops i.clobbers)).toList, ∃ r, x.2 = .reg r :=
      fun x hx => mem_pairs_reg hx
    have hL : ∀ x ∈ ((ops.zip (spillLocs ops i.clobbers)).toList.filter (·.1.kind == .use)).map
        (fun (o, l) => RItem.move (spillHome (spillHomes vc) o.vreg o.cls) l), PlainMv [] x := by
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨⟨o, l⟩, hol, rfl⟩ := hx
      obtain ⟨r, hr⟩ := hpair _ (List.mem_filter.mp hol).1
      simp only at hr; subst hr
      exact ⟨_, _, rfl, by simp [spillHome, Loc.isSave], by simp [Loc.isSave], by simp⟩
    have hS : ∀ x ∈ (if i.isTerminator then [] else
        (keptPairs i (ops.zip (spillLocs ops i.clobbers)).toList).map fun (o, l) =>
          RItem.move l (spillHome (spillHomes vc) o.vreg o.cls)), PlainMv [] x := by
      intro x hx
      split at hx
      · cases hx
      · simp only [List.mem_map] at hx
        obtain ⟨⟨o, l⟩, hol, rfl⟩ := hx
        obtain ⟨r, hr⟩ := hpair _ (keptPairs_sub hol)
        simp only at hr; subst hr
        exact ⟨_, _, rfl, by simp [Loc.isSave], by simp [spillHome, Loc.isSave], by simp⟩
    have hLr : (∃ us, i = .rets us) → ∀ x ∈ ((ops.zip (spillLocs ops i.clobbers)).toList.filter
        (·.1.kind == .use)).map (fun (o, l) => RItem.move (spillHome (spillHomes vc) o.vreg o.cls) l),
        PlainMv calleeSaved x := by
      rintro ⟨us, hus⟩ x hx
      simp only [List.mem_map] at hx
      obtain ⟨⟨o, l⟩, hol, rfl⟩ := hx
      have hz := (List.mem_filter.mp hol).1
      have ho : o ∈ ops.toList := by
        rw [Array.toList_zip] at hz; exact (List.of_mem_zip hz).1
      obtain ⟨p, hc, hp⟩ := hrets us hus o ho
      obtain rfl := pair_fixed hz hc
      exact ⟨_, _, rfl, by simp [spillHome, Loc.isSave], by simp [Loc.isSave], fun r hr =>
        ⟨by simp [spillHome], fun e => hp (by injection e with e; rw [e]; exact hr)⟩⟩
    have hbody : bodyItem vc succs bi vb (i, k) =
        (if k + 1 == vb.insts.size && !vb.branchArgs.isEmpty then argMovesOf vc succs bi vb else []) ++
        ((match i with | .rets _ => spillRestores | _ => []) ++
          ((ops.zip (spillLocs ops i.clobbers)).toList.filter (·.1.kind == .use)).map
            (fun (o, l) => RItem.move (spillHome (spillHomes vc) o.vreg o.cls) l) ++
          [RItem.op k (spillLocs ops i.clobbers)] ++
          (if i.isTerminator then [] else
            (keptPairs i (ops.zip (spillLocs ops i.clobbers)).toList).map fun (o, l) =>
              RItem.move l (spillHome (spillHomes vc) o.vreg o.cls))) := by
      unfold bodyItem spillInst
      simp only [hops, List.append_assoc]
    generalize (if k + 1 == vb.insts.size && !vb.branchArgs.isEmpty then
      argMovesOf vc succs bi vb else []) = M at hM hbody
    generalize ((ops.zip (spillLocs ops i.clobbers)).toList.filter (·.1.kind == .use)).map
      (fun (o, l) => RItem.move (spillHome (spillHomes vc) o.vreg o.cls) l) = L at hL hLr hbody
    generalize (if i.isTerminator then [] else
      (keptPairs i (ops.zip (spillLocs ops i.clobbers)).toList).map fun (o, l) =>
        RItem.move l (spillHome (spillHomes vc) o.vreg o.cls)) = S at hS hbody
    have hrest := saveSegs_body vc succs bi vb hinst xs S
      (fun x hx => hxs x (List.mem_cons_of_mem _ hx)) hS
    rw [List.flatMap_cons, hbody]
    rcases rets_or i with ⟨us, rfl⟩ | ⟨hR, hne⟩
    · -- a `Rets`: save-free moves, the restores, then loads into return registers
      have hL' := hLr ⟨us, rfl⟩
      have hRm : ∀ x ∈ spillRestores, x.isMove = true := by
        intro x hx; simp only [spillRestores, List.mem_map] at hx; obtain ⟨_, _, rfl⟩ := hx; rfl
      have hMv : ∀ x ∈ M ++ (spillRestores ++ L), x.isMove = true := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact (hM x hx).isMove
        · rcases List.mem_append.mp hx with hx | hx
          · exact hRm x hx
          · exact (hL x hx).isMove
      have e : M ++ (spillRestores ++ L ++ [RItem.op k (spillLocs ops (MInst.rets us).clobbers)] ++ S) ++
          xs.flatMap (bodyItem vc succs bi vb) =
          (M ++ (spillRestores ++ L)) ++ (RItem.op k (spillLocs ops (MInst.rets us).clobbers) ::
            (S ++ xs.flatMap (bodyItem vc succs bi vb))) := by
        simp
      simp only at hbody ⊢
      rw [e, saveSegsOk_moves vb calleeSaved _ C _ hMv]
      simp only [saveSegsOk, hk, Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · simp only [ite_true]
        rw [← List.append_assoc, retTailOk_plain _ _ _ (fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · exact hC x hx
          · exact hM x hx)]
        exact retTailOk_restores calleeSaved L hL' [] calleeSaved rfl
      · rw [saveSegsOk_moves vb calleeSaved S [] _ (fun x hx => (hS x hx).isMove)]
        simpa using hrest
    · rw [hR]
      have hMv : ∀ x ∈ M ++ L, x.isMove = true := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact (hM x hx).isMove
        · exact (hL x hx).isMove
      have e : M ++ ([] ++ L ++ [RItem.op k (spillLocs ops i.clobbers)] ++ S) ++
          xs.flatMap (bodyItem vc succs bi vb) =
          (M ++ L) ++ (RItem.op k (spillLocs ops i.clobbers) :: (S ++ xs.flatMap (bodyItem vc succs bi vb))) := by
        simp
      rw [e, saveSegsOk_moves vb calleeSaved _ C _ hMv]
      simp only [saveSegsOk, hk, Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · split
        · rename_i hm; exfalso; revert hm; cases i <;> simp_all
        · simp only [List.all_eq_true]
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact (hC x hx).noSave
          · rcases List.mem_append.mp hx with hx | hx
            · exact (hM x hx).noSave
            · exact (hL x hx).noSave
      · rw [saveSegsOk_moves vb calleeSaved S [] _ (fun x hx => (hS x hx).isMove)]
        simpa using hrest

theorem plain_entryStores {vc : VCode} {succs preds : Array (Array Nat)} {s : Nat} {it : RItem}
    (hit : it ∈ spillEntryStores (spillHomes vc) vc succs preds s) : PlainMv [] it := by
  rw [Spill.spillEntryStores_eq (vc := vc) (succs := succs) (preds := preds) s] at hit
  simp only [List.map_map, List.mem_map] at hit
  obtain ⟨x, hx, rfl⟩ := hit
  obtain ⟨_, _, _, _, -, -, -, -, hx'⟩ := Spill.entryPairs_spec (vc := vc) (succs := succs) (preds := preds) hx
  obtain ⟨r, hr⟩ := termEdgeDefs_reg hx'
  exact ⟨_, _, rfl, by simp [hr, Loc.isSave], by simp [spillHome, Loc.isSave], by simp⟩

/-- **The spill allocation has Cranelift's callee-save shape** (`saveShapeOk`): block 0 starts
with the saves of every callee-saved register, every `Rets` is preceded by their restores (its
loads go into return registers, `SpillInstOk`), no other item touches a save slot. -/
theorem saveShapeOk_spill {vc : VCode} {ss ps : Array (Array Nat)} (hcfg : vc.cfg = .ok (ss, ps))
    (hloc : SpillLocalOk vc) : saveShapeOk vc (spillAlloc vc) = true := by
  unfold saveShapeOk
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨by rw [show (spillAlloc vc).saved = calleeSaved from rfl]; decide, ?_⟩
  rintro ⟨⟨vb, items⟩, b⟩ hx
  have hm := List.mem_zipIdx_iff_getElem?.mp hx
  rw [List.getElem?_zip_eq_some] at hm
  obtain ⟨hvb, hit⟩ := hm
  simp only [Array.getElem?_toList] at hvb hit
  rw [Spill.spillAlloc_block hcfg hvb] at hit
  obtain rfl := Option.some.inj hit
  have hinst : ∀ k i, vb.insts[k]? = some i → SpillInstOk i := fun k i hi => hloc.1 b vb k i hvb hi
  have hxs : ∀ x ∈ vb.insts.toList.zipIdx, vb.insts[x.2]? = some x.1 := fun x hx => by
    have := List.mem_zipIdx_iff_getElem?.mp hx; simpa using this
  have hE := fun it (h : it ∈ spillEntryStores (spillHomes vc) vc ss ps b) => plain_entryStores h
  have hsv : (spillAlloc vc).saved = calleeSaved := rfl
  simp only [hsv, List.toList_toArray]
  have hbody := saveSegs_body vc ss b vb hinst vb.insts.toList.zipIdx
    (spillEntryStores (spillHomes vc) vc ss ps b) hxs hE
  have hEm : ∀ x ∈ spillEntryStores (spillHomes vc) vc ss ps b, x.isMove = true :=
    fun x hx => (hE x hx).isMove
  split
  · rename_i hb
    simp only [beq_iff_eq] at hb
    subst hb
    have hlen : spillSaves.length = calleeSaved.length := by simp [spillSaves]
    simp only [ite_true, List.append_assoc, Bool.and_eq_true, beq_iff_eq]
    refine ⟨by rw [← hlen, List.take_left]; rfl, ?_⟩
    rw [← hlen, List.drop_left, saveSegsOk_moves _ _ _ _ _ hEm]
    simpa using hbody
  · rename_i hb
    simp only [beq_iff_eq] at hb
    simp only [hb, ite_false, List.nil_append]
    rw [saveSegsOk_moves _ _ _ _ _ hEm]
    simpa using hbody

/-! ## The assembly -/

/-- **`lowerRFunc` lowers the spill allocation** of a VCode with a CFG that meets the local
facts, `ctlInstOk` at every instruction, and `Args` first in block 0. -/
theorem lowerRFunc_spill_of {vc : VCode} {ss ps : Array (Array Nat)} (hcfg : vc.cfg = .ok (ss, ps))
    (hloc : SpillLocalOk vc)
    (hins : ∀ (b : Nat) (vb : VBlock) (k : Nat) (i : MInst), vc.blocks[b]? = some vb →
      vb.insts[k]? = some i → ctlInstOk b k i = true)
    (h0 : ∃ vb0 ds, vc.blocks[0]? = some vb0 ∧ vb0.insts[0]? = some (.args ds) ∧ 1 < vb0.insts.size) :
    ∃ af, lowerRFunc vc (spillAlloc vc) = .ok af :=
  lowerRFunc_of (ctlCheck_spill hcfg hloc hins h0) (saveShapeOk_spill hcfg hloc) fun b vb _ hvb hit it hm =>
    itemCode_spill vc (itemOk_spillAlloc hcfg hvb hit it hm) fun k i hi =>
      let ⟨ops, hops, _⟩ := hloc.1 b vb k i hvb hi
      ⟨ops, hops⟩

end E2E
