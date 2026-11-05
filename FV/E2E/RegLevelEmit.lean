import FV.Backend.Asm
import FV.Backend.Regalloc

/-!
# `emitFunc`'s code structure (M6 proof, register level)

`emitFunc` lays the blocks out in `emitOrder` (cold blocks last) as segments (`segsOf`: the
block's label, its code's lines but the last instruction's, then the last instruction's lines)
whose last-instruction lines become the emission plan's final lines (`emitPlan`: `MachBuffer`'s
simplification accepted by `segsOk`, or the lines themselves), then the deferred traps.
`emit_seg` locates every block's segment in the final lines; `segAt`/`tmOf`/`otOf` name a block's
segment, last-instruction lines and final lines.
-/

namespace Backend


theorem forIn_except_yield {ε σ α : Type} (l : List α) (s : σ)
    (f : α → σ → Except ε (ForInStep σ)) (g : α → σ → Except ε σ)
    (h : ∀ a s, f a s = ForInStep.yield <$> g a s) : forIn l s f = l.foldlM (fun s a => g a s) s := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih =>
    simp only [List.forIn_cons, List.foldlM_cons, h]
    cases g a s with
    | error e => rfl
    | ok s' => exact ih s'


/-! ## `lowerRFunc` as structural functions -/

/-- `lowerRFunc`'s loop body on one item (appending to `code`). -/
def itemStep (fr : RAFrame) (vb : VBlock) (code : Array AInst) : RItem → Except String (Array AInst)
  | .move src dst => do
    let l ← fr.moveInsts src dst
    pure (code ++ l.toArray)
  | .op k allocs => do
    let regs ← allocs.mapM (fun x => match x with
      | Loc.reg r => pure r
      | l => throw (toString "operand in " ++ toString (repr l)))
    match vb.insts[k]? with
    | some i => do
      match ← i.assign regs with
      | .args _ => pure code
      | .rets _ => pure (code.push .epilogueRet)
      | m => pure (code.push (.inst m))
    | none => throw "missing instruction"

/-- The code of one item. -/
def itemCode (fr : RAFrame) (vb : VBlock) (it : RItem) : Except String (List AInst) :=
  (·.toList) <$> itemStep fr vb #[] it

theorem itemStep_eq (fr : RAFrame) (vb : VBlock) (code : Array AInst) (it : RItem) :
    itemStep fr vb code it = (fun l => code ++ l.toArray) <$> itemCode fr vb it := by
  unfold itemCode
  cases it with
  | move src dst =>
    simp only [itemStep]
    cases fr.moveInsts src dst <;> simp [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  | op k allocs =>
    simp only [itemStep, bind, Except.bind]
    split
    · rfl
    · split
      · split
        · rfl
        · rename_i m _
          cases m <;> simp [pure, Except.pure, Functor.map, Except.map]
      · rfl

/-- The code of an item list. -/
def itemsCode (fr : RAFrame) (vb : VBlock) : List RItem → Except String (List AInst)
  | [] => pure []
  | it :: its => do
    let c1 ← itemCode fr vb it
    let c2 ← itemsCode fr vb its
    pure (c1 ++ c2)

theorem itemsCode_foldl (fr : RAFrame) (vb : VBlock) :
    ∀ (its : List RItem) (code : Array AInst),
      its.foldlM (fun c it => itemStep fr vb c it) code =
        (fun l => code ++ l.toArray) <$> itemsCode fr vb its
  | [], code => by simp [itemsCode, pure, Except.pure, Functor.map, Except.map]
  | it :: its, code => by
    simp only [List.foldlM_cons, itemsCode]
    rw [itemStep_eq]
    cases itemCode fr vb it with
    | error e => rfl
    | ok c1 =>
      have := itemsCode_foldl fr vb its (code ++ c1.toArray)
      simp only [Functor.map, Except.map, bind, Except.bind] at this ⊢
      rw [this]
      cases itemsCode fr vb its <;> simp [pure, Except.pure]

theorem mapIdxM_go_ok {α β ε : Type} {f : Nat → α → Except ε β} :
    ∀ (l : List α) (acc : Array β) (out : List β), List.mapIdxM.go f l acc = .ok out →
      out.length = acc.size + l.length ∧ (∀ i < acc.size, out[i]? = acc[i]?) ∧
      ∀ j a, l[j]? = some a → ∃ b, f (acc.size + j) a = .ok b ∧ out[acc.size + j]? = some b
  | [], acc, out, h => by
    simp only [List.mapIdxM.go, pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨by simp, fun i hi => by simp, fun j a hj => by simp at hj⟩
  | a :: l, acc, out, h => by
    simp only [List.mapIdxM.go, bind, Except.bind] at h
    cases hf : f acc.size a with
    | error e => rw [hf] at h; cases h
    | ok b =>
      rw [hf] at h
      obtain ⟨h1, h2, h3⟩ := mapIdxM_go_ok l (acc.push b) out h
      refine ⟨by simp at h1 ⊢; omega, fun i hi => by rw [h2 i (by simp; omega)]; simp [Array.getElem?_push, show i ≠ acc.size by omega], ?_⟩
      intro j a' hj
      cases j with
      | zero =>
        simp at hj
        subst hj
        refine ⟨b, hf, ?_⟩
        rw [Nat.add_zero, h2 acc.size (by simp)]
        simp
      | succ j =>
        simp at hj
        obtain ⟨b', hb', hout⟩ := h3 j a' hj
        simp only [Array.size_push] at hb' hout
        exact ⟨b', by rw [show acc.size + (j + 1) = acc.size + 1 + j by omega]; exact hb',
          by rw [show acc.size + (j + 1) = acc.size + 1 + j by omega]; exact hout⟩

theorem array_mapIdxM_ok {α β ε : Type} {f : Nat → α → Except ε β} {as : Array α} {bs : Array β}
    (h : as.mapIdxM f = .ok bs) :
    bs.size = as.size ∧ ∀ i a, as[i]? = some a → ∃ b, f i a = .ok b ∧ bs[i]? = some b := by
  have e := Array.toList_mapIdxM (xs := as) (f := f)
  rw [h] at e
  simp only [Functor.map, Except.map, List.mapIdxM] at e
  obtain ⟨h1, -, h3⟩ := mapIdxM_go_ok as.toList #[] bs.toList e.symm
  refine ⟨by simpa using h1, fun i a hi => ?_⟩
  obtain ⟨b, hb, hb'⟩ := h3 i a (by simpa using hi)
  exact ⟨b, by simpa using hb, by simpa using hb'⟩


/-- **`lowerRFunc` as a structural function**: block `b`'s code is the prologue (block 0) and
the items' code. -/
theorem lowerRFunc_ok {vc : VCode} {rf : RFunc} {af : AFunc} (h : lowerRFunc vc rf = .ok af) :
    (af.frameSize = (RAFrame.compute vc rf).total ∧ af.slotBase = (RAFrame.compute vc rf).size ∧
      af.blocks.size = (vc.blocks.zip rf.blocks).size ∧
      ∀ b vb items, vc.blocks[b]? = some vb → rf.blocks[b]? = some items →
        ∃ code, itemsCode (RAFrame.compute vc rf) vb items.toList = .ok code ∧
          af.blocks[b]? = some (vb.label, ((if b = 0 then [AInst.prologue] else []) ++ code).toArray)) ∧
      ((RAFrame.compute vc rf).total ≠ 0 → af.frame = true) ∧ ctlCheck vc rf = true := by
  unfold lowerRFunc at h
  simp only [bind, Except.bind] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i harg
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · cases h
  · rename_i blocks hb
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine And.intro ?_ ⟨fun _ => rfl, by simpa using harg⟩
    obtain ⟨hsz, hel⟩ := array_mapIdxM_ok hb
    refine ⟨rfl, rfl, hsz, fun b vb items hvb hit => ?_⟩
    have hz : (vc.blocks.zip rf.blocks)[b]? = some (vb, items) := by
      rw [Array.getElem?_zip_eq_some]; exact ⟨hvb, hit⟩
    obtain ⟨p, hp, hbp⟩ := hel b _ hz
    simp only at hp
    rw [← Array.forIn_toList, forIn_except_yield _ _ _ (fun it c => itemStep (RAFrame.compute vc rf) vb c it)] at hp
    · rw [itemsCode_foldl] at hp
      cases hc : itemsCode (RAFrame.compute vc rf) vb items.toList with
      | error e => rw [hc] at hp; cases hp
      | ok code =>
        rw [hc] at hp
        simp only [Functor.map, Except.map, pure, Except.pure, Except.ok.injEq] at hp
        subst hp
        refine ⟨code, rfl, ?_⟩
        rw [hbp]
        by_cases h0 : b = 0 <;> simp [h0]
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


/-- Every lowered function keeps a frame (fp/lr on the stack). -/
theorem lowerRFunc_frame {vc : VCode} {rf : RFunc} {af : AFunc} (h : lowerRFunc vc rf = .ok af) :
    af.frame = true := by
  unfold lowerRFunc at h
  simp only [bind, Except.bind] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl

/-- `lowerRFunc` checked the callee-save shape (`saveShapeOk`), and the function's prologue
pushes (its epilogue pops) the allocation's saved registers. -/
theorem lowerRFunc_saves {vc : VCode} {rf : RFunc} {af : AFunc} (h : lowerRFunc vc rf = .ok af) :
    saveShapeOk vc rf = true ∧ af.saves = rf.saved := by
  unfold lowerRFunc at h
  simp only [bind, Except.bind] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i hsh
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨by simpa using hsh, rfl⟩

theorem saveShapeOk_block {vc : VCode} {rf : RFunc} (h : saveShapeOk vc rf = true) {b : Nat}
    {vb : VBlock} {items : Array RItem} (hvb : vc.blocks[b]? = some vb)
    (hit : rf.blocks[b]? = some items) :
    (b = 0 → items.toList.take rf.saved.length = rf.saved.map (fun r => .move (.reg r) (.save r)) ∧
      saveSegsOk vb rf.saved [] (items.toList.drop rf.saved.length) = true) ∧
    (b ≠ 0 → saveSegsOk vb rf.saved [] items.toList = true) := by
  simp only [saveShapeOk, Bool.and_eq_true, List.all_eq_true] at h
  have h1 := h.2 ((vb, items), b) (List.mem_zipIdx_iff_getElem?.mpr (by
    rw [List.getElem?_zip_eq_some]
    exact ⟨by simpa using hvb, by simpa using hit⟩))
  by_cases hb : b = 0
  · subst hb
    simp only [beq_self_eq_true, ite_true, Bool.and_eq_true, beq_iff_eq] at h1
    exact ⟨fun _ => h1, fun h => absurd rfl h⟩
  · have hb' : (b == 0) = false := by simpa using hb
    simp only [hb', Bool.false_eq_true, ite_false] at h1
    exact ⟨fun h => absurd h hb, fun _ => h1⟩

/-! ## Block decomposition -/

theorem lines_traps {c : FnCtx} {m : MInst} {ps ps' : PState} {ls : List Line}
    (h : m.lines c ps = .ok (ls, ps')) : ps.traps.toList <+: ps'.traps.toList := by
  unfold MInst.lines at h
  split at h <;> simp only [bind, Except.bind, pure, Except.pure] at h
  all_goals (repeat' (first | (split at h) | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h)))
  all_goals first | exact List.prefix_refl _ | simp | skip
  all_goals first | cases h | simp [throw, throwThe, MonadExceptOf.throw] at h


theorem ainstLines_traps {c : FnCtx} {af : AFunc} {a : AInst} {ps ps' : PState} {ls : List Line}
    (h : ainstLines c af a ps = .ok (ls, ps')) : ps.traps.toList <+: ps'.traps.toList := by
  cases a with
  | inst m => exact lines_traps h
  | _ => simp only [ainstLines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h; rw [h.2]; exact List.prefix_refl _

theorem codeLinesE_traps {c : FnCtx} {af : AFunc} :
    ∀ {code : List AInst} {ps ps' : PState} {ls : List Line},
      codeLinesE c af code ps = .ok (ls, ps') → ps.traps.toList <+: ps'.traps.toList
  | [], ps, ps', ls, h => by
    simp only [codeLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h; rw [h.2]; exact List.prefix_refl _
  | a :: as, ps, ps', ls, h => by
    simp only [codeLinesE, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i r hr
      split at h
      · cases h
      · rename_i r2 hr2
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]
        exact (ainstLines_traps hr).trans (codeLinesE_traps hr2)


/-! ## Segments in emission order -/

/-- **`segsOf` block by block**: segment `i` is block `bs[i]`'s, its body the lines of the code
but the last instruction and its `term` the last instruction's lines, with the emitter's states
around them. -/
theorem segsOf_spec {c : FnCtx} {af : AFunc} :
    ∀ {bs : List ((Label × Array AInst) × Nat)} {ps psF : PState} {ss : List Seg},
      segsOf c af bs ps = .ok (ss, psF) →
      ss.length = bs.length ∧ ps.traps.toList <+: psF.traps.toList ∧
      ∀ (i : Nat) (s : Seg), ss[i]? = some s → ∃ (code : Array AInst) (ps1 psm ps2 : PState),
        bs[i]? = some ((s.label, code), s.idx) ∧
        codeLinesE c af code.toList.dropLast ps1 = .ok (s.body, psm) ∧
        codeLinesE c af code.toList.getLast?.toList psm = .ok (s.term, ps2) ∧
        ps.traps.toList <+: ps1.traps.toList ∧ ps2.traps.toList <+: psF.traps.toList
  | [], ps, psF, ss, h => by
    simp only [segsOf, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, List.prefix_refl _, fun i s hs => by simp at hs⟩
  | ((l, code), b) :: bs, ps, psF, ss, h => by
    simp only [segsOf, bind, Except.bind] at h
    split at h
    · cases h
    rename_i r1 h1
    split at h
    · cases h
    rename_i r2 h2
    split at h
    · cases h
    rename_i r3 h3
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hl, hp, hss⟩ := segsOf_spec h3
    have t1 := codeLinesE_traps h1
    have t2 := codeLinesE_traps h2
    refine ⟨by simp [hl], t1.trans (t2.trans hp), fun i s hs => ?_⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
      subst hs
      exact ⟨code, ps, r1.2, r2.2, rfl, h1, h2, List.prefix_refl _, hp⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hs
      obtain ⟨code', ps1, psm, ps2, hb, e1, e2, p1, p2⟩ := hss i s hs
      exact ⟨code', ps1, psm, ps2, by simpa using hb, e1, e2, t1.trans (t2.trans p1), p2⟩

/-- `emitOrder` lists every block (with its index) once. -/
theorem emitOrder_perm (af : AFunc) : (emitOrder af).Perm af.blocks.toList.zipIdx := by
  unfold emitOrder
  have := List.filter_append_perm (fun x : (Label × Array AInst) × Nat =>
    !(x.2 != 0 && af.cold[x.2]?.getD false)) af.blocks.toList.zipIdx
  simpa using this

/-- The entry block comes first in `emitOrder`. -/
theorem emitOrder_head {af : AFunc} {e : Label × Array AInst} (h : af.blocks[0]? = some e) :
    (emitOrder af).head? = some (e, 0) := by
  obtain ⟨bs, hb⟩ : ∃ bs, af.blocks.toList = e :: bs := by
    cases hl : af.blocks.toList with
    | nil => simp [← Array.getElem?_toList, hl] at h
    | cons e' bs =>
      rw [← Array.getElem?_toList, hl] at h
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      exact ⟨bs, by rw [h]⟩
  unfold emitOrder
  rw [hb]
  simp [List.zipIdx_cons]

/-- The indices of `emitOrder` are distinct. -/
theorem emitOrder_nodup (af : AFunc) : ((emitOrder af).map (·.2)).Nodup := by
  have hp := (emitOrder_perm af).map (·.2)
  refine hp.nodup_iff.mpr ?_
  have : (af.blocks.toList.zipIdx.map (·.2)) = List.range af.blocks.toList.length := by
    rw [List.zipIdx_eq_zip_range', List.map_snd_zip (by simp), List.range_eq_range']
  rw [this]
  exact List.nodup_range

/-- Block `b` is in `emitOrder`. -/
theorem emitOrder_mem {af : AFunc} {b : Nat} {e : Label × Array AInst} (h : af.blocks[b]? = some e) :
    (e, b) ∈ emitOrder af := by
  refine (emitOrder_perm af).mem_iff.mpr ?_
  rw [List.mem_zipIdx_iff_getElem?]
  simpa using h

/-- Every element of `emitOrder` is a block with its index. -/
theorem emitOrder_get {af : AFunc} {x : (Label × Array AInst) × Nat} (h : x ∈ emitOrder af) :
    af.blocks[x.2]? = some x.1 := by
  have := (emitOrder_perm af).mem_iff.mp h
  rw [List.mem_zipIdx_iff_getElem?] at this
  simpa using this

/-- `segsOk` pairs every segment with one final line list. -/
theorem segsOk_length {af : AFunc} {ss : List Seg} {os : List (List Line)} {L : List Line}
    (h : segsOk af ss os L = true) : os.length = ss.length := by
  unfold segsOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.symm

/-- What `machPlan` accepts. -/
theorem machPlan_spec {af : AFunc} {a : Bool} {ss : List Seg} {ps : PState} {p : Plan}
    (h : machPlan af a ss ps = some p) :
    p.segs = ss ∧ p.ps = ps ∧ p.outs.length = ss.length ∧ segsOk af ss p.outs p.lines = true ∧
      (∀ x ∈ p.alias, aliasOk af p.lines x = true) ∧
      padsOk af ((segsTrust af ss p.outs p.lines).contains ·) p.lines p.alias = true := by
  unfold machPlan at h
  simp only [bind, Option.bind] at h
  split at h
  · cases h
  rename_i os hos
  dsimp only at h
  split at h
  · rename_i hok
    simp only [Bool.and_eq_true] at hok
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨rfl, rfl, segsOk_length hok.1, hok.1, fun x hx => ?_, hok.2⟩
    simp only [List.mem_filter] at hx
    exact hx.2
  · cases h

/-- **The emission plan**: the segments of the blocks in `emitOrder`, one final line list each,
accepted by `segsOk`; every alias is justified (`aliasOk`). -/
theorem emitPlan_spec {k : Nat} {af : AFunc} {p : Plan} (h : emitPlan k af = .ok p) :
    segsOf ⟨k, af.slotBase⟩ af (emitOrder af) {} = .ok (p.segs, p.ps) ∧
      p.outs.length = p.segs.length ∧ segsOk af p.segs p.outs p.lines = true ∧
      ∀ x ∈ p.alias, aliasOk af p.lines x = true := by
  unfold emitPlan at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i r hr
  obtain ⟨ss, ps⟩ := r
  dsimp only at h
  split at h
  · rename_i p1 h1
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have h1' : machPlan af true ss ps = some p1 ∨ machPlan af false ss ps = some p1 := by
      cases e : machPlan af true ss ps with
      | some q => rw [e] at h1; simp only [Option.orElse] at h1; exact .inl h1
      | none => rw [e] at h1; simp only [Option.orElse] at h1; exact .inr h1
    obtain ⟨e1, e2, e3, e4, e5, -⟩ := h1'.elim machPlan_spec machPlan_spec
    exact ⟨by rw [e1, e2]; exact hr, by rw [e1]; exact e3, by rw [e1]; exact e4, e5⟩
  · split at h
    · rename_i hok
      simp only [Bool.and_eq_true] at hok
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨hr, by simp, hok.1, fun x hx => by simp at hx⟩
    · cases h

/-- **The emission plan's landing pads** (`padsOk`): the line the call-site table names for
each `try_call` handler represents the handler's block. -/
theorem emitPlan_pads {k : Nat} {af : AFunc} {p : Plan} (h : emitPlan k af = .ok p) :
    padsOk af ((segsTrust af p.segs p.outs p.lines).contains ·) p.lines p.alias = true := by
  unfold emitPlan at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i r hr
  obtain ⟨ss, ps⟩ := r
  dsimp only at h
  split at h
  · rename_i p1 h1
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have h1' : machPlan af true ss ps = some p1 ∨ machPlan af false ss ps = some p1 := by
      cases e : machPlan af true ss ps with
      | some q => rw [e] at h1; simp only [Option.orElse] at h1; exact .inl h1
      | none => rw [e] at h1; simp only [Option.orElse] at h1; exact .inr h1
    obtain ⟨e1, -, -, -, -, e6⟩ := h1'.elim machPlan_spec machPlan_spec
    rw [e1]
    exact e6
  · split at h
    · rename_i hok
      simp only [Bool.and_eq_true] at hok
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact hok.2
    · cases h

/-- Segment `i` in `segLines`: its label line, its body and final lines, then the next
segments. -/
theorem segLines_at : ∀ {ss : List Seg} {os : List (List Line)} {i : Nat} {s : Seg} {o : List Line},
    ss[i]? = some s → os[i]? = some o →
    ∃ A, segLines ss os =
        A ++ .label (.block s.label) :: (s.body ++ o) ++ segLines (ss.drop (i + 1)) (os.drop (i + 1)) ∧
      (i = 0 → A = [])
  | [], _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, h => by simp at h
  | s0 :: ss, o0 :: os, 0, s, o, h1, h2 => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
    subst h1 h2
    exact ⟨[], by simp [segLines], fun _ => rfl⟩
  | s0 :: ss, o0 :: os, i + 1, s, o, h1, h2 => by
    simp only [List.getElem?_cons_succ] at h1 h2
    obtain ⟨A, hA, -⟩ := segLines_at h1 h2
    refine ⟨.label (.block s0.label) :: (s0.body ++ o0) ++ A, ?_, fun h => by cases h⟩
    simp only [segLines, hA, List.drop_succ_cons]
    simp

/-! ## The final lines, block by block -/

/-- Block `b`'s segment and final lines in the emission plan of `emitFunc k af`. -/
def segAt (k : Nat) (af : AFunc) (b : Nat) : Option (Seg × List Line) :=
  match emitPlan k af with
  | .ok p => (p.segs.zip p.outs).find? (·.1.idx == b)
  | .error _ => none

/-- Block `b`'s last-instruction lines. -/
def tmOf (k : Nat) (af : AFunc) (b : Nat) : List Line := ((segAt k af b).map (·.1.term)).getD []

/-- Block `b`'s final lines (its last instruction's, after branch simplification). -/
def otOf (k : Nat) (af : AFunc) (b : Nat) : List Line := ((segAt k af b).map (·.2)).getD []

/-- The far labels `emitFunc` relaxes the branches to (`relaxOf` of the plan's lines). -/
def emitFar (c : FnCtx) (af : AFunc) : Lbl → Bool :=
  match emitPlan c.k af with
  | .ok p => relaxOf p.lines
  | .error _ => fun _ => false

set_option pp.proofs false in
theorem emitFunc_ok {k : Nat} {af : AFunc} {fa : FnAsm} (h : emitFunc k af = .ok fa) :
    ∃ p, emitPlan k af = .ok p ∧
      fa.lines.toList = relaxLines (emitFar ⟨k, af.slotBase⟩ af) p.lines ∧ fa.k = k := by
  unfold emitFunc at h
  cases hp : emitPlan k af with
  | error e =>
    have : emitPre k af = .error e := by simp [emitPre, hp, Functor.map, Except.map]
    rw [this] at h; cases h
  | ok p =>
    have : emitPre k af = .ok p.lines.toArray := by simp [emitPre, hp, Functor.map, Except.map]
    rw [this] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · simp only [Except.ok.injEq] at h
      subst h
      refine ⟨p, rfl, ?_, rfl⟩
      simp [emitFar, hp]

/-- Segment `i` of a plan is found by its block index. -/
theorem segAt_of {k : Nat} {af : AFunc} {p : Plan} (hp : emitPlan k af = .ok p) {i : Nat}
    {s : Seg} {o : List Line} (hs : p.segs[i]? = some s) (ho : p.outs[i]? = some o) :
    segAt k af s.idx = some (s, o) := by
  obtain ⟨hseg, hlen, -⟩ := emitPlan_spec hp
  obtain ⟨hl, -, hss⟩ := segsOf_spec hseg
  -- the indices of the segments are those of `emitOrder`, hence distinct
  have hidx : p.segs.map (·.idx) = (emitOrder af).map (·.2) := by
    apply List.ext_getElem?
    intro n
    simp only [List.getElem?_map]
    cases hn : p.segs[n]? with
    | none =>
      have : (emitOrder af).length ≤ n := by
        rw [← hl]; exact List.getElem?_eq_none_iff.mp hn
      simp [List.getElem?_eq_none_iff.mpr this]
    | some s' =>
      obtain ⟨code, -, -, -, hb, -⟩ := hss n s' hn
      simp [hb]
  have hnd : (p.segs.map (·.idx)).Nodup := hidx ▸ emitOrder_nodup af
  unfold segAt
  rw [hp]
  simp only
  have hz : (p.segs.zip p.outs)[i]? = some (s, o) := by
    rw [List.getElem?_zip_eq_some]; exact ⟨hs, ho⟩
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨by simp, i, (List.getElem?_eq_some_iff.mp hz).1, by simpa using (List.getElem?_eq_some_iff.mp hz).2, ?_⟩
  intro j hj
  have hj' : j < p.segs.length := by
    have := (List.getElem?_eq_some_iff.mp hz).1; simp at this; omega
  have hjz : j < (p.segs.zip p.outs).length := by
    have := (List.getElem?_eq_some_iff.mp hz).1; omega
  have hi : i < p.segs.length := by
    have := (List.getElem?_eq_some_iff.mp hz).1; simp at this; omega
  have hsi : p.segs[i] = s := by simpa using (List.getElem?_eq_some_iff.mp hs).2
  simp only [List.getElem_zip]
  have hne : p.segs[j].idx ≠ s.idx := by
    intro he
    have := (List.Nodup.getElem_inj hnd (i := j) (j := i) (hi := by simpa using hj')
      (hj := by simpa using hi)).mp (by simp [he, hsi])
    omega
  simpa using hne

/-- **Block `b` in the final lines**: its label at line `j`, then the relaxation of its body and
its final lines, then the following segments and the traps. -/
theorem emit_seg {k : Nat} {af : AFunc} {fa : FnAsm} (h : emitFunc k af = .ok fa) :
    ∃ p, emitPlan k af = .ok p ∧
      fa.lines.toList = relaxLines (emitFar ⟨k, af.slotBase⟩ af) p.lines ∧
      ∀ b l code, af.blocks[b]? = some (l, code) →
        ∃ i s o j ps1 psm ps2, p.segs[i]? = some s ∧ p.outs[i]? = some o ∧ s.idx = b ∧
          s.label = l ∧ segAt k af b = some (s, o) ∧
          fa.lines.toList[j]? = some (.label (.block l)) ∧
          fa.lines.toList.drop (j + 1) = relaxLines (emitFar ⟨k, af.slotBase⟩ af) (s.body ++ o) ++
            relaxLines (emitFar ⟨k, af.slotBase⟩ af)
              (segLines (p.segs.drop (i + 1)) (p.outs.drop (i + 1)) ++ trapLines p.ps) ∧
          codeLinesE ⟨k, af.slotBase⟩ af code.toList.dropLast ps1 = .ok (s.body, psm) ∧
          codeLinesE ⟨k, af.slotBase⟩ af code.toList.getLast?.toList psm = .ok (s.term, ps2) ∧
          ps2.traps.toList <+: p.ps.traps.toList ∧ (b = 0 → j = 0) := by
  obtain ⟨p, hp, hL, -⟩ := emitFunc_ok h
  generalize hF : emitFar ⟨k, af.slotBase⟩ af = F at hL ⊢
  refine ⟨p, hp, hL, fun b l code hbc => ?_⟩
  obtain ⟨hseg, hlen, -⟩ := emitPlan_spec hp
  obtain ⟨hl, -, hss⟩ := segsOf_spec hseg
  have hm := emitOrder_mem hbc
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hm
  have hil : i < p.segs.length := by rw [hl]; exact (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨s, hs⟩ : ∃ s, p.segs[i]? = some s := ⟨_, List.getElem?_eq_getElem hil⟩
  obtain ⟨o, ho⟩ : ∃ o, p.outs[i]? = some o :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlen]; exact hil)⟩
  obtain ⟨code', ps1, psm, ps2, hb, e1, e2, -, p2⟩ := hss i s hs
  rw [hi] at hb
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hb
  obtain ⟨A, hA, hA0⟩ := segLines_at hs ho
  refine ⟨i, s, o, (relaxLines F A).length, ps1, psm, ps2, hs, ho, rfl, rfl, segAt_of hp hs ho,
    ?_, ?_, e1, e2, p2, fun h0 => ?_⟩
  · rw [hL, Plan.lines, hA]
    simp [relaxLines, relaxLine, Line.relaxable?]
  · rw [hL, Plan.lines, hA]
    simp [relaxLines, relaxLine, Line.relaxable?, List.drop_append]
  · -- the entry block is the first segment
    rw [h0] at hi hbc
    have hh := emitOrder_head (af := af) (e := (s.label, code)) hbc
    have hi0 : (emitOrder af)[0]? = some ((s.label, code), 0) := by
      rw [← List.head?_eq_getElem?]; exact hh
    have hlt := (List.getElem?_eq_some_iff.mp hi).1
    have hlt0 := (List.getElem?_eq_some_iff.mp hi0).1
    have e : ((emitOrder af).map (·.2))[i]'(by simpa using hlt) =
        ((emitOrder af).map (·.2))[0]'(by simpa using hlt0) := by
      simp [(List.getElem?_eq_some_iff.mp hi).2, (List.getElem?_eq_some_iff.mp hi0).2]
    have : i = 0 := (List.Nodup.eq_of_getElem_eq (emitOrder_nodup af) _ _ e)
    simp [hA0 this, relaxLines]

end Backend
