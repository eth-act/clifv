module

public import FV.Backend.LinearScan
public import FV.Backend.Proof.SpillStep4Run

@[expose] public section

/-!
# Parallel moves of the Lean allocator (V4b-3/V4b-4, #275/#276)

`seqMoves ms scr tmp` sequentialises the parallel copy `ms` (the branch arguments of a `jump`
into the parameters' locations). `seqMoves_runs`: if it succeeds, the checker runs its items
and afterwards every destination holds what its source held before, and every location that is
no destination, no `tmp` location and no register `scr` returns keeps its content.
`seqMoves_reads`: every move that is no no-op reads its source in an emitted item.
`seqMoves_ok`: it succeeds when the destinations are distinct and, if a memory-to-memory move is
needed, `scr` has a register.
-/

namespace Backend.Proof.LS

open Backend Backend.LinearScan Backend.Proof.Spill

/-- A location the checker accepts for class `cl`: an allocatable register of the class, or a
stack slot of the class (below the frame's slot count: checked separately). -/
def LocCls (l : Loc) (cl : RegClass) : Prop :=
  (∃ r, l = .reg r ∧ r.allocatable = true ∧ r.realClass? = some cl) ∨ ∃ s, l = .stack s cl

/-! ## Helpers -/

private theorem LocCls.cls {l : Loc} {cl : RegClass} (h : LocCls l cl) : l.cls? = some cl := by
  rcases h with ⟨r, rfl, -, h⟩ | ⟨s, rfl⟩ <;> simp [Loc.cls?, *]

private theorem LocCls.locCls {l : Loc} {cl : RegClass} (h : LocCls l cl) : locCls l = cl := by
  simp [LinearScan.locCls, h.cls]

private theorem LocCls.uniq {l : Loc} {cl cl' : RegClass} (h : LocCls l cl) (h' : LocCls l cl') :
    cl = cl' := by
  have := h.cls.symm.trans h'.cls
  simpa using this

private theorem LocCls.index {l : Loc} {cl : RegClass} {n : Nat} (h : LocCls l cl)
    (hb : ∀ s c, l = .stack s c → s < n) : ∃ i, l.index = some i ∧ i < 128 + 2 * n := by
  rcases h with ⟨r, rfl, hra, -⟩ | ⟨s, rfl⟩
  · obtain ⟨i, hi, hlt⟩ := reg_index hra
    exact ⟨i, hi, by omega⟩
  · have := hb s cl rfl
    cases cl <;> simp [Loc.index] <;> omega

private theorem checkMove_ok {cc : CheckCtx} {w : String} {src dst : Loc} {cl : RegClass}
    (hs : LocCls src cl) (hd : LocCls dst cl) (hr : (src.isReg || dst.isReg) = true)
    (hbs : ∀ s c, src = .stack s c → s < cc.rf.spillSlots)
    (hbd : ∀ s c, dst = .stack s c → s < cc.rf.spillSlots) : cc.checkMove w src dst = .ok () := by
  rcases hs with ⟨r, rfl, hra, hrc⟩ | ⟨s, rfl⟩ <;>
    rcases hd with ⟨r', rfl, hra', hrc'⟩ | ⟨s', rfl⟩
  · simp [CheckCtx.checkMove, CheckCtx.locOk, Loc.cls?, hrc, hrc', hra, hra', ensure]; rfl
  · simp [CheckCtx.checkMove, CheckCtx.locOk, Loc.cls?, hrc, hra, ensure, hbd _ _ rfl]; rfl
  · simp [CheckCtx.checkMove, CheckCtx.locOk, Loc.cls?, hrc', hra', ensure, hbs _ _ rfl]; rfl
  · simp [Loc.isReg] at hr

/-- Stack slots of the emitted items are in the frame. -/
private def SlotsOk (n : Nat) (its : List RItem) : Prop :=
  ∀ it ∈ its, ∀ l ∈ it.locs, ∀ s cl, l = .stack s cl → s < n

private theorem not_written {its : List RItem} {l : Loc} {W : Loc → Prop}
    (hw : ∀ it ∈ its, ∃ s d, it = .move s d ∧ W d) (hl : ¬ W l) :
    ∀ it ∈ its, ∀ s, it ≠ .move s l := by
  intro it hit s he
  obtain ⟨s', d, rfl, hd⟩ := hw it hit
  injection he with _ h2
  subst h2
  exact hl hd

private theorem pigeon {α : Type} [DecidableEq α] : ∀ (D S : List α), D.Nodup → (∀ x ∈ D, x ∈ S) →
    S.length ≤ D.length → ∀ y ∈ S, y ∈ D
  | [], S, _, _, hl, y, hy => by
    cases S with
    | nil => simp at hy
    | cons => simp at hl
  | d :: D, S, hn, hsub, hl, y, hy => by
    rw [List.nodup_cons] at hn
    have hd : d ∈ S := hsub d List.mem_cons_self
    by_cases hyd : y = d
    · subst hyd; exact List.mem_cons_self
    · have ih := pigeon D (S.erase d) hn.2
        (fun x hx => (List.mem_erase_of_ne (fun h => hn.1 (by rw [← h]; exact hx))).mpr
          (hsub x (.tail _ hx)))
        (by rw [List.length_erase_of_mem hd]; simp at hl; omega) y ((List.mem_erase_of_ne hyd).mpr hy)
      exact .tail _ ih

private theorem eraseDups_spec {α : Type} [BEq α] [LawfulBEq α] (l : List α) :
    l.eraseDups.Nodup ∧ l.eraseDups.length ≤ l.length :=
  match l with
  | [] => by simp [List.eraseDups_nil]
  | a :: as => by
    rw [List.eraseDups_cons]
    have ih := eraseDups_spec (as.filter fun b => !b == a)
    have hlen := List.length_filter_le (fun b => !b == a) as
    refine ⟨List.nodup_cons.mpr ⟨fun h => ?_, ih.1⟩, by simp; omega⟩
    rw [List.mem_eraseDups, List.mem_filter] at h
    simp at h
termination_by l.length
decreasing_by simp only [List.length_cons]; exact Nat.lt_succ_of_le (List.length_filter_le _ _)

private theorem nodup_map_of_inj {α β : Type} {f : α → β} : ∀ {l : List α}, l.Nodup →
    (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) → (l.map f).Nodup
  | [], _, _ => by simp
  | a :: l, hn, hf => by
    rw [List.nodup_cons] at hn
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun h => ?_, nodup_map_of_inj hn.2 fun x hx y hy => hf x (.tail _ hx) y (.tail _ hy)⟩
    obtain ⟨b, hb, he⟩ := List.mem_map.mp h
    exact hn.1 (hf b (.tail _ hb) a List.mem_cons_self he ▸ hb)

private theorem erase_dest {P : List (Loc × Loc)} {x p : Loc × Loc} (h : (P.map (·.2)).Nodup)
    (hx : x ∈ P) (hp : p ∈ P.erase x) : p.2 ≠ x.2 := by
  induction P with
  | nil => simp at hx
  | cons y P ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rw [List.erase_cons] at hp
    split at hp
    · rename_i hyx
      have hyx : y = x := by simpa using hyx
      subst hyx
      exact fun he => h.1 (he ▸ List.mem_map_of_mem hp)
    · rename_i hyx
      have hyx : y ≠ x := by simpa using hyx
      have hx' : x ∈ P := (List.mem_cons.mp hx).resolve_left (Ne.symm hyx)
      rcases List.mem_cons.mp hp with rfl | hp
      · exact fun he => h.1 (he ▸ List.mem_map_of_mem hx')
      · exact ih h.2 hx' hp

/-! ## One move -/

private theorem emit_writes {scr : RegClass → Option Reg} {x : Loc × Loc} {its : List RItem}
    (h : emitMove scr x = .ok its) :
    ∀ it ∈ its, ∃ s d, it = .move s d ∧ (d = x.2 ∨ ∃ cl r, scr cl = some r ∧ d = .reg r) := by
  unfold emitMove at h
  split at h
  · obtain rfl := Except.ok.inj h
    intro it hit
    obtain rfl := List.mem_singleton.mp hit
    exact ⟨_, _, rfl, .inl rfl⟩
  · split at h
    · rename_i r hr
      obtain rfl := Except.ok.inj h
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro it (rfl | rfl)
      · exact ⟨_, _, rfl, .inr ⟨_, r, hr, rfl⟩⟩
      · exact ⟨_, _, rfl, .inl rfl⟩
    · cases h

private theorem emit_ok {scr : RegClass → Option Reg} {x : Loc × Loc}
    (hx : x.1.isReg = false → x.2.isReg = false → (scr (locCls x.1)).isSome) :
    ∃ its, emitMove scr x = .ok its := by
  unfold emitMove
  split
  · exact ⟨_, rfl⟩
  · rename_i hc
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hc
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (hx hc.1 hc.2)
    rw [hr]
    exact ⟨_, rfl⟩

section
variable {cc : CheckCtx} {vb : VBlock} {k : Nat}

private theorem emit_runs (hk : k ≠ vb.insts.size) {scr : RegClass → Option Reg}
    (hscrCls : ∀ cl r, scr cl = some r → LocCls (.reg r) cl) {x : Loc × Loc} {cl : RegClass}
    (hx1 : LocCls x.1 cl) (hx2 : LocCls x.2 cl) {its : List RItem} (h : emitMove scr x = .ok its)
    {b : AState} (hsz : b.size = 128 + 2 * cc.rf.spillSlots) (hsl : SlotsOk cc.rf.spillSlots its) :
    Runs cc vb k its b fun k' b' => k' = k ∧ b'.size = b.size ∧ b'.get x.2 = b.get x.1 ∧
      ∀ l, (∀ it ∈ its, ∀ s, it ≠ .move s l) → b'.get l = b.get l := by
  unfold emitMove at h
  split at h
  · rename_i hc
    obtain rfl := Except.ok.inj h
    have hb1 : ∀ s c, x.1 = .stack s c → s < cc.rf.spillSlots :=
      hsl _ List.mem_cons_self x.1 (by simp [RItem.locs])
    have hb2 : ∀ s c, x.2 = .stack s c → s < cc.rf.spillSlots :=
      hsl _ List.mem_cons_self x.2 (by simp [RItem.locs])
    obtain ⟨i, hi, hlt⟩ := hx2.index hb2
    exact Runs.move hk (checkMove_ok hx1 hx2 hc hb1 hb2)
      ⟨rfl, size_put _ _ _, get_put_self hi (by omega) _,
        fun l hl => get_put_ne (fun he => hl _ List.mem_cons_self x.1 (by rw [he])) _⟩
  · split at h
    · rename_i r hr
      obtain rfl := Except.ok.inj h
      rw [hx1.locCls] at hr
      have hrc := hscrCls _ _ hr
      have hnr : ∀ s c, Loc.reg r = .stack s c → s < cc.rf.spillSlots := by
        intro s c he; cases he
      have hb1 : ∀ s c, x.1 = .stack s c → s < cc.rf.spillSlots :=
        hsl _ List.mem_cons_self x.1 (by simp [RItem.locs])
      have hb2 : ∀ s c, x.2 = .stack s c → s < cc.rf.spillSlots :=
        hsl _ (.tail _ List.mem_cons_self) x.2 (by simp [RItem.locs])
      obtain ⟨i, hi, hlt⟩ := hx2.index hb2
      obtain ⟨ir, hir, hirlt⟩ := hrc.index hnr
      rw [← List.singleton_append]
      refine Runs.append (Q := fun k' b1 => k' = k ∧ b1 = b.put (.reg r) (b.get x.1))
        (Runs.move hk (checkMove_ok hx1 hrc (by simp [Loc.isReg]) hb1 hnr) ⟨rfl, rfl⟩)
        fun k' b1 ⟨hk', hb1'⟩ => ?_
      subst hk' hb1'
      refine Runs.move hk (checkMove_ok hrc hx2 (by simp [Loc.isReg]) hnr hb2)
        ⟨rfl, by simp only [size_put], ?_, ?_⟩
      · rw [get_put_self hi (by rw [size_put]; omega), get_put_self hir (by omega)]
      · intro l hl
        rw [get_put_ne (fun he => hl _ (.tail _ List.mem_cons_self) (.reg r) (by rw [he])),
          get_put_ne (fun he => hl _ List.mem_cons_self x.1 (by rw [he]))]
    · cases h

/-! ## The sequentialisation -/

/-- Every emitted item is a move into a pending destination, a temporary or a scratch register. -/
private theorem seqGo_writes {scr : RegClass → Option Reg} {tmp : RegClass → Loc} :
    ∀ (fuel : Nat) (P : List (Loc × Loc)) (its : List RItem), seqGo scr tmp fuel P = .ok its →
      ∀ it ∈ its, ∃ s d, it = .move s d ∧ ((∃ p ∈ P, p.2 = d) ∨ (∃ cl, tmp cl = d) ∨
        ∃ cl r, scr cl = some r ∧ d = .reg r) := by
  intro fuel
  induction fuel with
  | zero =>
    intro P its h
    cases P with
    | nil => obtain rfl := Except.ok.inj h; simp
    | cons => cases h
  | succ n ih =>
    intro P its h
    cases P with
    | nil => obtain rfl := Except.ok.inj h; simp
    | cons m ms =>
      simp only [seqGo] at h
      split at h
      · rename_i x hx
        obtain ⟨i1, h1, h2⟩ := Except.bind_ok h
        obtain ⟨i2, h3, h4⟩ := Except.bind_ok h2
        obtain rfl := Except.ok.inj h4
        intro it hit
        rcases List.mem_append.mp hit with hit | hit
        · obtain ⟨s, d, rfl, hd⟩ := emit_writes h1 it hit
          refine ⟨s, d, rfl, ?_⟩
          rcases hd with rfl | hd
          · exact .inl ⟨x, List.mem_of_find?_eq_some hx, rfl⟩
          · exact .inr (.inr hd)
        · obtain ⟨s, d, rfl, hd⟩ := ih _ _ h3 it hit
          refine ⟨s, d, rfl, ?_⟩
          rcases hd with ⟨p, hp, rfl⟩ | hd
          · exact .inl ⟨p, List.mem_of_mem_erase hp, rfl⟩
          · exact .inr hd
      · obtain ⟨i1, h1, h2⟩ := Except.bind_ok h
        obtain ⟨i2, h3, h4⟩ := Except.bind_ok h2
        obtain rfl := Except.ok.inj h4
        intro it hit
        rcases List.mem_append.mp hit with hit | hit
        · obtain ⟨s, d, rfl, hd⟩ := emit_writes h1 it hit
          refine ⟨s, d, rfl, ?_⟩
          rcases hd with rfl | hd
          · exact .inr (.inl ⟨_, rfl⟩)
          · exact .inr (.inr hd)
        · obtain ⟨s, d, rfl, hd⟩ := ih _ _ h3 it hit
          refine ⟨s, d, rfl, ?_⟩
          rcases hd with ⟨p, hp, rfl⟩ | hd
          · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
            exact .inl ⟨q, hq, rfl⟩
          · exact .inr hd

/-- **The sequentialisation runs** the parallel copy `P` from state `b`. -/
private theorem seqGo_runs (hk : k ≠ vb.insts.size) {scr : RegClass → Option Reg}
    {tmp : RegClass → Loc} (hscrCls : ∀ cl r, scr cl = some r → LocCls (.reg r) cl)
    (htmpCls : ∀ cl, LocCls (tmp cl) cl) (htmpScr : ∀ cl cl' r, scr cl' = some r → tmp cl ≠ .reg r) :
    ∀ (fuel : Nat) (P : List (Loc × Loc)) (its : List RItem) (b : AState),
      seqGo scr tmp fuel P = .ok its → b.size = 128 + 2 * cc.rf.spillSlots →
      SlotsOk cc.rf.spillSlots its → (P.map (·.2)).Nodup →
      (∀ p ∈ P, ∃ cl, LocCls p.1 cl ∧ LocCls p.2 cl) → (∀ p ∈ P, ∀ cl, p.2 ≠ tmp cl) →
      (∀ p ∈ P, ∀ cl r, scr cl = some r → p.1 ≠ .reg r ∧ p.2 ≠ .reg r) →
      Runs cc vb k its b fun k' b' => k' = k ∧ b'.size = b.size ∧
        (∀ p ∈ P, b'.get p.2 = b.get p.1) ∧ ∀ l, (∀ it ∈ its, ∀ s, it ≠ .move s l) → b'.get l = b.get l := by
  intro fuel
  induction fuel with
  | zero =>
    intro P its b h _ _ _ _ _ _
    cases P with
    | nil => obtain rfl := Except.ok.inj h; exact Runs.nil ⟨rfl, rfl, by simp, fun _ _ => rfl⟩
    | cons => cases h
  | succ n ih =>
    intro P its b h hsz hsl hnd hcls htmpP hscrP
    cases P with
    | nil => obtain rfl := Except.ok.inj h; exact Runs.nil ⟨rfl, rfl, by simp, fun _ _ => rfl⟩
    | cons m ms =>
      have hgo := h
      simp only [seqGo] at h
      split at h
      · rename_i x hx
        have hxP : x ∈ m :: ms := List.mem_of_find?_eq_some hx
        have hxr : ∀ p ∈ m :: ms, p.1 ≠ x.2 := by
          have := List.find?_some hx
          simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at this
          exact fun p hp he => this p hp he
        obtain ⟨i1, h1, h2⟩ := Except.bind_ok h
        obtain ⟨i2, h3, h4⟩ := Except.bind_ok h2
        obtain rfl := Except.ok.inj h4
        obtain ⟨cl, hc1, hc2⟩ := hcls x hxP
        refine Runs.append (emit_runs hk hscrCls hc1 hc2 h1 hsz
          fun it h => hsl it (List.mem_append_left _ h)) fun k1 b1 ⟨hk1, hsz1, hget1, hfr1⟩ => ?_
        subst hk1
        have ih' := ih _ i2 b1 h3 (by rw [hsz1, hsz]) (fun it h => hsl it (List.mem_append_right _ h))
          (hnd.sublist (List.erase_sublist.map _)) (fun p hp => hcls p (List.mem_of_mem_erase hp))
          (fun p hp => htmpP p (List.mem_of_mem_erase hp))
          (fun p hp => hscrP p (List.mem_of_mem_erase hp))
        refine ih'.mono fun k2 b2 ⟨e1, e2, e3, e4⟩ => ⟨e1, by rw [e2, hsz1], ?_, ?_⟩
        · intro p hp
          by_cases hpx : p = x
          · subst hpx
            rw [e4 p.2 (not_written (seqGo_writes _ _ _ h3) ?_), hget1]
            rintro (⟨q, hq, hqe⟩ | ⟨cl, hcl⟩ | ⟨cl, r, hr, hre⟩)
            · exact erase_dest hnd hxP hq hqe
            · exact htmpP p hxP cl hcl.symm
            · exact (hscrP p hxP cl r hr).2 hre
          · have hp' : p ∈ (m :: ms).erase x := (List.mem_erase_of_ne hpx).mpr hp
            rw [e3 p hp', hfr1 p.1 (not_written (emit_writes h1) ?_)]
            rintro (he | ⟨cl, r, hr, hre⟩)
            · exact hxr p hp he
            · exact (hscrP p hp cl r hr).1 hre
        · intro l hl
          rw [e4 l (fun it h => hl it (List.mem_append_right _ h)),
            hfr1 l (fun it h => hl it (List.mem_append_left _ h))]
      · rename_i hx
        -- only cycles are left: every source is a destination
        have hall : ∀ x ∈ m :: ms, x.2 ∈ (m :: ms).map (·.1) := by
          intro x hxm
          have := List.find?_eq_none.mp hx x hxm
          simp only [Bool.not_eq_true', Bool.not_eq_false, List.any_eq_true, beq_iff_eq] at this
          obtain ⟨p, hp, he⟩ := this
          exact List.mem_map.mpr ⟨p, hp, he⟩
        have hsrc : ∀ p ∈ m :: ms, ∃ q ∈ m :: ms, q.2 = p.1 := by
          intro p hp
          have := pigeon ((m :: ms).map (·.2)) ((m :: ms).map (·.1)) hnd
            (fun d hd => by
              obtain ⟨x, hxm, rfl⟩ := List.mem_map.mp hd
              exact hall x hxm)
            (by simp) p.1 (List.mem_map_of_mem hp)
          exact List.mem_map.mp this
        obtain ⟨i1, h1, h2⟩ := Except.bind_ok h
        obtain ⟨i2, h3, h4⟩ := Except.bind_ok h2
        obtain rfl := Except.ok.inj h4
        obtain ⟨cl, hm1, hm2⟩ := hcls m List.mem_cons_self
        have hcl := hm2.locCls
        have ht : LocCls (tmp (locCls m.2)) cl := by rw [hcl]; exact htmpCls cl
        refine Runs.append (emit_runs (x := (m.2, tmp (locCls m.2))) hk hscrCls hm2 ht h1 hsz
          fun it h => hsl it (List.mem_append_left _ h)) fun k1 b1 ⟨hk1, hsz1, hget1, hfr1⟩ => ?_
        subst hk1
        have hw1 := emit_writes h1
        have ih' := ih _ i2 b1 h3 (by rw [hsz1, hsz]) (fun it h => hsl it (List.mem_append_right _ h))
          (by simpa [List.map_map, Function.comp_def] using hnd)
          (by
            intro p' hp'
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hp'
            obtain ⟨cl', hp1, hp2⟩ := hcls p hp
            by_cases hpm : p.1 = m.2
            · have := (hpm ▸ hp1).uniq hm2
              subst this
              exact ⟨cl', by simpa [hpm] using ht, hp2⟩
            · exact ⟨cl', by simpa [hpm] using hp1, hp2⟩)
          (by
            intro p' hp'
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hp'
            exact htmpP p hp)
          (by
            intro p' hp' cl' r hr
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hp'
            refine ⟨?_, (hscrP p hp cl' r hr).2⟩
            by_cases hpm : p.1 = m.2
            · simpa [hpm] using htmpScr _ _ _ hr
            · simpa [hpm] using (hscrP p hp cl' r hr).1)
        refine ih'.mono fun k2 b2 ⟨e1, e2, e3, e4⟩ => ⟨e1, by rw [e2, hsz1], ?_, ?_⟩
        · intro p hp
          have := e3 _ (List.mem_map_of_mem hp)
          by_cases hpm : p.1 = m.2
          · simp only [hpm, beq_self_eq_true, ↓reduceIte] at this
            rw [this, hget1, hpm]
          · simp only [hpm, beq_iff_eq, ↓reduceIte] at this
            rw [this, hfr1 p.1 (not_written hw1 ?_)]
            rintro (he | ⟨cl', r, hr, hre⟩)
            · obtain ⟨q, hq, hqe⟩ := hsrc p hp
              exact htmpP q hq _ (hqe.trans he)
            · exact (hscrP p hp cl' r hr).1 hre
        · intro l hl
          rw [e4 l (fun it h => hl it (List.mem_append_right _ h)),
            hfr1 l (fun it h => hl it (List.mem_append_left _ h))]

end

/-- Can the next step of `seqGo` emit a move? -/
private def emOk (P : List (Loc × Loc)) : Bool := (P.find? fun x => !P.any (·.1 == x.2)).isSome

private theorem seqGo_ok {scr : RegClass → Option Reg} {tmp : RegClass → Loc}
    (htmpReg : ∀ cl, (tmp cl).isReg = false → (scr cl).isSome)
    (htmpCls : ∀ cl, locCls (tmp cl) = cl) :
    ∀ (fuel : Nat) (P : List (Loc × Loc)), 2 * P.length + (if emOk P then 0 else 1) ≤ fuel →
      (∀ x ∈ P, x.1.isReg = false → x.2.isReg = false → (scr (locCls x.1)).isSome) →
      (∀ x ∈ P, locCls x.1 = locCls x.2) → (∀ x ∈ P, ∀ cl, x.2 ≠ tmp cl) →
      ∃ its, seqGo scr tmp fuel P = .ok its := by
  intro fuel
  induction fuel with
  | zero =>
    intro P hf _ _ _
    cases P with
    | nil => exact ⟨[], rfl⟩
    | cons => simp at hf <;> omega
  | succ n ih =>
    intro P hf hscrP hclsP htmpP
    cases P with
    | nil => exact ⟨[], rfl⟩
    | cons m ms =>
      have hle : (if emOk (m :: ms) then 0 else 1) ≤ 1 := by split <;> omega
      simp only [seqGo]
      split
      · rename_i x hx
        have hxP : x ∈ m :: ms := List.mem_of_find?_eq_some hx
        obtain ⟨i1, h1⟩ := emit_ok (hscrP x hxP)
        have hlen := List.length_erase_of_mem hxP
        have hle' : (if emOk ((m :: ms).erase x) then 0 else 1) ≤ 1 := by split <;> omega
        obtain ⟨i2, h2⟩ := ih ((m :: ms).erase x) (by simp only [List.length_cons] at hf hlen ⊢; omega)
          (fun y hy => hscrP y (List.mem_of_mem_erase hy))
          (fun y hy => hclsP y (List.mem_of_mem_erase hy))
          (fun y hy => htmpP y (List.mem_of_mem_erase hy))
        refine ⟨i1 ++ i2, ?_⟩
        simp only [h1, h2, bind, Except.bind, pure, Except.pure]
      · rename_i hx
        have hem : emOk (m :: ms) = false := by
          simp only [emOk, hx, Option.isSome_none]
        rw [hem] at hf
        obtain ⟨i1, h1⟩ := emit_ok (scr := scr) (x := (m.2, tmp (locCls m.2)))
          fun _ ht => htmpReg _ ht
        obtain ⟨i2, h2⟩ := ih _ (by
            have : emOk ((m :: ms).map fun x => (if x.1 == m.2 then tmp (locCls m.2) else x.1, x.2)) =
                true := by
              unfold emOk
              rw [List.find?_isSome]
              refine ⟨_, List.mem_map_of_mem List.mem_cons_self, ?_⟩
              simp only [Bool.not_eq_true', List.any_eq_false, List.mem_map, beq_iff_eq]
              rintro _ ⟨q, hq, rfl⟩
              by_cases hqm : q.1 = m.2
              · simpa [hqm] using (htmpP m List.mem_cons_self _).symm
              · simp [hqm]
            rw [this]
            simp only [List.length_map, List.length_cons, Bool.false_eq_true, ↓reduceIte] at hf ⊢
            omega)
          (by
            intro y hy hy1 _
            obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
            by_cases hqm : q.1 = m.2
            · simp only [hqm, beq_self_eq_true, ↓reduceIte] at hy1 ⊢
              rw [htmpCls]
              exact htmpReg _ hy1
            · simp only [hqm, beq_iff_eq, ↓reduceIte] at hy1 ⊢
              exact hscrP q hq hy1 (by assumption))
          (by
            intro y hy
            obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
            by_cases hqm : q.1 = m.2
            · simp only [hqm, beq_self_eq_true, ↓reduceIte]
              rw [htmpCls, ← hqm, hclsP q hq]
            · simp only [hqm, beq_iff_eq, ↓reduceIte]
              exact hclsP q hq)
          (by
            intro y hy
            obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
            exact htmpP q hq)
        refine ⟨i1 ++ i2, ?_⟩
        simp only [h1, h2, bind, Except.bind, pure, Except.pure]

private theorem mem_cleanMoves {ms : List (Loc × Loc)} {p : Loc × Loc} :
    p ∈ cleanMoves ms ↔ p ∈ ms ∧ p.1 ≠ p.2 := by
  obtain ⟨p1, p2⟩ := p
  simp [cleanMoves, List.mem_eraseDups, List.mem_filter]

private theorem length_cleanMoves (ms : List (Loc × Loc)) : (cleanMoves ms).length ≤ ms.length :=
  Nat.le_trans (eraseDups_spec _).2 (List.length_filter_le _ _)

/-! ## Main theorems -/

/-- **The parallel copy runs**: every destination gets its source's content; a location no emitted
move writes keeps its own; every emitted move writes a destination, a temporary or a scratch
register. -/
theorem seqMoves_runs {cc : CheckCtx} {vb : VBlock} {k : Nat} (hk : k ≠ vb.insts.size)
    {ms : List (Loc × Loc)} {scr : RegClass → Option Reg} {tmp : RegClass → Loc}
    {its : List RItem} (h : seqMoves ms scr tmp = .ok its) {a : AState}
    (hsz : a.size = 128 + 2 * cc.rf.spillSlots)
    (hslots : ∀ it ∈ its, ∀ l ∈ it.locs, ∀ s cl, l = .stack s cl → s < cc.rf.spillSlots)
    (hdst : ∀ m ∈ ms, ∀ m' ∈ ms, m.2 = m'.2 → m.1 = m'.1)
    (hms : ∀ m ∈ ms, ∃ cl, LocCls m.1 cl ∧ LocCls m.2 cl)
    (hscr : ∀ (cl : RegClass) (r : Reg), scr cl = some r → LocCls (.reg r) cl ∧ ∀ m ∈ ms, m.1 ≠ .reg r ∧ m.2 ≠ .reg r)
    (htmp : ∀ cl, LocCls (tmp cl) cl ∧ (∀ m ∈ ms, m.1 ≠ tmp cl ∧ m.2 ≠ tmp cl) ∧
      ∀ r, scr cl = some r → tmp cl ≠ .reg r) :
    Runs cc vb k its a fun k' a' => k' = k ∧ a'.size = a.size ∧
      (∀ m ∈ ms, a'.get m.2 = a.get m.1) ∧
      (∀ l, (∀ it ∈ its, ∀ s, it ≠ .move s l) → a'.get l = a.get l) ∧
      (∀ it ∈ its, ∀ s d, it = .move s d → (∃ m ∈ ms, m.2 = d) ∨ (∃ cl, tmp cl = d) ∨
        (∃ cl r, scr cl = some r ∧ d = .reg r)) := by
  unfold seqMoves at h
  have hnd : ((cleanMoves ms).map (·.2)).Nodup := by
    refine nodup_map_of_inj (eraseDups_spec _).1 fun p hp q hq he => ?_
    have hp' := (mem_cleanMoves.mp hp).1
    have hq' := (mem_cleanMoves.mp hq).1
    exact Prod.ext (hdst p hp' q hq' he) he
  have htmpScr : ∀ cl cl' r, scr cl' = some r → tmp cl ≠ .reg r := by
    intro cl cl' r hr he
    have := (htmp cl).1.uniq (he ▸ (hscr cl' r hr).1)
    subst this
    exact (htmp cl).2.2 r hr he
  have hw := seqGo_writes _ _ _ h
  refine (seqGo_runs hk (fun cl r hr => (hscr cl r hr).1) (fun cl => (htmp cl).1) htmpScr _ _ _ a h
    hsz hslots hnd (fun p hp => hms p (mem_cleanMoves.mp hp).1)
    (fun p hp cl => ((htmp cl).2.1 p (mem_cleanMoves.mp hp).1).2)
    (fun p hp cl r hr => (hscr cl r hr).2 p (mem_cleanMoves.mp hp).1)).mono
    fun k' a' ⟨e1, e2, e3, e4⟩ => ⟨e1, e2, ?_, e4, ?_⟩
  · intro m hm
    by_cases hm12 : m.1 = m.2
    · rw [hm12]
      refine e4 m.2 (not_written hw ?_)
      rintro (⟨p, hp, hpe⟩ | ⟨cl, hcl⟩ | ⟨cl, r, hr, hre⟩)
      · obtain ⟨hp', hp12⟩ := mem_cleanMoves.mp hp
        exact hp12 ((hdst p hp' m hm hpe).trans (hm12.trans hpe.symm))
      · exact ((htmp cl).2.1 m hm).2 hcl.symm
      · exact ((hscr cl r hr).2 m hm).2 hre
    · exact e3 m (mem_cleanMoves.mpr ⟨hm, hm12⟩)
  · intro it hit s d he
    obtain ⟨s', d', he', hd⟩ := hw it hit
    rw [he] at he'
    injection he' with _ hdd
    subst hdd
    rcases hd with ⟨p, hp, hpe⟩ | hd
    · exact .inl ⟨p, (mem_cleanMoves.mp hp).1, hpe⟩
    · exact .inr hd

/-- Only moves are emitted. -/
theorem seqMoves_items {ms : List (Loc × Loc)} {scr : RegClass → Option Reg} {tmp : RegClass → Loc}
    {its : List RItem} (h : seqMoves ms scr tmp = .ok its) : ∀ it ∈ its, ∃ s d, it = .move s d :=
  fun it hit => by
    obtain ⟨s, d, he, -⟩ := seqGo_writes _ _ _ h it hit
    exact ⟨s, d, he⟩

/-- The items of one move read its source. -/
private theorem emit_reads {scr : RegClass → Option Reg} {x : Loc × Loc} {its : List RItem}
    (h : emitMove scr x = .ok its) : ∃ it ∈ its, x.1 ∈ it.locs := by
  unfold emitMove at h
  split at h
  · obtain rfl := Except.ok.inj h
    exact ⟨_, List.mem_cons_self, by simp [RItem.locs]⟩
  · split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨_, List.mem_cons_self, by simp [RItem.locs]⟩
    · cases h

/-- Every pending move's source is read by an emitted item. -/
private theorem seqGo_reads {scr : RegClass → Option Reg} {tmp : RegClass → Loc} :
    ∀ (fuel : Nat) (P : List (Loc × Loc)) (its : List RItem), seqGo scr tmp fuel P = .ok its →
      ∀ m ∈ P, ∃ it ∈ its, m.1 ∈ it.locs := by
  intro fuel
  induction fuel with
  | zero =>
    intro P its h
    cases P with
    | nil => simp
    | cons => cases h
  | succ n ih =>
    intro P its h
    cases P with
    | nil => simp
    | cons m ms =>
      simp only [seqGo] at h
      split at h
      · rename_i x hx
        obtain ⟨i1, h1, h2⟩ := Except.bind_ok h
        obtain ⟨i2, h3, h4⟩ := Except.bind_ok h2
        obtain rfl := Except.ok.inj h4
        intro p hp
        by_cases hpx : p = x
        · subst hpx
          obtain ⟨it, hit, hl⟩ := emit_reads h1
          exact ⟨it, List.mem_append_left _ hit, hl⟩
        · obtain ⟨it, hit, hl⟩ := ih _ _ h3 p ((List.mem_erase_of_ne hpx).mpr hp)
          exact ⟨it, List.mem_append_right _ hit, hl⟩
      · obtain ⟨i1, h1, h2⟩ := Except.bind_ok h
        obtain ⟨i2, h3, h4⟩ := Except.bind_ok h2
        obtain rfl := Except.ok.inj h4
        intro p hp
        obtain ⟨it, hit, hl⟩ := ih _ _ h3 _ (List.mem_map_of_mem (f := fun x =>
          (if x.1 == m.2 then tmp (locCls m.2) else x.1, x.2)) hp)
        by_cases hpm : p.1 = m.2
        · obtain ⟨it', hit', hl'⟩ := emit_reads h1
          exact ⟨it', List.mem_append_left _ hit', by rw [hpm]; exact hl'⟩
        · simp only [hpm, beq_iff_eq, ↓reduceIte] at hl
          exact ⟨it, List.mem_append_right _ hit, hl⟩

/-- **Every move that is no no-op reads its source** in an emitted item. -/
theorem seqMoves_reads {ms : List (Loc × Loc)} {scr : RegClass → Option Reg} {tmp : RegClass → Loc}
    {its : List RItem} (h : seqMoves ms scr tmp = .ok its) :
    ∀ m ∈ ms, m.1 ≠ m.2 → ∃ it ∈ its, m.1 ∈ it.locs :=
  fun m hm hne => seqGo_reads _ _ _ h m (mem_cleanMoves.mpr ⟨hm, hne⟩)

/-- **The parallel copy succeeds** with distinct destinations, a register for every
memory-to-memory move, and temporaries of their class outside the copy. -/
theorem seqMoves_ok {ms : List (Loc × Loc)} {scr : RegClass → Option Reg} {tmp : RegClass → Loc}
    (hdst : ∀ m ∈ ms, ∀ m' ∈ ms, m.2 = m'.2 → m.1 = m'.1)
    (hscr : ∀ m ∈ ms, m.1.isReg = false → m.2.isReg = false → (scr (locCls m.1)).isSome)
    (htmpReg : ∀ cl, (tmp cl).isReg = false → (scr cl).isSome)
    (htmpCls : ∀ cl, locCls (tmp cl) = cl)
    (htmp : ∀ cl, ∀ m ∈ ms, m.1 ≠ tmp cl ∧ m.2 ≠ tmp cl)
    (hcls : ∀ m ∈ ms, locCls m.1 = locCls m.2) :
    ∃ its, seqMoves ms scr tmp = .ok its := by
  have hlen := length_cleanMoves ms
  have hle : (if emOk (cleanMoves ms) then 0 else 1) ≤ 1 := by split <;> omega
  exact seqGo_ok htmpReg htmpCls _ _ (by omega)
    (fun x hx => hscr x (mem_cleanMoves.mp hx).1) (fun x hx => hcls x (mem_cleanMoves.mp hx).1)
    (fun x hx cl => (htmp cl x (mem_cleanMoves.mp hx).1).2)

end Backend.Proof.LS
