import FV.E2E.RegLevelUnwind
import FV.E2E.RegLevelCall
import FV.E2E.RegLevelFrame

/-!
# The frame invariant at the calls of a run (S10e, #232)

`Unw.FrameSaved R.af R.s0 s` (`FV/E2E/RegLevelUnwind.lean`) is what the unwinder's row needs to
restore a frame: CFA = x29 + 16 = entry sp, the entry x29/x30 at CFA − 16/−8, each register the
prologue pushes holding its entry value in its slot, every other callee-saved register holding
its entry value. This file proves it at every `op` item (in particular every `call`/`tryCall`) of
the register-level simulation of a function with a frame.

* `savedCheck vc rf`: a decidable check on the allocation. No edge enters block 0; outside
  block 0's leading save moves `.move (.reg r) (.save r)` (`RFunc.saveRegs`) no item writes a
  save slot or a callee-saved register the entry block does not save (`RItem.bodyOk`); the
  saved registers are callee-saved; and `lowerRFunc vc rf` succeeds (its prologue pushes the
  saved registers, `saveShapeOk`).
* `SavedInv rf keep e`: an invariant of the allocated code's configurations, for the entry
  values `e`, preserved by every `MStep vc sem keep rf` for any `sem` (`savedInv_step`,
  `savedInv_star`), true initially (`savedInv_init`; `entry_calleeSaved`/`savedInv_q_init`: the
  initial store of `q_init` holds the entry state's callee-saved registers).
* `frameSaved_of_q`: from `Q` at an `op` item and `SavedInv`, `Unw.FrameSaved`.

The invariant does not use `checkAlloc_sound`'s relation: the check is about which locations
the items write, and the invariant follows the values of the save slots and the unsaved
callee-saved registers through the items directly.
-/

namespace Backend

/-- The register a callee-save move `.move (.reg r) (.save r)` saves. -/
def RItem.saveReg? : RItem → Option Reg
  | .move (.reg r) (.save r') => if r = r' then some r else none
  | _ => none

/-- The registers the leading save moves of `its` save. -/
def RItem.leadSaves : List RItem → List Reg
  | [] => []
  | it :: its => match it.saveReg? with
    | some r => r :: leadSaves its
    | none => []

/-- The registers the entry block's leading save moves save. -/
def RFunc.saveRegs (rf : RFunc) : List Reg := RItem.leadSaves (rf.blocks[0]?.getD #[]).toList

/-- Membership of a register in a list (by `DecidableEq`, not `Reg`'s derived `BEq`). -/
def memB (r : Reg) (l : List Reg) : Bool := l.any fun c => decide (c = r)

theorem memB_iff {r : Reg} {l : List Reg} : memB r l = true ↔ r ∈ l := by
  simp [memB]

/-- A location the body may write when the entry block saves `sv`: no save slot, no
callee-saved register outside `sv`. -/
def bodyWritable (sv : List Reg) : Loc → Bool
  | .save _ => false
  | .reg r => !memB r calleeSaved || memB r sv
  | .stack _ _ => true

/-- Every location the item may write is `bodyWritable` (for an `op`: all its locations). -/
def RItem.bodyOk (sv : List Reg) : RItem → Bool
  | .move _ dst => bodyWritable sv dst
  | .op _ allocs => allocs.all (bodyWritable sv)

/-- The items of block `b` after the entry block's leading save moves. -/
def bodyOf (b : Nat) (items : List RItem) : List RItem :=
  if b = 0 then items.dropWhile (·.saveReg?.isSome) else items

/-- The allocation part of `savedCheck`: no edge enters block 0, the items outside the entry
block's leading save moves are `bodyOk`, the saved registers are callee-saved. -/
def savedCheckRF (vc : VCode) (rf : RFunc) : Bool :=
  (match vc.cfg with
   | .ok (ss, _) => ss.toList.all (·.toList.all (· != 0))
   | .error _ => true) &&
  (List.range rf.blocks.size).all (fun b =>
    (bodyOf b (rf.blocks[b]?.getD #[]).toList).all (·.bodyOk rf.saveRegs)) &&
  rf.saveRegs.all (memB · calleeSaved)

/-- **The check of the frame invariant** on an allocation (`savedCheckRF`, and the lowering
succeeds). It holds for the allocations the backend lowers (regalloc2's via `allocResult`, and
the spill allocation). -/
def savedCheck (vc : VCode) (rf : RFunc) : Bool :=
  savedCheckRF vc rf && (lowerRFunc vc rf).toBool

end Backend

namespace Backend.Proof

open Backend E2E Backend.Proof.UnwindTables

/-! ## The invariant -/

/-- **The saved-registers invariant** of a configuration of the allocated code, for the entry
values `e`: the remaining items are a suffix of the block; every callee-saved register the
entry block does not save keeps its `keep`-part of the entry value; the registers of the
pending leading save moves hold their entry values; the other saved registers' slots hold
them. -/
def SavedInv {V W : Type} (rf : RFunc) (keep : Reg → V → V) (e : Reg → V) : MConf V W → Prop
  | .run ⟨b, its, m, _⟩ =>
    (∃ pre, (rf.blocks[b]?.getD #[]).toList = pre ++ its) ∧
    (∀ r ∈ calleeSaved, r ∉ rf.saveRegs → keep r (m (.reg r)) = keep r (e r)) ∧
    (∀ r ∈ RItem.leadSaves its, m (.reg r) = e r) ∧
    (∀ r ∈ rf.saveRegs, r ∉ RItem.leadSaves its → m (.save r) = e r)
  | _ => True

/-! ## The check's facts -/

theorem saveReg?_some {it : RItem} {r : Reg} (h : it.saveReg? = some r) :
    it = .move (.reg r) (.save r) := by
  match it, h with
  | .move (.reg a) (.save a'), h =>
    simp only [RItem.saveReg?] at h
    split at h
    · cases h; subst a'; rfl
    · cases h

theorem saveReg?_none_of_bodyOk {sv : List Reg} {it : RItem} (h : it.bodyOk sv = true) :
    it.saveReg? = none := by
  cases it with
  | op k a => rfl
  | move src dst =>
    cases src <;> cases dst <;> simp_all [RItem.saveReg?, RItem.bodyOk, bodyWritable]

theorem leadSaves_nil_of_bodyOk {sv : List Reg} :
    ∀ {l : List RItem}, (∀ it ∈ l, it.bodyOk sv = true) → RItem.leadSaves l = []
  | [], _ => rfl
  | it :: l, h => by
    simp [RItem.leadSaves, saveReg?_none_of_bodyOk (h it (by simp))]

theorem suffix_dropWhile {α : Type} {p : α → Bool} {x : α} {rest : List α} (hx : p x = false) :
    ∀ pre : List α, (x :: rest) <:+ (pre ++ x :: rest).dropWhile p
  | [] => by simp [hx]
  | y :: pre => by
    simp only [List.cons_append, List.dropWhile]
    split
    · exact suffix_dropWhile hx pre
    · exact List.suffix_append (y :: pre) (x :: rest)

/-- An item that is no save move, and every item after it, is in the block's body. -/
theorem mem_bodyOf {b : Nat} {items pre rest : List RItem} {x : RItem}
    (h : items = pre ++ x :: rest) (hx : x.saveReg? = none) : ∀ y ∈ x :: rest, y ∈ bodyOf b items := by
  intro y hy
  subst h
  unfold bodyOf
  split
  · exact (suffix_dropWhile (p := (·.saveReg?.isSome)) (by simp [hx]) pre).subset hy
  · exact List.mem_append_right _ hy

theorem bodyWritable_ne_save {sv : List Reg} {l : Loc} (h : bodyWritable sv l = true) (r : Reg) :
    l ≠ .save r := by
  rintro rfl; simp [bodyWritable] at h

theorem bodyWritable_ne_reg {sv : List Reg} {l : Loc} (h : bodyWritable sv l = true) {r : Reg}
    (hr : r ∈ calleeSaved) (hn : r ∉ sv) : l ≠ .reg r := by
  rintro rfl; simp [bodyWritable, memB_iff.2 hr, memB_iff, hn] at h

theorem savedCheckRF_succ {vc : VCode} {rf : RFunc} (h : savedCheckRF vc rf = true) {b j s : Nat}
    (hs : succOf vc b j = some s) : s ≠ 0 := by
  simp only [savedCheckRF, Bool.and_eq_true] at h
  obtain ⟨⟨h1, -⟩, -⟩ := h
  unfold succOf at hs
  cases hcfg : vc.cfg with
  | error _ => simp [hcfg] at hs
  | ok p =>
    obtain ⟨ss, ps⟩ := p
    simp only [hcfg, Option.bind_eq_some_iff] at hs h1
    obtain ⟨row, hrow, hj⟩ := hs
    simp only [List.all_eq_true, Array.mem_toList_iff] at h1
    have := h1 row (Array.mem_of_getElem? hrow) s (Array.mem_of_getElem? hj)
    simpa using this

theorem savedCheckRF_body {vc : VCode} {rf : RFunc} (h : savedCheckRF vc rf = true) {b : Nat}
    {items : Array RItem} (hb : rf.blocks[b]? = some items) :
    ∀ y ∈ bodyOf b items.toList, y.bodyOk rf.saveRegs = true := by
  simp only [savedCheckRF, Bool.and_eq_true] at h
  obtain ⟨⟨-, h2⟩, -⟩ := h
  simp only [List.all_eq_true, List.mem_range] at h2
  have hlt : b < rf.blocks.size := (Array.getElem?_eq_some_iff.1 hb).1
  have := h2 b hlt
  rw [hb] at this
  exact this

theorem savedCheckRF_cs {vc : VCode} {rf : RFunc} (h : savedCheckRF vc rf = true) :
    ∀ r ∈ rf.saveRegs, r ∈ calleeSaved := by
  simp only [savedCheckRF, Bool.and_eq_true] at h
  obtain ⟨-, h3⟩ := h
  simp only [List.all_eq_true, memB_iff] at h3
  exact h3

/-! ## Preservation -/

/-- The locations an `op` item writes are among its allocations. -/
theorem mem_allocs_of_dl {V : Type} {ops : Array Operand} {allocs : Array Loc}
    {q1 : Operand × Loc → Bool} {q2 : (Operand × Loc) × V → Bool} {os : List V}
    {p : (Operand × Loc) × V} (hp : p ∈ (((ops.zip allocs).toList.filter q1).zip os).filter q2) :
    p.1.2 ∈ allocs.toList := by
  have h1 := (List.mem_filter.1 hp).1
  obtain ⟨p1, p2⟩ := p
  have h2 := (List.of_mem_zip h1).1
  have h3 := (List.mem_filter.1 h2).1
  rw [Array.toList_zip] at h3
  obtain ⟨o, l⟩ := p1
  exact (List.of_mem_zip h3).2

/-- **`SavedInv` is preserved by every step** of the allocated code, for any instruction
semantics `sem`. -/
theorem savedInv_step {V W : Type} {vc : VCode} {rf : RFunc} (hc : savedCheckRF vc rf = true)
    {sem : ISem V W} {keep : Reg → V → V} {e : Reg → V} {c c' : MConf V W}
    (hs : MStep vc sem keep rf c c') (hi : SavedInv rf keep e c) : SavedInv rf keep e c' := by
  cases hs with
  | @move b src dst its m w =>
    obtain ⟨⟨pre, hpre⟩, hA, hC, hB⟩ := hi
    cases hsr : (RItem.move src dst).saveReg? with
    | some r =>
      obtain ⟨rfl, rfl⟩ : src = .reg r ∧ dst = .save r := by
        have := saveReg?_some hsr
        simpa using this
      have hls : RItem.leadSaves (.move (.reg r) (.save r) :: its) = r :: RItem.leadSaves its := by
        simp [RItem.leadSaves, hsr]
      rw [hls] at hC hB
      refine ⟨⟨pre ++ [.move (.reg r) (.save r)], by simp [hpre]⟩, ?_, ?_, ?_⟩
      · intro r' hr' hns
        simp only [upd, reduceCtorEq, ite_false]
        exact hA r' hr' hns
      · intro r' hr'
        simp only [upd, reduceCtorEq, ite_false]
        exact hC r' (List.mem_cons_of_mem _ hr')
      · intro r' hr' hn
        simp only [upd]
        by_cases h : r' = r
        · subst h; simpa using hC _ List.mem_cons_self
        · have hne : Loc.save r' ≠ Loc.save r := by simpa using h
          simp only [hne, ite_false]
          exact hB r' hr' (by simp [h, hn])
    | none =>
      cases hbk : rf.blocks[b]? with
      | none => simp [hbk] at hpre
      | some items =>
        rw [hbk, Option.getD_some] at hpre
        have hbody := fun y hy => savedCheckRF_body hc hbk y (mem_bodyOf hpre hsr y hy)
        have hok : bodyWritable rf.saveRegs dst = true := hbody _ List.mem_cons_self
        have hls : RItem.leadSaves its = [] :=
          leadSaves_nil_of_bodyOk fun y hy => hbody y (List.mem_cons_of_mem _ hy)
        have hls0 : RItem.leadSaves (.move src dst :: its) = [] := by
          simp [RItem.leadSaves, hsr]
        rw [hls0] at hB
        refine ⟨⟨pre ++ [.move src dst], by simp [hbk, hpre]⟩, ?_, ?_, ?_⟩
        · intro r' hr' hns
          simp only [upd]
          simp only [(bodyWritable_ne_reg hok hr' hns).symm, ite_false]
          exact hA r' hr' hns
        · intro r' hr'; rw [hls] at hr'; cases hr'
        · intro r' hr' _
          simp only [upd]
          simp only [(bodyWritable_ne_save hok r').symm, ite_false]
          exact hB r' hr' (by simp)
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 c' hvb hik hops hsz hsem hlen hho hcl hn =>
    obtain ⟨⟨pre, hpre⟩, hA, hC, hB⟩ := hi
    have hsr : (RItem.op k allocs).saveReg? = none := rfl
    cases hbk : rf.blocks[b]? with
    | none => simp [hbk] at hpre
    | some items =>
      rw [hbk, Option.getD_some] at hpre
      have hbody := fun y hy => savedCheckRF_body hc hbk y (mem_bodyOf hpre hsr y hy)
      have hok : allocs.all (bodyWritable rf.saveRegs) = true := hbody _ List.mem_cons_self
      rw [Array.all_eq_true'] at hok
      have hls : RItem.leadSaves its = [] :=
        leadSaves_nil_of_bodyOk fun y hy => hbody y (List.mem_cons_of_mem _ hy)
      have hls0 : RItem.leadSaves (.op k allocs :: its) = [] := rfl
      rw [hls0] at hB
      -- the writes of the item avoid `l` when no allocation is `l`
      have hnot : ∀ (l : Loc), (∀ a ∈ allocs, a ≠ l) →
          ∀ {q1 : Operand × Loc → Bool} {q2 : (Operand × Loc) × V → Bool} {os : List V},
          l ∉ ((((ops.zip allocs).toList.filter q1).zip os).filter q2).map (·.1.2) := by
        intro l hl q1 q2 os hm
        obtain ⟨p, hp, hpl⟩ := List.mem_map.1 hm
        exact hl _ (Array.mem_toList_iff.1 (mem_allocs_of_dl hp)) hpl
      have hsave : ∀ r, ∀ a ∈ allocs, a ≠ .save r := fun r a ha =>
        bodyWritable_ne_save (hok a ha) r
      have hregs : ∀ r ∈ calleeSaved, r ∉ rf.saveRegs → ∀ a ∈ allocs, a ≠ .reg r :=
        fun r hr hn a ha => bodyWritable_ne_reg (hok a ha) hr hn
      -- the store after the item
      have hS : ∀ r, writeM m2 ((((ops.zip allocs).toList.filter (·.1.isDef)).zip outs').filter
          (·.1.1.isLate)) (.save r) = m (.save r) := by
        intro r
        rw [writeM_not_mem (hnot _ (hsave r)), hcl.1 _ (fun c _ => by simp),
          writeM_not_mem (hnot _ (hsave r))]
      have hR : ∀ r ∈ calleeSaved, r ∉ rf.saveRegs →
          keep r (writeM m2 ((((ops.zip allocs).toList.filter (·.1.isDef)).zip outs').filter
            (·.1.1.isLate)) (.reg r)) = keep r (m (.reg r)) := by
        intro r hr hn
        rw [writeM_not_mem (hnot _ (hregs r hr hn))]
        by_cases hcb : r ∈ i.clobbers
        · rw [hcl.2 r hcb hr, writeM_not_mem (hnot _ (hregs r hr hn))]
        · rw [hcl.1 _ (fun c hc he => hcb (by cases he; exact hc)),
            writeM_not_mem (hnot _ (hregs r hr hn))]
      cases hn with
      | next _ =>
        refine ⟨⟨pre ++ [.op k allocs], by simp [hbk, hpre]⟩, ?_, ?_, ?_⟩
        · intro r hr hns; rw [hR r hr hns]; exact hA r hr hns
        · intro r hr; rw [hls] at hr; cases hr
        · intro r hr _; rw [hS r]; exact hB r hr (by simp)
      | @goto j s items' _ hsucc hitems =>
        have hs0 := savedCheckRF_succ hc hsucc
        have hls' : RItem.leadSaves items'.toList = [] := by
          refine leadSaves_nil_of_bodyOk fun y hy => savedCheckRF_body hc hitems y ?_
          simp only [bodyOf, hs0, ite_false]; exact hy
        refine ⟨⟨[], by simp [hitems]⟩, ?_, ?_, ?_⟩
        · intro r hr hns; rw [hR r hr hns]; exact hA r hr hns
        · intro r hr; rw [hls'] at hr; cases hr
        · intro r hr _; rw [hS r]; exact hB r hr (by simp)
      | ret _ => trivial
      | halt => trivial

/-- `SavedInv` along a run of the allocated code. -/
theorem savedInv_star {V W : Type} {vc : VCode} {rf : RFunc} (hc : savedCheckRF vc rf = true)
    {sem : ISem V W} {keep : Reg → V → V} {e : Reg → V} {c c' : MConf V W}
    (hs : Star (MStep vc sem keep rf) c c') (hi : SavedInv rf keep e c) : SavedInv rf keep e c' := by
  induction hs with
  | refl => exact hi
  | step h _ ih => exact ih (savedInv_step hc h hi)

/-- **`SavedInv` holds initially**, for the entry values the initial store holds in the
registers. -/
theorem savedInv_init {V W : Type} (rf : RFunc) (keep : Reg → V → V) (m₀ : Loc → V) (w₀ : W) :
    SavedInv rf keep (fun r => m₀ (.reg r)) (MConf.init rf m₀ w₀) := by
  have h0 : rf.blocks[0]! = rf.blocks[0]?.getD #[] := by
    cases h : rf.blocks[0]? <;> simp [getElem!_def, h] <;> rfl
  refine ⟨⟨[], by simp [h0]⟩, fun _ _ _ => rfl, fun _ _ => rfl, fun r hr hn => absurd ?_ hn⟩
  simpa [RFunc.saveRegs, h0] using hr

/-- The callee-saved registers of a state that differs from `s0` only in the pc, x29, sp, x16,
x17 and the flags (the state after the prologue, `q_init`) hold their values in `s0`. (#581:
the premise also allows x17 and the flags, which Cranelift's stack-probe loop sets; the former
premise implies it.) -/
theorem entry_calleeSaved {fr : RAFrame} {s0 s1 : Arm.ArmState}
    (h : ∀ f, f ≠ .PC → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → f ≠ .GPR 16#5 → f ≠ .GPR 17#5 →
      (∀ fl, f ≠ .FLAG fl) → Arm.r f s1 = Arm.r f s0) :
    ∀ r ∈ calleeSaved, locVal fr s1 (.reg r) = regVal s0 r := by
  intro r hr
  simp only [calleeSaved, List.mem_append, List.mem_map, List.mem_range] at hr
  rcases hr with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · have hne : ∀ k : Nat, k < 10 →
        rnum (19 + k) ≠ 29#5 ∧ rnum (19 + k) ≠ 31#5 ∧ rnum (19 + k) ≠ 16#5 ∧ rnum (19 + k) ≠ 17#5 := by
      decide
    obtain ⟨h1, h2, h3, h4⟩ := hne i hi
    simp only [locVal, regVal]
    rw [h _ (by simp) (by simpa using h1) (by simpa using h2) (by simpa using h3) (by simpa using h4)
      (by simp)]
  · simp only [locVal, regVal]
    rw [h _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]

/-- The initial configuration `q_init` gives satisfies `SavedInv` for the entry state's
callee-saved registers. -/
theorem savedInv_q_init {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW R.F R.vc.EntryArg R.af R.s0 w₀) :
    ∃ n, Q R (iterN R.step n R.s0) (MConf.init R.rf (locVal R.fr (iterN R.step n R.s0)) w₀) ∧
      (∀ r ∈ calleeSaved, locVal R.fr (iterN R.step n R.s0) (.reg r) = regVal R.s0 r) ∧
      ∀ keep : Reg → CV → CV, SavedInv R.rf keep (fun r => locVal R.fr (iterN R.step n R.s0) (.reg r))
        (MConf.init R.rf (locVal R.fr (iterN R.step n R.s0)) w₀) := by
  obtain ⟨n, -, hq, -, hf⟩ := q_init hR hent hbe
  exact ⟨n, hq, entry_calleeSaved hf, fun keep => savedInv_init _ _ _ _⟩

/-! ## The frame at an `op` item -/

theorem rowLookup_mem {l : List (Nat × Int)} {k : Nat} {v : Int} (h : l.lookup k = some v) :
    (k, v) ∈ l := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    obtain ⟨k', v'⟩ := p
    simp only [List.lookup] at h
    split at h
    · rename_i hk
      cases h
      simp only [beq_iff_eq] at hk
      subst hk
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem rowLookup_ne_none {l : List (Nat × Int)} {k : Nat} {v : Int} (h : (k, v) ∈ l) :
    l.lookup k ≠ none := by
  intro hn
  have := List.lookup_eq_none_iff.1 hn _ h
  simp at this

theorem mem_pushGroups {rs : List Reg} {g : List Reg} (hg : g ∈ pushGroups rs) :
    ∀ r ∈ g, r ∈ rs := by
  obtain ⟨hp, ho⟩ := pairsOf_mem rs
  unfold pushGroups at hg
  simp only [List.mem_append, List.mem_map, Option.mem_toList, List.mem_reverse] at hg
  rcases hg with ⟨r, hr, rfl⟩ | ⟨⟨a, b⟩, hab, rfl⟩
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact ho _ hr
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact (hp _ hab).1
    · exact (hp _ hab).2

theorem pushGroups_complete {rs : List Reg} {r : Reg} (hr : r ∈ rs) :
    ∃ g ∈ pushGroups rs, r ∈ g := by
  have hf := pairsOf_flat rs
  rw [← hf] at hr
  unfold pushGroups
  rcases List.mem_append.1 hr with hr | hr
  · obtain ⟨⟨a, b⟩, hab, hm⟩ := List.mem_flatMap.1 hr
    exact ⟨[a, b], List.mem_append_right _ (List.mem_map.2 ⟨(a, b), List.mem_reverse.2 hab, rfl⟩),
      hm⟩
  · exact ⟨[r], List.mem_append_left _ (List.mem_map.2 ⟨r, hr, rfl⟩), List.mem_singleton_self _⟩

/-- A row of the pushes: the slot of a pushed register. -/
theorem mem_pushRows {saves : List Reg} {st d : Nat} {off : Int}
    (h : (d, off) ∈ (pushRows saves st).map offsetPair) :
    ∃ r, (r ∈ savesInt saves ∨ r ∈ savesFloat saves) ∧ r.dwarf? = some d ∧
      off = (clobberOff saves r : Int) - clobberBytes saves - 16 := by
  obtain ⟨x, hx, hxe⟩ := List.mem_map.1 h
  simp only [pushRows, List.mem_flatMap, List.mem_filterMap, Option.map_eq_some_iff] at hx
  obtain ⟨⟨g, i⟩, hgi, r, hr, dr, hdr, rfl⟩ := hx
  simp only [offsetPair, Prod.mk.injEq] at hxe
  obtain ⟨rfl, rfl⟩ := hxe
  have hg := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hgi)
  rcases List.mem_append.1 hg with hg | hg
  · exact ⟨r, .inl (mem_pushGroups hg r hr), hdr, rfl⟩
  · exact ⟨r, .inr (mem_pushGroups hg r hr), hdr, rfl⟩

/-- Every pushed register has a row. -/
theorem pushRows_complete {saves : List Reg} {st : Nat} {r : Reg}
    (hr : r ∈ savesInt saves ∨ r ∈ savesFloat saves) {d : Nat} (hd : r.dwarf? = some d) :
    ∃ off, (d, off) ∈ (pushRows saves st).map offsetPair := by
  obtain ⟨g, hg, hrg⟩ : ∃ g ∈ pushGroups (savesInt saves) ++ pushGroups (savesFloat saves), r ∈ g := by
    rcases hr with hr | hr
    · obtain ⟨g, hg, h⟩ := pushGroups_complete hr; exact ⟨g, List.mem_append_left _ hg, h⟩
    · obtain ⟨g, hg, h⟩ := pushGroups_complete hr; exact ⟨g, List.mem_append_right _ hg, h⟩
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hg
  refine ⟨(clobberOff saves r : Int) - clobberBytes saves - 16, List.mem_map.2 ⟨(st + 4 * (i + 1),
    .offset d ((clobberOff saves r : Int) - clobberBytes saves - 16)), ?_, rfl⟩⟩
  simp only [pushRows, List.mem_flatMap, List.mem_filterMap, Option.map_eq_some_iff]
  exact ⟨(g, i), List.mem_zipIdx_iff_getElem?.2 hi, r, hrg, d, hd, rfl⟩

theorem savesIF_of {saves : List Reg} {r : Reg} (hc : r ∈ calleeSaved) (h : r ∈ saves) :
    r ∈ savesInt saves ∨ r ∈ savesFloat saves := by
  rcases calleeSaved_cases hc with ⟨n, rfl, -⟩ | ⟨n, rfl, -⟩
  · exact .inl (List.mem_filter.2 ⟨h, rfl⟩)
  · exact .inr (List.mem_filter.2 ⟨h, rfl⟩)

theorem saves_of_IF {saves : List Reg} {r : Reg} (h : r ∈ savesInt saves ∨ r ∈ savesFloat saves) :
    r ∈ saves := by
  rcases h with h | h <;> exact (List.mem_filter.1 h).1

/-- The address of a push slot: CFA + its row's offset is the bottom of the clobber area + the
slot's `clobberOff`. -/
theorem addr_pushRow (x : BitVec 64) (cb o : Nat) (hcb : cb < 2 ^ 62) (ho : o < 2 ^ 62) :
    x + BitVec.ofInt 64 ((o : Int) - cb - 16) = x - BitVec.ofNat 64 (16 + cb) + BitVec.ofNat 64 o := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  have := x.isLt
  omega

/-- The value the unwinder restores for a pushed register is its slot value. -/
theorem dwarfVal_slotVal {r : Reg} {d : Nat} (hc : r ∈ calleeSaved) (hd : r.dwarf? = some d)
    (s : Arm.ArmState) : Unw.dwarfVal s d = slotVal s r := by
  rcases calleeSaved_cases hc with ⟨n, rfl, h1, h2⟩ | ⟨n, rfl, h1, h2⟩
  · simp only [Reg.dwarf?, Option.some.injEq] at hd
    subst hd
    simp [Unw.dwarfVal, show n < 32 by omega, xreg, slotVal, rnum]
  · simp only [Reg.dwarf?, Option.some.injEq] at hd
    subst hd
    simp only [Unw.dwarfVal, show ¬ 64 + n < 32 by omega, ite_false, show 64 ≤ 64 + n by omega,
      show 64 + n < 96 by omega, and_self, ite_true, slotVal, rnum]
    rw [show 64 + n - 64 = n by omega]

/-- Every save move of a return tail is excluded: no item of a valid tail stores into a save
slot. -/
theorem retTailOk_noSaveDst {saved : List Reg} :
    ∀ {D : List Reg} {L : List RItem}, retTailOk saved D L = true →
      ∀ a r, RItem.move a (.save r) ∉ L
  | _, [], _, _, _, h => by simp at h
  | D, it :: rest, h, a, r, hm => by
    unfold retTailOk at h
    split at h
    · rename_i r' h1 h2
      simp only [Bool.and_eq_true] at h
      rcases List.mem_cons.1 hm with e | hm
      · rw [RItem.eq_restore h1 h2] at e; cases e
      · exact retTailOk_noSaveDst h.2 a r hm
    · simp only [Bool.and_eq_true] at h
      rcases List.mem_cons.1 hm with e | hm
      · subst e; simp [RItem.avoids, Loc.isSave] at h
      · exact retTailOk_noSaveDst h.2 a r hm

theorem saveSegsOk_noSaveDst {vb : VBlock} {saved : List Reg} :
    ∀ {pend L : List RItem}, saveSegsOk vb saved pend L = true →
      ∀ a r, RItem.move a (.save r) ∉ pend ++ L
  | pend, [], h, a, r, hm => by
    simp only [saveSegsOk, List.all_eq_true] at h
    have := h _ (by simpa using hm)
    simp [RItem.noSave, Loc.isSave] at this
  | pend, .move x y :: L, h, a, r, hm => by
    simp only [saveSegsOk] at h
    exact saveSegsOk_noSaveDst h a r (by simpa using hm)
  | pend, .op k al :: L, h, a, r, hm => by
    simp only [saveSegsOk, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rcases List.mem_append.1 hm with hm | hm
    · split at h1
      · exact retTailOk_noSaveDst h1 a r hm
      · simp only [Bool.false_eq_true, ite_false, List.all_eq_true] at h1
        have := h1 _ hm
        simp [RItem.noSave, Loc.isSave] at this
    · rcases List.mem_cons.1 hm with e | hm
      · cases e
      · exact saveSegsOk_noSaveDst h2 a r (by simpa using hm)

theorem mem_leadSaves : ∀ {l : List RItem} {r : Reg}, r ∈ RItem.leadSaves l →
    RItem.move (.reg r) (.save r) ∈ l
  | [], _, h => by simp [RItem.leadSaves] at h
  | it :: l, r, h => by
    simp only [RItem.leadSaves] at h
    split at h
    · rename_i r' hr'
      rcases List.mem_cons.1 h with rfl | h
      · rw [saveReg?_some hr']; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_leadSaves h)
    · simp at h

/-- **The entry block saves only registers of `rf.saved`** (`saveShapeOk`: block 0 starts with
the saves of `rf.saved`, and no later item stores into a save slot). -/
theorem saveRegs_saved {R : RL} (hR : R.Wf) {r : Reg} (h : r ∈ R.rf.saveRegs) : r ∈ R.rf.saved := by
  obtain ⟨hsh, -⟩ := lowerRFunc_saves hR.alloc
  obtain ⟨vb, items, -, -, -, -, -, hvb, hit, -⟩ := entry_block hR
  obtain ⟨h0, -⟩ := saveShapeOk_block hsh hvb hit
  obtain ⟨htake, hseg⟩ := h0 rfl
  simp only [RFunc.saveRegs, hit, Option.getD_some] at h
  have hm := mem_leadSaves h
  rw [← List.take_append_drop R.rf.saved.length items.toList] at hm
  rcases List.mem_append.1 hm with hm | hm
  · rw [htake] at hm
    obtain ⟨r', hr', e⟩ := List.mem_map.1 hm
    simp only [RItem.move.injEq, Loc.reg.injEq, Loc.save.injEq] at e
    rw [← e.1]; exact hr'
  · exact absurd (by simpa using hm) (saveSegsOk_noSaveDst hseg (.reg r) r)

/-- **The frame invariant at a state related to an `op` item's store** (in particular at every
`call`/`tryCall`, and at the unwinder's restored state of a raising call) of the register-level
simulation of a function with a frame: from `StRel`, `SavedInv` for the entry state's
callee-saved values and the check, the unwinder's `FrameSaved`. -/
theorem frameSaved_of_stRel {R : RL} (hR : R.Wf) {ra : BitVec 64}
    (hent : AbiCall R.fb R.base ra R.s0) (hf : R.af.frame = true)
    (hc : savedCheck R.vc R.rf = true) {e : Reg → CV}
    (he : ∀ r ∈ calleeSaved, e r = regVal R.s0 r) {s : Arm.ArmState} {b k : Nat}
    {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hst : StRel R s m w)
    (hinv : SavedInv R.rf ckeep e (.run ⟨b, .op k allocs :: its, m, w⟩ : MConf CV Arm.ArmState)) :
    Unw.FrameSaved R.af R.s0 s := by
  obtain ⟨-, hA, -, -⟩ := hinv
  obtain ⟨-, -, hsav, hsv, -, hcb, -, hst', -⟩ := RL.frame_facts hR
  have hcbl := hsv.clobber_le
  have hreg : ∀ r ∈ calleeSaved, m (.reg r) = regVal s r := fun r hr =>
    hst.store (.reg r) (fun r' e' => by cases e'; exact calleeSaved_allocatable hr) trivial
  obtain ⟨h29, h30, hsl⟩ := RL.top_bytes hR hent (hst.fplr hf)
  have hns : ∀ r ∈ calleeSaved, r ∉ R.af.saves → r ∉ R.rf.saveRegs := fun r _ hn hm =>
    hn (hsav ▸ saveRegs_saved hR hm)
  have hunsaved : ∀ r ∈ calleeSaved, ∀ d, r.dwarf? = some d →
      ((pushRows R.af.saves 8).map offsetPair).reverse.lookup d = none → r ∉ R.af.saves := by
    intro r hc d hd hl hr
    obtain ⟨off, hm⟩ := pushRows_complete (st := 8) (savesIF_of hc hr) hd
    exact rowLookup_ne_none (List.mem_reverse.2 hm) hl
  apply Unw.frameAt_frameRow
  · rw [hst.fp hf]; exact BitVec.sub_add_cancel _ _
  · rw [show spv R.s0 + BitVec.ofInt 64 (-16) = spv R.s0 - 16#64 by
      rw [show BitVec.ofInt 64 (-16) = -16#64 by decide, BitVec.sub_eq_add_neg]]
    exact h29
  · rw [show spv R.s0 + BitVec.ofInt 64 (-8) = spv R.s0 - 16#64 + 8#64 by
      rw [show BitVec.ofInt 64 (-8) = -8#64 by decide]; bv_omega]
    exact h30
  · intro d off hl
    obtain ⟨r, hr, hd, rfl⟩ := mem_pushRows (List.mem_reverse.1 (rowLookup_mem hl))
    have hrs := saves_of_IF hr
    have hc := hsv.1 r hrs
    have := clobberOff_le hsv hrs
    rw [dwarfVal_slotVal hc hd, Unw.ld64, addr_pushRow _ _ _ (by omega) (by omega)]
    exact hsl r hrs
  · intro n hn h29' hl
    have hnc : Reg.x n ∈ calleeSaved := by
      simp only [calleeSavedX, List.mem_map, List.mem_range] at hn
      obtain ⟨a, ha, rfl⟩ := hn
      simp only [calleeSaved, List.mem_append, List.mem_map, List.mem_range, Reg.x.injEq]
      exact .inl ⟨a, by omega, rfl⟩
    have h := hA _ hnc (hns _ hnc (hunsaved _ hnc n rfl hl))
    simp only [ckeep] at h
    rw [hreg _ hnc, he _ hnc] at h
    simp only [regVal] at h
    have h64 := congrArg (BitVec.setWidth 64) h
    simp only [BitVec.setWidth_setWidth_of_le _ (show 64 ≤ 128 by decide),
      BitVec.setWidth_eq] at h64
    exact h64
  · intro n h8 h16 hl
    have hnc : Reg.v n ∈ calleeSaved := by
      simp only [calleeSaved, List.mem_append, List.mem_map, List.mem_range, Reg.v.injEq]
      exact .inr ⟨n - 8, by omega, by omega⟩
    have h := hA _ hnc (hns _ hnc (hunsaved _ hnc (64 + n) rfl hl))
    simp only [ckeep] at h
    rw [hreg _ hnc, he _ hnc] at h
    simp only [regVal] at h
    have h64 := congrArg (BitVec.setWidth 64) h
    simp only [BitVec.setWidth_setWidth_of_le _ (show 64 ≤ 128 by decide)] at h64
    exact h64

/-- **The frame invariant at an `op` item** (in particular at every `call`/`tryCall`) of the
register-level simulation of a function with a frame: from `Q`, `SavedInv` for the entry
state's callee-saved values and the check, the unwinder's `FrameSaved`. -/
theorem frameSaved_of_q {R : RL} (hR : R.Wf) {ra : BitVec 64}
    (hent : AbiCall R.fb R.base ra R.s0) (hf : R.af.frame = true)
    (hc : savedCheck R.vc R.rf = true) {e : Reg → CV}
    (he : ∀ r ∈ calleeSaved, e r = regVal R.s0 r) {s : Arm.ArmState} {b k : Nat}
    {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩))
    (hinv : SavedInv R.rf ckeep e (.run ⟨b, .op k allocs :: its, m, w⟩ : MConf CV Arm.ArmState)) :
    Unw.FrameSaved R.af R.s0 s :=
  frameSaved_of_stRel hR hent hf hc he (q_stRel hq) hinv

end Backend.Proof
