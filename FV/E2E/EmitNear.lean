import FV.Backend.Proof.FrameLines
import FV.E2E.EmitPreOk
import FV.Backend.Proof.RelaxLayout
import FV.E2E.EmitCondsDefs
import FV.Backend.Proof.AssignOk
import FV.Backend.EmitOk

/-!
# The near PC-relative lines of the spill path reach their labels (V6b)

`E2E.emitFunc_spill_near`: the lines of `emitFunc k af`, for `af` the lowering of the spill
allocation, satisfy `NearOk` (`FV/Backend/Proof/RelaxLayout.lean`): every PC-relative line that
branch relaxation does not handle reaches its label.

Those lines (`Line.nearTgt`: a label operand other than `.skip`, not `b`, and not relaxable)
are the atomic loops' `cbnz x24, l` / `b.ne out` to `.loop` labels (`rmwLoopLines`,
`casLoopLines`), the jump table's `adr t1, jt`, and `b.al`/`b.nv` — which `MInst.lines` produces
only from a `condBr`/`trapIf` with an `al`/`nv` condition: `VCode.noAlwaysB` excludes them (an
explicit decidable premise on the prepared VCode; the control-shape analysis `CtlShape` does not
track conditions). No line carries a trap code and a label operand.

The proof is a segmentation of the line list (`Good`): single lines with no near label, and
self-contained near blocks (`NearBlk`: at most 8 lines, no `b`, none relaxable, every near
label defined inside). `MInst.lines` produces such lists (`lines_ok`); `fallthrough` (`ftList`)
keeps them (`good_ft`: it only drops `b` lines — which target blocks, `Line.bOk` — and rewrites
a conditional branch followed by `b e; l:` to a relaxable branch to the block `e`); relaxation
keeps them (`good_relax`); and in a `Good` list a near line's label is at most 8 lines, so
32 bytes, away (`good_nearOk`, with `labelOffsets_go_label`).
-/

namespace Backend

def Insn.isBr : Insn → Bool
  | .b _ => true
  | _ => false

def Line.nearTgt : Line → Option Lbl
  | .ins i tr =>
    match i.pcRelSpec? with
    | some (t, _, _) =>
      if t = .skip ∨ i.isBr = true ∨ (tr = none ∧ i.relaxTarget?.isSome = true) then none else some t
    | none => none
  | _ => none

def Line.isBLine : Line → Bool
  | .ins (.b _) _ => true
  | _ => false

/-- A line's branch shape: a `b` targets a block; a conditional branch carries no trap code and
no `al`/`nv` condition (so retargeting it to a block makes it relaxable). -/
def Line.bOk : Line → Bool
  | .ins (.b (.block _)) _ => true
  | .ins (.b _) _ => false
  | .ins (.bcond c _) tr => tr.isNone && c != .al && c != .nv
  | .ins (.cbz ..) tr | .ins (.tbz ..) tr => tr.isNone
  | _ => true

def Line.nearOkB (ln : Line) : Bool := ln.nearTgt.isNone && ln.bOk

/-- Every instruction of the allocated function has no `al`/`nv` branch condition. -/
def AFunc.NoAlways (af : AFunc) : Prop :=
  ∀ p ∈ af.blocks.toList, ∀ m, AInst.inst m ∈ p.2.toList → m.noAlways = true

end Backend

namespace E2E.EmitNear

open Backend


theorem condTarget_invertTo {c : Insn} {l e : Lbl} (h : c.condTarget? = some l) :
    (c.invertTo e).condTarget? = some e := by
  cases c <;> simp_all [Insn.condTarget?, Insn.invertTo]
  rename_i cc _
  cases cc <;> simp_all [Cond.invert]
  all_goals first
    | decide
    | (obtain ⟨⟨h1, h2⟩, _⟩ := h
       first | exact absurd h1 (by decide) | exact absurd h2 (by decide))

theorem nearTgt_invert {c : Insn} {l : Lbl} {b : Label} (h : c.condTarget? = some l) :
    (Line.ins (c.invertTo (.block b)) none).nearTgt = none := by
  have h2 := condTarget_invertTo (e := .block b) h
  generalize c.invertTo (.block b) = d at h2
  cases d <;> simp_all [Line.nearTgt, Insn.condTarget?, Insn.pcRelSpec?, Insn.relaxTarget?, Insn.isBr]


/-- A self-contained near block: its PC-relative lines whose label relaxation does not handle
name a label of the block. -/
structure NearBlk (s : List Line) : Prop where
  ne : s ≠ []
  len : s.length ≤ 8
  nob : ∀ ln ∈ s, ln.isBLine = false
  norelax : ∀ ln ∈ s, ln.relaxable? = none
  near : ∀ ln ∈ s, ∀ t, ln.nearTgt = some t → Line.label t ∈ s
  tail : (∃ l, s.getLast? = some (.label l)) ∨ ∀ ln ∈ s.dropLast, ln.nearTgt = none

inductive Good : List Line → Prop
  | nil : Good []
  | safe {ln : Line} {L : List Line} : ln.nearTgt = none → Good L → Good (ln :: L)
  | blk {s L : List Line} : NearBlk s → Good L → Good (s ++ L)

theorem Good.append {A B : List Line} (ha : Good A) (hb : Good B) : Good (A ++ B) := by
  induction ha with
  | nil => exact hb
  | safe h _ ih => exact .safe h ih
  | blk h _ ih => rw [List.append_assoc]; exact .blk h ih

theorem Good.safes {P B : List Line} (hp : ∀ ln ∈ P, ln.nearTgt = none) (hb : Good B) :
    Good (P ++ B) := by
  induction P with
  | nil => exact hb
  | cons x P ih =>
    exact .safe (hp x (by simp)) (ih fun ln h => hp ln (by simp [h]))


theorem relaxLines_append (far : Lbl → Bool) (A B : List Line) :
    relaxLines far (A ++ B) = relaxLines far A ++ relaxLines far B := by
  simp [relaxLines]

theorem relaxLines_fix (far : Lbl → Bool) :
    ∀ s : List Line, (∀ ln ∈ s, ln.relaxable? = none) → relaxLines far s = s
  | [], _ => rfl
  | ln :: s, h => by
    have e : relaxLines far (ln :: s) = relaxLine far ln ++ relaxLines far s := by
      simp [relaxLines]
    rw [e, relaxLines_fix far s fun x hx => h x (by simp [hx])]
    simp [relaxLine, h ln (by simp)]

theorem relaxLine_safe (far : Lbl → Bool) {ln : Line} (h : ln.nearTgt = none) :
    ∀ x ∈ relaxLine far ln, x.nearTgt = none := by
  unfold relaxLine
  split
  · rename_i c t hr
    split
    · cases ln with
      | ins i tr =>
        cases tr with
        | none =>
          simp only [Line.relaxable?, Option.map_eq_some_iff] at hr
          obtain ⟨t', ht', e⟩ := hr
          cases e
          have hc : c.condTarget?.isSome := by
            unfold Insn.relaxTarget? at ht'; split at ht' <;> simp_all
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · cases c <;> simp_all [Line.nearTgt, Insn.condTarget?, Insn.invertTo, Insn.pcRelSpec?]
          · simp [Line.nearTgt, Insn.pcRelSpec?, Insn.isBr]
        | some => simp [Line.relaxable?] at hr
      | _ => simp [Line.relaxable?] at hr
    · simpa using h
  · simpa using h

/-! ## `MachBuffer`'s simplification -/

/-- A line `MachBuffer` may remove or rewrite: a `b`, or a relaxable conditional branch. -/
def _root_.Backend.Line.removable (ln : Line) : Bool := ln.isBLine || ln.relaxable?.isSome

theorem removable_nearTgt {ln : Line} (h : ln.removable = true) : ln.nearTgt = none := by
  cases ln with
  | ins i tr =>
    simp only [Line.removable, Bool.or_eq_true, Option.isSome_iff_exists] at h
    rcases h with h | ⟨⟨c, t⟩, h⟩
    · cases i <;> simp_all [Line.isBLine, Line.nearTgt, Insn.pcRelSpec?, Insn.isBr]
    · cases tr with
      | none =>
        simp only [Line.relaxable?, Option.map_eq_some_iff, Prod.mk.injEq] at h
        obtain ⟨t', ht', rfl, -⟩ := h
        simp only [Line.nearTgt]
        split
        · split <;> simp_all
        · rfl
      | some _ => simp [Line.relaxable?] at h
  | word => rfl
  | label => rfl

/-- `MachBuffer`'s output `O` from its input `I`: lines kept, removable lines removed or
replaced by removable lines. -/
inductive MBRel : List Line → List Line → Prop
  | nil : MBRel [] []
  | keep {x : Line} {I O : List Line} : MBRel I O → MBRel (x :: I) (x :: O)
  | drop {x : Line} {I O : List Line} : x.removable = true → MBRel I O → MBRel (x :: I) O
  | repl {x y : Line} {I O : List Line} : x.removable = true → y.removable = true →
      y.bOk = true → MBRel I O → MBRel (x :: I) (y :: O)

theorem MBRel.snoc {I O : List Line} (h : MBRel I O) (x : Line) : MBRel (I ++ [x]) (O ++ [x]) := by
  induction h with
  | nil => exact .keep .nil
  | keep _ ih => exact .keep ih
  | drop hx _ ih => exact .drop hx ih
  | repl hx hy hb _ ih => exact .repl hx hy hb ih

theorem MBRel.erase {I O : List Line} (h : MBRel I O) :
    ∀ (k : Nat) (z : Line), O[k]? = some z → z.removable = true → MBRel I (O.eraseIdx k) := by
  induction h with
  | nil => intro k z hz; simp at hz
  | keep h ih =>
    intro k z hz hr
    cases k with
    | zero => simp at hz; subst hz; simpa using MBRel.drop hr h
    | succ k => simpa using MBRel.keep (ih k z (by simpa using hz) hr)
  | drop hx _ ih => intro k z hz hr; exact .drop hx (ih k z hz hr)
  | repl hx hy hb h ih =>
    intro k z hz hr
    cases k with
    | zero => simpa using MBRel.drop hx h
    | succ k => simpa using MBRel.repl hx hy hb (ih k z (by simpa using hz) hr)

theorem MBRel.set {I O : List Line} (h : MBRel I O) :
    ∀ (p : Nat) (z y : Line), O[p]? = some z → z.removable = true → y.removable = true →
      y.bOk = true → MBRel I (O.set p y) := by
  induction h with
  | nil => intro p z y hz; simp at hz
  | keep h ih =>
    intro p z y hz hr hy hb
    cases p with
    | zero => simp at hz; subst hz; simpa using MBRel.repl hr hy hb h
    | succ p => simpa using MBRel.keep (ih p z y (by simpa using hz) hr hy hb)
  | drop hx _ ih => intro p z y hz hr hy hb; exact .drop hx (ih p z y hz hr hy hb)
  | repl hx hy' hb' h ih =>
    intro p z y hz hr hy hb
    cases p with
    | zero => simpa using MBRel.repl hx hy hb h
    | succ p => simpa using MBRel.repl hx hy' hb' (ih p z y (by simpa using hz) hr hy hb)

theorem MBRel.bOk {I O : List Line} (h : MBRel I O) (hI : ∀ x ∈ I, x.bOk = true) :
    ∀ y ∈ O, y.bOk = true := by
  induction h with
  | nil => simp
  | keep _ ih =>
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hI _ (by simp)
    · exact ih (fun x hx => hI x (by simp [hx])) y hy
  | drop _ _ ih => exact ih (fun x hx => hI x (by simp [hx]))
  | repl _ _ hb _ ih =>
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hb
    · exact ih (fun x hx => hI x (by simp [hx])) y hy

theorem MBRel.prefix : ∀ {s L O : List Line}, (∀ x ∈ s, x.removable = false) →
    MBRel (s ++ L) O → ∃ O', O = s ++ O' ∧ MBRel L O'
  | [], _, O, _, h => ⟨O, rfl, h⟩
  | x :: s, L, O, hs, h => by
    cases h with
    | keep h =>
      obtain ⟨O', rfl, h'⟩ := MBRel.prefix (fun y hy => hs y (by simp [hy])) h
      exact ⟨O', rfl, h'⟩
    | drop hx _ => simp [hs x (by simp)] at hx
    | repl hx _ _ _ => simp [hs x (by simp)] at hx

/-- **`MachBuffer`'s output of a `Good` line list is `Good`**: the removable lines are single
lines of the segmentation, never inside a near block. -/
theorem good_mbrel {I : List Line} (h : Good I) : ∀ {O : List Line}, MBRel I O → Good O := by
  induction h with
  | nil => intro O hr; cases hr; exact .nil
  | safe hs _ ih =>
    intro O hr
    cases hr with
    | keep hr => exact .safe hs (ih hr)
    | drop _ hr => exact ih hr
    | repl _ hy _ hr => exact .safe (removable_nearTgt hy) (ih hr)
  | @blk s L hs _ ih =>
    intro O hr
    have hns : ∀ x ∈ s, x.removable = false := fun x hx => by
      simp [Line.removable, hs.nob x hx, hs.norelax x hx]
    obtain ⟨O', rfl, hr'⟩ := MBRel.prefix hns hr
    exact .blk hs (ih hr')

/-! ## Retargeting, relaxation and the reach -/

/-- A self-contained block of at most `n` lines. -/
structure NearBlkN (n : Nat) (s : List Line) : Prop where
  ne : s ≠ []
  len : s.length ≤ n
  near : ∀ ln ∈ s, ∀ t, ln.nearTgt = some t → Line.label t ∈ s

/-- `Good` with blocks of at most `n` lines (that may hold relaxable or retargeted branches). -/
inductive GoodN (n : Nat) : List Line → Prop
  | nil : GoodN n []
  | safe {ln : Line} {L : List Line} : ln.nearTgt = none → GoodN n L → GoodN n (ln :: L)
  | blk {s L : List Line} : NearBlkN n s → GoodN n L → GoodN n (s ++ L)

theorem GoodN.append {n : Nat} {A B : List Line} (ha : GoodN n A) (hb : GoodN n B) :
    GoodN n (A ++ B) := by
  induction ha with
  | nil => exact hb
  | safe h _ ih => exact .safe h ih
  | blk h _ ih => rw [List.append_assoc]; exact .blk h ih

theorem GoodN.safes {n : Nat} {P B : List Line} (hp : ∀ ln ∈ P, ln.nearTgt = none)
    (hb : GoodN n B) : GoodN n (P ++ B) := by
  induction P with
  | nil => exact hb
  | cons x P ih => exact .safe (hp x (by simp)) (ih fun ln h => hp ln (by simp [h]))

theorem good_goodN {L : List Line} (h : Good L) : GoodN 8 L := by
  induction h with
  | nil => exact .nil
  | safe hs _ ih => exact .safe hs ih
  | blk hs _ ih => exact .blk ⟨hs.ne, hs.len, hs.near⟩ ih

/-- Retargeting a line to its target's image under `f` (the target itself or a block label)
keeps it, or makes it a line without near label. -/
theorem relabel_cases (f : Lbl → Lbl) (hf : ∀ t, f t = t ∨ ∃ X, f t = .block X) (ln : Line)
    (hb : ln.bOk = true) : ln.relabel f = ln ∨ (ln.relabel f).nearTgt = none := by
  cases ln with
  | label _ => exact .inl rfl
  | word _ _ => exact .inr rfl
  | ins i tc =>
    cases i with
    | b t => exact .inr (by simp [Line.relabel, Line.target?, Insn.setTarget, Line.nearTgt,
        Insn.pcRelSpec?, Insn.isBr])
    | bcond c t =>
      rcases hf t with e | ⟨X, e⟩
      · exact .inl (by simp [Line.relabel, Line.target?, Insn.setTarget, e])
      · simp only [Line.bOk, Bool.and_eq_true, bne_iff_ne, ne_eq, Option.isNone_iff_eq_none] at hb
        obtain ⟨⟨rfl, h1⟩, h2⟩ := hb
        refine .inr ?_
        simp only [Line.relabel, Line.target?, Insn.setTarget, e, Line.nearTgt, Insn.pcRelSpec?]
        split
        · rfl
        · rename_i hn
          exfalso; apply hn
          simp [Insn.isBr, Insn.relaxTarget?, Insn.condTarget?, h1, h2]
    | cbz nz w r t =>
      rcases hf t with e | ⟨X, e⟩
      · exact .inl (by simp [Line.relabel, Line.target?, Insn.setTarget, e])
      · simp only [Line.bOk, Option.isNone_iff_eq_none] at hb
        subst hb
        exact .inr (by simp [Line.relabel, Line.target?, Insn.setTarget, e, Line.nearTgt,
          Insn.pcRelSpec?, Insn.isBr, Insn.relaxTarget?, Insn.condTarget?])
    | tbz nz r bit t =>
      rcases hf t with e | ⟨X, e⟩
      · exact .inl (by simp [Line.relabel, Line.target?, Insn.setTarget, e])
      · simp only [Line.bOk, Option.isNone_iff_eq_none] at hb
        subst hb
        exact .inr (by simp [Line.relabel, Line.target?, Insn.setTarget, e, Line.nearTgt,
          Insn.pcRelSpec?, Insn.isBr, Insn.relaxTarget?, Insn.condTarget?])
    | _ => exact .inl rfl

/-- Retargeting a line keeps its branch shape (a `b` is retargeted to a block). -/
theorem relabel_bOk (f : Lbl → Lbl) (hf : ∀ t, f t = t ∨ ∃ X, f t = .block X) (y : Line)
    (hb : y.bOk = true) : (y.relabel f).bOk = true := by
  cases y with
  | ins i tc =>
    cases i <;> simp only [Line.relabel, Line.target?, Insn.setTarget]
    all_goals first
      | exact hb
      | (rename_i t; rcases hf t with e | ⟨X, e⟩ <;> rw [e] <;> first | exact hb | rfl)
  | word _ _ => rfl
  | label _ => rfl

theorem goodN_relabel {n : Nat} (f : Lbl → Lbl) (hf : ∀ t, f t = t ∨ ∃ X, f t = .block X)
    {L : List Line} (h : GoodN n L) (hb : ∀ ln ∈ L, ln.bOk = true) :
    GoodN n (L.map (Line.relabel f)) := by
  induction h with
  | nil => exact .nil
  | @safe ln L hs _ ih =>
    refine .safe ?_ (ih fun x hx => hb x (by simp [hx]))
    rcases relabel_cases f hf ln (hb ln (by simp)) with e | e
    · rw [e]; exact hs
    · exact e
  | @blk s L hs _ ih =>
    rw [List.map_append]
    refine .blk ⟨by simpa using hs.ne, by simpa using hs.len, ?_⟩
      (ih fun x hx => hb x (by simp [hx]))
    intro x hx t ht
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    rcases relabel_cases f hf y (hb y (by simp [hy])) with e | e
    · rw [e] at ht
      exact List.mem_map.2 ⟨_, hs.near y hy t ht, rfl⟩
    · rw [e] at ht; cases ht

theorem relaxLine_length (far : Lbl → Bool) (ln : Line) : (relaxLine far ln).length ≤ 2 := by
  unfold relaxLine
  split
  · split <;> simp
  · simp

theorem relaxLines_length (far : Lbl → Bool) :
    ∀ s : List Line, (relaxLines far s).length ≤ 2 * s.length
  | [] => by simp [relaxLines]
  | ln :: s => by
    have := relaxLines_length far s
    have := relaxLine_length far ln
    simp only [relaxLines, List.flatMap_cons, List.length_append, List.length_cons] at *
    omega

theorem goodN_relax {n : Nat} (far : Lbl → Bool) {L : List Line} (h : GoodN n L) :
    GoodN (2 * n) (relaxLines far L) := by
  induction h with
  | nil => exact .nil
  | @safe ln L hs _ ih =>
    rw [show ln :: L = [ln] ++ L from rfl, relaxLines_append]
    exact GoodN.safes (by simpa [relaxLines] using relaxLine_safe far hs) ih
  | @blk s L hs _ ih =>
    rw [relaxLines_append]
    refine .blk ⟨relaxLines_ne_nil hs.ne, by have := relaxLines_length far s; have := hs.len; omega,
      ?_⟩ ih
    intro x hx t ht
    simp only [relaxLines, List.mem_flatMap] at hx ⊢
    obtain ⟨y, hy, hx⟩ := hx
    cases hr : y.relaxable? with
    | some ct =>
      have hyr : y.removable = true := by simp [Line.removable, hr]
      have := relaxLine_safe far (removable_nearTgt hyr) x hx
      rw [this] at ht; cases ht
    | none =>
      have hx' : x = y := by simpa [relaxLine, hr] using hx
      subst hx'
      exact ⟨.label t, hs.near x hy t ht, by simp [relaxLine, Line.relaxable?]⟩

theorem goodN_near {n : Nat} {L : List Line} (h : GoodN n L) :
    ∀ j ln t, L[j]? = some ln → ln.nearTgt = some t →
      ∃ j', L[j']? = some (.label t) ∧ j' < j + n ∧ j < j' + n := by
  induction h with
  | nil => intro j ln t hj; simp at hj
  | safe hs _ ih =>
    intro j ln t hj ht
    cases j with
    | zero => simp at hj; subst hj; simp [hs] at ht
    | succ j =>
      obtain ⟨j', h1, h2, h3⟩ := ih j ln t (by simpa using hj) ht
      exact ⟨j' + 1, by simpa using h1, by omega, by omega⟩
  | @blk s L hs _ ih =>
    intro j ln t hj ht
    by_cases hjs : j < s.length
    · rw [List.getElem?_append_left hjs] at hj
      have hm := hs.near ln (List.mem_of_getElem? hj) t ht
      obtain ⟨j', hj'⟩ := List.mem_iff_getElem?.mp hm
      have hj's : j' < s.length := by
        rcases Nat.lt_or_ge j' s.length with h | h
        · exact h
        · rw [List.getElem?_eq_none h] at hj'; cases hj'
      have := hs.len
      exact ⟨j', by rw [List.getElem?_append_left hj's]; exact hj', by omega, by omega⟩
    · rw [List.getElem?_append_right (by omega)] at hj
      obtain ⟨j', h1, h2, h3⟩ := ih _ ln t hj ht
      exact ⟨s.length + j', by rw [List.getElem?_append_right (by omega)]; simpa using h1,
        by omega, by omega⟩

theorem lineOffset_mono : ∀ (L : List Line) (j d : Nat),
    lineOffset L j ≤ lineOffset L (j + d) ∧ lineOffset L (j + d) ≤ lineOffset L j + 4 * d
  | [], j, d => by simp [lineOffset]
  | ln :: L, 0, 0 => by simp
  | ln :: L, 0, d + 1 => by
    have := lineOffset_mono L 0 d
    rw [Nat.zero_add, lineOffset_cons_succ]
    have hs : ln.size ≤ 4 := by cases ln <;> simp [Line.size]
    simp [lineOffset] at this ⊢
    omega
  | ln :: L, j + 1, d => by
    have := lineOffset_mono L j d
    rw [show j + 1 + d = (j + d) + 1 by omega, lineOffset_cons_succ, lineOffset_cons_succ]
    omega

theorem nearTgt_eq {i : Insn} {tr : Option Clif.TrapCode} {t : Lbl} {reach align : Int}
    (hs : i.pcRelSpec? = some (t, reach, align)) (ht : t ≠ .skip) (hb : ∀ x, i ≠ .b x)
    (hr : tr = none → i.relaxTarget? = none) : (Line.ins i tr).nearTgt = some t := by
  have hb' : i.isBr = false := by cases i <;> simp_all [Insn.isBr]
  simp only [Line.nearTgt, hs]
  split
  · rename_i h
    exfalso
    rcases h with h | h | ⟨rfl, h⟩
    · exact ht h
    · simp [hb'] at h
    · simp [hr rfl] at h
  · rfl

theorem goodN_nearOk {L : List Line} (h : GoodN 16 L) : NearOk L := by
  intro m hm j i tr t reach align o hj hs ht hb hr ho
  obtain ⟨j', hj', h1, h2⟩ := goodN_near h j _ t hj (nearTgt_eq hs ht hb hr)
  have hl := labelOffsets_go_label hm hj'
  rw [ho, Nat.zero_add] at hl
  cases hl
  obtain ⟨hr1, -, -⟩ := Insn.pcRelSpec_bounds hs
  rcases Nat.le_total j j' with hle | hle
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    have := lineOffset_mono L j d
    omega
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    have := lineOffset_mono L j' d
    omega

theorem good_of_nearOkB {ls : List Line} (h : ∀ ln ∈ ls, ln.nearOkB = true) :
    Good ls ∧ ∀ ln ∈ ls, ln.bOk = true := by
  refine ⟨?_, fun ln hl => by have := h ln hl; simp [Line.nearOkB] at this; exact this.2⟩
  simpa using Good.safes (P := ls) (B := []) (fun ln hl => by
    have := h ln hl; simp [Line.nearOkB] at this; exact this.1) .nil

theorem loadConst64_nearOkB (rd : Reg) (v : Nat) : ∀ ln ∈ loadConst64 rd v, ln.nearOkB = true := by
  intro ln hl
  simp only [loadConst64, List.mem_cons, List.mem_filterMap, List.mem_range] at hl
  rcases hl with rfl | ⟨j, -, hj⟩
  · simp [Line.nearOkB, Line.nearTgt, Line.bOk, Insn.pcRelSpec?]
  · split at hj
    · cases hj; simp [Line.nearOkB, Line.nearTgt, Line.bOk, Insn.pcRelSpec?]
    · cases hj

theorem memFinalize_nearOkB {c : FnCtx} {m : AMode} {b : Nat} {pre : List Line} {m' : AMode}
    (h : memFinalize c m b = .ok (pre, m')) : ∀ ln ∈ pre, ln.nearOkB = true := by
  have key : ∀ (base : Reg) (off : Int) (r : List Line × AMode), r = (match simm9? off with
      | some s => ([], .unscaled base s)
      | none => match uimm12Scaled? off b with
        | some o => ([], .unsignedOffset base o)
        | none => (loadConst64 (.x 16) (u64 off), .regExtended base (.x 16) .sxtx)) →
      ∀ ln ∈ r.1, ln.nearOkB = true := by
    intro base off r hr
    subst hr
    split
    · simp
    · split
      · simp
      · exact loadConst64_nearOkB _ _
  unfold memFinalize at h
  split at h <;> simp only [pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
    Except.ok.injEq, reduceCtorEq] at h
  all_goals first
    | exact key _ _ _ h.symm
    | (cases h; simp)

set_option hygiene false in
macro "emitNear_fin" : tactic => `(tactic| (
  obtain ⟨rfl, -⟩ := h
  exact good_of_nearOkB (by simp_all [Line.nearOkB, Line.nearTgt, Line.bOk, Insn.pcRelSpec?, Insn.isBr,
    Insn.relaxTarget?, Insn.condTarget?, CondBrKind.insn, MInst.noAlways])))

theorem plain_line {i : Insn} {tr : Option Clif.TrapCode} (h : i.pcRelSpec? = none) :
    (Line.ins i tr).isBLine = false ∧ (Line.ins i tr).relaxable? = none ∧
      (Line.ins i tr).nearTgt = none := by
  refine ⟨?_, ?_, by simp [Line.nearTgt, h]⟩
  · cases i <;> simp_all [Line.isBLine, Insn.pcRelSpec?]
  · cases tr
    · have : i.condTarget? = none := by cases i <;> simp_all [Insn.condTarget?, Insn.pcRelSpec?]
      simp [Line.relaxable?, Insn.relaxTarget?, this]
    · rfl

theorem rmwLoopMid_plain (op : AtomicRmwLoopOp) (bits : Nat) :
    (∀ i ∈ rmwLoopMid op bits, i.pcRelSpec? = none) ∧ (rmwLoopMid op bits).length ≤ 3 := by
  have hc : ∀ o, (rmwLoopCmp o bits).pcRelSpec? = none := by
    intro o; unfold rmwLoopCmp; split <;> rfl
  have hs : (∀ i ∈ rmwLoopSext bits, i.pcRelSpec? = none) ∧ (rmwLoopSext bits).length ≤ 1 := by
    unfold rmwLoopSext; split <;> simp [Insn.pcRelSpec?]
  obtain ⟨hs1, hs2⟩ := hs
  constructor
  · cases op <;> simp only [rmwLoopMid, List.forall_mem_append, List.forall_mem_cons, hc,
      List.not_mem_nil, true_and]
    all_goals first
      | exact hs1
      | (refine ⟨hs1, ?_⟩; simp [Insn.pcRelSpec?])
      | simp [Insn.pcRelSpec?]
  · cases op <;> simp [rmwLoopMid] <;> omega

theorem nearBlk_rmw (bits : Nat) (op : AtomicRmwLoopOp) (fl : Clif.MemFlags) (n : Nat) :
    NearBlk (rmwLoopLines bits op fl (.loop n)) := by
  obtain ⟨hmid, hlen⟩ := rmwLoopMid_plain op bits
  have hbody : ∀ ln ∈ rmwLoopBody bits op fl,
      ln.isBLine = false ∧ ln.relaxable? = none ∧ ln.nearTgt = none := by
    intro ln hl
    simp only [rmwLoopBody, List.mem_append, List.mem_singleton, List.mem_map] at hl
    rcases hl with (rfl | ⟨i, hi, rfl⟩) | rfl
    · exact plain_line rfl
    · exact plain_line (hmid i hi)
    · exact plain_line rfl
  have hhead : ∀ ln ∈ Line.label (.loop n) :: rmwLoopBody bits op fl,
      ln.isBLine = false ∧ ln.relaxable? = none ∧ ln.nearTgt = none := by
    intro ln hl
    simp only [List.mem_cons] at hl
    rcases hl with rfl | hl
    · simp [Line.isBLine, Line.relaxable?, Line.nearTgt]
    · exact hbody ln hl
  have e : rmwLoopLines bits op fl (.loop n) =
      (Line.label (.loop n) :: rmwLoopBody bits op fl) ++ [.ins (.cbz true true (.x 24) (.loop n))] := rfl
  have hcbz : (Line.ins (.cbz true true (.x 24) (.loop n)) none).nearTgt = some (.loop n) := by
    simp [Line.nearTgt, Insn.pcRelSpec?, Insn.isBr, Insn.relaxTarget?, Insn.condTarget?]
  rw [e]
  refine ⟨by simp, ?_, ?_, ?_, ?_, Or.inr ?_⟩
  · simp [rmwLoopBody]; omega
  · intro ln hl
    simp only [List.mem_append, List.mem_singleton] at hl
    rcases hl with hl | rfl
    · exact (hhead ln hl).1
    · rfl
  · intro ln hl
    simp only [List.mem_append, List.mem_singleton] at hl
    rcases hl with hl | rfl
    · exact (hhead ln hl).2.1
    · simp [Line.relaxable?, Insn.relaxTarget?, Insn.condTarget?]
  · intro ln hl t ht
    simp only [List.mem_append, List.mem_singleton] at hl
    rcases hl with hl | rfl
    · rw [(hhead ln hl).2.2] at ht; cases ht
    · rw [hcbz] at ht; cases ht; simp
  · rw [List.dropLast_concat]
    exact fun ln hl => (hhead ln hl).2.2

theorem casLoopCmp_plain (bits : Nat) : (casLoopCmp bits).pcRelSpec? = none := by
  unfold casLoopCmp; split <;> rfl

theorem nearBlk_cas (bits : Nat) (fl : Clif.MemFlags) (n : Nat) :
    NearBlk (casLoopLines bits fl (.loop n) (.loop (n + 1))) := by
  have hc := plain_line (tr := none) (casLoopCmp_plain bits)
  refine ⟨by simp [casLoopLines], by simp [casLoopLines, casLoopHead], ?_, ?_, ?_, Or.inl ⟨_, rfl⟩⟩
  · intro ln hl
    simp only [casLoopLines, casLoopHead, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [Line.isBLine]
  · intro ln hl
    simp only [casLoopLines, casLoopHead, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact (plain_line rfl).2.1
        | exact hc.2.1
        | simp_all (config := {decide := true}) [Line.relaxable?, Insn.relaxTarget?, Insn.condTarget?]
  · intro ln hl t ht
    simp only [casLoopLines, casLoopHead, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all (config := {decide := true}) [Line.nearTgt, Insn.pcRelSpec?, Insn.isBr,
        Insn.relaxTarget?, Insn.condTarget?, casLoopLines, casLoopHead]

theorem nearBlk_jt (t1 t2 : Reg) (n : Nat) :
    NearBlk [.ins (.adr t1 (.jt n)), .ins (.load .sload32 t2 (.regScaledExtended t1 t2 .uxtw)),
      .ins (.aluRRR .add true t1 t1 t2), .ins (.br t1), .label (.jt n)] := by
  refine ⟨by simp, by simp, ?_, ?_, ?_, Or.inl ⟨_, rfl⟩⟩
  · simp [Line.isBLine]
  · simp [Line.relaxable?, Insn.relaxTarget?, Insn.condTarget?]
  · simp [Line.nearTgt, Insn.pcRelSpec?, Insn.isBr, Insn.relaxTarget?, Insn.condTarget?]

theorem casLoopLines_bOk (bits : Nat) (fl : Clif.MemFlags) (a o : Lbl) :
    ∀ ln ∈ casLoopLines bits fl a o, ln.bOk = true := by
  intro ln hl
  simp only [casLoopLines, casLoopHead, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | rfl
    | (unfold casLoopCmp; split <;> rfl)
    | simp (config := {decide := true}) [Line.bOk]

theorem rmwLoopLines_bOk (bits : Nat) (op : AtomicRmwLoopOp) (fl : Clif.MemFlags) (l : Lbl) :
    ∀ ln ∈ rmwLoopLines bits op fl l, ln.bOk = true := by
  intro ln hl
  simp only [rmwLoopLines, rmwLoopBody, List.mem_cons, List.mem_append, List.mem_map,
    List.mem_singleton, List.not_mem_nil, or_false] at hl
  rcases hl with (rfl | (rfl | ⟨i, hi, rfl⟩) | rfl) | rfl
  · rfl
  · rfl
  · have := EmitLabels.rmwLoopMid_pc op bits i hi
    cases i <;> simp_all [Line.bOk, Insn.pcRelSpec?]
  · rfl
  · simp [Line.bOk]

theorem lines_ok {c : FnCtx} {ps ps' : PState} {m : MInst} {ls : List Line}
    (hm : m.noAlways = true) (h : m.lines c ps = .ok (ls, ps')) :
    Good ls ∧ ∀ ln ∈ ls, ln.bOk = true := by
  cases m
  all_goals first
    | (simp [MInst.lines, pure, Except.pure] at h; obtain ⟨rfl, -⟩ := h; refine good_of_nearOkB ?_
       simp [Line.nearOkB, Line.nearTgt, Line.bOk, Insn.pcRelSpec?]; done)
    | skip
  case aluRRImmLogic =>
    simp only [MInst.lines] at h
    split at h <;> simp [pure, Except.pure, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw] at h <;> emitNear_fin
  case aluRRImmShift =>
    simp only [MInst.lines] at h
    split at h <;> simp [pure, Except.pure, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw] at h <;> emitNear_fin
  case aluRRRShift =>
    simp only [MInst.lines] at h
    split at h <;> simp [pure, Except.pure] at h <;> emitNear_fin
  case mov =>
    simp only [MInst.lines] at h
    split at h <;> simp [pure, Except.pure] at h <;> emitNear_fin
  case extend =>
    simp only [MInst.lines] at h
    repeat' split at h
    all_goals simp [pure, Except.pure] at h
    all_goals emitNear_fin
  case load op rd mem fl =>
    simp only [MInst.lines] at h
    cases hmf : memFinalize c mem op.bytes with
    | error e => simp [hmf, bind, Except.bind] at h
    | ok r =>
      obtain ⟨pre, mem'⟩ := r
      simp [hmf, bind, Except.bind, pure, Except.pure] at h
      obtain ⟨rfl, -⟩ := h
      refine good_of_nearOkB fun ln hl => ?_
      simp only [List.mem_append, List.mem_singleton] at hl
      rcases hl with hl | rfl
      · exact memFinalize_nearOkB hmf ln hl
      · simp [Line.nearOkB, Line.nearTgt, Line.bOk, Insn.pcRelSpec?]
  case store op rd mem fl =>
    simp only [MInst.lines] at h
    cases hmf : memFinalize c mem op.bytes with
    | error e => simp [hmf, bind, Except.bind] at h
    | ok r =>
      obtain ⟨pre, mem'⟩ := r
      simp [hmf, bind, Except.bind, pure, Except.pure] at h
      obtain ⟨rfl, -⟩ := h
      refine good_of_nearOkB fun ln hl => ?_
      simp only [List.mem_append, List.mem_singleton] at hl
      rcases hl with hl | rfl
      · exact memFinalize_nearOkB hmf ln hl
      · simp [Line.nearOkB, Line.nearTgt, Line.bOk, Insn.pcRelSpec?]
  case fpuLoad sz rd mem fl =>
    simp only [MInst.lines] at h
    cases hmf : memFinalize c mem sz.bytes with
    | error e => simp [hmf, bind, Except.bind] at h
    | ok r =>
      obtain ⟨pre, mem'⟩ := r
      simp [hmf, bind, Except.bind, pure, Except.pure] at h
      obtain ⟨rfl, -⟩ := h
      refine good_of_nearOkB fun ln hl => ?_
      simp only [List.mem_append, List.mem_singleton] at hl
      rcases hl with hl | rfl
      · exact memFinalize_nearOkB hmf ln hl
      · simp [Line.nearOkB, Line.nearTgt, Line.bOk, Insn.pcRelSpec?]
  case fpuStore sz rd mem fl =>
    simp only [MInst.lines] at h
    cases hmf : memFinalize c mem sz.bytes with
    | error e => simp [hmf, bind, Except.bind] at h
    | ok r =>
      obtain ⟨pre, mem'⟩ := r
      simp [hmf, bind, Except.bind, pure, Except.pure] at h
      obtain ⟨rfl, -⟩ := h
      refine good_of_nearOkB fun ln hl => ?_
      simp only [List.mem_append, List.mem_singleton] at hl
      rcases hl with hl | rfl
      · exact memFinalize_nearOkB hmf ln hl
      · simp [Line.nearOkB, Line.nearTgt, Line.bOk, Insn.pcRelSpec?]
  case vecDupImm =>
    simp only [MInst.lines] at h
    split at h <;> simp [pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    emitNear_fin
  case loadAddr rd mem =>
    simp only [MInst.lines] at h
    cases hmf : memFinalize c mem 1 with
    | error e => simp [hmf, bind, Except.bind] at h
    | ok r =>
      obtain ⟨pre, mem'⟩ := r
      simp only [hmf, bind, Except.bind] at h
      have htail : ∀ tl : List Line, (∃ rn rm e, tl = [.ins (.aluRRRExtend .add true rd rn rm e)]) ∨
          (∃ rn off, tl = MInst.lines.addOff rd rn off) → ∀ ln ∈ tl, ln.nearOkB = true := by
        rintro tl (⟨rn, rm, e, rfl⟩ | ⟨rn, off, rfl⟩) ln hl
        · simp at hl; subst hl; simp [Line.nearOkB, Line.nearTgt, Line.bOk, Insn.pcRelSpec?]
        · unfold MInst.lines.addOff at hl
          repeat' split at hl
          all_goals simp at hl
          all_goals subst hl; simp [Line.nearOkB, Line.nearTgt, Line.bOk, Insn.pcRelSpec?]
      split at h <;> simp [pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
      all_goals
        obtain ⟨rfl, -⟩ := h
        refine good_of_nearOkB fun ln hl => ?_
        simp only [List.mem_append] at hl
        rcases hl with hl | hl
        · exact memFinalize_nearOkB hmf ln hl
      · exact htail _ (.inl ⟨_, _, _, rfl⟩) ln hl
      · exact htail _ (.inr ⟨_, _, rfl⟩) ln hl
      · exact htail _ (.inr ⟨_, _, rfl⟩) ln hl
  case call info =>
    simp only [MInst.lines] at h
    split at h <;> simp [pure, Except.pure] at h <;> emitNear_fin
  case args => simp [MInst.lines, throw, throwThe, MonadExceptOf.throw] at h
  case rets => simp [MInst.lines, throw, throwThe, MonadExceptOf.throw] at h
  case jump => simp [MInst.lines, pure, Except.pure] at h; emitNear_fin
  case testBitAndBranch => simp [MInst.lines, pure, Except.pure] at h; emitNear_fin
  case condBr t e k =>
    simp [MInst.lines, pure, Except.pure] at h
    cases k <;> emitNear_fin
  case trapIf k code =>
    simp [MInst.lines, pure, Except.pure] at h
    cases k <;> emitNear_fin
  case tryCall info ti =>
    simp only [MInst.lines] at h
    cases hd : info.dest <;> simp [hd, pure, Except.pure] at h <;> emitNear_fin
  case elfTlsGetAddr =>
    simp only [MInst.lines] at h
    split at h <;> simp [pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    emitNear_fin
  case jtSequence d ts ridx t1 t2 =>
    simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine ⟨?_, ?_⟩
    · have h1 : (Cond.hs == Cond.al) = false := by decide
      have h2 : (Cond.hs == Cond.nv) = false := by decide
      refine .safe (by simp [Line.nearTgt, Insn.pcRelSpec?, Insn.isBr, Insn.relaxTarget?,
        Insn.condTarget?, h1, h2]) (.safe (by simp [Line.nearTgt, Insn.pcRelSpec?]) ?_)
      have hw := Good.safes (P := ts.map fun l => Line.word (.block l) (.jt ps.jt)) (B := [])
        (by simp [Line.nearTgt]) .nil
      rw [List.append_nil] at hw
      exact .blk (nearBlk_jt t1 t2 ps.jt) hw
    · simp [Line.bOk]
  case atomicRmwLoop ty op fl addr operand oldval s1 s2 =>
    simp only [MInst.lines] at h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      have hb := nearBlk_rmw ty.bits op fl ps.aloop
      exact ⟨by simpa using Good.blk hb .nil, rmwLoopLines_bOk _ _ _ _⟩
  case atomicCasLoop ty fl addr expect replace oldval scratch =>
    simp only [MInst.lines] at h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      have hb := nearBlk_cas ty.bits fl ps.aloop
      exact ⟨by simpa using Good.blk hb .nil, casLoopLines_bOk _ _ _ _⟩


theorem nearOkB_ins {i : Insn} {tr : Option Clif.TrapCode} (h : i.pcRelSpec? = none) :
    (Line.ins i tr).nearOkB = true := by
  have := (plain_line (tr := tr) h).2.2
  cases i <;> simp_all [Line.nearOkB, Line.bOk, Insn.pcRelSpec?]

theorem prologue_nearOkB (saves : List Reg) (size : Nat) :
    ∀ ln ∈ prologueLines saves size, ln.nearOkB = true := by
  intro ln hl
  simp only [prologueLines, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with (((rfl | rfl) | hl) | hl) | hl
  · exact nearOkB_ins rfl
  · exact nearOkB_ins rfl
  · obtain ⟨i, rfl, a, b, rfl | rfl⟩ := mem_pushLines hl <;> exact nearOkB_ins rfl
  · obtain ⟨i, rfl, a, b, rfl | rfl⟩ := mem_pushLines hl <;> exact nearOkB_ins rfl
  · rcases mem_spAdjLines hl with ⟨i, -, rfl⟩ | hl | rfl
    · exact nearOkB_ins rfl
    · exact loadConst64_nearOkB _ _ ln hl
    · exact nearOkB_ins rfl

theorem epilogue_nearOkB (saves : List Reg) (size : Nat) :
    ∀ ln ∈ epilogueLines saves size, ln.nearOkB = true := by
  intro ln hl
  simp only [epilogueLines, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with ((hl | hl) | hl) | rfl | rfl
  · rcases mem_spAdjLines hl with ⟨i, -, rfl⟩ | hl | rfl
    · exact nearOkB_ins rfl
    · exact loadConst64_nearOkB _ _ ln hl
    · exact nearOkB_ins rfl
  · obtain ⟨i, rfl, a, b, rfl | rfl⟩ := mem_popLines hl <;> exact nearOkB_ins rfl
  · obtain ⟨i, rfl, a, b, rfl | rfl⟩ := mem_popLines hl <;> exact nearOkB_ins rfl
  · exact nearOkB_ins rfl
  · exact nearOkB_ins rfl

theorem codeLinesE_good {c : FnCtx} {af : AFunc} :
    ∀ (code : List AInst) (ps ps' : PState) (ls : List Line),
      (∀ m, AInst.inst m ∈ code → m.noAlways = true) →
      codeLinesE c af code ps = .ok (ls, ps') → Good ls ∧ ∀ ln ∈ ls, ln.bOk = true
  | [], ps, ps', ls, _, h => by
    simp [codeLinesE, pure, Except.pure] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨.nil, by simp⟩
  | a :: as, ps, ps', ls, hna, h => by
    simp only [codeLinesE, bind, Except.bind] at h
    cases h1 : ainstLines c af a ps with
    | error e => rw [h1] at h; cases h
    | ok r1 =>
      rw [h1] at h
      dsimp only at h
      cases h2 : codeLinesE c af as r1.2 with
      | error e => rw [h2] at h; cases h
      | ok r2 =>
        rw [h2] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        obtain ⟨rfl, -⟩ := Prod.mk.inj h
        obtain ⟨g2, b2⟩ := codeLinesE_good as r1.2 r2.2 r2.1
          (fun m hm => hna m (by simp [hm])) h2
        have g1 : Good r1.1 ∧ ∀ ln ∈ r1.1, ln.bOk = true := by
          cases a with
          | inst m =>
            exact lines_ok (hna m (by simp)) (by simpa [ainstLines] using h1)
          | prologue =>
            simp only [ainstLines, pure, Except.pure, Except.ok.injEq] at h1
            subst h1
            split
            · exact good_of_nearOkB (prologue_nearOkB _ _)
            · exact ⟨.nil, by simp⟩
          | epilogueRet =>
            simp only [ainstLines, pure, Except.pure, Except.ok.injEq] at h1
            subst h1
            split
            · exact good_of_nearOkB (epilogue_nearOkB _ _)
            · exact good_of_nearOkB (by simp [Line.nearOkB, Line.nearTgt, Line.bOk, Insn.pcRelSpec?])
        exact ⟨g1.1.append g2, by
          intro ln hl
          simp only [List.mem_append] at hl
          rcases hl with hl | hl
          · exact g1.2 ln hl
          · exact b2 ln hl⟩

/-- The segments' unsimplified lines are `Good`, every line with its branch shape (`bOk`). -/
theorem segsOf_good {c : FnCtx} {af : AFunc} :
    ∀ (bs : List ((Label × Array AInst) × Nat)) (ps ps' : PState) (ss : List Seg),
      (∀ p ∈ bs, ∀ m, AInst.inst m ∈ p.1.2.toList → m.noAlways = true) →
      segsOf c af bs ps = .ok (ss, ps') →
      Good (segLines ss (ss.map (·.term))) ∧ ∀ ln ∈ segLines ss (ss.map (·.term)), ln.bOk = true
  | [], ps, ps', ss, _, h => by
    simp only [segsOf, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨.nil, by simp [segLines]⟩
  | ((l, code), i) :: bs, ps, ps', ss, hna, h => by
    simp only [segsOf] at h
    obtain ⟨⟨l1, ps1⟩, h1, h⟩ := exceptBind_ok h
    obtain ⟨⟨l2, ps2⟩, h2, h⟩ := exceptBind_ok h
    obtain ⟨⟨l3, ps3⟩, h3, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hna0 := hna _ (List.mem_cons_self ..)
    obtain ⟨g1, b1⟩ := codeLinesE_good _ ps ps1 l1
      (fun m hm => hna0 m ((List.dropLast_sublist _).subset hm)) h1
    obtain ⟨g2, b2⟩ := codeLinesE_good _ ps1 ps2 l2
      (fun m hm => hna0 m (EmitLabels.mem_of_getLast?_toList hm)) h2
    obtain ⟨g3, b3⟩ := segsOf_good bs ps2 _ l3 (fun p hp => hna p (by simp [hp])) h3
    simp only [List.map_cons, segLines, List.cons_append, List.append_assoc]
    refine ⟨.safe (by simp [Line.nearTgt]) (g1.append (g2.append g3)), ?_⟩
    intro ln hl
    simp only [List.mem_cons, List.mem_append] at hl
    rcases hl with rfl | hl | hl | hl
    · rfl
    · exact b1 ln hl
    · exact b2 ln hl
    · exact b3 ln hl

theorem trapLines_nearOkB (ps : PState) : ∀ ln ∈ trapLines ps, ln.nearOkB = true := by
  intro ln hl
  simp only [trapLines, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hl
  obtain ⟨p, -, rfl | rfl⟩ := hl
  · simp [Line.nearOkB, Line.nearTgt, Line.bOk]
  · exact nearOkB_ins rfl

theorem stepLine_removable {ln : Line} {t : Lbl}
    (h : (ln.ubr?).orElse (fun _ => ln.cbr?) = some t) : ln.removable = true ∧ ∃ X, t = .block X := by
  unfold Line.ubr? Line.cbr? at h
  split at h
  · simp only [Option.orElse, Option.some.injEq] at h
    subst h
    exact ⟨by simp [Line.removable, Line.isBLine], _, rfl⟩
  · simp only [Option.orElse] at h
    split at h
    · rename_i c _
      split at h
      · rename_i l hc
        cases h
        refine ⟨?_, _, rfl⟩
        simp [Line.removable, Line.relaxable?, Insn.relaxTarget?, hc]
      · cases h
    · cases h

/-- The inverse of a conditional branch to a block, retargeted to a block, keeps the branch
shape and stays relaxable. -/
theorem invert_shape {c : Insn} {tc : Option Clif.TrapCode} {ct : Lbl}
    (hct : (Line.ins c tc).cbr? = some ct) (X : Label) :
    tc = none ∧ (Line.ins (c.invertTo (.block X)) none).removable = true ∧
      (Line.ins (c.invertTo (.block X)) none).bOk = true := by
  cases tc with
  | some _ => simp [Line.cbr?] at hct
  | none =>
    refine ⟨rfl, ?_, ?_⟩
    · obtain ⟨l, hl⟩ : ∃ l, c.condTarget? = some l := by
        simp only [Line.cbr?] at hct
        split at hct
        · exact ⟨_, by assumption⟩
        · cases hct
      have := condTarget_invertTo (e := .block X) hl
      simp [Line.removable, Line.relaxable?, Insn.relaxTarget?, this]
    · cases c <;> simp_all [Line.cbr?, Insn.condTarget?, Insn.invertTo, Line.bOk]
      rename_i cc _
      cases cc <;> simp_all [Cond.invert] <;> decide

theorem foldl_insert_get {t : Lbl} : ∀ (als : List Lbl) (A : Std.TreeMap Lbl Lbl) (k x : Lbl),
    (als.foldl (fun a l => a.insert l t) A)[k]? = some x → A[k]? = some x ∨ x = t
  | [], A, k, x, h => .inl h
  | l :: als, A, k, x, h => by
    rcases foldl_insert_get als (A.insert l t) k x h with h' | h'
    · rw [Std.TreeMap.getElem?_insert] at h'
      split at h'
      · cases h'; exact .inr rfl
      · exact .inl h'
    · exact .inr h'

/-- What `MachBuffer` keeps of its input `I` (the lines pushed so far): its lines are `I`'s
with removable lines removed or replaced (`MBRel`), and the labels are aliased to blocks. -/
def MBGood (I : List Line) (m : MBuf) : Prop :=
  MBRel I m.out.toList ∧ ∀ k x : Lbl, m.alias[k]? = some x → ∃ X : Label, x = .block X

theorem step_mbGood {I : List Line} (allLabels : Bool) (m m' : MBuf) (hm : MBGood I m)
    (h : MBuf.step allLabels m = some m') : MBGood I m' := by
  obtain ⟨hr, ha⟩ := hm
  obtain ⟨k, ln, t, -, hkln, ht, hc⟩ := step_cases allLabels m m' h
  obtain ⟨hrem, X, rfl⟩ := stepLine_removable ht
  have hE : MBRel I (m.erase k).toList := by
    simp only [MBuf.erase, List.toList_toArray]
    exact hr.erase k ln (by simpa using hkln) hrem
  rcases hc with ⟨ho, hal⟩ | ⟨ho, als, hal⟩ | ⟨p, c, tc, ct, hpk, hp, hct, -, ho, hal⟩
  · exact ⟨by rw [ho]; exact hE, by rw [hal]; exact ha⟩
  · refine ⟨by rw [ho]; exact hr, fun k' x hx => ?_⟩
    rw [hal] at hx
    rcases foldl_insert_get als _ k' x hx with hx | rfl
    · exact ha k' x hx
    · exact ⟨X, rfl⟩
  · refine ⟨?_, by rw [hal]; exact ha⟩
    obtain ⟨rfl, hy1, hy2⟩ := invert_shape hct X
    rw [ho, Array.set!, Array.toList_setIfInBounds]
    refine hE.set p (Line.ins c) _ ?_ ?_ hy1 hy2
    · simp only [MBuf.erase, List.toList_toArray, List.getElem?_eraseIdx_of_lt hpk,
        Array.getElem?_toList, hp]
    · obtain ⟨-, l, hl⟩ : True ∧ ∃ l, c.condTarget? = some l := by
        simp only [Line.cbr?] at hct
        split at hct
        · exact ⟨trivial, _, by assumption⟩
        · cases hct
      simp only [Line.removable, Line.relaxable?, Insn.relaxTarget?] at hct ⊢
      simp only [Line.cbr?] at hct
      split at hct
      · rename_i l' hl'
        simp [hl']
      · cases hct

theorem optimize_mbGood {I : List Line} (allLabels : Bool) (m : MBuf) (hm : MBGood I m) :
    MBGood I (MBuf.optimize allLabels m) := by
  unfold MBuf.optimize
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  refine mbForIn_inv (P := MBGood I) _ _ _ hm ?_
  intro _ s hs
  split
  · rename_i m' h; exact step_mbGood _ _ _ hs h
  · exact hs

/-- **`MachBuffer`'s simplification keeps the near lines' reach** (blocks of at most 8 lines). -/
theorem machBuf_goodN (allLabels : Bool) (ls : List Line) (hg : Good ls)
    (hb : ∀ ln ∈ ls, ln.bOk = true) :
    GoodN 8 (machBuf allLabels ls).1 ∧ ∀ ln ∈ (machBuf allLabels ls).1, ln.bOk = true := by
  have hfold : ∀ (L I : List Line) (m : MBuf), MBGood I m →
      MBGood (I ++ L) (L.foldl (fun m ln =>
        let m := { m with out := m.out.push ln }
        if ln matches .label _ then m.optimize allLabels else m) m) := by
    intro L
    induction L with
    | nil => intro I m h; simpa using h
    | cons ln L ih =>
      intro I m h
      rw [List.foldl_cons, show I ++ ln :: L = (I ++ [ln]) ++ L by simp]
      apply ih
      have hp : MBGood (I ++ [ln]) { m with out := m.out.push ln } :=
        ⟨by rw [Array.toList_push]; exact h.1.snoc ln, h.2⟩
      split
      · exact optimize_mbGood _ _ hp
      · exact hp
  obtain ⟨hr, ha⟩ := optimize_mbGood allLabels _
    (by simpa using hfold ls [] {} ⟨.nil, fun k x hx => by simp at hx⟩)
  have hbo := hr.bOk hb
  have hf : ∀ t, (MBuf.optimize allLabels (ls.foldl (fun m ln =>
        let m := { m with out := m.out.push ln }
        if ln matches .label _ then m.optimize allLabels else m) {})).res t = t ∨
      ∃ X, (MBuf.optimize allLabels (ls.foldl (fun m ln =>
        let m := { m with out := m.out.push ln }
        if ln matches .label _ then m.optimize allLabels else m) {})).res t = .block X := by
    intro t
    rcases EmitLabels.res_cases _ t with e | ⟨k, hk⟩
    · exact .inl e
    · exact .inr (ha k _ hk)
  unfold machBuf
  dsimp only
  refine ⟨goodN_relabel _ hf (good_goodN (good_mbrel hg hr)) hbo, fun ln hl => ?_⟩
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hl
  exact relabel_bOk _ hf y (hbo y hy)

/-- The emission plan's lines: `GoodN 8`, every line with its branch shape. -/
theorem emitPlan_goodN {k : Nat} {af : AFunc} {p : Plan} (h : emitPlan k af = .ok p)
    (hna : af.NoAlways) :
    GoodN 8 (segLines p.segs p.outs) ∧ ∀ ln ∈ segLines p.segs p.outs, ln.bOk = true := by
  have hz : af.blocks.toList.zipIdx.map (·.1) = af.blocks.toList := by
    rw [List.zipIdx_eq_zip_range', List.map_fst_zip (by simp)]
  obtain ⟨hg, hb⟩ := segsOf_good _ _ _ _ (fun x hx m hm => hna x.1 (by
    rw [← hz]; exact List.mem_map.2 ⟨x, (emitOrder_perm af).mem_iff.mp hx, rfl⟩) m hm)
    (emitPlan_spec h).1
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
    rcases h1' with h1' | h1' <;>
    · obtain ⟨hs, hsp⟩ := machPlan_split h1'
      rw [hs] at hg hb ⊢
      rw [splitSegs_lines _ _ _ hsp]
      exact machBuf_goodN _ _ hg hb
  · split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨good_goodN hg, hb⟩
    · cases h

theorem visit_noAlways {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : OpSpec → Reg → m Reg) (i : MInst) :
    MInst.noAlways <$> MInst.visitOperands f i = (fun _ => i.noAlways) <$> MInst.visitOperands f i := by
  cases i
  case condBr a b k =>
    cases k <;> simp [MInst.visitOperands, CondBrKind.visit, MInst.noAlways]
  case trapIf k c =>
    cases k <;> simp [MInst.visitOperands, CondBrKind.visit, MInst.noAlways]
  case call info =>
    rcases info with ⟨dest, us, ds⟩
    cases dest <;> simp [MInst.visitOperands, MInst.noAlways]
  case tryCall info ti =>
    rcases info with ⟨dest, us, ds⟩
    cases dest <;> simp [MInst.visitOperands, MInst.noAlways]
  all_goals simp [MInst.visitOperands, MInst.noAlways]

theorem assign_noAlways {i i' : MInst} {regs : Array Reg} (h : i.assign regs = .ok i') :
    i'.noAlways = i.noAlways := by
  rw [Proof.assign_eq] at h
  have e := congrArg (fun x => StateT.run x 0)
    (visit_noAlways (m := StateT Nat (Except String)) (Proof.putOp regs) i)
  simp only [StateT.run_map] at e
  cases hr : (MInst.visitOperands (Proof.putOp regs) i).run 0 with
  | error err => simp [hr, bind, Except.bind] at h
  | ok p =>
    rw [hr] at e h
    simp only [bind, Except.bind] at h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simpa [Functor.map, Except.map] using e

theorem slotStoreAt_noAlways (cls : RegClass) (r : Reg) (off : Nat) :
    ∀ m ∈ slotStoreAt cls r off, m.noAlways = true := by
  intro m hm
  unfold slotStoreAt at hm
  split at hm
  · simp only [List.mem_singleton] at hm
    subst hm
    unfold slotStore
    cases cls <;> rfl
  · simp only [spAddrX16, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil,
      or_false] at hm
    rcases hm with ((rfl | ⟨_, _, rfl⟩) | rfl) | rfl <;> (try cases cls) <;> rfl

theorem slotLoadAt_noAlways (cls : RegClass) (r : Reg) (off : Nat) :
    ∀ m ∈ slotLoadAt cls r off, m.noAlways = true := by
  intro m hm
  unfold slotLoadAt at hm
  split at hm
  · simp only [List.mem_singleton] at hm
    subst hm
    unfold slotLoad
    cases cls <;> rfl
  · simp only [spAddrX16, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil,
      or_false] at hm
    rcases hm with ((rfl | ⟨_, _, rfl⟩) | rfl) | rfl <;> (try cases cls) <;> rfl

theorem moveInsts_noAlways {fr : RAFrame} {src dst : Loc} {l : List AInst}
    (h : fr.moveInsts src dst = .ok l) : ∀ m, AInst.inst m ∈ l → m.noAlways = true := by
  intro m hm
  unfold RAFrame.moveInsts at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h; cases hm
  · cases h; cases hm
  · split at h
    · cases h
      simp only [List.mem_singleton, AInst.inst.injEq] at hm
      subst hm
      rfl
    · cases h
      rcases List.mem_append.mp (mem_map_inst hm) with h | h
      · exact slotStoreAt_noAlways _ _ _ m h
      · exact slotLoadAt_noAlways _ _ _ m h
  · split at h
    · cases h
    · cases h
      exact slotStoreAt_noAlways _ _ _ m (mem_map_inst hm)
  · split at h
    · cases h
    · cases h
      exact slotLoadAt_noAlways _ _ _ m (mem_map_inst hm)
  · cases h

end E2E.EmitNear

namespace E2E

open Backend EmitNear

/-- **The near PC-relative lines reach their labels**, for an allocated function without
`al`/`nv` branch conditions. -/
theorem emitFunc_near_of {k : Nat} {af : AFunc} {fa : FnAsm} (hna : af.NoAlways)
    (he : emitFunc k af = .ok fa) : NearOk fa.lines.toList := by
  obtain ⟨p, hp, hL, -⟩ := emitFunc_ok he
  obtain ⟨g, -⟩ := emitPlan_goodN hp hna
  rw [hL]
  apply goodN_nearOk
  apply goodN_relax (n := 8)
  exact g.append (GoodN.safes (fun ln hl => by
    have := trapLines_nearOkB p.ps ln hl; simp [Line.nearOkB] at this; exact this.1) .nil |>
    fun h => by simpa using h)

/-- **The lowering keeps the conditions**: every instruction of `lowerRFunc vc rf` is a move's
(no conditional branch) or the allocated form of an instruction of `vc` (same conditions). -/
theorem af_noAlways_of {vc : VCode} {rf : RFunc} {af : AFunc} (hna : vc.noAlwaysB = true)
    (h : lowerRFunc vc rf = .ok af) : af.NoAlways := by
  intro p hp m hm
  obtain ⟨⟨-, -, hsz, hbl⟩, -, -⟩ := lowerRFunc_ok h
  obtain ⟨b, hb⟩ := List.mem_iff_getElem?.mp hp
  rw [Array.getElem?_toList] at hb
  have hlt : b < (vc.blocks.zip rf.blocks).size := by
    rw [← hsz]; exact (Array.getElem?_eq_some_iff.mp hb).1
  rw [Array.size_zip] at hlt
  obtain ⟨vb, hvb⟩ : ∃ vb, vc.blocks[b]? = some vb := ⟨_, Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨items, hit⟩ : ∃ items, rf.blocks[b]? = some items :=
    ⟨_, Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨cd, hcd, hb'⟩ := hbl b vb items hvb hit
  rw [hb] at hb'
  cases hb'
  have hm' : AInst.inst m ∈ cd := by
    simp only [List.mem_append] at hm
    rcases hm with h | h
    · split at h <;> simp at h
    · exact h
  obtain ⟨it, -, c1, hc1, hmc⟩ := mem_itemsCode hcd hm'
  cases it with
  | move src dst => exact moveInsts_noAlways (itemCode_move_ok hc1) m hmc
  | op kk allocs =>
    obtain ⟨regs, i, i', -, hi, hasg, hcase⟩ := Backend.Proof.itemCode_op hc1
    have hvi : i.noAlways = true := by
      simp only [VCode.noAlwaysB, List.all_eq_true] at hna
      exact hna vb (List.mem_of_getElem? (by simpa using hvb)) i
        (List.mem_of_getElem? (by simpa using hi))
    rcases hcase with ⟨rfl, -, -⟩ | ⟨ds, -, rfl⟩ | ⟨us, -, rfl⟩
    · simp only [List.mem_singleton, AInst.inst.injEq] at hmc
      subst hmc
      rw [assign_noAlways hasg]; exact hvi
    · cases hmc
    · simp at hmc

/-- **The near PC-relative lines of the spill path reach their labels** (V6b): for the lowering
`af` of the spill allocation of a prepared VCode without `al`/`nv` branch conditions, the lines
`emitFunc` produces satisfy `NearOk`. -/
theorem emitFunc_spill_near {vcp : VCode} {af : AFunc} {k : Nat} {fa : FnAsm}
    (hna : vcp.noAlwaysB = true) (ha : lowerRFunc vcp (spillAlloc vcp) = .ok af)
    (he : emitFunc k af = .ok fa) : NearOk fa.lines.toList :=
  emitFunc_near_of (af_noAlways_of hna ha) he

end E2E
