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

def Line.bOk : Line → Bool
  | .ins (.b (.block _)) _ => true
  | .ins (.b _) _ => false
  | _ => true

def Line.nearOkB (ln : Line) : Bool := ln.nearTgt.isNone && ln.bOk

/-- Every instruction of the allocated function has no `al`/`nv` branch condition. -/
def AFunc.NoAlways (af : AFunc) : Prop :=
  ∀ p ∈ af.blocks.toList, ∀ m, AInst.inst m ∈ p.2.toList → m.noAlways = true

end Backend

namespace E2E.EmitNear

open Backend

theorem ftStep_cases (ln : Line) (n1 n2 : Option Line) :
    ftStep ln n1 n2 = ([ln], 1) ∨ (ftStep ln n1 n2 = ([], 1) ∧ ln.isBLine = true) ∨
    ∃ c e l, ln = .ins c none ∧ n1 = some (.ins (.b e) none) ∧ n2 = some (.label l) ∧
      c.condTarget? = some l ∧ ftStep ln n1 n2 = ([.ins (c.invertTo e) none], 2) := by
  unfold ftStep
  repeat' split
  all_goals simp_all [Line.isBLine]

theorem ftStep_keep {ln : Line} {n1 n2 : Option Line} (hb : ln.isBLine = false)
    (h : ln.isLabel = true ∨ ∀ e, n1 ≠ some (.ins (.b e) none)) : ftStep ln n1 n2 = ([ln], 1) := by
  rcases ftStep_cases ln n1 n2 with h1 | ⟨_, h2⟩ | ⟨c, e, l, rfl, rfl, rfl, _, _⟩
  · exact h1
  · simp [hb] at h2
  · simp [Line.isLabel] at h

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

theorem Good.tail_b' {M : List Line} (h : Good M) :
    ∀ x L, M = x :: L → x.isBLine = true → Good L := by
  intro x L e hx
  cases h with
  | nil => cases e
  | safe _ h => simp only [List.cons.injEq] at e; obtain ⟨-, rfl⟩ := e; exact h
  | blk hs hL =>
    rename_i s L0
    cases s with
    | nil => exact absurd rfl hs.ne
    | cons y s =>
      simp only [List.cons_append, List.cons.injEq] at e
      obtain ⟨rfl, -⟩ := e
      simp [hs.nob y (by simp)] at hx

theorem Good.tail_b {x : Line} {L : List Line} (h : Good (x :: L)) (hx : x.isBLine = true) :
    Good L := h.tail_b' x L rfl hx

theorem ftList_keep {ln : Line} {rest : List Line} (hb : ln.isBLine = false)
    (h : ln.isLabel = true ∨ ∀ e, rest[0]? ≠ some (.ins (.b e) none)) :
    ftList (ln :: rest) = ln :: ftList rest := by
  rw [ftList_cons, ftStep_keep hb h]
  simp

theorem ftList_noB_prefix (Z : List Line) :
    ∀ (x : Line) (s : List Line), (∀ ln ∈ x :: s, ln.isBLine = false) →
      ftList (x :: s ++ Z) = (x :: s).dropLast ++ ftList ((x :: s).getLast (by simp) :: Z)
  | x, [], _ => by simp
  | x, y :: s, h => by
    rw [List.cons_append, ftList_keep (h x (by simp)) (Or.inr fun e => ?_)]
    · rw [ftList_noB_prefix Z y s (fun ln hl => h ln (List.mem_cons_of_mem _ hl))]
      simp
    · intro he
      simp only [List.cons_append, List.getElem?_cons_zero, Option.some.injEq] at he
      have := h y (by simp)
      simp [he, Line.isBLine] at this

theorem good_ft : ∀ (n : Nat) (L : List Line), L.length ≤ n → Good L →
    (∀ ln ∈ L, ln.bOk = true) → Good (ftList L)
  | 0, L, hn, hg, _ => by
    have : L = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [ftList]; exact .nil
  | n + 1, L, hn, hg, hb => by
    cases hg with
    | nil => simp [ftList]; exact .nil
    | safe hs hL =>
      rename_i ln L'
      have hb' : ∀ x ∈ L', x.bOk = true := fun x hx => hb x (by simp [hx])
      have ih := good_ft n L' (by simp at hn; omega) hL hb'
      rw [ftList_cons]
      rcases ftStep_cases ln L'[0]? L'[1]? with h1 | ⟨h2, -⟩ | ⟨c, e, l, rfl, h1, h2, hc, h3⟩
      · rw [h1]; simpa using Good.safe hs ih
      · rw [h2]; simpa using ih
      · rw [h3]
        obtain ⟨L'', rfl⟩ : ∃ L'', L' = .ins (.b e) none :: L'' := by
          cases L' with
          | nil => simp at h1
          | cons y L'' => simp at h1; exact ⟨L'', by rw [h1]⟩
        have hbe := hb' (.ins (.b e) none) (by simp)
        obtain ⟨b, rfl⟩ : ∃ b, e = .block b := by
          cases e <;> simp [Line.bOk] at hbe; exact ⟨_, rfl⟩
        have hg'' := hL.tail_b (by rfl)
        simp only [List.drop_succ_cons, List.drop_zero, List.singleton_append]
        exact .safe (nearTgt_invert hc)
          (good_ft n L'' (by simp at hn; omega) hg'' fun x hx => hb' x (by simp [hx]))
    | blk hs hL =>
      rename_i s Z
      have hbZ : ∀ x ∈ Z, x.bOk = true := fun x hx => hb x (by simp [hx])
      obtain ⟨x, s', rfl⟩ : ∃ x s', s = x :: s' := by
        cases s with
        | nil => exact absurd rfl hs.ne
        | cons x s' => exact ⟨x, s', rfl⟩
      have hlen : Z.length ≤ n := by simp at hn; omega
      rw [ftList_noB_prefix Z x s' hs.nob]
      generalize hlast : (x :: s').getLast (by simp) = last
      have hsplit : x :: s' = (x :: s').dropLast ++ [last] := by
        rw [← hlast]; exact (List.dropLast_concat_getLast _).symm
      have hlm : last ∈ x :: s' := by rw [← hlast]; exact List.getLast_mem _
      rw [ftList_cons]
      rcases ftStep_cases last Z[0]? Z[1]? with h1 | ⟨-, h2⟩ | ⟨c, e, l, rfl, h1, h2, hc, h3⟩
      · rw [h1]
        have := Good.blk hs (good_ft n Z hlen hL hbZ)
        simp only [List.drop_succ_cons, List.drop_zero, List.singleton_append]
        rw [hsplit] at this
        simpa using this
      · simp [hs.nob last hlm] at h2
      · rw [h3]
        obtain ⟨Z'', rfl⟩ : ∃ Z'', Z = .ins (.b e) none :: Z'' := by
          cases Z with
          | nil => simp at h1
          | cons y Z'' => simp at h1; exact ⟨Z'', by rw [h1]⟩
        have hbe := hbZ (.ins (.b e) none) (by simp)
        obtain ⟨b, rfl⟩ : ∃ b, e = .block b := by
          cases e <;> simp [Line.bOk] at hbe; exact ⟨_, rfl⟩
        have hdl : ∀ ln ∈ (x :: s').dropLast, ln.nearTgt = none := by
          rcases hs.tail with ⟨l', hl'⟩ | h
          · rw [List.getLast?_eq_some_getLast (by simp), hlast] at hl'
            cases hl'
          · exact h
        simp only [List.drop_succ_cons, List.drop_zero, List.singleton_append]
        exact Good.safes hdl (.safe (nearTgt_invert hc)
          (good_ft n Z'' (by simp at hlen; omega) (hL.tail_b rfl)
            fun y hy => hbZ y (by simp [hy])))

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

theorem good_relax (far : Lbl → Bool) {L : List Line} (h : Good L) : Good (relaxLines far L) := by
  induction h with
  | nil => exact .nil
  | @safe ln L hs _ ih =>
    rw [show ln :: L = [ln] ++ L from rfl, relaxLines_append]
    exact Good.safes (by simpa [relaxLines] using relaxLine_safe far hs) ih
  | blk hs _ ih =>
    rw [relaxLines_append, relaxLines_fix far _ hs.norelax]
    exact .blk hs ih

theorem good_near {L : List Line} (h : Good L) :
    ∀ j ln t, L[j]? = some ln → ln.nearTgt = some t →
      ∃ j', L[j']? = some (.label t) ∧ j' < j + 8 ∧ j < j' + 8 := by
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

theorem good_nearOk {L : List Line} (h : Good L) : NearOk L := by
  intro m hm j i tr t reach align o hj hs ht hb hr ho
  obtain ⟨j', hj', h1, h2⟩ := good_near h j _ t hj (nearTgt_eq hs ht hb hr)
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
      refine ⟨by simpa using Good.blk hb .nil, fun ln hl => ?_⟩
      have := hb.nob ln hl
      cases ln with
      | ins i tr => cases i <;> simp_all [Line.bOk, Line.isBLine]
      | _ => rfl
  case atomicCasLoop ty fl addr expect replace oldval scratch =>
    simp only [MInst.lines] at h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      have hb := nearBlk_cas ty.bits fl ps.aloop
      refine ⟨by simpa using Good.blk hb .nil, fun ln hl => ?_⟩
      have := hb.nob ln hl
      cases ln with
      | ins i tr => cases i <;> simp_all [Line.bOk, Line.isBLine]
      | _ => rfl


theorem nearOkB_ins {i : Insn} {tr : Option Clif.TrapCode} (h : i.pcRelSpec? = none) :
    (Line.ins i tr).nearOkB = true := by
  have := (plain_line (tr := tr) h).2.2
  cases i <;> simp_all [Line.nearOkB, Line.bOk, Insn.pcRelSpec?]

theorem prologue_nearOkB (n : Nat) : ∀ ln ∈ prologueLines n, ln.nearOkB = true := by
  intro ln hl
  unfold prologueLines at hl
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with (rfl | rfl) | hl
  · exact nearOkB_ins rfl
  · exact nearOkB_ins rfl
  · split at hl
    · simp at hl
    · split at hl
      · simp at hl; subst hl; exact nearOkB_ins rfl
      · simp only [List.mem_append, List.mem_singleton] at hl
        rcases hl with hl | rfl
        · exact loadConst64_nearOkB _ _ ln hl
        · exact nearOkB_ins rfl

theorem epilogue_nearOkB (n : Nat) : ∀ ln ∈ epilogueLines n, ln.nearOkB = true := by
  intro ln hl
  unfold epilogueLines at hl
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with hl | (rfl | rfl)
  · split at hl
    · simp at hl
    · split at hl
      · simp at hl; subst hl; exact nearOkB_ins rfl
      · simp only [List.mem_append, List.mem_singleton] at hl
        rcases hl with hl | rfl
        · exact loadConst64_nearOkB _ _ ln hl
        · exact nearOkB_ins rfl
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
            · exact good_of_nearOkB (prologue_nearOkB _)
            · exact ⟨.nil, by simp⟩
          | epilogueRet =>
            simp only [ainstLines, pure, Except.pure, Except.ok.injEq] at h1
            subst h1
            split
            · exact good_of_nearOkB (epilogue_nearOkB _)
            · exact good_of_nearOkB (by simp [Line.nearOkB, Line.nearTgt, Line.bOk, Insn.pcRelSpec?])
        exact ⟨g1.1.append g2, by
          intro ln hl
          simp only [List.mem_append] at hl
          rcases hl with hl | hl
          · exact g1.2 ln hl
          · exact b2 ln hl⟩

theorem blocksLinesE_good {c : FnCtx} {af : AFunc} :
    ∀ (bs : List (Label × Array AInst)) (ps ps' : PState) (ls : List Line),
      (∀ p ∈ bs, ∀ m, AInst.inst m ∈ p.2.toList → m.noAlways = true) →
      blocksLinesE c af bs ps = .ok (ls, ps') → Good ls ∧ ∀ ln ∈ ls, ln.bOk = true
  | [], ps, ps', ls, _, h => by
    simp [blocksLinesE, pure, Except.pure] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨.nil, by simp⟩
  | (l, code) :: bs, ps, ps', ls, hna, h => by
    simp only [blocksLinesE, bind, Except.bind] at h
    cases h1 : codeLinesE c af code.toList ps with
    | error e => rw [h1] at h; cases h
    | ok r1 =>
      rw [h1] at h
      dsimp only at h
      cases h2 : blocksLinesE c af bs r1.2 with
      | error e => rw [h2] at h; cases h
      | ok r2 =>
        rw [h2] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        obtain ⟨rfl, -⟩ := Prod.mk.inj h
        obtain ⟨g2, b2⟩ := blocksLinesE_good bs r1.2 r2.2 r2.1
          (fun p hp => hna p (by simp [hp])) h2
        obtain ⟨g1, b1⟩ := codeLinesE_good code.toList ps r1.2 r1.1
          (hna (l, code) (by simp)) h1
        refine ⟨.safe (by simp [Line.nearTgt]) (g1.append g2), ?_⟩
        intro ln hl
        simp only [List.mem_cons, List.mem_append] at hl
        rcases hl with (rfl | hl) | hl
        · rfl
        · exact b1 ln hl
        · exact b2 ln hl

theorem trapLines_nearOkB (ts : List (Lbl × Clif.TrapCode)) : ∀ ln ∈ trapLines ts, ln.nearOkB = true := by
  intro ln hl
  simp only [trapLines, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hl
  obtain ⟨p, -, rfl | rfl⟩ := hl
  · simp [Line.nearOkB, Line.nearTgt, Line.bOk]
  · exact nearOkB_ins rfl

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
  obtain ⟨body, ps, hb, hL, -⟩ := emitFunc_ok he
  obtain ⟨g, bo⟩ := blocksLinesE_good af.blocks.toList {} ps body hna hb
  rw [hL]
  apply good_nearOk
  apply good_relax
  exact (good_ft body.length body (Nat.le_refl _) g bo).append (good_of_nearOkB (trapLines_nearOkB _)).1

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
