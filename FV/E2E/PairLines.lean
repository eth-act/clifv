import FV.E2E.RegLevelRelax

/-!
# `adrp` pairs stay adjacent in `emitFunc`'s lines

The second word of an `adrp` pair (`ldr …, :got_lo12:` / `add …, :lo12:`) is emitted only by
`loadExtNameGot`/`loadExtNameNear`, right after its first word (`adrp`), and neither
`fallthrough` (which only drops or rewrites branches before a label) nor branch relaxation
(which only rewrites conditional branches) separates them: `emitFunc_pairsClosed`.

The proof uses the boolean `pcOk b L` ("every second word of `L` follows a first word; `b`: the
line before `L` is a first word"), which is closed under `++` (`pcOk_append`).
-/

namespace Backend.Proof

open Backend

/-- The second word of an `adrp` pair. -/
def _root_.Backend.Insn.pairSecond : Insn → Bool
  | .ldrGotLo12 .. | .addLo12 .. => true
  | _ => false

/-- Every second word of an `adrp` pair in `L` immediately follows a first word (`adrpGot`/`adrp`). -/
def PairsClosed (L : List Line) : Prop :=
  ∀ k x t, L[k]? = some (.ins x t) → x.pairSecond = true →
    ∃ k' y t', k = k' + 1 ∧ L[k']? = some (.ins y t') ∧ ((∃ a b, y = .adrpGot a b) ∨ ∃ a b c, y = .adrp a b c)

/-- The line is the second word of an `adrp` pair. -/
def lnSecond : Line → Bool
  | .ins x _ => x.pairSecond
  | _ => false

/-- The line is the first word of an `adrp` pair. -/
def lnFirst : Line → Bool
  | .ins (.adrpGot ..) _ | .ins (.adrp ..) _ => true
  | _ => false

/-- Every second word of `L` follows a first word (`b`: the line before `L` is a first word). -/
def pcOk : Bool → List Line → Bool
  | _, [] => true
  | b, ln :: L => (!lnSecond ln || b) && pcOk (lnFirst ln) L

theorem pcOk_mono : ∀ {L : List Line} (b : Bool), pcOk false L = true → pcOk b L = true
  | [], _, _ => rfl
  | ln :: L, b, h => by
    simp only [pcOk, Bool.or_false, Bool.and_eq_true, Bool.not_eq_true'] at h ⊢
    exact ⟨by simp [h.1], h.2⟩

theorem pcOk_append : ∀ {A B : List Line} {b : Bool},
    pcOk b A = true → pcOk false B = true → pcOk b (A ++ B) = true
  | [], _, b, _, hB => pcOk_mono b hB
  | ln :: A, B, b, hA, hB => by
    simp only [pcOk, List.cons_append, Bool.and_eq_true] at hA ⊢
    exact ⟨hA.1, pcOk_append hA.2 hB⟩

theorem pcOk_of_noSecond : ∀ {L : List Line} (b : Bool),
    (∀ ln ∈ L, lnSecond ln = false) → pcOk b L = true
  | [], _, _ => rfl
  | ln :: L, b, h => by
    simp only [pcOk, h ln (by simp), Bool.not_false, Bool.true_or, Bool.true_and]
    exact pcOk_of_noSecond _ (fun x hx => h x (by simp [hx]))

@[simp] theorem lnSecond_ins (x : Insn) (t : Option Clif.TrapCode) :
    lnSecond (.ins x t) = x.pairSecond := rfl
@[simp] theorem lnSecond_label (l : Lbl) : lnSecond (.label l) = false := rfl
@[simp] theorem lnSecond_word (x y : Lbl) : lnSecond (.word x y) = false := rfl

@[simp] theorem pcOk_label (b : Bool) (l : Lbl) (L : List Line) :
    pcOk b (.label l :: L) = pcOk false L := by
  rw [pcOk]; rfl

theorem lnFirst_eq {ln : Line} (h : lnFirst ln = true) :
    ∃ y t, ln = .ins y t ∧ ((∃ a b, y = .adrpGot a b) ∨ ∃ a b c, y = .adrp a b c) := by
  unfold lnFirst at h
  split at h
  · exact ⟨_, _, rfl, .inl ⟨_, _, rfl⟩⟩
  · exact ⟨_, _, rfl, .inr ⟨_, _, _, rfl⟩⟩
  · cases h

theorem pcOk_sound : ∀ {L : List Line} {b : Bool}, pcOk b L = true →
    ∀ k x t, L[k]? = some (.ins x t) → x.pairSecond = true →
      (k = 0 ∧ b = true) ∨ ∃ k' y t', k = k' + 1 ∧ L[k']? = some (.ins y t') ∧
        ((∃ a b, y = .adrpGot a b) ∨ ∃ a b c, y = .adrp a b c)
  | [], _, _, k, x, t, hk, _ => by simp at hk
  | ln :: L, b, h, 0, x, t, hk, hx => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk
    simp only [pcOk, lnSecond, hx, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
    exact .inl ⟨rfl, h.1⟩
  | ln :: L, b, h, k + 1, x, t, hk, hx => by
    simp only [pcOk, Bool.and_eq_true] at h
    simp only [List.getElem?_cons_succ] at hk
    refine .inr ?_
    rcases pcOk_sound h.2 k x t hk hx with ⟨rfl, hf⟩ | ⟨k', y, t', rfl, hk', hy⟩
    · obtain ⟨y, t', rfl, hy⟩ := lnFirst_eq hf
      exact ⟨0, y, t', rfl, rfl, hy⟩
    · exact ⟨k' + 1, y, t', rfl, by simpa using hk', hy⟩

theorem pairsClosed_of_pcOk {L : List Line} (h : pcOk false L = true) : PairsClosed L := by
  intro k x t hk hx
  rcases pcOk_sound h k x t hk hx with ⟨-, h0⟩ | h'
  · cases h0
  · exact h'

/-! ## Conditional branches are not pair words -/

theorem cond_noPair {c : Insn} {l : Lbl} (h : c.condTarget? = some l) (e : Lbl) (t : Option Clif.TrapCode) :
    lnSecond (.ins c t) = false ∧ lnFirst (.ins c t) = false ∧
      lnSecond (.ins (c.invertTo e) t) = false ∧ lnFirst (.ins (c.invertTo e) t) = false := by
  cases c <;> simp_all [Insn.condTarget?, Insn.invertTo, lnSecond, lnFirst, Insn.pairSecond]

/-! ## `fallthrough` -/

/-- The three outcomes of one `fallthrough` step. -/
theorem ftStep_cases (ln : Line) (n1 n2 : Option Line) :
    ftStep ln n1 n2 = ([ln], 1) ∨
      (∃ x l, ln = .ins (.b x) none ∧ n1 = some (.label l) ∧ ftStep ln n1 n2 = ([], 1)) ∨
      (∃ c e l, ln = .ins c none ∧ c.condTarget? = some l ∧ n1 = some (.ins (.b e) none) ∧
        n2 = some (.label l) ∧ ftStep ln n1 n2 = ([.ins (c.invertTo e) none], 2)) := by
  unfold ftStep
  repeat' split
  all_goals simp_all

theorem pcOk_ftList : ∀ (n : Nat) (L : List Line) (b : Bool), L.length ≤ n →
    pcOk b L = true → pcOk b (ftList L) = true
  | _, [], _, _, _ => by simp [ftList, pcOk]
  | n + 1, ln :: rest, b, hn, h => by
    rw [ftList_cons]
    rcases ftStep_cases ln rest[0]? rest[1]? with he | ⟨x, l, rfl, h1, he⟩ | ⟨c, e, l, rfl, hc, h1, h2, he⟩
    · rw [he]
      simp only [pcOk, Bool.and_eq_true] at h
      simp only [List.drop_one, List.tail_cons, List.singleton_append, pcOk, Bool.and_eq_true]
      exact ⟨h.1, pcOk_ftList n rest _ (by simp at hn; omega) h.2⟩
    · rw [he]
      cases rest with
      | nil => simp at h1
      | cons y rest' =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h1
        subst h1
        rw [pcOk, Bool.and_eq_true, pcOk_label] at h
        simp only [List.drop_one, List.tail_cons, List.nil_append]
        exact pcOk_ftList n _ b (by simp at hn ⊢; omega) h.2
    · rw [he]
      cases rest with
      | nil => simp at h1
      | cons y rest =>
      cases rest with
      | nil => simp at h2
      | cons z rest' =>
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h1 h2
        subst h1 h2
        obtain ⟨-, -, hs, hf⟩ := cond_noPair hc e none
        rw [pcOk, Bool.and_eq_true, pcOk, Bool.and_eq_true, pcOk_label] at h
        simp only [List.drop_succ_cons, List.drop_zero, List.singleton_append]
        rw [pcOk, hs, hf]
        simp only [Bool.not_false, Bool.true_or, Bool.true_and]
        exact pcOk_ftList n _ _ (by simp at hn ⊢; omega) h.2.2

/-! ## Branch relaxation -/

theorem pcOk_relaxLines (f : Lbl → Bool) : ∀ (L : List Line) (b : Bool),
    pcOk b L = true → pcOk b (relaxLines f L) = true
  | [], _, _ => rfl
  | ln :: L, b, h => by
    rw [relaxLines_cons]
    have keep : relaxLine f ln = [ln] → pcOk b (relaxLine f ln ++ relaxLines f L) = true := by
      intro hr
      rw [hr]
      simp only [pcOk, Bool.and_eq_true, List.singleton_append] at h ⊢
      exact ⟨h.1, pcOk_relaxLines f L _ h.2⟩
    match ln, h with
    | .ins c (some tc), h => exact keep rfl
    | .label l, h => exact keep rfl
    | .word x y, h => exact keep rfl
    | .ins c none, h =>
      rcases relaxLine_cases f c with hr | ⟨t, ht, hr⟩
      · exact keep hr
      · rw [hr]
        obtain ⟨-, hf, hs, hf'⟩ := cond_noPair (relaxTarget_condTarget ht) .skip none
        simp only [pcOk, hf, Bool.and_eq_true] at h
        simp only [List.cons_append, List.nil_append]
        rw [pcOk, pcOk, hs, hf']
        exact by simpa [lnSecond, lnFirst, Insn.pairSecond] using pcOk_relaxLines f L _ h.2

/-! ## The lines of one instruction -/

theorem loadConst64_noSecond (rd : Reg) (v : Nat) : ∀ ln ∈ loadConst64 rd v, lnSecond ln = false := by
  intro ln h
  simp only [loadConst64, List.mem_cons, List.mem_filterMap] at h
  rcases h with rfl | ⟨j, _, hj⟩
  · rfl
  · split at hj
    · simp only [Option.some.injEq] at hj; subst hj; rfl
    · cases hj

theorem memFinalize_noSecond {c : FnCtx} {mm : AMode} {b : Nat} {v : List Line × AMode}
    (hm : memFinalize c mm b = .ok v) : ∀ ln ∈ v.1, lnSecond ln = false := by
  obtain ⟨pre, am⟩ := v
  intro ln hln
  unfold memFinalize at hm
  have hfin : ∀ (base : Reg) (off : Int) pre am,
      (match simm9? off with
        | some s => (([] : List Line), AMode.unscaled base s)
        | none => match uimm12Scaled? off b with
          | some o => ([], .unsignedOffset base o)
          | none => (loadConst64 (.x 16) (u64 off), .regExtended base (.x 16) .sxtx)) = (pre, am) →
      ln ∈ pre → lnSecond ln = false := by
    intro base off pre am e hin
    split at e
    · cases e; simp at hin
    · split at e
      · cases e; simp at hin
      · cases e
        exact loadConst64_noSecond _ _ _ hin
  split at hm <;> simp only [pure, Except.pure, Except.ok.injEq] at hm <;>
    first | exact hfin _ _ _ _ hm hln | (cases hm; simp at hln) | cases hm

@[simp] theorem CondBrKind.insn_pairSecond (k : CondBrKind) (l : Lbl) : (k.insn l).pairSecond = false := by
  cases k <;> rfl

@[simp] theorem casLoopCmp_pairSecond (bits : Nat) : (casLoopCmp bits).pairSecond = false := by
  unfold casLoopCmp; split <;> rfl

@[simp] theorem rmwLoopCmp_pairSecond (op : AtomicRmwLoopOp) (bits : Nat) :
    (rmwLoopCmp op bits).pairSecond = false := by
  unfold rmwLoopCmp; split <;> rfl

@[simp] theorem rmwLoopSext_pairSecond (bits : Nat) : ∀ i ∈ rmwLoopSext bits, i.pairSecond = false := by
  unfold rmwLoopSext; split <;> simp <;> rfl

@[simp] theorem rmwLoopMid_pairSecond (op : AtomicRmwLoopOp) (bits : Nat) :
    ∀ i ∈ rmwLoopMid op bits, i.pairSecond = false := by
  cases op <;> simp [rmwLoopMid, or_imp, forall_and] <;> (repeat' constructor) <;>
    exact rmwLoopSext_pairSecond bits

theorem lines_pcOk {c : FnCtx} {m : MInst} {ps ps' : PState} {ls : List Line}
    (h : m.lines c ps = .ok (ls, ps')) : pcOk false ls = true := by
  unfold MInst.lines at h
  split at h <;> simp only [bind, Except.bind, pure, Except.pure] at h
  all_goals (repeat' (first | (split at h) | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h)))
  all_goals first | cases h | (simp [throw, throwThe, MonadExceptOf.throw] at h) | skip
  all_goals first | rfl | apply pcOk_of_noSecond
  all_goals simp [MInst.lines.addOff, rmwLoopLines, rmwLoopBody, casLoopLines, casLoopHead, or_imp,
    forall_and]
  all_goals (repeat' constructor)
  all_goals first
    | exact memFinalize_noSecond ‹_›
    | exact rmwLoopMid_pairSecond _ _
    | (simp [throw, throwThe, MonadExceptOf.throw] at *; done)
    | ((repeat' split) <;> simp <;> rfl)

/-! ## Prologue, epilogue, blocks, traps -/

theorem prologueLines_noSecond (size : Nat) : ∀ ln ∈ prologueLines size, lnSecond ln = false := by
  intro ln hln
  simp only [prologueLines, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hln
  rcases hln with (rfl | rfl) | hln
  · rfl
  · rfl
  · split at hln
    · simp at hln
    · split at hln
      · simp at hln; subst hln; rfl
      · rcases List.mem_append.1 hln with h1 | h1
        · exact loadConst64_noSecond _ _ _ h1
        · simp at h1; subst h1; rfl

theorem epilogueLines_noSecond (size : Nat) : ∀ ln ∈ epilogueLines size, lnSecond ln = false := by
  intro ln hln
  simp only [epilogueLines, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hln
  rcases hln with hln | (rfl | rfl)
  · split at hln
    · simp at hln
    · split at hln
      · simp at hln; subst hln; rfl
      · rcases List.mem_append.1 hln with h1 | h1
        · exact loadConst64_noSecond _ _ _ h1
        · simp at h1; subst h1; rfl
  · rfl
  · rfl

theorem ainstLines_pcOk {c : FnCtx} {af : AFunc} {a : AInst} {ps ps' : PState} {ls : List Line}
    (h : ainstLines c af a ps = .ok (ls, ps')) : pcOk false ls = true := by
  cases a with
  | inst m => exact lines_pcOk h
  | prologue =>
    simp only [ainstLines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    split
    · exact pcOk_of_noSecond _ (prologueLines_noSecond _)
    · rfl
  | epilogueRet =>
    simp only [ainstLines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    split
    · exact pcOk_of_noSecond _ (epilogueLines_noSecond _)
    · rfl

theorem codeLinesE_pcOk {c : FnCtx} {af : AFunc} :
    ∀ (code : List AInst) (ps ps' : PState) (ls : List Line),
      codeLinesE c af code ps = .ok (ls, ps') → pcOk false ls = true
  | [], ps, ps', ls, h => by
    simp only [codeLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h; rfl
  | a :: as, ps, ps', ls, h => by
    simp only [codeLinesE, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i r hr
      split at h
      · cases h
      · rename_i r2 hr2
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact pcOk_append (ainstLines_pcOk hr) (codeLinesE_pcOk as _ _ _ hr2)

theorem blocksLinesE_pcOk {c : FnCtx} {af : AFunc} :
    ∀ (bs : List (Label × Array AInst)) (ps ps' : PState) (ls : List Line),
      blocksLinesE c af bs ps = .ok (ls, ps') → pcOk false ls = true
  | [], ps, ps', ls, h => by
    simp only [blocksLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h; rfl
  | (l, code) :: bs, ps, ps', ls, h => by
    simp only [blocksLinesE, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i r hr
      split at h
      · cases h
      · rename_i r2 hr2
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        rw [List.cons_append, pcOk_label]
        exact pcOk_append (codeLinesE_pcOk _ _ _ _ hr) (blocksLinesE_pcOk bs _ _ _ hr2)

theorem trapLines_noSecond (ts : List (Lbl × Clif.TrapCode)) : ∀ ln ∈ trapLines ts, lnSecond ln = false := by
  intro ln hln
  simp only [trapLines, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hln
  obtain ⟨p, -, rfl | rfl⟩ := hln <;> rfl

/-! ## `emitFunc` -/

/-- **`adrp` pairs in `emitFunc`'s lines**: every second word (`ldr …, :got_lo12:` /
`add …, :lo12:`) immediately follows a first word (`adrp …, :got:` / `adrp`). -/
theorem emitFunc_pairsClosed {k : Nat} {af : AFunc} {fa : FnAsm} (h : emitFunc k af = .ok fa) :
    PairsClosed fa.lines.toList := by
  obtain ⟨body, ps, hb, hl, -⟩ := emitFunc_ok h
  rw [hl]
  refine pairsClosed_of_pcOk (pcOk_relaxLines _ _ _ (pcOk_append ?_ ?_))
  · exact pcOk_ftList _ _ _ (Nat.le_refl _) (blocksLinesE_pcOk _ _ _ _ hb)
  · exact pcOk_of_noSecond _ (trapLines_noSecond _)

end Backend.Proof
