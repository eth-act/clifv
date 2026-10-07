import FV.Link.RelocShape
import FV.E2E.PairLines
import FV.E2E.ExecWords
import FV.Backend.Proof.EncodeLayout
import FV.E2E.LinkCheck

/-! # The compiler's relocations have the linker's shapes (L1)

`relocShapes_of_pipeT`: the relocations of every function the pipeline compiles pass the
code-only half of the linker's check, `relocShapesB` (`FV/Link/RelocShape.lean`).

* **Emission.** The relocated instructions come in fixed sequences: `adrp …, :got:` then
  `ldr …, :got_lo12:` (same register and symbol), `adrp` then `add …, :lo12:` (same register,
  symbol and addend), and the four-instruction TLS descriptor sequence. `SeqOk L` says `L`
  is a concatenation of such sequences and of other lines (a small automaton, `seqStep`);
  `MInst.lines` emits whole sequences, and neither `fallthrough` nor branch relaxation (which
  only drop or rewrite branches, outside any sequence) nor removing labels breaks them
  (`emitFunc_seqOk`, `seqOk_codeLines`).
* **Layout.** Code word `k` is code line `k`, relocations are at `4 * k` of their instruction
  (`FnAsm.layout_unfold`, `mem_codeRelocs`), hence at distinct offsets; the relocated
  instructions encode with zero immediates (`blW 0`, `adrpW rd 0`, `ldrW rd rd 0`,
  `addW rd rd 0`, with `rd < 31` since the pair's two encodings reject both `sp` and `xzr`).
-/

namespace Backend.Proof

open Backend

/-! ## The sequence automaton -/

/-- The instructions of a relocated sequence. -/
def _root_.Backend.Insn.seq : Insn → Bool
  | .adrpGot .. | .ldrGotLo12 .. | .adrp .. | .addLo12 .. | .adrpTlsDesc .. | .ldrTlsDescLo12 ..
  | .addTlsDescLo12 .. | .blrTlsDesc .. => true
  | _ => false

/-- A line outside every relocated sequence. -/
def lnFree : Line → Bool
  | .ins i _ => !i.seq
  | _ => true

/-- What the next line must be: nothing in particular, or the next word of a sequence. -/
inductive SeqSt where
  | free
  | got (rd : Reg) (s : String)
  | near (rd : Reg) (s : String) (a : Int)
  | tls1 (s : String)
  | tls2 (s : String)
  | tls3 (s : String)

/-- One line of the automaton. -/
def seqStep (st : SeqSt) (ln : Line) : Option SeqSt :=
  match st with
  | .free =>
    match ln with
    | .ins (.adrpGot rd s) _ => some (.got rd s)
    | .ins (.adrp rd s a) _ => some (.near rd s a)
    | .ins (.adrpTlsDesc _ s) _ => some (.tls1 s)
    | ln => if lnFree ln then some .free else none
  | .got rd s =>
    match ln with
    | .ins (.ldrGotLo12 rd' rn s') _ => if rd' = rd ∧ rn = rd ∧ s' = s then some .free else none
    | _ => none
  | .near rd s a =>
    match ln with
    | .ins (.addLo12 rd' rn s' a') _ =>
      if rd' = rd ∧ rn = rd ∧ s' = s ∧ a' = a then some .free else none
    | _ => none
  | .tls1 s =>
    match ln with
    | .ins (.ldrTlsDescLo12 _ _ s') _ => if s' = s then some (.tls2 s) else none
    | _ => none
  | .tls2 s =>
    match ln with
    | .ins (.addTlsDescLo12 _ _ s') _ => if s' = s then some (.tls3 s) else none
    | _ => none
  | .tls3 s =>
    match ln with
    | .ins (.blrTlsDesc _ s') _ => if s' = s then some .free else none
    | _ => none

/-- The automaton on a line list. -/
def seqGo : SeqSt → List Line → Option SeqSt
  | s, [] => some s
  | s, ln :: L => (seqStep s ln).bind (seqGo · L)

/-- `L` is made of whole relocated sequences and free lines. -/
def SeqOk (L : List Line) : Prop := seqGo .free L = some .free

theorem seqGo_append : ∀ (s : SeqSt) (A B : List Line),
    seqGo s (A ++ B) = (seqGo s A).bind (seqGo · B)
  | s, [], B => rfl
  | s, ln :: A, B => by
    simp only [List.cons_append, seqGo]
    cases seqStep s ln with
    | none => rfl
    | some s' => simp only [Option.bind_some]; exact seqGo_append s' A B

theorem seqOk_append {A B : List Line} (hA : SeqOk A) (hB : SeqOk B) : SeqOk (A ++ B) := by
  unfold SeqOk at *
  rw [seqGo_append, hA]
  exact hB

theorem seqStep_of_free {ln : Line} (h : lnFree ln = true) {s s' : SeqSt}
    (hs : seqStep s ln = some s') : s = .free ∧ s' = .free := by
  cases s <;> simp only [seqStep] at hs <;> split at hs <;> simp_all [lnFree, Insn.seq]

theorem seqStep_free {ln : Line} (h : lnFree ln = true) : seqStep .free ln = some .free := by
  simp only [seqStep]
  split <;> simp_all [lnFree, Insn.seq]

theorem seqGo_free_cons {ln : Line} (h : lnFree ln = true) (L : List Line) :
    seqGo .free (ln :: L) = seqGo .free L := by
  simp [seqGo, seqStep_free h]

theorem seqGo_free_inv {ln : Line} (h : lnFree ln = true) {L : List Line} {s s' : SeqSt}
    (hs : seqGo s (ln :: L) = some s') : s = .free ∧ seqGo .free L = some s' := by
  simp only [seqGo] at hs
  cases e : seqStep s ln with
  | none => simp [e] at hs
  | some s1 =>
    obtain ⟨rfl, rfl⟩ := seqStep_of_free h e
    simp only [e, Option.bind_some] at hs
    exact ⟨rfl, hs⟩

theorem seqOk_of_free : ∀ {L : List Line}, (∀ ln ∈ L, lnFree ln = true) → SeqOk L
  | [], _ => rfl
  | ln :: L, h => by
    unfold SeqOk
    rw [seqGo_free_cons (h ln (by simp))]
    exact seqOk_of_free (fun x hx => h x (by simp [hx]))

/-! ## Removing labels -/

theorem codeLines_cons_label (l : Lbl) (L : List Line) :
    codeLines (.label l :: L) = codeLines L := by
  simp [codeLines, Line.isLabel]

theorem codeLines_cons_code {ln : Line} (h : ln.isLabel = false) (L : List Line) :
    codeLines (ln :: L) = ln :: codeLines L := by
  simp [codeLines, h]

theorem seqGo_codeLines : ∀ {L : List Line} {s s' : SeqSt}, seqGo s L = some s' →
    seqGo s (codeLines L) = some s'
  | [], _, _, h => h
  | ln :: L, s, s', h => by
    cases hl : ln.isLabel with
    | true =>
      cases ln with
      | label l =>
        obtain ⟨rfl, h'⟩ := seqGo_free_inv rfl h
        rw [codeLines_cons_label, seqGo_codeLines h']
      | ins => simp [Line.isLabel] at hl
      | word => simp [Line.isLabel] at hl
    | false =>
      rw [codeLines_cons_code hl]
      simp only [seqGo] at h ⊢
      cases e : seqStep s ln with
      | none => simp [e] at h
      | some s1 =>
        simp only [e, Option.bind_some] at h ⊢
        exact seqGo_codeLines h

theorem seqOk_codeLines {L : List Line} (h : SeqOk L) : SeqOk (codeLines L) :=
  seqGo_codeLines h

/-! ## `fallthrough` and branch relaxation -/

theorem cond_free {c : Insn} {l : Lbl} (h : c.condTarget? = some l) (e : Lbl)
    (t : Option Clif.TrapCode) :
    lnFree (.ins c t) = true ∧ lnFree (.ins (c.invertTo e) t) = true := by
  cases c <;> simp_all [Insn.condTarget?, Insn.invertTo, lnFree, Insn.seq]

theorem seqGo_ftList : ∀ (n : Nat) (L : List Line) (s : SeqSt), L.length ≤ n →
    seqGo s L = some .free → seqGo s (ftList L) = some .free
  | _, [], _, _, h => by simpa [ftList] using h
  | n + 1, ln :: rest, s, hn, h => by
    rw [ftList_cons]
    rcases ftStep_cases ln rest[0]? rest[1]? with he | ⟨x, l, rfl, h1, he⟩ | ⟨c, e, l, rfl, hc, h1, h2, he⟩
    · rw [he]
      simp only [List.drop_one, List.tail_cons, List.singleton_append, seqGo] at h ⊢
      cases e : seqStep s ln with
      | none => simp [e] at h
      | some s1 =>
        simp only [e, Option.bind_some] at h ⊢
        exact seqGo_ftList n rest _ (by simp at hn; omega) h
    · rw [he]
      cases rest with
      | nil => simp at h1
      | cons y rest' =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h1
        subst h1
        obtain ⟨rfl, h'⟩ := seqGo_free_inv rfl h
        simp only [List.drop_one, List.tail_cons, List.nil_append]
        exact seqGo_ftList n _ _ (by simp at hn ⊢; omega) h'
    · rw [he]
      cases rest with
      | nil => simp at h1
      | cons y rest =>
      cases rest with
      | nil => simp at h2
      | cons z rest' =>
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h1 h2
        subst h1 h2
        obtain ⟨hc1, hc2⟩ := cond_free hc e none
        obtain ⟨rfl, h'⟩ := seqGo_free_inv hc1 h
        obtain ⟨-, h''⟩ := seqGo_free_inv rfl h'
        simp only [List.drop_succ_cons, List.drop_zero, List.singleton_append]
        rw [seqGo_free_cons hc2]
        exact seqGo_ftList n _ _ (by simp at hn ⊢; omega) h''

theorem seqGo_relaxLines (f : Lbl → Bool) : ∀ (L : List Line) (s : SeqSt),
    seqGo s L = some .free → seqGo s (relaxLines f L) = some .free
  | [], _, h => h
  | ln :: L, s, h => by
    rw [relaxLines_cons]
    have keep : relaxLine f ln = [ln] → seqGo s (relaxLine f ln ++ relaxLines f L) = some .free := by
      intro hr
      rw [hr]
      simp only [List.singleton_append, seqGo] at h ⊢
      cases e : seqStep s ln with
      | none => simp [e] at h
      | some s1 =>
        simp only [e, Option.bind_some] at h ⊢
        exact seqGo_relaxLines f L _ h
    match ln, h with
    | .ins c (some tc), h => exact keep rfl
    | .label l, h => exact keep rfl
    | .word x y, h => exact keep rfl
    | .ins c none, h =>
      rcases relaxLine_cases f c with hr | ⟨t, ht, hr⟩
      · exact keep hr
      · rw [hr]
        obtain ⟨hc1, hc2⟩ := cond_free (relaxTarget_condTarget ht) .skip none
        obtain ⟨rfl, h'⟩ := seqGo_free_inv hc1 h
        simp only [List.cons_append, List.nil_append]
        rw [seqGo_free_cons hc2, seqGo_free_cons rfl]
        exact seqGo_relaxLines f L _ h'

/-! ## The lines of one instruction -/

theorem loadConst64_free (rd : Reg) (v : Nat) : ∀ ln ∈ loadConst64 rd v, lnFree ln = true := by
  intro ln h
  simp only [loadConst64, List.mem_cons, List.mem_filterMap] at h
  rcases h with rfl | ⟨j, _, hj⟩
  · rfl
  · split at hj
    · simp only [Option.some.injEq] at hj; subst hj; rfl
    · cases hj

theorem memFinalize_free {c : FnCtx} {mm : AMode} {b : Nat} {v : List Line × AMode}
    (hm : memFinalize c mm b = .ok v) : ∀ ln ∈ v.1, lnFree ln = true := by
  obtain ⟨pre, am⟩ := v
  intro ln hln
  unfold memFinalize at hm
  have hfin : ∀ (base : Reg) (off : Int) pre am,
      (match simm9? off with
        | some s => (([] : List Line), AMode.unscaled base s)
        | none => match uimm12Scaled? off b with
          | some o => ([], .unsignedOffset base o)
          | none => (loadConst64 (.x 16) (u64 off), .regExtended base (.x 16) .sxtx)) = (pre, am) →
      ln ∈ pre → lnFree ln = true := by
    intro base off pre am e hin
    split at e
    · cases e; simp at hin
    · split at e
      · cases e; simp at hin
      · cases e
        exact loadConst64_free _ _ _ hin
  split at hm <;> simp only [pure, Except.pure, Except.ok.injEq] at hm <;>
    first | exact hfin _ _ _ _ hm hln | (cases hm; simp at hln) | cases hm

@[simp] theorem CondBrKind.insn_seq (k : CondBrKind) (l : Lbl) : (k.insn l).seq = false := by
  cases k <;> rfl

@[simp] theorem casLoopCmp_seq (bits : Nat) : (casLoopCmp bits).seq = false := by
  unfold casLoopCmp; split <;> rfl

@[simp] theorem rmwLoopCmp_seq (op : AtomicRmwLoopOp) (bits : Nat) :
    (rmwLoopCmp op bits).seq = false := by
  unfold rmwLoopCmp; split <;> rfl

@[simp] theorem rmwLoopSext_seq (bits : Nat) : ∀ i ∈ rmwLoopSext bits, i.seq = false := by
  unfold rmwLoopSext; split <;> simp <;> rfl

@[simp] theorem rmwLoopMid_seq (op : AtomicRmwLoopOp) (bits : Nat) :
    ∀ i ∈ rmwLoopMid op bits, i.seq = false := by
  cases op <;> simp [rmwLoopMid, or_imp, forall_and] <;> (repeat' constructor) <;>
    exact rmwLoopSext_seq bits

theorem lines_seqOk {c : FnCtx} {m : MInst} {ps ps' : PState} {ls : List Line}
    (h : m.lines c ps = .ok (ls, ps')) : SeqOk ls := by
  unfold MInst.lines at h
  split at h <;> simp only [bind, Except.bind, pure, Except.pure] at h
  all_goals (repeat' (first | (split at h) | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h)))
  all_goals first | cases h | (simp [throw, throwThe, MonadExceptOf.throw] at h) | skip
  all_goals first | (simp [SeqOk, seqGo, seqStep, lnFree, Insn.seq]; done) | apply seqOk_of_free
  all_goals simp [lnFree, Insn.seq, MInst.lines.addOff, rmwLoopLines, rmwLoopBody, casLoopLines,
    casLoopHead, or_imp, forall_and]
  all_goals (repeat' constructor)
  all_goals first
    | exact memFinalize_free ‹_›
    | exact rmwLoopMid_seq _ _
    | (simp [throw, throwThe, MonadExceptOf.throw] at *; done)
    | ((repeat' split) <;> first
        | (simp <;> rfl)
        | (rename_i heq; have h' := congrArg Insn.seq heq
           simp only [CondBrKind.insn_seq, casLoopCmp_seq] at h'; simp [Insn.seq] at h'))

/-! ## Prologue, epilogue, blocks, traps -/

theorem prologueLines_free (size : Nat) : ∀ ln ∈ prologueLines size, lnFree ln = true := by
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
        · exact loadConst64_free _ _ _ h1
        · simp at h1; subst h1; rfl

theorem epilogueLines_free (size : Nat) : ∀ ln ∈ epilogueLines size, lnFree ln = true := by
  intro ln hln
  simp only [epilogueLines, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hln
  rcases hln with hln | (rfl | rfl)
  · split at hln
    · simp at hln
    · split at hln
      · simp at hln; subst hln; rfl
      · rcases List.mem_append.1 hln with h1 | h1
        · exact loadConst64_free _ _ _ h1
        · simp at h1; subst h1; rfl
  · rfl
  · rfl

theorem ainstLines_seqOk {c : FnCtx} {af : AFunc} {a : AInst} {ps ps' : PState} {ls : List Line}
    (h : ainstLines c af a ps = .ok (ls, ps')) : SeqOk ls := by
  cases a with
  | inst m => exact lines_seqOk h
  | prologue =>
    simp only [ainstLines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    split
    · exact seqOk_of_free (prologueLines_free _)
    · rfl
  | epilogueRet =>
    simp only [ainstLines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    split
    · exact seqOk_of_free (epilogueLines_free _)
    · rfl

theorem codeLinesE_seqOk {c : FnCtx} {af : AFunc} :
    ∀ (code : List AInst) (ps ps' : PState) (ls : List Line),
      codeLinesE c af code ps = .ok (ls, ps') → SeqOk ls
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
        exact seqOk_append (ainstLines_seqOk hr) (codeLinesE_seqOk as _ _ _ hr2)

theorem blocksLinesE_seqOk {c : FnCtx} {af : AFunc} :
    ∀ (bs : List (Label × Array AInst)) (ps ps' : PState) (ls : List Line),
      blocksLinesE c af bs ps = .ok (ls, ps') → SeqOk ls
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
        unfold SeqOk
        rw [List.cons_append, seqGo_free_cons rfl]
        exact seqOk_append (codeLinesE_seqOk _ _ _ _ hr) (blocksLinesE_seqOk bs _ _ _ hr2)

theorem trapLines_free (ts : List (Lbl × Clif.TrapCode)) : ∀ ln ∈ trapLines ts, lnFree ln = true := by
  intro ln hln
  simp only [trapLines, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hln
  obtain ⟨p, -, rfl | rfl⟩ := hln <;> rfl

/-- **`emitFunc`'s lines are whole relocated sequences and free lines.** -/
theorem emitFunc_seqOk {k : Nat} {af : AFunc} {fa : FnAsm} (h : emitFunc k af = .ok fa) :
    SeqOk fa.lines.toList := by
  obtain ⟨body, ps, hb, hl, -⟩ := emitFunc_ok h
  rw [hl]
  refine seqGo_relaxLines _ _ _ (seqOk_append ?_ ?_)
  · exact seqGo_ftList _ _ _ (Nat.le_refl _) (blocksLinesE_seqOk _ _ _ _ hb)
  · exact seqOk_of_free (trapLines_free _)

end Backend.Proof

namespace Backend.Proof

open Backend

/-! ## The automaton's runs and steps -/

/-- A run of the automaton: the state before each line. -/
theorem seqGo_states : ∀ {L : List Line} {s s' : SeqSt}, seqGo s L = some s' →
    ∃ σ : Nat → SeqSt, σ 0 = s ∧ σ L.length = s' ∧
      ∀ k ln, L[k]? = some ln → seqStep (σ k) ln = some (σ (k + 1))
  | [], s, s', h => ⟨fun _ => s, rfl, by simpa [seqGo] using h, fun k ln hk => by simp at hk⟩
  | ln :: L, s, s', h => by
    simp only [seqGo] at h
    cases e : seqStep s ln with
    | none => simp [e] at h
    | some s1 =>
      simp only [e, Option.bind_some] at h
      obtain ⟨σ, h0, hl, hs⟩ := seqGo_states h
      refine ⟨fun k => match k with | 0 => s | k + 1 => σ k, rfl, by simpa using hl, ?_⟩
      intro k ln' hk
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        simp [e, h0]
      | succ k =>
        simp only [List.getElem?_cons_succ] at hk
        exact hs k ln' hk

theorem seqStep_into_got {st : SeqSt} {ln : Line} {rd : Reg} {s : String}
    (h : seqStep st ln = some (.got rd s)) : ∃ t, ln = .ins (.adrpGot rd s) t := by
  cases st <;> simp only [seqStep] at h <;> (repeat' split at h) <;> simp_all

theorem seqStep_into_near {st : SeqSt} {ln : Line} {rd : Reg} {s : String} {a : Int}
    (h : seqStep st ln = some (.near rd s a)) : ∃ t, ln = .ins (.adrp rd s a) t := by
  cases st <;> simp only [seqStep] at h <;> (repeat' split at h) <;> simp_all

theorem seqStep_into_tls1 {st : SeqSt} {ln : Line} {s : String}
    (h : seqStep st ln = some (.tls1 s)) : ∃ r t, ln = .ins (.adrpTlsDesc r s) t := by
  cases st <;> simp only [seqStep] at h <;> (repeat' split at h) <;> simp_all

theorem seqStep_into_tls2 {st : SeqSt} {ln : Line} {s : String}
    (h : seqStep st ln = some (.tls2 s)) :
    st = .tls1 s ∧ ∃ r1 r2 t, ln = .ins (.ldrTlsDescLo12 r1 r2 s) t := by
  cases st <;> simp only [seqStep] at h <;> (repeat' split at h) <;> simp_all

theorem seqStep_into_tls3 {st : SeqSt} {ln : Line} {s : String}
    (h : seqStep st ln = some (.tls3 s)) :
    st = .tls2 s ∧ ∃ r1 r2 t, ln = .ins (.addTlsDescLo12 r1 r2 s) t := by
  cases st <;> simp only [seqStep] at h <;> (repeat' split at h) <;> simp_all

theorem seqStep_from_got {ln : Line} {rd : Reg} {s : String} {st' : SeqSt}
    (h : seqStep (.got rd s) ln = some st') :
    st' = .free ∧ ∃ t, ln = .ins (.ldrGotLo12 rd rd s) t := by
  simp only [seqStep] at h; (repeat' split at h) <;> simp_all

theorem seqStep_from_near {ln : Line} {rd : Reg} {s : String} {a : Int} {st' : SeqSt}
    (h : seqStep (.near rd s a) ln = some st') :
    st' = .free ∧ ∃ t, ln = .ins (.addLo12 rd rd s a) t := by
  simp only [seqStep] at h; (repeat' split at h) <;> simp_all

theorem seqStep_from_tls1 {ln : Line} {s : String} {st' : SeqSt}
    (h : seqStep (.tls1 s) ln = some st') :
    st' = .tls2 s ∧ ∃ r1 r2 t, ln = .ins (.ldrTlsDescLo12 r1 r2 s) t := by
  simp only [seqStep] at h; (repeat' split at h) <;> simp_all

theorem seqStep_from_tls2 {ln : Line} {s : String} {st' : SeqSt}
    (h : seqStep (.tls2 s) ln = some st') :
    st' = .tls3 s ∧ ∃ r1 r2 t, ln = .ins (.addTlsDescLo12 r1 r2 s) t := by
  simp only [seqStep] at h; (repeat' split at h) <;> simp_all

theorem seqStep_from_tls3 {ln : Line} {s : String} {st' : SeqSt}
    (h : seqStep (.tls3 s) ln = some st') :
    st' = .free ∧ ∃ r t, ln = .ins (.blrTlsDesc r s) t := by
  simp only [seqStep] at h; (repeat' split at h) <;> simp_all

theorem seqStep_at_adrpGot {st st' : SeqSt} {rd : Reg} {s : String} {t : Option Clif.TrapCode}
    (h : seqStep st (.ins (.adrpGot rd s) t) = some st') : st' = .got rd s := by
  cases st <;> simp_all [seqStep]

theorem seqStep_at_adrp {st st' : SeqSt} {rd : Reg} {s : String} {a : Int}
    {t : Option Clif.TrapCode}
    (h : seqStep st (.ins (.adrp rd s a) t) = some st') : st' = .near rd s a := by
  cases st <;> simp_all [seqStep]

theorem seqStep_at_adrpTls {st st' : SeqSt} {rd : Reg} {s : String} {t : Option Clif.TrapCode}
    (h : seqStep st (.ins (.adrpTlsDesc rd s) t) = some st') : st' = .tls1 s := by
  cases st <;> simp_all [seqStep]

theorem seqStep_at_ldrGot {st st' : SeqSt} {rd rn : Reg} {s : String} {t : Option Clif.TrapCode}
    (h : seqStep st (.ins (.ldrGotLo12 rd rn s) t) = some st') : ∃ r, st = .got r s := by
  cases st <;> simp_all [seqStep, lnFree, Insn.seq]

theorem seqStep_at_addLo {st st' : SeqSt} {rd rn : Reg} {s : String} {a : Int}
    {t : Option Clif.TrapCode}
    (h : seqStep st (.ins (.addLo12 rd rn s a) t) = some st') : ∃ r, st = .near r s a := by
  cases st <;> simp_all [seqStep, lnFree, Insn.seq]

theorem seqStep_at_ldrTls {st st' : SeqSt} {rd rn : Reg} {s : String} {t : Option Clif.TrapCode}
    (h : seqStep st (.ins (.ldrTlsDescLo12 rd rn s) t) = some st') : st = .tls1 s := by
  cases st <;> simp_all [seqStep, lnFree, Insn.seq]

theorem seqStep_at_addTls {st st' : SeqSt} {rd rn : Reg} {s : String} {t : Option Clif.TrapCode}
    (h : seqStep st (.ins (.addTlsDescLo12 rd rn s) t) = some st') : st = .tls2 s := by
  cases st <;> simp_all [seqStep, lnFree, Insn.seq]

theorem seqStep_at_blrTls {st st' : SeqSt} {rn : Reg} {s : String} {t : Option Clif.TrapCode}
    (h : seqStep st (.ins (.blrTlsDesc rn s) t) = some st') : st = .tls3 s := by
  cases st <;> simp_all [seqStep, lnFree, Insn.seq]

end Backend.Proof

namespace Link

open E2E E2E.LinkCheck E2E.BinCheck Backend Backend.Proof

/-! ## Encodings with zero immediates -/

theorem rd5_adrpW {n : Nat} (h : n < 31) : rd5 (adrpW n 0) = n := by
  simp [rd5, adrpW, adrLike, imm21]
  omega

theorem encode_bl {env : Env} {s : String} {w : BitVec 32}
    (h : (Insn.bl s).encode env = .ok w) : w = blW 0 := by
  obtain ⟨a, ha, rfl⟩ := Insn.encode_eq_ok.1 h
  simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm] at ha
  subst ha
  decide

theorem encode_got {env env' : Env} {rd : Reg} {s : String} {w0 w1 : BitVec 32}
    (h0 : (Insn.adrpGot rd s).encode env = .ok w0)
    (h1 : (Insn.ldrGotLo12 rd rd s).encode env' = .ok w1) :
    ∃ n, n < 31 ∧ w0 = adrpW n 0 ∧ w1 = ldrW n n 0 := by
  obtain ⟨a0, ha0, rfl⟩ := Insn.encode_eq_ok.1 h0
  obtain ⟨a1, ha1, rfl⟩ := Insn.encode_eq_ok.1 h1
  cases rd with
  | x n =>
    by_cases hn : n ≤ 30
    · simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, Reg.encZR, Reg.encSP, hn] at ha0 ha1
      subst ha0 ha1
      refine ⟨n, by omega, ?_, ?_⟩
      · rw [ExecWords.adrpW_bits (by omega)]; rfl
      · rw [ExecWords.ldrW_bits (by omega) (by omega) (by decide)]; rfl
    · simp [Insn.toArmInst, Insn.armFields, Reg.encZR, hn] at ha0
  | _ => simp [Insn.toArmInst, Insn.armFields, Reg.encZR, Reg.encSP] at ha0 ha1

theorem encode_near {env env' : Env} {rd : Reg} {s : String} {ad : Int} {w0 w1 : BitVec 32}
    (h0 : (Insn.adrp rd s ad).encode env = .ok w0)
    (h1 : (Insn.addLo12 rd rd s ad).encode env' = .ok w1) :
    ∃ n, n < 31 ∧ w0 = adrpW n 0 ∧ w1 = addW n n 0 := by
  obtain ⟨a0, ha0, rfl⟩ := Insn.encode_eq_ok.1 h0
  obtain ⟨a1, ha1, rfl⟩ := Insn.encode_eq_ok.1 h1
  cases rd with
  | x n =>
    by_cases hn : n ≤ 30
    · simp [Insn.toArmInst, Insn.armFields, Arm.ArmInst.norm, Reg.encZR, Reg.encSP, hn] at ha0 ha1
      subst ha0 ha1
      refine ⟨n, by omega, ?_, ?_⟩
      · rw [ExecWords.adrpW_bits (by omega)]; rfl
      · rw [ExecWords.addW_bits (by omega) (by omega) (by decide)]; rfl
    · simp [Insn.toArmInst, Insn.armFields, Reg.encZR, hn] at ha0
  | _ => simp [Insn.toArmInst, Insn.armFields, Reg.encZR, Reg.encSP] at ha0 ha1

/-! ## Relocation offsets -/

theorem filterMap_zipIdx_offsets {α : Type} (F : α × Nat → Option Reloc)
    (hF : ∀ x k r, F (x, k) = some r → r.offset = 4 * k) :
    ∀ (L : List α) (n : Nat), (((L.zipIdx n).filterMap F).map (·.offset)).Pairwise (· < ·) ∧
      ∀ r ∈ (L.zipIdx n).filterMap F, 4 * n ≤ r.offset
  | [], n => by simp
  | x :: L, n => by
    obtain ⟨ih1, ih2⟩ := filterMap_zipIdx_offsets F hF L (n + 1)
    simp only [List.zipIdx_cons, List.filterMap_cons]
    cases e : F (x, n) with
    | none => exact ⟨ih1, fun r hr => by have := ih2 r hr; omega⟩
    | some r0 =>
      have h0 := hF x n r0 e
      simp only [List.map_cons, List.pairwise_cons, List.mem_map, List.mem_cons]
      refine ⟨⟨?_, ih1⟩, ?_⟩
      · rintro o ⟨r, hr, rfl⟩
        have := ih2 r hr; omega
      · rintro r (rfl | hr)
        · omega
        · have := ih2 r hr; omega

/-- The relocations of code lines are at distinct offsets. -/
theorem codeRelocs_nodup (code : List Line) : ((codeRelocs code).map (·.offset)).Nodup := by
  unfold codeRelocs
  refine ((filterMap_zipIdx_offsets _ ?_ code 0).1).imp Nat.ne_of_lt
  intro x k r h
  cases x with
  | ins i t =>
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h
    rfl
  | word => simp at h
  | label => simp at h

/-! ## The shapes -/

/-- **Relocation shapes of a laid-out function** whose code lines are whole relocated sequences
and free lines. -/
theorem relocShapesB_of_seqOk {fa : FnAsm} {a : Art} (hl : fa.layout = .ok a.fb)
    (hs : SeqOk (codeLines fa.lines.toList)) : relocShapesB a = true := by
  obtain ⟨m, ctx, -, hw, -, hr, -⟩ := FnAsm.layout_unfold hl
  generalize codeLines fa.lines.toList = code at hw hr hs
  obtain ⟨hsz, -, hwd⟩ := encodeCode_spec hw
  simp only [List.size_toArray, List.length_nil, Nat.zero_add] at hsz hwd
  have hword : ∀ k i t, code[k]? = some (.ins i t) →
      ∃ env w, i.encode env = .ok w ∧ wordOf a k = w := by
    intro k i t hk
    obtain ⟨w, h1, h2⟩ := hwd k _ hk
    exact ⟨_, w, h1, by simp [wordOf, h2]⟩
  have hrel : ∀ k i t ty s ad, code[k]? = some (.ins i t) → i.reloc? = some (ty, s, ad) →
      (⟨4 * k, ty, s, ad⟩ : Reloc) ∈ a.fb.relocs := by
    intro k i t ty s ad hk hi
    rw [hr]
    exact mem_codeRelocs.2 ⟨k, i, t, hk, hi, rfl⟩
  have hhas : ∀ k i t ty s ad, code[k]? = some (.ins i t) → i.reloc? = some (ty, s, ad) →
      hasAt a (4 * k) ty = true := by
    intro k i t ty s ad hk hi
    exact List.any_eq_true.2 ⟨_, hrel k i t ty s ad hk hi, by simp⟩
  obtain ⟨σ, h0, hend, hstep⟩ := seqGo_states hs
  have hlt : ∀ {k ln}, code[k]? = some ln → k < code.length :=
    fun hk => (List.getElem?_eq_some_iff.1 hk).1
  have hnext : ∀ k, k < code.length → σ (k + 1) ≠ .free →
      ∃ ln, code[k + 1]? = some ln ∧ seqStep (σ (k + 1)) ln = some (σ (k + 1 + 1)) := by
    intro k hk hne
    have : k + 1 < code.length := by
      rcases Nat.lt_or_ge (k + 1) code.length with h | h
      · exact h
      · exact absurd (by rw [show k + 1 = code.length by omega]; exact hend) hne
    exact ⟨_, List.getElem?_eq_getElem this, hstep _ _ (List.getElem?_eq_getElem this)⟩
  have hprev : ∀ k, k < code.length → σ k ≠ .free →
      ∃ k' ln, k = k' + 1 ∧ code[k']? = some ln ∧ seqStep (σ k') ln = some (σ k) := by
    intro k hk hne
    cases k with
    | zero => exact absurd h0 hne
    | succ k' =>
      exact ⟨k', _, rfl, List.getElem?_eq_getElem (by omega),
        hstep _ _ (List.getElem?_eq_getElem (by omega))⟩
  simp only [relocShapesB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨by rw [hr]; exact codeRelocs_nodup code, ?_⟩
  intro r hrm
  rw [hr] at hrm
  obtain ⟨k, i, t, hk, hi, ho⟩ := mem_codeRelocs.1 hrm
  have hkl := hlt hk
  have hσ := hstep k _ hk
  obtain ⟨o, ty, sym, add⟩ := r
  simp only at hi ho
  subst ho
  have hd : 4 * k / 4 = k := by omega
  cases i <;> simp [Insn.reloc?] at hi
  case bl s =>
    obtain ⟨rfl, rfl, rfl⟩ := hi
    obtain ⟨env, w, hw, hwo⟩ := hword k _ t hk
    simp [relocShapeB, hd, hsz, hkl, hwo, encode_bl hw]
  case adrpGot rd s =>
    obtain ⟨rfl, rfl, rfl⟩ := hi
    have e1 := seqStep_at_adrpGot hσ
    obtain ⟨ln1, hk1, hσ1⟩ := hnext k hkl (by rw [e1]; nofun)
    rw [e1] at hσ1
    obtain ⟨-, t1, rfl⟩ := seqStep_from_got hσ1
    obtain ⟨_, w0, hw0, hwo0⟩ := hword k _ t hk
    obtain ⟨_, w1, hw1, hwo1⟩ := hword (k + 1) _ t1 hk1
    obtain ⟨n, hn31, rfl, rfl⟩ := encode_got hw0 hw1
    have hm1 := hrel (k + 1) _ t1 .ld64GotLo12Nc s 0 hk1 rfl
    have hk1l := hlt hk1
    simp [relocShapeB, hd, hsz, hkl, hk1l, hwo0, hwo1, rd5_adrpW hn31, hn31, loOf]
    exact ⟨_, hm1, by simp; omega⟩
  case adrp rd s ad =>
    obtain ⟨rfl, rfl, rfl⟩ := hi
    have e1 := seqStep_at_adrp hσ
    obtain ⟨ln1, hk1, hσ1⟩ := hnext k hkl (by rw [e1]; nofun)
    rw [e1] at hσ1
    obtain ⟨-, t1, rfl⟩ := seqStep_from_near hσ1
    obtain ⟨_, w0, hw0, hwo0⟩ := hword k _ t hk
    obtain ⟨_, w1, hw1, hwo1⟩ := hword (k + 1) _ t1 hk1
    obtain ⟨n, hn31, rfl, rfl⟩ := encode_near hw0 hw1
    have hm1 := hrel (k + 1) _ t1 .addAbsLo12Nc s ad hk1 rfl
    have hk1l := hlt hk1
    simp [relocShapeB, hd, hsz, hkl, hk1l, hwo0, hwo1, rd5_adrpW hn31, hn31, loOf]
    exact ⟨_, hm1, by simp; omega⟩
  case ldrGotLo12 rd rn s =>
    obtain ⟨rfl, rfl, rfl⟩ := hi
    obtain ⟨r0, e⟩ := seqStep_at_ldrGot hσ
    obtain ⟨k', ln', rfl, hk', hσ'⟩ := hprev k hkl (by rw [e]; nofun)
    rw [e] at hσ'
    obtain ⟨t', rfl⟩ := seqStep_into_got hσ'
    have hm := hrel k' _ t' .adrGotPage s 0 hk' rfl
    simp [relocShapeB, hsz, hkl]
    exact ⟨_, hm, by simp; omega⟩
  case addLo12 rd rn s ad =>
    obtain ⟨rfl, rfl, rfl⟩ := hi
    obtain ⟨r0, e⟩ := seqStep_at_addLo hσ
    obtain ⟨k', ln', rfl, hk', hσ'⟩ := hprev k hkl (by rw [e]; nofun)
    rw [e] at hσ'
    obtain ⟨t', rfl⟩ := seqStep_into_near hσ'
    have hm := hrel k' _ t' .adrPrelPgHi21 s ad hk' rfl
    simp [relocShapeB, hsz, hkl]
    exact ⟨_, hm, by simp; omega⟩
  case adrpTlsDesc rd s =>
    obtain ⟨rfl, rfl, rfl⟩ := hi
    have e1 := seqStep_at_adrpTls hσ
    obtain ⟨ln1, hk1, hσ1⟩ := hnext k hkl (by rw [e1]; nofun)
    rw [e1] at hσ1
    obtain ⟨e2, r1, r2, t1, rfl⟩ := seqStep_from_tls1 hσ1
    obtain ⟨ln2, hk2, hσ2⟩ := hnext (k + 1) (hlt hk1) (by rw [e2]; nofun)
    rw [e2] at hσ2
    obtain ⟨e3, r3, r4, t2, rfl⟩ := seqStep_from_tls2 hσ2
    obtain ⟨ln3, hk3, hσ3⟩ := hnext (k + 1 + 1) (hlt hk2) (by rw [e3]; nofun)
    rw [e3] at hσ3
    obtain ⟨-, r5, t3, rfl⟩ := seqStep_from_tls3 hσ3
    have a1 := hhas _ _ _ .tlsDescLd64Lo12 s 0 hk1 rfl
    have a2 := hhas _ _ _ .tlsDescAddLo12 s 0 hk2 rfl
    have a3 := hhas _ _ _ .tlsDescCall s 0 hk3 rfl
    have l3 := hlt hk3
    rw [show 4 * (k + 1) = 4 * k + 4 by omega] at a1
    rw [show 4 * (k + 1 + 1) = 4 * k + 8 by omega] at a2
    rw [show 4 * (k + 1 + 1 + 1) = 4 * k + 12 by omega] at a3
    simp only [relocShapeB, hd, hsz, a1, a2, a3]
    simp [hkl]
    omega
  case ldrTlsDescLo12 r1 r2 s =>
    obtain ⟨rfl, rfl, rfl⟩ := hi
    have e := seqStep_at_ldrTls hσ
    obtain ⟨k', ln', rfl, hk', hσ'⟩ := hprev k hkl (by rw [e]; nofun)
    rw [e] at hσ'
    obtain ⟨r, t', rfl⟩ := seqStep_into_tls1 hσ'
    have a0 := hhas _ _ _ .tlsDescAdrPage21 s 0 hk' rfl
    rw [show 4 * k' = 4 * (k' + 1) - 4 by omega] at a0
    simp only [relocShapeB, hsz, a0]
    simp [hkl]; omega
  case addTlsDescLo12 r1 r2 s =>
    obtain ⟨rfl, rfl, rfl⟩ := hi
    have e := seqStep_at_addTls hσ
    obtain ⟨k', ln', rfl, hk', hσ'⟩ := hprev k hkl (by rw [e]; nofun)
    rw [e] at hσ'
    obtain ⟨e', r3, r4, t', rfl⟩ := seqStep_into_tls2 hσ'
    obtain ⟨k'', ln'', rfl, hk'', hσ''⟩ := hprev k' (hlt hk') (by rw [e']; nofun)
    rw [e'] at hσ''
    obtain ⟨r, t'', rfl⟩ := seqStep_into_tls1 hσ''
    have a0 := hhas _ _ _ .tlsDescAdrPage21 s 0 hk'' rfl
    rw [show 4 * k'' = 4 * (k'' + 1 + 1) - 8 by omega] at a0
    simp only [relocShapeB, hsz, a0]
    simp [hkl]; omega
  case blrTlsDesc r1 s =>
    obtain ⟨rfl, rfl, rfl⟩ := hi
    have e := seqStep_at_blrTls hσ
    obtain ⟨k', ln', rfl, hk', hσ'⟩ := hprev k hkl (by rw [e]; nofun)
    rw [e] at hσ'
    obtain ⟨e', r3, r4, t', rfl⟩ := seqStep_into_tls3 hσ'
    obtain ⟨k'', ln'', rfl, hk'', hσ''⟩ := hprev k' (hlt hk') (by rw [e']; nofun)
    rw [e'] at hσ''
    obtain ⟨e'', r5, r6, t'', rfl⟩ := seqStep_into_tls2 hσ''
    obtain ⟨k3, ln3, rfl, hk3, hσ3⟩ := hprev k'' (hlt hk'') (by rw [e'']; nofun)
    rw [e''] at hσ3
    obtain ⟨r, t3, rfl⟩ := seqStep_into_tls1 hσ3
    have a0 := hhas _ _ _ .tlsDescAdrPage21 s 0 hk3 rfl
    rw [show 4 * k3 = 4 * (k3 + 1 + 1 + 1) - 12 by omega] at a0
    simp only [relocShapeB, hsz, a0]
    simp [hkl]; omega

/-- **The compiler's relocations have the linker's shapes**: `pipeT`'s artifact passes the
code-only half of `relocsOkB` (`relocsOkB_of`). -/
theorem relocShapes_of_pipeT {g : Clif.Function} {k : Nat} {base : BitVec 64} {o : Lean.Json}
    {a : Art} (ha : pipeT g k base o = .ok a) : relocShapesB a = true := by
  obtain ⟨-, -, -, -, he, hl, -⟩ := pipeT_spec ha
  exact relocShapesB_of_seqOk hl (seqOk_codeLines (emitFunc_seqOk he))

end Link
