import FV.Link.RelocShapeProof

/-!
# TLS descriptor sequences stay whole in `emitFunc`'s lines

`MInst.lines` emits Cranelift's `ElfTlsGetAddr` as six lines (`adrp x0, :tlsdesc:sym`,
`ldr tmp, [x0, :tlsdesc_lo12:sym]`, `add x0, x0, :tlsdesc_lo12:sym`, `blr tmp`,
`mrs tmp, tpidr_el0`, `add x0, x0, tmp`, with `tmp ≠ x0`), and it is the only emitter of
`adrp …, :tlsdesc:`. Neither `fallthrough` (which only drops or rewrites branches before a label)
nor branch relaxation (which only rewrites conditional branches) touches these lines, so every
TLSDESC `adrp` of an emitted function starts the whole sequence: `emitFunc_tlsClosed`.

The proof uses a forward automaton (`tlsSeqStep`, `TlsSeqSt`): outside a sequence any line but a
TLSDESC `adrp` is accepted; inside, only the next line of the sequence is. `TlsSeqOk L` (the run
from `free` ends in `free`) is closed under `++` (`tlsSeqOk_append`) and sound (`tlsClosed_of_ok`).
The free-line facts of the relocated-sequence automaton (`FV/Link/RelocShapeProof.lean`) are
reused through `lnNoAdrp_of_free`.
-/

namespace Backend.Proof

open Backend

/-- Every TLSDESC `adrp` of `L` starts the whole six-line sequence of `ElfTlsGetAddr`. -/
def TlsClosed (L : List Line) : Prop :=
  ∀ k rd n t, L[k]? = some (.ins (.adrpTlsDesc rd n) t) →
    rd = .x 0 ∧ ∃ tmp, tmp ≠ .x 0 ∧
      (∃ t1, L[k+1]? = some (.ins (.ldrTlsDescLo12 tmp (.x 0) n) t1)) ∧
      (∃ t2, L[k+2]? = some (.ins (.addTlsDescLo12 (.x 0) (.x 0) n) t2)) ∧
      (∃ t3, L[k+3]? = some (.ins (.blrTlsDesc tmp n) t3)) ∧
      (∃ t4, L[k+4]? = some (.ins (.mrsTpidrEl0 tmp) t4)) ∧
      (∃ t5, L[k+5]? = some (.ins (.aluRRR .add true (.x 0) (.x 0) tmp) t5))

/-! ## The automaton -/

/-- Where the run is: outside a sequence, or after its `adrp` / `ldr` / `add` / `blr` / `mrs`. -/
inductive TlsSeqSt where
  | free
  | a1 (n : String)
  | a2 (n : String) (tmp : Reg)
  | a3 (n : String) (tmp : Reg)
  | a4 (tmp : Reg)
  | a5 (tmp : Reg)
  deriving DecidableEq

/-- One line of the automaton. -/
def tlsSeqStep : TlsSeqSt → Line → Option TlsSeqSt
  | .free, .ins (.adrpTlsDesc rd n) _ => if rd = .x 0 then some (.a1 n) else none
  | .free, _ => some .free
  | .a1 n, .ins (.ldrTlsDescLo12 tmp rn n') _ =>
    if rn = .x 0 ∧ n' = n ∧ tmp ≠ .x 0 then some (.a2 n tmp) else none
  | .a2 n tmp, .ins (.addTlsDescLo12 rd rn n') _ =>
    if rd = .x 0 ∧ rn = .x 0 ∧ n' = n then some (.a3 n tmp) else none
  | .a3 n tmp, .ins (.blrTlsDesc r n') _ => if r = tmp ∧ n' = n then some (.a4 tmp) else none
  | .a4 tmp, .ins (.mrsTpidrEl0 r) _ => if r = tmp then some (.a5 tmp) else none
  | .a5 tmp, .ins (.aluRRR op is64 rd rn rm) _ =>
    if op = .add ∧ is64 = true ∧ rd = .x 0 ∧ rn = .x 0 ∧ rm = tmp then some .free else none
  | _, _ => none

/-- The automaton on a line list. -/
def tlsSeqGo : TlsSeqSt → List Line → Option TlsSeqSt
  | s, [] => some s
  | s, ln :: L => (tlsSeqStep s ln).bind (tlsSeqGo · L)

/-- Every sequence started in `L` is completed in `L`. -/
def TlsSeqOk (L : List Line) : Prop := tlsSeqGo .free L = some .free

theorem tlsSeqGo_append : ∀ (s : TlsSeqSt) (A B : List Line),
    tlsSeqGo s (A ++ B) = (tlsSeqGo s A).bind (tlsSeqGo · B)
  | s, [], B => rfl
  | s, ln :: A, B => by
    simp only [List.cons_append, tlsSeqGo]
    cases tlsSeqStep s ln with
    | none => rfl
    | some s' => simp only [Option.bind_some]; exact tlsSeqGo_append s' A B

theorem tlsSeqOk_append {A B : List Line} (hA : TlsSeqOk A) (hB : TlsSeqOk B) : TlsSeqOk (A ++ B) := by
  unfold TlsSeqOk at *
  rw [tlsSeqGo_append, hA]
  exact hB

theorem tlsSeqGo_cons_inv {s s' : TlsSeqSt} {ln : Line} {L : List Line}
    (h : tlsSeqGo s (ln :: L) = some s') : ∃ s1, tlsSeqStep s ln = some s1 ∧ tlsSeqGo s1 L = some s' := by
  simp only [tlsSeqGo] at h
  cases e : tlsSeqStep s ln with
  | none => simp [e] at h
  | some s1 => simp only [e, Option.bind_some] at h; exact ⟨s1, rfl, h⟩

/-! ## Lines outside every sequence -/

/-- The instruction is a TLSDESC `adrp`. -/
def _root_.Backend.Insn.isAdrpTls : Insn → Bool
  | .adrpTlsDesc .. => true
  | _ => false

/-- The line is not a TLSDESC `adrp` (the automaton stays `free` on it). -/
def lnNoAdrp : Line → Bool
  | .ins x _ => !x.isAdrpTls
  | _ => true

theorem Insn.isAdrpTls_of_seq {x : Insn} (h : x.seq = false) : x.isAdrpTls = false := by
  cases x <;> simp_all [Insn.seq, Insn.isAdrpTls]

theorem lnNoAdrp_of_free {ln : Line} (h : lnFree ln = true) : lnNoAdrp ln = true := by
  cases ln with
  | ins x t =>
    simp only [lnFree, Bool.not_eq_true'] at h
    simp [lnNoAdrp, Insn.isAdrpTls_of_seq h]
  | _ => rfl

theorem tlsSeqStep_free {ln : Line} (h : lnNoAdrp ln = true) : tlsSeqStep .free ln = some .free := by
  unfold tlsSeqStep
  split <;> simp_all [lnNoAdrp, Insn.isAdrpTls]

theorem tlsSeqGo_free_cons {ln : Line} (h : lnNoAdrp ln = true) (L : List Line) :
    tlsSeqGo .free (ln :: L) = tlsSeqGo .free L := by
  simp [tlsSeqGo, tlsSeqStep_free h]

theorem tlsSeqOk_of_noAdrp : ∀ {L : List Line}, (∀ ln ∈ L, lnNoAdrp ln = true) → TlsSeqOk L
  | [], _ => rfl
  | ln :: L, h => by
    unfold TlsSeqOk
    rw [tlsSeqGo_free_cons (h ln (by simp))]
    exact tlsSeqOk_of_noAdrp (fun x hx => h x (by simp [hx]))

theorem tlsSeqOk_of_free {L : List Line} (h : ∀ ln ∈ L, lnFree ln = true) : TlsSeqOk L :=
  tlsSeqOk_of_noAdrp fun ln hln => lnNoAdrp_of_free (h ln hln)

/-- The instruction may occur in a sequence. -/
def _root_.Backend.Insn.tlsPart : Insn → Bool
  | .adrpTlsDesc .. | .ldrTlsDescLo12 .. | .addTlsDescLo12 .. | .blrTlsDesc .. | .mrsTpidrEl0 ..
  | .aluRRR .. => true
  | _ => false

/-- A line no state of a sequence accepts (labels, branches). -/
def lnPlain : Line → Bool
  | .ins x _ => !x.tlsPart
  | _ => true

theorem tlsSeqStep_of_plain {ln : Line} (h : lnPlain ln = true) {s s' : TlsSeqSt}
    (hs : tlsSeqStep s ln = some s') : s = .free ∧ s' = .free := by
  unfold tlsSeqStep at hs
  split at hs <;> simp_all [lnPlain, Insn.tlsPart]

theorem tlsSeqGo_free_inv {ln : Line} (h : lnPlain ln = true) {L : List Line} {s s' : TlsSeqSt}
    (hs : tlsSeqGo s (ln :: L) = some s') : s = .free ∧ tlsSeqGo .free L = some s' := by
  obtain ⟨s1, e, hs⟩ := tlsSeqGo_cons_inv hs
  obtain ⟨rfl, rfl⟩ := tlsSeqStep_of_plain h e
  exact ⟨rfl, hs⟩

theorem lnNoAdrp_of_plain {ln : Line} (h : lnPlain ln = true) : lnNoAdrp ln = true := by
  cases ln with
  | ins x t => cases x <;> simp_all [lnPlain, lnNoAdrp, Insn.tlsPart, Insn.isAdrpTls]
  | _ => rfl

/-! ## Soundness -/

theorem tlsSeqStep_a1 {n : String} {ln : Line} {s' : TlsSeqSt} (h : tlsSeqStep (.a1 n) ln = some s') :
    ∃ tmp t, tmp ≠ .x 0 ∧ ln = .ins (.ldrTlsDescLo12 tmp (.x 0) n) t ∧ s' = .a2 n tmp := by
  unfold tlsSeqStep at h
  split at h <;> simp_all
  obtain ⟨⟨-, -, h1⟩, rfl⟩ := h
  exact ⟨_, h1, rfl, rfl⟩

theorem tlsSeqStep_a2 {n : String} {tmp : Reg} {ln : Line} {s' : TlsSeqSt}
    (h : tlsSeqStep (.a2 n tmp) ln = some s') :
    ∃ t, ln = .ins (.addTlsDescLo12 (.x 0) (.x 0) n) t ∧ s' = .a3 n tmp := by
  unfold tlsSeqStep at h
  split at h <;> simp_all

theorem tlsSeqStep_a3 {n : String} {tmp : Reg} {ln : Line} {s' : TlsSeqSt}
    (h : tlsSeqStep (.a3 n tmp) ln = some s') :
    ∃ t, ln = .ins (.blrTlsDesc tmp n) t ∧ s' = .a4 tmp := by
  unfold tlsSeqStep at h
  split at h <;> simp_all

theorem tlsSeqStep_a4 {tmp : Reg} {ln : Line} {s' : TlsSeqSt} (h : tlsSeqStep (.a4 tmp) ln = some s') :
    ∃ t, ln = .ins (.mrsTpidrEl0 tmp) t ∧ s' = .a5 tmp := by
  unfold tlsSeqStep at h
  split at h <;> simp_all

theorem tlsSeqStep_a5 {tmp : Reg} {ln : Line} {s' : TlsSeqSt} (h : tlsSeqStep (.a5 tmp) ln = some s') :
    ∃ t, ln = .ins (.aluRRR .add true (.x 0) (.x 0) tmp) t ∧ s' = .free := by
  unfold tlsSeqStep at h
  split at h <;> simp_all

theorem tlsSeqStep_adrp {s s' : TlsSeqSt} {rd : Reg} {n : String} {t : Option Clif.TrapCode}
    (h : tlsSeqStep s (.ins (.adrpTlsDesc rd n) t) = some s') : rd = .x 0 ∧ s' = .a1 n := by
  unfold tlsSeqStep at h
  split at h <;> simp_all

/-- After a TLSDESC `adrp`, a completed run reads the other five lines of the sequence. -/
theorem tlsSeqGo_a1 {n : String} {L : List Line} (h : tlsSeqGo (.a1 n) L = some .free) :
    ∃ tmp, tmp ≠ .x 0 ∧ ∃ t1 t2 t3 t4 t5 rest,
      L = .ins (.ldrTlsDescLo12 tmp (.x 0) n) t1 :: .ins (.addTlsDescLo12 (.x 0) (.x 0) n) t2 ::
        .ins (.blrTlsDesc tmp n) t3 :: .ins (.mrsTpidrEl0 tmp) t4 ::
        .ins (.aluRRR .add true (.x 0) (.x 0) tmp) t5 :: rest := by
  rcases L with _ | ⟨l1, L⟩
  · simp [tlsSeqGo] at h
  obtain ⟨s1, e1, h⟩ := tlsSeqGo_cons_inv h
  obtain ⟨tmp, t1, htmp, rfl, rfl⟩ := tlsSeqStep_a1 e1
  rcases L with _ | ⟨l2, L⟩
  · simp [tlsSeqGo] at h
  obtain ⟨s2, e2, h⟩ := tlsSeqGo_cons_inv h
  obtain ⟨t2, rfl, rfl⟩ := tlsSeqStep_a2 e2
  rcases L with _ | ⟨l3, L⟩
  · simp [tlsSeqGo] at h
  obtain ⟨s3, e3, h⟩ := tlsSeqGo_cons_inv h
  obtain ⟨t3, rfl, rfl⟩ := tlsSeqStep_a3 e3
  rcases L with _ | ⟨l4, L⟩
  · simp [tlsSeqGo] at h
  obtain ⟨s4, e4, h⟩ := tlsSeqGo_cons_inv h
  obtain ⟨t4, rfl, rfl⟩ := tlsSeqStep_a4 e4
  rcases L with _ | ⟨l5, L⟩
  · simp [tlsSeqGo] at h
  obtain ⟨s5, e5, -⟩ := tlsSeqGo_cons_inv h
  obtain ⟨t5, rfl, rfl⟩ := tlsSeqStep_a5 e5
  exact ⟨tmp, htmp, t1, t2, t3, t4, t5, L, rfl⟩

theorem tlsClosed_of_go : ∀ {L : List Line} {s : TlsSeqSt}, tlsSeqGo s L = some .free → TlsClosed L
  | [], _, _, k, rd, n, t, hk => by simp at hk
  | ln :: L, s, h, 0, rd, n, t, hk => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk
    obtain ⟨s1, e, h⟩ := tlsSeqGo_cons_inv h
    obtain ⟨rfl, rfl⟩ := tlsSeqStep_adrp e
    obtain ⟨tmp, htmp, t1, t2, t3, t4, t5, rest, rfl⟩ := tlsSeqGo_a1 h
    exact ⟨rfl, tmp, htmp, ⟨t1, rfl⟩, ⟨t2, rfl⟩, ⟨t3, rfl⟩, ⟨t4, rfl⟩, ⟨t5, rfl⟩⟩
  | ln :: L, s, h, k + 1, rd, n, t, hk => by
    obtain ⟨s1, -, h⟩ := tlsSeqGo_cons_inv h
    simp only [List.getElem?_cons_succ] at hk
    obtain ⟨h0, tmp, htmp, ⟨t1, h1⟩, ⟨t2, h2⟩, ⟨t3, h3⟩, ⟨t4, h4⟩, ⟨t5, h5⟩⟩ :=
      tlsClosed_of_go h k rd n t hk
    exact ⟨h0, tmp, htmp, ⟨t1, by simpa using h1⟩, ⟨t2, by simpa using h2⟩,
      ⟨t3, by simpa using h3⟩, ⟨t4, by simpa using h4⟩, ⟨t5, by simpa using h5⟩⟩

theorem tlsClosed_of_ok {L : List Line} (h : TlsSeqOk L) : TlsClosed L := tlsClosed_of_go h

/-! ## `fallthrough` and branch relaxation -/

theorem cond_plain {c : Insn} {l : Lbl} (h : c.condTarget? = some l) (e : Lbl)
    (t : Option Clif.TrapCode) :
    lnPlain (.ins c t) = true ∧ lnPlain (.ins (c.invertTo e) t) = true := by
  cases c <;> simp_all [Insn.condTarget?, Insn.invertTo, lnPlain, Insn.tlsPart]

theorem tlsSeqGo_ftList : ∀ (n : Nat) (L : List Line) (s : TlsSeqSt), L.length ≤ n →
    tlsSeqGo s L = some .free → tlsSeqGo s (ftList L) = some .free
  | _, [], _, _, h => by simpa [ftList] using h
  | n + 1, ln :: rest, s, hn, h => by
    rw [ftList_cons]
    rcases ftStep_cases ln rest[0]? rest[1]? with he | ⟨x, l, rfl, h1, he⟩ | ⟨c, e, l, rfl, hc, h1, h2, he⟩
    · rw [he]
      simp only [List.drop_one, List.tail_cons, List.singleton_append, tlsSeqGo] at h ⊢
      cases e : tlsSeqStep s ln with
      | none => simp [e] at h
      | some s1 =>
        simp only [e, Option.bind_some] at h ⊢
        exact tlsSeqGo_ftList n rest _ (by simp at hn; omega) h
    · rw [he]
      cases rest with
      | nil => simp at h1
      | cons y rest' =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h1
        subst h1
        obtain ⟨rfl, h'⟩ := tlsSeqGo_free_inv rfl h
        simp only [List.drop_one, List.tail_cons, List.nil_append]
        exact tlsSeqGo_ftList n _ _ (by simp at hn ⊢; omega) h'
    · rw [he]
      cases rest with
      | nil => simp at h1
      | cons y rest =>
      cases rest with
      | nil => simp at h2
      | cons z rest' =>
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h1 h2
        subst h1 h2
        obtain ⟨hc1, hc2⟩ := cond_plain hc e none
        obtain ⟨rfl, h'⟩ := tlsSeqGo_free_inv hc1 h
        obtain ⟨-, h''⟩ := tlsSeqGo_free_inv rfl h'
        simp only [List.drop_succ_cons, List.drop_zero, List.singleton_append]
        rw [tlsSeqGo_free_cons (lnNoAdrp_of_plain hc2)]
        exact tlsSeqGo_ftList n _ _ (by simp at hn ⊢; omega) h''

theorem tlsSeqGo_relaxLines (f : Lbl → Bool) : ∀ (L : List Line) (s : TlsSeqSt),
    tlsSeqGo s L = some .free → tlsSeqGo s (relaxLines f L) = some .free
  | [], _, h => h
  | ln :: L, s, h => by
    rw [relaxLines_cons]
    have keep : relaxLine f ln = [ln] → tlsSeqGo s (relaxLine f ln ++ relaxLines f L) = some .free := by
      intro hr
      rw [hr]
      simp only [List.singleton_append, tlsSeqGo] at h ⊢
      cases e : tlsSeqStep s ln with
      | none => simp [e] at h
      | some s1 =>
        simp only [e, Option.bind_some] at h ⊢
        exact tlsSeqGo_relaxLines f L _ h
    match ln, h with
    | .ins c (some tc), h => exact keep rfl
    | .label l, h => exact keep rfl
    | .word x y, h => exact keep rfl
    | .ins c none, h =>
      rcases relaxLine_cases f c with hr | ⟨t, ht, hr⟩
      · exact keep hr
      · rw [hr]
        obtain ⟨hc1, hc2⟩ := cond_plain (relaxTarget_condTarget ht) .skip none
        obtain ⟨rfl, h'⟩ := tlsSeqGo_free_inv hc1 h
        simp only [List.cons_append, List.nil_append]
        rw [tlsSeqGo_free_cons (lnNoAdrp_of_plain hc2), tlsSeqGo_free_cons rfl]
        exact tlsSeqGo_relaxLines f L _ h'

/-! ## The lines of one instruction -/

@[simp] theorem CondBrKind.insn_isAdrpTls (k : CondBrKind) (l : Lbl) : (k.insn l).isAdrpTls = false :=
  Insn.isAdrpTls_of_seq (CondBrKind.insn_seq k l)

@[simp] theorem casLoopCmp_isAdrpTls (bits : Nat) : (casLoopCmp bits).isAdrpTls = false :=
  Insn.isAdrpTls_of_seq (casLoopCmp_seq bits)

@[simp] theorem rmwLoopCmp_isAdrpTls (op : AtomicRmwLoopOp) (bits : Nat) :
    (rmwLoopCmp op bits).isAdrpTls = false :=
  Insn.isAdrpTls_of_seq (rmwLoopCmp_seq op bits)

@[simp] theorem rmwLoopMid_isAdrpTls (op : AtomicRmwLoopOp) (bits : Nat) :
    ∀ i ∈ rmwLoopMid op bits, i.isAdrpTls = false :=
  fun i hi => Insn.isAdrpTls_of_seq (rmwLoopMid_seq op bits i hi)

/-- The six lines of `ElfTlsGetAddr` form one whole sequence. -/
theorem tlsSeqOk_six {rd tmp : Reg} (n : String) (h : ¬(rd != .x 0 || tmp == .x 0) = true) :
    TlsSeqOk [.ins (.adrpTlsDesc (.x 0) n) none, .ins (.ldrTlsDescLo12 tmp (.x 0) n) none,
      .ins (.addTlsDescLo12 (.x 0) (.x 0) n) none, .ins (.blrTlsDesc tmp n) none,
      .ins (.mrsTpidrEl0 tmp) none, .ins (.aluRRR .add true (.x 0) (.x 0) tmp) none] := by
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, not_or, Decidable.not_not] at h
  simp [TlsSeqOk, tlsSeqGo, tlsSeqStep, h.2]

theorem lines_tlsOk {c : FnCtx} {m : MInst} {ps ps' : PState} {ls : List Line}
    (h : m.lines c ps = .ok (ls, ps')) : TlsSeqOk ls := by
  unfold MInst.lines at h
  split at h <;> simp only [bind, Except.bind, pure, Except.pure] at h
  all_goals (repeat' (first | (split at h) | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h)))
  all_goals first | cases h | (simp [throw, throwThe, MonadExceptOf.throw] at h) | skip
  all_goals first | exact tlsSeqOk_six _ ‹_› | apply tlsSeqOk_of_noAdrp
  all_goals simp [lnNoAdrp, Insn.isAdrpTls, MInst.lines.addOff, rmwLoopLines, rmwLoopBody,
    casLoopLines, casLoopHead, or_imp, forall_and]
  all_goals (repeat' constructor)
  all_goals first
    | exact fun ln hln => lnNoAdrp_of_free (memFinalize_free ‹_› ln hln)
    | exact rmwLoopMid_isAdrpTls _ _
    | (simp [throw, throwThe, MonadExceptOf.throw] at *; done)
    | ((repeat' split) <;> first
        | (simp <;> rfl)
        | (rename_i heq; have h' := congrArg Insn.isAdrpTls heq
           simp only [CondBrKind.insn_isAdrpTls, casLoopCmp_isAdrpTls] at h'
           simp [Insn.isAdrpTls] at h'))

/-! ## Prologue, epilogue, blocks, traps -/

theorem ainstLines_tlsOk {c : FnCtx} {af : AFunc} {a : AInst} {ps ps' : PState} {ls : List Line}
    (h : ainstLines c af a ps = .ok (ls, ps')) : TlsSeqOk ls := by
  cases a with
  | inst m => exact lines_tlsOk h
  | prologue =>
    simp only [ainstLines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    split
    · exact tlsSeqOk_of_free (prologueLines_free _ _)
    · rfl
  | epilogueRet =>
    simp only [ainstLines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    split
    · exact tlsSeqOk_of_free (epilogueLines_free _ _)
    · rfl

theorem codeLinesE_tlsOk {c : FnCtx} {af : AFunc} :
    ∀ (code : List AInst) (ps ps' : PState) (ls : List Line),
      codeLinesE c af code ps = .ok (ls, ps') → TlsSeqOk ls
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
        exact tlsSeqOk_append (ainstLines_tlsOk hr) (codeLinesE_tlsOk as _ _ _ hr2)

theorem blocksLinesE_tlsOk {c : FnCtx} {af : AFunc} :
    ∀ (bs : List (Label × Array AInst)) (ps ps' : PState) (ls : List Line),
      blocksLinesE c af bs ps = .ok (ls, ps') → TlsSeqOk ls
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
        unfold TlsSeqOk
        rw [List.cons_append, tlsSeqGo_free_cons rfl]
        exact tlsSeqOk_append (codeLinesE_tlsOk _ _ _ _ hr) (blocksLinesE_tlsOk bs _ _ _ hr2)

/-! ## `emitFunc` -/

/-- **TLS sequences in `emitFunc`'s lines**: every TLSDESC `adrp` starts the whole six-line
sequence of `ElfTlsGetAddr`. -/
theorem emitFunc_tlsClosed {k : Nat} {af : AFunc} {fa : FnAsm} (h : emitFunc k af = .ok fa) :
    TlsClosed fa.lines.toList := by
  obtain ⟨body, ps, hb, hl, -⟩ := emitFunc_ok h
  rw [hl]
  refine tlsClosed_of_go (tlsSeqOk_append (tlsSeqGo_relaxLines _ _ _ (tlsSeqOk_append ?_ ?_))
    (tlsSeqOk_of_free fun ln hln => ?_))
  · exact tlsSeqGo_ftList _ _ _ (Nat.le_refl _) (blocksLinesE_tlsOk _ _ _ _ hb)
  · exact tlsSeqOk_of_free (trapLines_free _)
  · rcases emitPool_mem hln with ⟨w, rfl⟩ | ⟨n, rfl⟩ <;> rfl

/-! ## Non-vacuity -/

/-- The six lines `MInst.lines` emits for `ElfTlsGetAddr sym x0 x1` are `TlsClosed`. -/
example : TlsClosed [.ins (.adrpTlsDesc (.x 0) "sym") none,
    .ins (.ldrTlsDescLo12 (.x 1) (.x 0) "sym") none, .ins (.addTlsDescLo12 (.x 0) (.x 0) "sym") none,
    .ins (.blrTlsDesc (.x 1) "sym") none, .ins (.mrsTpidrEl0 (.x 1)) none,
    .ins (.aluRRR .add true (.x 0) (.x 0) (.x 1)) none] :=
  tlsClosed_of_ok (by unfold TlsSeqOk; decide)

/-- A TLSDESC `adrp` cut off after its `ldr` is not `TlsClosed`. -/
example : ¬ TlsClosed [.ins (.adrpTlsDesc (.x 0) "sym") none,
    .ins (.ldrTlsDescLo12 (.x 1) (.x 0) "sym") none, .ins (.b .skip) none] := by
  intro h
  obtain ⟨-, -, -, -, ⟨t2, h2⟩, -⟩ := h 0 (.x 0) "sym" none rfl
  simp at h2

end Backend.Proof
