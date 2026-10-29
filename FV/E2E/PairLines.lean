import FV.E2E.RegLevelRelax
import FV.E2E.EmitSize

/-!
# `adrp` pairs stay adjacent in `emitFunc`'s lines

The second word of an `adrp` pair (`ldr …, :got_lo12:` / `add …, :lo12:`) is emitted only by
`loadExtNameGot`/`loadExtNameNear`, right after its first word (`adrp`), and neither
`MachBuffer`'s branch simplification (which only removes branches, inverts a conditional branch
in place and retargets, `machBuf_pcOk`) nor branch relaxation (which only rewrites conditional
branches) separates them: `emitFunc_pairsClosed`.

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

/-! ## `MachBuffer`'s simplification -/

/-- Whether the last line of `A` (`b` for none) is a first word. -/
def lastF (b : Bool) (A : List Line) : Bool :=
  match A.getLast? with
  | some a => lnFirst a
  | none => b

theorem pcOk_snoc : ∀ (A : List Line) (b : Bool) (x : Line),
    pcOk b (A ++ [x]) = (pcOk b A && (!lnSecond x || lastF b A))
  | [], b, x => by simp [pcOk, lastF]
  | a :: A, b, x => by
    rw [List.cons_append, pcOk, pcOk, pcOk_snoc A (lnFirst a) x]
    have : lastF (lnFirst a) A = lastF b (a :: A) := by
      cases A with
      | nil => simp [lastF]
      | cons a' A' =>
        simp only [lastF]
        cases hz : (a' :: A').getLast? with
        | none => simp at hz
        | some z =>
          rw [List.getLast?_cons_cons, hz]
    rw [this, Bool.and_assoc]

theorem pcOk_left : ∀ {A B : List Line} {b : Bool}, pcOk b (A ++ B) = true → pcOk b A = true
  | [], _, _, _ => rfl
  | a :: A, B, b, h => by
    simp only [List.cons_append, pcOk, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, pcOk_left h.2⟩

/-- A line that is neither word of a pair. -/
def NoPair (ln : Line) : Prop := lnFirst ln = false ∧ lnSecond ln = false

theorem pcOk_eraseIdx : ∀ (L : List Line) (k : Nat) (b : Bool), pcOk b L = true →
    (∀ x, L[k]? = some x → NoPair x) → (∀ y, L[k + 1]? = some y → lnSecond y = false) →
    pcOk b (L.eraseIdx k) = true
  | [], _, _, _, _, _ => rfl
  | x :: L, 0, b, h, hx, hy => by
    have hx' := hx x rfl
    simp only [pcOk, hx'.1, hx'.2, Bool.not_false, Bool.true_or, Bool.true_and] at h
    simp only [List.eraseIdx_cons_zero]
    cases L with
    | nil => rfl
    | cons y R =>
      have hy' := hy y rfl
      simp only [pcOk, hy', Bool.not_false, Bool.true_or, Bool.true_and] at h ⊢
      exact h
  | a :: L, k + 1, b, h, hx, hy => by
    simp only [pcOk, Bool.and_eq_true, List.eraseIdx_cons_succ] at h ⊢
    exact ⟨h.1, pcOk_eraseIdx L k _ h.2 (fun x h' => hx x (by simpa using h'))
      (fun y h' => hy y (by simpa using h'))⟩

theorem pcOk_set : ∀ (L : List Line) (p : Nat) (b : Bool) (y : Line), pcOk b L = true →
    (∀ x, L[p]? = some x → NoPair x) → NoPair y → pcOk b (L.set p y) = true
  | [], _, _, _, _, _, _ => rfl
  | x :: L, 0, b, y, h, hx, hy => by
    have hx' := hx x rfl
    simp only [pcOk, hx'.1, hx'.2, Bool.not_false, Bool.true_or, Bool.true_and] at h
    simp only [List.set_cons_zero, pcOk, hy.1, hy.2, Bool.not_false, Bool.true_or, Bool.true_and]
    exact h
  | a :: L, p + 1, b, y, h, hx, hy => by
    simp only [pcOk, Bool.and_eq_true, List.set_cons_succ] at h ⊢
    exact ⟨h.1, pcOk_set L p _ y h.2 (fun x h' => hx x (by simpa using h')) hy⟩

theorem relabel_pair (f : Lbl → Lbl) (ln : Line) :
    lnFirst (ln.relabel f) = lnFirst ln ∧ lnSecond (ln.relabel f) = lnSecond ln := by
  cases ln with
  | ins i tc => cases i <;> exact ⟨rfl, rfl⟩
  | word _ _ => exact ⟨rfl, rfl⟩
  | label _ => exact ⟨rfl, rfl⟩

theorem pcOk_relabel (f : Lbl → Lbl) : ∀ (L : List Line) (b : Bool),
    pcOk b (L.map (Line.relabel f)) = pcOk b L
  | [], _ => rfl
  | ln :: L, b => by
    simp only [List.map_cons, pcOk, (relabel_pair f ln).1, (relabel_pair f ln).2,
      pcOk_relabel f L]

theorem stepLine_noPair {ln : Line} {t : Lbl} (h : (ln.ubr?).orElse (fun _ => ln.cbr?) = some t) :
    NoPair ln := by
  cases ln with
  | ins i tc =>
    cases tc with
    | none =>
      cases i <;> simp_all [Line.ubr?, Line.cbr?, Option.orElse, NoPair, lnFirst, lnSecond,
        Insn.pairSecond, Insn.condTarget?]
    | some _ => simp [Line.ubr?, Line.cbr?, Option.orElse] at h
  | _ => simp [Line.ubr?, Line.cbr?, Option.orElse] at h

theorem step_pcOk (allLabels : Bool) (m m' : MBuf) (hm : pcOk false m.out.toList = true)
    (h : MBuf.step allLabels m = some m') : pcOk false m'.out.toList = true := by
  obtain ⟨k, ln, t, hlc, hkln, ht, hc⟩ := step_cases allLabels m m' h
  have hE : pcOk false (m.erase k).toList = true := by
    simp only [MBuf.erase, List.toList_toArray]
    refine pcOk_eraseIdx _ k false hm (fun x hx => ?_) (fun y hy => ?_)
    · simp only [Array.getElem?_toList, hkln, Option.some.injEq] at hx
      subst hx; exact stepLine_noPair ht
    · have hlt : k + 1 < m.out.size := by
        have := (List.getElem?_eq_some_iff.mp hy).1; simpa using this
      obtain ⟨l, rfl⟩ := lastCode_tail m.out m.out.size k hlc (k + 1) y (by omega) hlt
        (by simpa using hy)
      rfl
  rcases hc with ⟨ho, -⟩ | ⟨ho, -⟩ | ⟨p, c, tc, ct, hpk, hp, hct, -, ho, -⟩
  · rw [ho]; exact hE
  · rw [ho]; exact hm
  · rw [ho, Array.set!, Array.toList_setIfInBounds]
    have hcond : ∃ l, c.condTarget? = some l := by
      cases tc with
      | none =>
        simp only [Line.cbr?] at hct
        split at hct
        · exact ⟨_, by assumption⟩
        · cases hct
      | some _ => simp [Line.cbr?] at hct
    obtain ⟨l, hl⟩ := hcond
    obtain ⟨h1, h2, h3, h4⟩ := cond_noPair hl t tc
    refine pcOk_set _ p false _ hE (fun x hx => ?_) ⟨h4, h3⟩
    simp only [MBuf.erase, List.toList_toArray, List.getElem?_eraseIdx_of_lt hpk,
      Array.getElem?_toList, hp, Option.some.injEq] at hx
    subst hx
    exact ⟨h2, h1⟩

theorem optimize_pcOk (allLabels : Bool) (m : MBuf) (hm : pcOk false m.out.toList = true) :
    pcOk false (MBuf.optimize allLabels m).out.toList = true := by
  unfold MBuf.optimize
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  refine mbForIn_inv (P := fun m' : MBuf => pcOk false m'.out.toList = true) _ _ _ hm ?_
  intro _ s hs
  split
  · rename_i m' h; exact step_pcOk _ _ _ hs h
  · exact hs

/-- **`MachBuffer`'s simplification keeps the pairs adjacent.** -/
theorem machBuf_pcOk (allLabels : Bool) (ls : List Line) (h : pcOk false ls = true) :
    pcOk false (machBuf allLabels ls).1 = true := by
  -- the fold: the lines pushed so far `I`, the buffer ending in `I`'s last first word
  have hfold : ∀ (L I : List Line) (m : MBuf), pcOk false (I ++ L) = true →
      pcOk false m.out.toList = true →
      (∀ F, I.getLast? = some F → lnFirst F = true → m.out.toList.getLast? = some F) →
      pcOk false (L.foldl (fun m ln =>
        let m := { m with out := m.out.push ln }
        if ln matches .label _ then m.optimize allLabels else m) m).out.toList = true := by
    intro L
    induction L with
    | nil => intro I m _ hm _; exact hm
    | cons ln L ih =>
      intro I m hI hm hlast
      rw [List.foldl_cons]
      apply ih (I ++ [ln])
      · simpa using hI
      · have hI' := pcOk_left (A := I ++ [ln]) (B := L) (by simpa using hI)
        rw [pcOk_snoc] at hI'
        simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hI'
        have hp : pcOk false (m.out.push ln).toList = true := by
          rw [Array.toList_push, pcOk_snoc]
          simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
          refine ⟨hm, ?_⟩
          rcases hI'.2 with hs | hf
          · exact .inl hs
          · refine .inr ?_
            unfold lastF at hf ⊢
            split at hf
            · rename_i F hF
              rw [hlast F hF hf]
              exact hf
            · cases hf
        split
        · exact optimize_pcOk _ _ hp
        · exact hp
      · intro F hF hf
        simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
          Option.some.injEq] at hF
        subst hF
        split
        · simp_all [lnFirst]
        · simp [Array.toList_push]
  unfold machBuf
  dsimp only
  rw [pcOk_relabel]
  exact optimize_pcOk _ _ (hfold ls [] {} (by simpa using h) rfl (fun F hF => by simp at hF))

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

theorem spAdjLines_noSecond (sub : Bool) (size : Nat) :
    ∀ ln ∈ spAdjLines sub size, lnSecond ln = false := by
  intro ln hln
  unfold spAdjLines at hln
  split at hln
  · simp at hln
  · split at hln
    · simp at hln; subst hln; cases sub <;> rfl
    · rcases List.mem_append.1 hln with h1 | h1
      · exact loadConst64_noSecond _ _ _ h1
      · simp at h1; subst h1; cases sub <;> rfl

theorem pushLines_noSecond (int : Bool) (rs : List Reg) :
    ∀ ln ∈ pushLines int rs, lnSecond ln = false := by
  intro ln hln
  simp only [pushLines, List.mem_append, List.mem_map] at hln
  rcases hln with hln | ⟨⟨a, b⟩, -, rfl⟩
  · split at hln
    · simp only [List.mem_singleton] at hln; subst hln; cases int <;> rfl
    · simp at hln
  · cases int <;> rfl

theorem popLines_noSecond (int : Bool) (rs : List Reg) :
    ∀ ln ∈ popLines int rs, lnSecond ln = false := by
  intro ln hln
  simp only [popLines, List.mem_append, List.mem_map] at hln
  rcases hln with ⟨⟨a, b⟩, -, rfl⟩ | hln
  · cases int <;> rfl
  · split at hln
    · simp only [List.mem_singleton] at hln; subst hln; cases int <;> rfl
    · simp at hln

theorem prologueLines_noSecond (saves : List Reg) (size : Nat) :
    ∀ ln ∈ prologueLines saves size, lnSecond ln = false := by
  intro ln hln
  simp only [prologueLines, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hln
  rcases hln with (((rfl | rfl) | hln) | hln) | hln
  · rfl
  · rfl
  · exact pushLines_noSecond _ _ _ hln
  · exact pushLines_noSecond _ _ _ hln
  · exact spAdjLines_noSecond _ _ _ hln

theorem epilogueLines_noSecond (saves : List Reg) (size : Nat) :
    ∀ ln ∈ epilogueLines saves size, lnSecond ln = false := by
  intro ln hln
  simp only [epilogueLines, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hln
  rcases hln with ((hln | hln) | hln) | (rfl | rfl)
  · exact spAdjLines_noSecond _ _ _ hln
  · exact popLines_noSecond _ _ _ hln
  · exact popLines_noSecond _ _ _ hln
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
    · exact pcOk_of_noSecond _ (prologueLines_noSecond _ _)
    · rfl
  | epilogueRet =>
    simp only [ainstLines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    split
    · exact pcOk_of_noSecond _ (epilogueLines_noSecond _ _)
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

/-- The segments' unsimplified lines keep the pairs adjacent. -/
theorem segsOf_pcOk {c : FnCtx} {af : AFunc} :
    ∀ (bs : List ((Label × Array AInst) × Nat)) (ps ps' : PState) (ss : List Seg),
      segsOf c af bs ps = .ok (ss, ps') → pcOk false (segLines ss (ss.map (·.term))) = true
  | [], ps, ps', ss, h => by
    simp only [segsOf, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h; rfl
  | ((l, code), i) :: bs, ps, ps', ss, h => by
    simp only [segsOf] at h
    obtain ⟨⟨l1, ps1⟩, h1, h⟩ := E2E.exceptBind_ok h
    obtain ⟨⟨l2, ps2⟩, h2, h⟩ := E2E.exceptBind_ok h
    obtain ⟨⟨l3, ps3⟩, h3, h⟩ := E2E.exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [List.map_cons, segLines, List.cons_append, pcOk_label, List.append_assoc]
    exact pcOk_append (codeLinesE_pcOk _ _ _ _ h1)
      (pcOk_append (codeLinesE_pcOk _ _ _ _ h2) (segsOf_pcOk bs _ _ _ h3))

/-- The emission plan's lines keep the pairs adjacent. -/
theorem emitPlan_pcOk {k : Nat} {af : AFunc} {p : Plan} (h : emitPlan k af = .ok p) :
    pcOk false (segLines p.segs p.outs) = true := by
  have hraw := segsOf_pcOk _ _ _ _ (emitPlan_spec h).1
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
      rw [hs] at hraw ⊢
      rw [splitSegs_lines _ _ _ hsp]
      exact machBuf_pcOk _ _ hraw
  · split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact hraw
    · cases h

theorem trapLines_noSecond (ps : PState) : ∀ ln ∈ trapLines ps, lnSecond ln = false := by
  intro ln hln
  simp only [trapLines, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hln
  obtain ⟨p, -, rfl | rfl⟩ := hln <;> rfl

/-! ## `emitFunc` -/

/-- **`adrp` pairs in `emitFunc`'s lines**: every second word (`ldr …, :got_lo12:` /
`add …, :lo12:`) immediately follows a first word (`adrp …, :got:` / `adrp`). -/
theorem emitFunc_pairsClosed {k : Nat} {af : AFunc} {fa : FnAsm} (h : emitFunc k af = .ok fa) :
    PairsClosed fa.lines.toList := by
  obtain ⟨p, hp, hl, -⟩ := emitFunc_ok h
  rw [hl]
  refine pairsClosed_of_pcOk (pcOk_relaxLines _ _ _ (pcOk_append ?_ ?_))
  · exact emitPlan_pcOk hp
  · exact pcOk_of_noSecond _ (trapLines_noSecond _)

end Backend.Proof
