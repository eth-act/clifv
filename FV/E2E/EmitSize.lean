import FV.E2E.RegLevelEmit
import FV.Backend.Proof.RelaxLayout
import FV.Backend.SpillAlloc

/-!
# The size of the spill allocation's code (`E2E.emitFunc_spill_size`)

The layout needs the emitted function to be below `2 ^ 27` bytes (the ±128 MiB reach of `b`).
That is a genuine input condition (a function can be arbitrarily large), so it is decided on
the prepared VCode: `spillSizeOkB vcp` sums a per-item word bound (`itemWords`) over the
spill allocation `spillAlloc vcp` and requires the sum below `2 ^ 24` words. The bound only
counts items, never frame offsets, so it is cheap and independent of the frame layout:

* an instruction (`instWords`): the lines of its `MInst.lines` expansion — a load/store/`LoadAddr`
  with `memFinalize`'s `x16` constant (≤ 5), the LL/SC loops and the TLS sequence (≤ 7), a jump
  table (7 + its targets), the two-instruction forms (2; a `trapIf` counts its deferred `udf`), a
  `Rets` its epilogue (7), everything else 1;
* a move (`moveWords`): a slot load or store (`slotLoadAt`/`slotStoreAt`, ≤ 10 words with
  `spAddrX16`), a register-to-register move at most two of them (20);
* every block a prologue (7).

`fallthrough` only drops or merges lines and relaxation at most doubles the code
(`emitFunc_size_le`), so the code is at most `8 · spillWordBound vcp` bytes.
-/

namespace E2E
open Backend

/-- An upper bound on the words `MInst.lines` emits for an instruction, including the deferred
trap of a `trapIf`; for a `Rets`, the epilogue `lowerRFunc` puts in its place. -/
def instWords : MInst → Nat
  | .load .. | .store .. | .loadAddr .. => 5
  | .atomicRmwLoop .. | .atomicCasLoop .. | .elfTlsGetAddr .. => 7
  | .jtSequence _ ts _ _ _ => 7 + ts.length
  | .condBr .. | .testBitAndBranch .. | .tryCall .. | .trapIf .. | .loadExtNameGot ..
  | .loadExtNameNear .. => 2
  | .rets _ => 7
  | _ => 1

/-- An upper bound on the words of an `AInst`. -/
def aInstWords : AInst → Nat
  | .prologue | .epilogueRet => 7
  | .inst m => instWords m

/-- An upper bound on the words of a move (`RAFrame.moveInsts`). -/
def moveWords : Loc → Loc → Nat
  | .reg _, .reg _ => 20
  | _, _ => 10

/-- An upper bound on the words of an allocated item of block `vb`. -/
def itemWords (vb : VBlock) : RItem → Nat
  | .move s d => moveWords s d
  | .op k _ => match vb.insts[k]? with
    | some i => instWords i
    | none => 0

/-- An upper bound on the words of the code `lowerRFunc vc rf` emits (a prologue's worth per
block). -/
def rfWords (vc : VCode) (rf : RFunc) : Nat :=
  ((vc.blocks.zip rf.blocks).toList.map fun (vb, items) =>
    7 + (items.toList.map (itemWords vb)).sum).sum

/-- The word bound of the spill allocation's code. -/
def spillWordBound (vcp : VCode) : Nat := rfWords vcp (spillAlloc vcp)

/-- The size condition of the spill allocation's code: below `2 ^ 24` words, so the emitted
function (at most `8 · spillWordBound vcp` bytes) is below `2 ^ 27` bytes. -/
def spillSizeOkB (vcp : VCode) : Bool := decide (spillWordBound vcp < 2 ^ 24)

/-! ## Lines of one instruction (`MInst.lines`) -/

theorem loadConst64_length (rd : Reg) (v : Nat) : (loadConst64 rd v).length ≤ 4 := by
  unfold loadConst64
  simp only [List.length_cons]
  have := List.length_filterMap_le (fun j => if (mask64 v / 2 ^ (16 * (j + 1))) % 2 ^ 16 != 0 then
    some (Line.ins (.movk true rd ⟨(mask64 v / 2 ^ (16 * (j + 1))) % 2 ^ 16, j + 1⟩)) else none) (List.range 3)
  simp only [List.length_range] at this
  omega

theorem memFinalize_length {c : FnCtx} {m : AMode} {b : Nat} {pre : List Line} {m' : AMode}
    (h : memFinalize c m b = .ok (pre, m')) : pre.length ≤ 4 := by
  unfold memFinalize at h
  split at h <;> simp only [pure, Except.pure, Except.ok.injEq, throw, throwThe, MonadExceptOf.throw] at h
  all_goals first
    | (cases h; done)
    | ((try split at h) <;> (try split at h) <;> (try simp only [Prod.mk.injEq] at h) <;>
        obtain ⟨rfl, -⟩ := h <;> simp [loadConst64_length])

theorem memFinalize_length' {c : FnCtx} {m : AMode} {b : Nat} {v : List Line × AMode}
    (h : memFinalize c m b = .ok v) : v.1.length ≤ 4 := memFinalize_length (m' := v.2) h

theorem rmwLoopMid_length (op : AtomicRmwLoopOp) (bits : Nat) : (rmwLoopMid op bits).length ≤ 3 := by
  have : (rmwLoopSext bits).length ≤ 1 := by
    unfold rmwLoopSext; split <;> simp
  cases op <;> simp [rmwLoopMid] <;> omega

theorem rmwLoopLines_length (bits : Nat) (op : AtomicRmwLoopOp) (fl : Clif.MemFlags) (l : Lbl) :
    (rmwLoopLines bits op fl l).length ≤ 7 := by
  have := rmwLoopMid_length op bits
  simp [rmwLoopLines, rmwLoopBody]
  omega

theorem addOff_length (rd rn : Reg) (off : Int) : (MInst.lines.addOff rd rn off).length ≤ 1 := by
  unfold MInst.lines.addOff; repeat' split
  all_goals simp

/-- An instruction's lines and the trap it defers fit its word bound. -/
theorem lines_length {c : FnCtx} {m : MInst} {ps ps' : PState} {ls : List Line}
    (h : m.lines c ps = .ok (ls, ps')) : ls.length + ps'.traps.size ≤ instWords m + ps.traps.size := by
  unfold MInst.lines at h
  split at h <;> simp only [bind, Except.bind, pure, Except.pure] at h
  all_goals (repeat' (split at h))
  all_goals first
    | (simp [throw, throwThe, MonadExceptOf.throw] at *; done)
    | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
       simp [instWords]; done)
    | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
       try have := memFinalize_length' ‹memFinalize _ _ _ = _›
       simp [instWords, rmwLoopLines_length, casLoopLines, casLoopHead] <;>
         first | omega | exact Nat.add_le_add ‹_› (addOff_length _ _ _))

/-! ## The allocated code (`lowerRFunc`)

`MInst.assign` only replaces registers, so it keeps `instWords` (`assign_words`). -/

theorem visit_words {m : Type → Type} [Monad m] [LawfulMonad m] (f : OpSpec → Reg → m Reg) (i : MInst) :
    instWords <$> MInst.visitOperands f i = (fun _ => instWords i) <$> MInst.visitOperands f i := by
  cases i
  case call info =>
    obtain ⟨dest, uses, defs⟩ := info
    cases dest <;> simp [MInst.visitOperands, instWords]
  case tryCall info ti =>
    obtain ⟨dest, uses, defs⟩ := info
    cases dest <;> simp [MInst.visitOperands, instWords]
  all_goals simp [MInst.visitOperands, instWords]

theorem exceptBind_ok {ε α β : Type} {x : Except ε α} {g : α → Except ε β} {b : β}
    (h : x >>= g = .ok b) : ∃ a, x = .ok a ∧ g a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem visit_run_words {f : OpSpec → Reg → StateT Nat (Except String) Reg} {i i' : MInst} {k k' : Nat}
    (h : (MInst.visitOperands f i).run k = .ok (i', k')) : instWords i' = instWords i := by
  have := congrArg (fun x => StateT.run x k) (visit_words f i)
  simp only [StateT.run_map, h] at this
  simpa [Functor.map, Except.map] using this

theorem assign_words {i m : MInst} {regs : Array Reg} (h : i.assign regs = .ok m) :
    instWords m = instWords i := by
  unfold MInst.assign at h
  obtain ⟨⟨i', k⟩, h1, h2⟩ := exceptBind_ok h
  rw [← visit_run_words h1]
  simp only at h2
  split at h2
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h2
  · simp only [pure, Except.pure, Except.ok.injEq] at h2
    rw [h2]


theorem spAddrX16_words (off : Nat) : ((spAddrX16 off).map instWords).sum ≤ 5 := by
  unfold spAddrX16
  simp only [List.map_cons, List.map_append, List.map_map, List.sum_cons, List.sum_append]
  have : ∀ L : List (Nat × Nat), (L.map (instWords ∘ fun p => MInst.movK (.x 16) (.x 16) ⟨p.1, p.2⟩ .size64)).sum = L.length := by
    intro L; induction L <;> simp_all [instWords]; omega
  rw [this]
  have := List.length_filter_le (fun x : Nat × Nat => x.1 != 0)
    ([1, 2, 3].map fun i => ((mask64 off / 2 ^ (16 * i)) % 2 ^ 16, i))
  simp [instWords] at this ⊢
  omega

theorem slotStoreAt_words (cls : RegClass) (r : Reg) (off : Nat) :
    ((slotStoreAt cls r off).map instWords).sum ≤ 10 := by
  have := spAddrX16_words off
  unfold slotStoreAt slotStore
  split <;> cases cls <;> simp [instWords] <;> omega

theorem slotLoadAt_words (cls : RegClass) (r : Reg) (off : Nat) :
    ((slotLoadAt cls r off).map instWords).sum ≤ 10 := by
  have := spAddrX16_words off
  unfold slotLoadAt slotLoad
  split <;> cases cls <;> simp [instWords] <;> omega

theorem moveInsts_words {fr : RAFrame} {src dst : Loc} {l : List AInst}
    (h : fr.moveInsts src dst = .ok l) : (l.map aInstWords).sum ≤ moveWords src dst := by
  have hs := slotStoreAt_words
  have hl := slotLoadAt_words
  have h10 : ∀ s d, 10 ≤ moveWords s d := by intro s d; unfold moveWords; split <;> omega
  unfold RAFrame.moveInsts at h
  split at h
  · split at h <;> simp only [pure, Except.pure, Except.ok.injEq] at h <;> subst h
    · simp [aInstWords, instWords, moveWords]
    · simp only [List.map_append, List.map_map, List.sum_append, moveWords]
      have e : aInstWords ∘ AInst.inst = instWords := rfl
      rw [e]
      exact Nat.add_le_add (hs _ _ _) (hl _ _ _)
  · obtain ⟨o, -, h2⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h2
    subst h2
    rw [List.map_map]
    exact Nat.le_trans (hs _ _ _) (h10 _ _)
  · obtain ⟨o, -, h2⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h2
    subst h2
    rw [List.map_map]
    exact Nat.le_trans (hl _ _ _) (h10 _ _)
  · simp [throw, throwThe, MonadExceptOf.throw] at h


theorem itemCode_words {fr : RAFrame} {vb : VBlock} {it : RItem} {c : List AInst}
    (h : itemCode fr vb it = .ok c) : (c.map aInstWords).sum ≤ itemWords vb it := by
  unfold itemCode at h
  cases it with
  | move src dst =>
    simp only [itemStep] at h
    cases hm : fr.moveInsts src dst with
    | error e => simp [hm, bind, Except.bind, Functor.map, Except.map] at h
    | ok l =>
      simp [hm, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
      subst h
      simpa [itemWords] using moveInsts_words hm
  | op k allocs =>
    simp only [itemStep, bind, Except.bind] at h
    split at h
    · simp [Functor.map, Except.map] at h
    split at h
    · rename_i i hi
      split at h
      · simp [Functor.map, Except.map] at h
      rename_i m hm
      have hw := assign_words hm
      simp only [itemWords, hi]
      split at h <;> simp [pure, Except.pure, Functor.map, Except.map] at h <;> subst h
      all_goals (rw [← hw]; simp [aInstWords, instWords])
    · simp [Functor.map, Except.map] at h

theorem itemsCode_words {fr : RAFrame} {vb : VBlock} :
    ∀ {its : List RItem} {c : List AInst}, itemsCode fr vb its = .ok c →
      (c.map aInstWords).sum ≤ (its.map (itemWords vb)).sum
  | [], c, h => by
    simp [itemsCode, pure, Except.pure] at h; subst h; simp
  | it :: its, c, h => by
    simp only [itemsCode] at h
    obtain ⟨c1, h1, h⟩ := exceptBind_ok h
    obtain ⟨c2, h2, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have := itemCode_words h1
    have := itemsCode_words h2
    simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    omega

/-- An upper bound on the words of an allocated function's code. -/
def afWords (af : AFunc) : Nat := (af.blocks.toList.map fun b => (b.2.toList.map aInstWords).sum).sum

theorem sum_map_le_of_getElem? {α β : Type} {f : α → Nat} {g : β → Nat} :
    ∀ {l1 : List α} {l2 : List β}, l1.length = l2.length →
      (∀ (i : Nat) a b, l1[i]? = some a → l2[i]? = some b → f a ≤ g b) → (l1.map f).sum ≤ (l2.map g).sum
  | [], [], _, _ => by simp
  | a :: l1, b :: l2, hl, h => by
    simp only [List.map_cons, List.sum_cons]
    have := h 0 a b rfl rfl
    have := sum_map_le_of_getElem? (l1 := l1) (l2 := l2) (by simpa using hl)
      (fun i x y h1 h2 => h (i + 1) x y h1 h2)
    omega
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem lowerRFunc_words {vc : VCode} {rf : RFunc} {af : AFunc} (h : lowerRFunc vc rf = .ok af) :
    afWords af ≤ rfWords vc rf := by
  obtain ⟨⟨-, -, hsz, hb⟩, -, -⟩ := lowerRFunc_ok h
  unfold afWords rfWords
  apply sum_map_le_of_getElem?
  · simpa using hsz
  · intro i x y hx hy
    obtain ⟨vb, items⟩ := y
    rw [Array.getElem?_toList, Array.getElem?_zip_eq_some] at hy
    obtain ⟨code, hc, ha⟩ := hb i vb items hy.1 hy.2
    rw [Array.getElem?_toList, ha] at hx
    cases hx
    have := itemsCode_words hc
    simp only [List.map_append, List.sum_append]
    split <;> simp [aInstWords] <;> omega

/-! ## The lines before relaxation (`emitPre`)

`fallthrough` (`ftList`) only drops lines or merges two into one; labels are empty. -/

/-- The byte size of a line list. -/
def linesBytes (L : List Line) : Nat := (L.map Line.size).sum

theorem linesBytes_le_length : ∀ L : List Line, linesBytes L ≤ 4 * L.length
  | [] => by simp [linesBytes]
  | ln :: L => by
    have := linesBytes_le_length L
    have : ln.size ≤ 4 := by cases ln <;> simp [Line.size]
    simp only [linesBytes, List.map_cons, List.sum_cons, List.length_cons] at *
    omega

theorem linesBytes_drop (j : Nat) (L : List Line) : linesBytes (L.drop j) ≤ linesBytes L := by
  have := congrArg linesBytes (List.take_append_drop j L)
  simp only [linesBytes, List.map_append, List.sum_append] at this ⊢
  omega

theorem ftStep_size (ln : Line) (n1 n2 : Option Line) : linesBytes (ftStep ln n1 n2).1 ≤ ln.size := by
  unfold ftStep
  repeat' split
  all_goals first | (simp [linesBytes]; done) | simp [linesBytes, Line.size]

theorem ftList_size : ∀ (n : Nat) (L : List Line), L.length ≤ n → linesBytes (ftList L) ≤ linesBytes L
  | _, [], _ => by simp [ftList, linesBytes]
  | 0, _ :: _, hl => by simp at hl
  | n + 1, ln :: rest, hl => by
    rw [ftList_cons]
    have hp := (ftStep_pos ln rest[0]? rest[1]?).1
    have hs := ftStep_size ln rest[0]? rest[1]?
    generalize (ftStep ln rest[0]? rest[1]?) = st at hp hs
    obtain ⟨out, k⟩ := st
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by simp at hp; omega⟩
    simp only [List.drop_succ_cons] at *
    have ih := ftList_size n (rest.drop j) (by simp at hl ⊢; omega)
    have := linesBytes_drop j rest
    simp only [linesBytes, List.map_append, List.sum_append, List.map_cons, List.sum_cons] at *
    omega

theorem prologueLines_length (n : Nat) : (prologueLines n).length ≤ 7 := by
  have := loadConst64_length (.x 16) n
  unfold prologueLines
  repeat' split
  all_goals simp
  omega

theorem epilogueLines_length (n : Nat) : (epilogueLines n).length ≤ 7 := by
  have := loadConst64_length (.x 16) n
  unfold epilogueLines
  repeat' split
  all_goals simp
  omega

theorem ainstLines_length {c : FnCtx} {af : AFunc} {a : AInst} {ps ps' : PState} {ls : List Line}
    (h : ainstLines c af a ps = .ok (ls, ps')) :
    ls.length + ps'.traps.size ≤ aInstWords a + ps.traps.size := by
  cases a with
  | inst m => exact lines_length h
  | prologue =>
    simp only [ainstLines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have := prologueLines_length af.frameSize
    split <;> simp [aInstWords] <;> omega
  | epilogueRet =>
    simp only [ainstLines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have := epilogueLines_length af.frameSize
    split <;> simp [aInstWords] <;> omega

theorem codeLinesE_length {c : FnCtx} {af : AFunc} :
    ∀ {code : List AInst} {ps ps' : PState} {ls : List Line},
      codeLinesE c af code ps = .ok (ls, ps') →
        ls.length + ps'.traps.size ≤ (code.map aInstWords).sum + ps.traps.size
  | [], ps, ps', ls, h => by
    simp only [codeLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | a :: as, ps, ps', ls, h => by
    simp only [codeLinesE] at h
    obtain ⟨⟨l1, ps1⟩, h1, h⟩ := exceptBind_ok h
    obtain ⟨⟨l2, ps2⟩, h2, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have := ainstLines_length h1
    have := codeLinesE_length h2
    simp only [List.length_append, List.map_cons, List.sum_cons] at *
    omega

theorem blocksLinesE_size {c : FnCtx} {af : AFunc} :
    ∀ {bs : List (Label × Array AInst)} {ps ps' : PState} {ls : List Line},
      blocksLinesE c af bs ps = .ok (ls, ps') →
        linesBytes ls + 4 * ps'.traps.size ≤
          4 * (bs.map fun b => (b.2.toList.map aInstWords).sum).sum + 4 * ps.traps.size
  | [], ps, ps', ls, h => by
    simp only [blocksLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [linesBytes]
  | (l, code) :: bs, ps, ps', ls, h => by
    simp only [blocksLinesE] at h
    obtain ⟨⟨l1, ps1⟩, h1, h⟩ := exceptBind_ok h
    obtain ⟨⟨l2, ps2⟩, h2, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have := codeLinesE_length h1
    have := linesBytes_le_length l1
    have := blocksLinesE_size h2
    simp only [linesBytes, List.map_cons, List.map_append, List.sum_append, List.sum_cons, Line.size] at *
    omega

/-- `emitPre`'s lines are at most `4 · afWords af` bytes. -/
theorem emitPre_size {k : Nat} {af : AFunc} {pre : Array Line} (h : emitPre k af = .ok pre) :
    linesBytes pre.toList ≤ 4 * afWords af := by
  obtain ⟨body, ps, hb, rfl⟩ := emitPre_ok h
  have h1 := blocksLinesE_size hb
  have h2 := ftList_size body.length body (Nat.le_refl _)
  have h3 : ∀ ts : List (Lbl × Clif.TrapCode),
      linesBytes (ts.flatMap fun p => [Line.label p.1, Line.ins (.udf 0xc11f) (some p.2)]) = 4 * ts.length := by
    intro ts; induction ts <;> simp_all [linesBytes, Line.size]; omega
  simp only [linesBytes, List.map_append, List.sum_append] at *
  rw [h3, Array.length_toList]
  simp only [afWords]
  simp at h1
  omega

/-! ## The bound -/

/-- The code `emitFunc` produces from any allocation `rf` `lowerRFunc` lowers is at most
`8 · rfWords vc rf` bytes (4 per word; relaxation at most doubles it, `emitFunc_size_le`). -/
theorem emitFunc_size_rf {vc : VCode} {rf : RFunc} {af : AFunc} {k : Nat} {fa : FnAsm}
    (ha : lowerRFunc vc rf = .ok af) (he : emitFunc k af = .ok fa) :
    fa.size ≤ 8 * rfWords vc rf := by
  obtain ⟨pre, hp, -⟩ := emitFunc_unfold he
  have h1 := emitFunc_size_le he hp
  have h2 := emitPre_size hp
  have h3 := lowerRFunc_words ha
  simp only [linesBytes] at h2
  omega

/-- **The spill allocation's code fits the `b` range**: under the size condition
`spillSizeOkB vcp`, the code of the spill allocation is below `2 ^ 27` bytes. -/
theorem emitFunc_spill_size {vcp : VCode} {af : AFunc} {k : Nat} {fa : FnAsm}
    (hsz : spillSizeOkB vcp = true) (ha : lowerRFunc vcp (spillAlloc vcp) = .ok af)
    (he : emitFunc k af = .ok fa) : fa.size < 2 ^ 27 := by
  have h1 := emitFunc_size_rf ha he
  have h2 : spillWordBound vcp < 2 ^ 24 := by simpa [spillSizeOkB] using hsz
  unfold spillWordBound at h2
  omega

end E2E
