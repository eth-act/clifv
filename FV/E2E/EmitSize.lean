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
  `Rets` its epilogue (7 besides the pops of the saved registers), everything else 1;
* a move (`moveWords`): a slot load or store (`slotLoadAt`/`slotStoreAt`, ≤ 10 words with
  `spAddrX16`), a register-to-register move at most two of them (20); a save or a restore emits
  nothing, its 10 words pay for its push in the prologue or its pop in the epilogue;
* every block a prologue (7 besides the pushes).

`fallthrough` only drops or merges lines, and relaxation at most doubles the code plus 12 bytes
of literal pool per literal load (`emitFunc_size_le`); a literal load is the one line of a
five-word `FpuLoad` (`lines_lit`), so the code is at most `8 · spillWordBound vcp` bytes.

An `ldr (literal)` reaches ±1 MiB and the pool follows the function's body, so `spillSizeOkB`
also requires the bound below `2 ^ 17` words when the VCode has a literal-pool load
(`poolReachB`, #565). Cranelift instead emits a constant island inside such a function; one over
1 MiB with a pool load falls back to cg_clif's code (Cranelift's).
-/

namespace E2E
open Backend

/-- An upper bound on the words `MInst.lines` emits for an instruction, including the deferred
trap of a `trapIf`; for a `Rets`, the epilogue `lowerRFunc` puts in its place. -/
def instWords : MInst → Nat
  | .load .. | .store .. | .loadAddr .. | .fpuLoad .. | .fpuStore .. => 5
  | .atomicRmwLoop .. | .atomicCasLoop .. | .elfTlsGetAddr .. => 7
  | .jtSequence _ ts _ _ _ => 7 + ts.length
  | .condBr .. | .testBitAndBranch .. | .tryCall .. | .trapIf .. | .loadExtNameGot ..
  | .loadExtNameNear .. => 2
  | .rets _ => 7
  | _ => 1

/-- An upper bound on the words of an `AInst` of a function saving `n` registers: the prologue
and the epilogue push/pop at most one register per instruction. -/
def aInstWords (n : Nat) : AInst → Nat
  | .prologue | .epilogueRet => 7 + n
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

/-- The literal-pool load (an `FpuLoad` of a constant-pool entry, #565): the one instruction whose
lines contain an `ldr (literal)` (`lines_lit_zero`). -/
def _root_.Backend.MInst.isLitLoad : MInst → Bool
  | .fpuLoad _ _ (.const _) _ => true
  | _ => false

/-- No literal-pool load in the VCode. -/
def _root_.Backend.VCode.noPoolB (vc : VCode) : Bool :=
  vc.blocks.toList.all fun vb => vb.insts.toList.all fun i => !i.isLitLoad

/-- The literal loads reach their pool entries: the code is below 1 MiB (`2 ^ 17` words, the
reach of an `ldr (literal)`) or has no literal-pool load (#565). -/
def poolReachB (vcp : VCode) : Bool := decide (spillWordBound vcp < 2 ^ 17) || vcp.noPoolB

/-- The size condition of the spill allocation's code: below `2 ^ 24` words, so the emitted
function (at most `8 · spillWordBound vcp` bytes) is below `2 ^ 27` bytes, and its literal loads
reach the pool (`poolReachB`). -/
def spillSizeOkB (vcp : VCode) : Bool := decide (spillWordBound vcp < 2 ^ 24) && poolReachB vcp

theorem spillSizeOkB_bound {vcp : VCode} (h : spillSizeOkB vcp = true) :
    spillWordBound vcp < 2 ^ 24 := by
  simp only [spillSizeOkB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem spillSizeOkB_reach {vcp : VCode} (h : spillSizeOkB vcp = true) : poolReachB vcp = true := by
  simp only [spillSizeOkB, Bool.and_eq_true] at h
  exact h.2

theorem spillSizeOkB_of {vcp : VCode} (h1 : spillWordBound vcp < 2 ^ 24)
    (h2 : poolReachB vcp = true) : spillSizeOkB vcp = true := by
  simp [spillSizeOkB, h1, h2]

/-- `poolReachB` of a VCode without literal-pool load. -/
theorem poolReachB_of_noPool {vcp : VCode} (h : vcp.noPoolB = true) : poolReachB vcp = true := by
  simp [poolReachB, h]

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

/-! ### Literal-pool loads (`Line.isLit`)

Only the `FpuLoad` of a constant-pool entry emits a literal load (`fpuLoadLit`, one line); its
five-word bound also pays for the pool entry `emitFunc_size_le` charges it (`lines_lit`). -/

theorem loadConst64_lit (rd : Reg) (v : Nat) : (loadConst64 rd v).countP Line.isLit = 0 := by
  unfold loadConst64
  rw [List.countP_cons, List.countP_eq_zero.2]
  · simp [Line.isLit]
  · intro x hx
    obtain ⟨j, -, hj⟩ := List.mem_filterMap.1 hx
    dsimp only at hj
    split at hj
    · cases hj; simp [Line.isLit]
    · cases hj

theorem memFinalize_lit {c : FnCtx} {m : AMode} {b : Nat} {v : List Line × AMode}
    (h : memFinalize c m b = .ok v) : v.1.countP Line.isLit = 0 := by
  obtain ⟨pre, m'⟩ := v
  unfold memFinalize at h
  split at h <;> simp only [pure, Except.pure, Except.ok.injEq, throw, throwThe, MonadExceptOf.throw] at h
  all_goals first
    | (cases h; done)
    | ((try split at h) <;> (try split at h) <;> (try simp only [Prod.mk.injEq] at h) <;>
        obtain ⟨rfl, -⟩ := h <;> simp [loadConst64_lit])

theorem rmwLoopLines_lit (bits : Nat) (op : AtomicRmwLoopOp) (fl : Clif.MemFlags) (l : Lbl) :
    (rmwLoopLines bits op fl l).countP Line.isLit = 0 := by
  have hc : ∀ t, Line.isLit (.ins (rmwLoopCmp op bits) t) = false := by
    intro t; unfold rmwLoopCmp; split <;> rfl
  have hs : ((rmwLoopSext bits).map fun i => Line.ins i).countP Line.isLit = 0 := by
    unfold rmwLoopSext; split <;> simp [Line.isLit]
  cases op <;> simp_all [rmwLoopLines, rmwLoopBody, rmwLoopMid, Line.isLit]

theorem casLoopCmp_lit (bits : Nat) (t : Option Clif.TrapCode) :
    Line.isLit (.ins (casLoopCmp bits) t) = false := by
  unfold casLoopCmp; repeat' split
  all_goals rfl

theorem casLoopLines_lit (bits : Nat) (fl : Clif.MemFlags) (again out : Lbl) :
    (casLoopLines bits fl again out).countP Line.isLit = 0 := by
  simp only [casLoopLines, casLoopHead, List.countP_cons, List.countP_append, List.countP_nil,
    casLoopCmp_lit]
  simp [Line.isLit]

theorem addOff_lit (rd rn : Reg) (off : Int) : (MInst.lines.addOff rd rn off).countP Line.isLit = 0 := by
  unfold MInst.lines.addOff; repeat' split
  all_goals simp [Line.isLit]

/-- Only the `FpuLoad` of a constant-pool entry emits a literal load. -/
theorem lines_lit_zero {c : FnCtx} {m : MInst} {ps ps' : PState} {ls : List Line}
    (hm : ∀ s rd cst fl, m ≠ .fpuLoad s rd (.const cst) fl)
    (h : m.lines c ps = .ok (ls, ps')) : ls.countP Line.isLit = 0 := by
  unfold MInst.lines at h
  split at h <;> simp only [bind, Except.bind, pure, Except.pure] at h
  all_goals (repeat' (split at h))
  all_goals first
    | (simp [throw, throwThe, MonadExceptOf.throw] at *; done)
    | (exact absurd rfl (hm _ _ _ _))
    | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
       try have := memFinalize_lit ‹memFinalize _ _ _ = _›
       (try cases ‹CondBrKind›) <;>
         simp_all [Line.isLit, CondBrKind.insn, List.countP_map, Function.comp_def,
           rmwLoopLines_lit, casLoopLines_lit, addOff_lit])

/-- An instruction's lines, twice its literal loads and the trap it defers fit its word bound. -/
theorem lines_lit {c : FnCtx} {m : MInst} {ps ps' : PState} {ls : List Line}
    (h : m.lines c ps = .ok (ls, ps')) :
    ls.length + 2 * ls.countP Line.isLit + ps'.traps.size ≤ instWords m + ps.traps.size := by
  have hl := lines_length h
  by_cases hm : ∃ s rd cst fl, m = .fpuLoad s rd (.const cst) fl
  · obtain ⟨s, rd, cst, fl, rfl⟩ := hm
    simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [instWords, Line.isLit]
  · have := lines_lit_zero (fun s rd cst fl he => hm ⟨s, rd, cst, fl, he⟩) h
    omega

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

theorem moveInsts_words {fr : RAFrame} {src dst : Loc} {l : List AInst} (n : Nat)
    (h : fr.moveInsts src dst = .ok l) : (l.map (aInstWords n)).sum ≤ moveWords src dst := by
  have hs := slotStoreAt_words
  have hl := slotLoadAt_words
  have h10 : ∀ s d, 10 ≤ moveWords s d := by intro s d; unfold moveWords; split <;> omega
  unfold RAFrame.moveInsts at h
  split at h
  all_goals first
    | (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; simp; done)
    | skip
  · split at h <;> simp only [pure, Except.pure, Except.ok.injEq] at h <;> subst h
    · simp [aInstWords, instWords, moveWords]
    · simp only [List.map_append, List.map_map, List.sum_append, moveWords]
      have e : aInstWords n ∘ AInst.inst = instWords := rfl
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


/-- Whether an instruction is a `Rets`. -/
def retsB : MInst → Bool
  | .rets _ => true
  | _ => false

theorem visit_retsB {m : Type → Type} [Monad m] [LawfulMonad m] (f : OpSpec → Reg → m Reg) (i : MInst) :
    retsB <$> MInst.visitOperands f i = (fun _ => retsB i) <$> MInst.visitOperands f i := by
  cases i
  case call info =>
    obtain ⟨dest, uses, defs⟩ := info
    cases dest <;> simp [MInst.visitOperands, retsB]
  case tryCall info ti =>
    obtain ⟨dest, uses, defs⟩ := info
    cases dest <;> simp [MInst.visitOperands, retsB]
  all_goals simp [MInst.visitOperands, retsB]

theorem visit_run_retsB {f : OpSpec → Reg → StateT Nat (Except String) Reg} {i i' : MInst} {k k' : Nat}
    (h : (MInst.visitOperands f i).run k = .ok (i', k')) : retsB i' = retsB i := by
  have := congrArg (fun x => StateT.run x k) (visit_retsB f i)
  simp only [StateT.run_map, h] at this
  simpa [Functor.map, Except.map] using this

/-- `MInst.assign` keeps a `Rets` a `Rets` (and anything else not one). -/
theorem assign_rets {i : MInst} {regs : Array Reg} {us : List (Reg × Reg)}
    (h : i.assign regs = .ok (.rets us)) : ∃ us', i = .rets us' := by
  unfold MInst.assign at h
  obtain ⟨⟨i', k⟩, h1, h2⟩ := exceptBind_ok h
  have hv := visit_run_retsB h1
  simp only at h2
  split at h2
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h2
  · simp only [pure, Except.pure, Except.ok.injEq] at h2
    subst h2
    cases i <;> simp_all [retsB]

/-- The restores (moves out of a save slot into their register) among `L`. -/
def cntR (L : List RItem) : Nat := (L.filter fun it => it.restoreReg.isSome && it.isRestore).length

theorem cntR_append (A B : List RItem) : cntR (A ++ B) = cntR A + cntR B := by
  simp [cntR, List.filter_append]

/-- A return tail restores every saved register. -/
theorem retTailOk_len (saved : List Reg) : ∀ (done : List Reg) (L : List RItem),
    retTailOk saved done L = true → saved.length ≤ done.length + cntR L
  | done, [], h => by
    simp only [retTailOk] at h
    have := List.length_eq_of_beq h
    simp [cntR]; omega
  | done, it :: L, h => by
    rw [retTailOk] at h
    split at h
    · rename_i r h1 h2
      simp only [Bool.and_eq_true] at h
      have := retTailOk_len saved (done ++ [r]) L h.2
      have hc : cntR (it :: L) = cntR L + 1 := by
        simp [cntR, List.filter_cons, h1, h2]
      simp only [List.length_append, List.length_singleton] at this
      omega
    · simp only [Bool.and_eq_true] at h
      have := retTailOk_len saved done L h.2
      have hc : cntR L ≤ cntR (it :: L) := by
        simp only [cntR, List.filter_cons]; split <;> simp
      omega

theorem itemCode_words {fr : RAFrame} {vb : VBlock} {it : RItem} {c : List AInst} (n : Nat)
    (h : itemCode fr vb it = .ok c) :
    (c.map (aInstWords n)).sum ≤ itemWords vb it + (match it with
      | .op k _ => if (vb.insts[k]? matches some (.rets _)) then n else 0
      | .move _ _ => 0) := by
  unfold itemCode at h
  cases it with
  | move src dst =>
    simp only [itemStep] at h
    cases hm : fr.moveInsts src dst with
    | error e => simp [hm, bind, Except.bind, Functor.map, Except.map] at h
    | ok l =>
      simp [hm, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h
      subst h
      simpa [itemWords] using moveInsts_words n hm
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
      · simp
      · rename_i us
        obtain ⟨us', rfl⟩ := assign_rets hm
        simp [aInstWords, instWords]
      · rw [← hw]; simp [aInstWords]
    · simp [Functor.map, Except.map] at h

/-- The code of the items `its` of a block passing `saveSegsOk` (`pend` the moves since the last
instruction): every epilogue's pops are paid by the restores before it (10 words each). -/
theorem itemsCode_words {fr : RAFrame} {vb : VBlock} {saved : List Reg} :
    ∀ {pend its : List RItem} {c : List AInst}, saveSegsOk vb saved pend its = true →
      itemsCode fr vb its = .ok c →
      (c.map (aInstWords saved.length)).sum ≤ (its.map (itemWords vb)).sum + 10 * cntR pend
  | _, [], c, _, h => by
    simp [itemsCode, pure, Except.pure] at h; subst h; simp
  | pend, it :: its, c, hs, h => by
    simp only [itemsCode] at h
    obtain ⟨c1, h1, h⟩ := exceptBind_ok h
    obtain ⟨c2, h2, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hc1 := itemCode_words saved.length h1
    cases it with
    | move a b =>
      simp only [saveSegsOk] at hs
      have ih := itemsCode_words hs h2
      rw [cntR_append] at ih
      simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      simp only [Nat.add_zero] at hc1
      by_cases hr : ((RItem.move a b).restoreReg.isSome && (RItem.move a b).isRestore) = true
      · -- a restore: no code, 10 words
        obtain ⟨r, rfl⟩ : ∃ r, a = .save r := by
          cases a <;> simp_all [RItem.restoreReg]
        have hc0 : c1 = [] := by
          unfold itemCode itemStep at h1
          cases b <;> simp [RAFrame.moveInsts, bind, Except.bind, pure, Except.pure, Functor.map,
            Except.map] at h1 <;> first | exact h1 | exact h1.symm
        have h1' : cntR [RItem.move (.save r) b] = 1 := by simp [cntR, hr]
        have hmw : itemWords vb (.move (.save r) b) = 10 := by
          simp [itemWords, moveWords]
        subst hc0
        simp only [List.map_nil, List.sum_nil, hmw] at ih ⊢
        rw [h1'] at ih
        omega
      · have h1' : cntR [RItem.move a b] = 0 := by simp [cntR, hr]
        rw [h1'] at ih
        omega
    | op k allocs =>
      simp only [saveSegsOk, Bool.and_eq_true] at hs
      have ih := itemsCode_words hs.2 h2
      simp only [cntR, List.filter_nil, List.length_nil, Nat.mul_zero, Nat.add_zero] at ih
      have hpay : (if (vb.insts[k]? matches some (.rets _)) then saved.length else 0) ≤
          10 * cntR pend := by
        by_cases hk : (vb.insts[k]? matches some (.rets _)) = true
        · rw [if_pos hk]
          obtain ⟨us, hus⟩ : ∃ us, vb.insts[k]? = some (.rets us) := by
            revert hk
            cases vb.insts[k]? with
            | none => simp
            | some i => cases i <;> simp
          simp only [hus, ite_true] at hs
          have := retTailOk_len saved [] pend hs.1
          simp only [List.length_nil, Nat.zero_add] at this; omega
        · rw [if_neg hk]; exact Nat.zero_le _
      simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons] at hc1 ⊢
      omega

/-- The saves of block 0 emit no code. -/
theorem itemsCode_saves {fr : RAFrame} {vb : VBlock} : ∀ (rs : List Reg) (L : List RItem) {c : List AInst},
    itemsCode fr vb (rs.map (fun r => RItem.move (.reg r) (.save r)) ++ L) = .ok c →
    itemsCode fr vb L = .ok c
  | [], L, c, h => by simpa using h
  | r :: rs, L, c, h => by
    simp only [List.map_cons, List.cons_append, itemsCode] at h
    obtain ⟨c1, h1, h⟩ := exceptBind_ok h
    obtain ⟨c2, h2, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hc0 : c1 = [] := by
      unfold itemCode itemStep at h1
      simp [RAFrame.moveInsts, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h1
      first | exact h1.symm | exact h1
    subst hc0
    simpa using itemsCode_saves rs L h2

theorem saveItems_words (vb : VBlock) (rs : List Reg) :
    ((rs.map (fun r => RItem.move (.reg r) (.save r))).map (itemWords vb)).sum = 10 * rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [itemWords, moveWords] at ih ⊢; omega

/-- An upper bound on the words of an allocated function's code. -/
def afWords (af : AFunc) : Nat :=
  (af.blocks.toList.map fun b => (b.2.toList.map (aInstWords af.saves.length)).sum).sum

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
  obtain ⟨hsh, hsv⟩ := lowerRFunc_saves h
  unfold afWords rfWords
  rw [hsv]
  apply sum_map_le_of_getElem?
  · simpa using hsz
  · intro i x y hx hy
    obtain ⟨vb, items⟩ := y
    rw [Array.getElem?_toList, Array.getElem?_zip_eq_some] at hy
    obtain ⟨code, hc, ha⟩ := hb i vb items hy.1 hy.2
    rw [Array.getElem?_toList, ha] at hx
    cases hx
    obtain ⟨h0, h1⟩ := saveShapeOk_block hsh hy.1 hy.2
    by_cases hi : i = 0
    · subst hi
      obtain ⟨htake, hseg⟩ := h0 rfl
      have hsplit := List.take_append_drop rf.saved.length items.toList
      rw [htake] at hsplit
      rw [← hsplit] at hc
      have hw := itemsCode_words hseg (itemsCode_saves _ _ hc)
      have hW : (items.toList.map (itemWords vb)).sum =
          10 * rf.saved.length + ((items.toList.drop rf.saved.length).map (itemWords vb)).sum := by
        have := congrArg (fun l => (l.map (itemWords vb)).sum) hsplit
        simp only [List.map_append, List.sum_append, saveItems_words] at this
        omega
      simp only [cntR, List.filter_nil, List.length_nil, Nat.mul_zero, Nat.add_zero] at hw
      simp only [ite_true, List.toList_toArray, List.map_append, List.sum_append, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, aInstWords, hW]
      omega
    · have hw := itemsCode_words (h1 hi) hc
      simp only [cntR, List.filter_nil, List.length_nil, Nat.mul_zero, Nat.add_zero] at hw
      simp only [hi, ite_false, List.toList_toArray, List.nil_append]
      omega

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

theorem isLit_invertTo (c : Insn) (e : Lbl) (t : Option Clif.TrapCode) :
    Line.isLit (.ins (c.invertTo e) t) = Line.isLit (.ins c t) := by
  unfold Insn.invertTo; split <;> rfl

/-- `fallthrough` adds no literal load: it drops a `b` or inverts a conditional branch. -/
theorem ftStep_lit (ln : Line) (n1 n2 : Option Line) :
    (ftStep ln n1 n2).1.countP Line.isLit ≤ [ln].countP Line.isLit := by
  unfold ftStep
  repeat' split
  all_goals first | (simp [isLit_invertTo]; done) | simp_all

theorem ftList_lit : ∀ (n : Nat) (L : List Line), L.length ≤ n →
    (ftList L).countP Line.isLit ≤ L.countP Line.isLit
  | _, [], _ => by simp [ftList]
  | 0, _ :: _, hl => by simp at hl
  | n + 1, ln :: rest, hl => by
    rw [ftList_cons]
    have hp := (ftStep_pos ln rest[0]? rest[1]?).1
    have hs := ftStep_lit ln rest[0]? rest[1]?
    generalize (ftStep ln rest[0]? rest[1]?) = st at hp hs
    obtain ⟨out, k⟩ := st
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by simp at hp; omega⟩
    simp only [List.drop_succ_cons] at *
    have ih := ftList_lit n (rest.drop j) (by simp at hl ⊢; omega)
    have := (List.drop_sublist j rest).countP_le (p := Line.isLit)
    rw [show ln :: rest = [ln] ++ rest from rfl, List.countP_append, List.countP_append]
    omega

theorem pairsOf_count : ∀ rs : List Reg,
    (pairsOf rs).1.length + (if (pairsOf rs).2.isSome then 1 else 0) ≤ rs.length
  | [] => by simp [pairsOf]
  | [_] => by simp [pairsOf]
  | a :: b :: rs => by
    have := pairsOf_count rs
    rcases h : pairsOf rs with ⟨ps, o⟩
    rw [h] at this
    simp only [pairsOf, h, List.length_cons] at this ⊢
    omega

theorem pushLines_length (int : Bool) (rs : List Reg) : (pushLines int rs).length ≤ rs.length := by
  have := pairsOf_count rs
  unfold pushLines
  rcases h : pairsOf rs with ⟨ps, _ | r⟩ <;> simp_all <;> omega

theorem popLines_length (int : Bool) (rs : List Reg) : (popLines int rs).length ≤ rs.length := by
  have := pairsOf_count rs
  unfold popLines
  rcases h : pairsOf rs with ⟨ps, _ | r⟩ <;> simp_all <;> omega

theorem spAdjLines_length (sub : Bool) (size : Nat) : (spAdjLines sub size).length ≤ 5 := by
  have := loadConst64_length (.x 16) size
  unfold spAdjLines
  split
  · simp
  · split
    · simp
    · simp only [List.length_append, List.length_singleton]; omega

theorem saves_split : ∀ saves : List Reg,
    (savesInt saves).length + (savesFloat saves).length ≤ saves.length
  | [] => by simp [savesInt, savesFloat]
  | r :: rs => by
    have := saves_split rs
    cases r <;> simp_all [savesInt, savesFloat, List.filter_cons] <;> omega

/-- The prologue: fp/lr, x29, at most one push per saved register, the `sp` adjustment. -/
theorem prologueLines_length (saves : List Reg) (n : Nat) :
    (prologueLines saves n).length ≤ 7 + saves.length := by
  have := pushLines_length true (savesInt saves)
  have := pushLines_length false (savesFloat saves)
  have := spAdjLines_length true (n - clobberBytes saves)
  have := saves_split saves
  simp only [prologueLines, List.length_append, List.length_cons, List.length_nil]
  omega

theorem epilogueLines_length (saves : List Reg) (n : Nat) :
    (epilogueLines saves n).length ≤ 7 + saves.length := by
  have := popLines_length true (savesInt saves)
  have := popLines_length false (savesFloat saves)
  have := spAdjLines_length false (n - clobberBytes saves)
  have := saves_split saves
  simp only [epilogueLines, List.length_append, List.length_cons, List.length_nil]
  omega

theorem pushLines_lit (int : Bool) (rs : List Reg) : (pushLines int rs).countP Line.isLit = 0 := by
  unfold pushLines
  rcases pairsOf rs with ⟨ps, _ | r⟩ <;> cases int <;> simp [List.countP_eq_zero, Line.isLit]

theorem popLines_lit (int : Bool) (rs : List Reg) : (popLines int rs).countP Line.isLit = 0 := by
  unfold popLines
  rcases pairsOf rs with ⟨ps, _ | r⟩ <;> cases int <;> simp [List.countP_eq_zero, Line.isLit]

theorem spAdjLines_lit (sub : Bool) (size : Nat) : (spAdjLines sub size).countP Line.isLit = 0 := by
  have := loadConst64_lit (.x 16) size
  unfold spAdjLines
  repeat' split
  all_goals simp [List.countP_append, Line.isLit, this]

theorem prologueLines_lit (saves : List Reg) (n : Nat) :
    (prologueLines saves n).countP Line.isLit = 0 := by
  simp [prologueLines, List.countP_append, pushLines_lit, spAdjLines_lit, Line.isLit]

theorem epilogueLines_lit (saves : List Reg) (n : Nat) :
    (epilogueLines saves n).countP Line.isLit = 0 := by
  simp [epilogueLines, List.countP_append, popLines_lit, spAdjLines_lit, Line.isLit]

theorem ainstLines_length {c : FnCtx} {af : AFunc} {a : AInst} {ps ps' : PState} {ls : List Line}
    (h : ainstLines c af a ps = .ok (ls, ps')) :
    ls.length + ps'.traps.size ≤ aInstWords af.saves.length a + ps.traps.size := by
  cases a with
  | inst m => exact lines_length h
  | prologue =>
    simp only [ainstLines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have := prologueLines_length af.saves af.frameSize
    split <;> simp [aInstWords] <;> omega
  | epilogueRet =>
    simp only [ainstLines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have := epilogueLines_length af.saves af.frameSize
    split <;> simp [aInstWords] <;> omega

theorem ainstLines_lit {c : FnCtx} {af : AFunc} {a : AInst} {ps ps' : PState} {ls : List Line}
    (h : ainstLines c af a ps = .ok (ls, ps')) :
    ls.length + 2 * ls.countP Line.isLit + ps'.traps.size ≤
      aInstWords af.saves.length a + ps.traps.size := by
  cases a with
  | inst m => exact lines_lit h
  | prologue =>
    simp only [ainstLines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have := prologueLines_length af.saves af.frameSize
    split <;> simp [aInstWords, prologueLines_lit] <;> omega
  | epilogueRet =>
    simp only [ainstLines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have := epilogueLines_length af.saves af.frameSize
    split <;> simp [aInstWords, epilogueLines_lit, Line.isLit] <;> omega

theorem codeLinesE_length {c : FnCtx} {af : AFunc} :
    ∀ {code : List AInst} {ps ps' : PState} {ls : List Line},
      codeLinesE c af code ps = .ok (ls, ps') →
        ls.length + ps'.traps.size ≤ (code.map (aInstWords af.saves.length)).sum + ps.traps.size
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

theorem codeLinesE_lit {c : FnCtx} {af : AFunc} :
    ∀ {code : List AInst} {ps ps' : PState} {ls : List Line},
      codeLinesE c af code ps = .ok (ls, ps') →
        ls.length + 2 * ls.countP Line.isLit + ps'.traps.size ≤
          (code.map (aInstWords af.saves.length)).sum + ps.traps.size
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
    have := ainstLines_lit h1
    have := codeLinesE_lit h2
    simp only [List.length_append, List.countP_append, List.map_cons, List.sum_cons] at *
    omega

theorem blocksLinesE_size {c : FnCtx} {af : AFunc} :
    ∀ {bs : List (Label × Array AInst)} {ps ps' : PState} {ls : List Line},
      blocksLinesE c af bs ps = .ok (ls, ps') →
        linesBytes ls + 4 * ps'.traps.size ≤
          4 * (bs.map fun b => (b.2.toList.map (aInstWords af.saves.length)).sum).sum + 4 * ps.traps.size
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

/-- `blocksLinesE_size` with the literal loads: each costs at most the 8 bytes its pool entry
adds beyond the doubled code. -/
theorem blocksLinesE_lit {c : FnCtx} {af : AFunc} :
    ∀ {bs : List (Label × Array AInst)} {ps ps' : PState} {ls : List Line},
      blocksLinesE c af bs ps = .ok (ls, ps') →
        linesBytes ls + 8 * ls.countP Line.isLit + 4 * ps'.traps.size ≤
          4 * (bs.map fun b => (b.2.toList.map (aInstWords af.saves.length)).sum).sum +
            4 * ps.traps.size
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
    have := codeLinesE_lit h1
    have := linesBytes_le_length l1
    have := blocksLinesE_lit h2
    have hl : Line.isLit (.label (.block l)) = false := rfl
    simp only [linesBytes, List.map_cons, List.map_append, List.sum_append, List.sum_cons, Line.size,
      List.countP_cons, List.countP_append, hl, Bool.false_eq_true, ↓reduceIte] at *
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

/-- `emitPre`'s lines with 8 bytes per literal load are at most `4 · afWords af` bytes. -/
theorem emitPre_size_lit {k : Nat} {af : AFunc} {pre : Array Line} (h : emitPre k af = .ok pre) :
    linesBytes pre.toList + 8 * pre.toList.countP Line.isLit ≤ 4 * afWords af := by
  obtain ⟨body, ps, hb, rfl⟩ := emitPre_ok h
  have h1 := blocksLinesE_lit hb
  have h2 := ftList_size body.length body (Nat.le_refl _)
  have h2' := ftList_lit body.length body (Nat.le_refl _)
  have h3 : ∀ ts : List (Lbl × Clif.TrapCode),
      linesBytes (ts.flatMap fun p => [Line.label p.1, Line.ins (.udf 0xc11f) (some p.2)]) = 4 * ts.length := by
    intro ts; induction ts <;> simp_all [linesBytes, Line.size]; omega
  have h4 : ∀ ts : List (Lbl × Clif.TrapCode),
      (ts.flatMap fun p => [Line.label p.1, Line.ins (.udf 0xc11f) (some p.2)]).countP Line.isLit = 0 := by
    intro ts; induction ts with
    | nil => rfl
    | cons p ts ih => rw [List.flatMap_cons, List.countP_append, ih]; simp [Line.isLit]
  simp only [linesBytes, List.map_append, List.sum_append, List.countP_append] at *
  rw [h3, h4, Array.length_toList]
  simp only [afWords]
  simp at h1
  omega

/-! ### No literal-pool load, no literal line (`emitPre_lit0`) -/

/-- No literal-pool load among the allocated function's instructions. -/
def _root_.Backend.AFunc.NoLit (af : AFunc) : Prop :=
  ∀ p ∈ af.blocks.toList, ∀ m, AInst.inst m ∈ p.2.toList → m.isLitLoad = false

theorem lines_lit_of {c : FnCtx} {m : MInst} {ps ps' : PState} {ls : List Line}
    (hm : m.isLitLoad = false) (h : m.lines c ps = .ok (ls, ps')) : ls.countP Line.isLit = 0 :=
  lines_lit_zero (fun s rd cst fl he => by rw [he] at hm; cases hm) h

theorem ainstLines_lit0 {c : FnCtx} {af : AFunc} {a : AInst} {ps ps' : PState} {ls : List Line}
    (ha : ∀ m, a = .inst m → m.isLitLoad = false) (h : ainstLines c af a ps = .ok (ls, ps')) :
    ls.countP Line.isLit = 0 := by
  cases a with
  | inst m => exact lines_lit_of (ha m rfl) h
  | prologue =>
    simp only [ainstLines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    split <;> simp [prologueLines_lit]
  | epilogueRet =>
    simp only [ainstLines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    split <;> simp [epilogueLines_lit, Line.isLit]

theorem codeLinesE_lit0 {c : FnCtx} {af : AFunc} :
    ∀ {code : List AInst} {ps ps' : PState} {ls : List Line},
      (∀ m, AInst.inst m ∈ code → m.isLitLoad = false) →
      codeLinesE c af code ps = .ok (ls, ps') → ls.countP Line.isLit = 0
  | [], ps, ps', ls, _, h => by
    simp only [codeLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | a :: as, ps, ps', ls, hn, h => by
    simp only [codeLinesE] at h
    obtain ⟨⟨l1, ps1⟩, h1, h⟩ := exceptBind_ok h
    obtain ⟨⟨l2, ps2⟩, h2, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [List.countP_append,
      ainstLines_lit0 (fun m hm => hn m (by subst hm; exact List.mem_cons_self)) h1,
      codeLinesE_lit0 (fun m hm => hn m (List.mem_cons_of_mem _ hm)) h2]

theorem blocksLinesE_lit0 {c : FnCtx} {af : AFunc} :
    ∀ {bs : List (Label × Array AInst)} {ps ps' : PState} {ls : List Line},
      (∀ p ∈ bs, ∀ m, AInst.inst m ∈ p.2.toList → m.isLitLoad = false) →
      blocksLinesE c af bs ps = .ok (ls, ps') → ls.countP Line.isLit = 0
  | [], ps, ps', ls, _, h => by
    simp only [blocksLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | (l, code) :: bs, ps, ps', ls, hn, h => by
    simp only [blocksLinesE] at h
    obtain ⟨⟨l1, ps1⟩, h1, h⟩ := exceptBind_ok h
    obtain ⟨⟨l2, ps2⟩, h2, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have e1 := codeLinesE_lit0 (fun m hm => hn _ List.mem_cons_self m hm) h1
    have e2 := blocksLinesE_lit0 (fun p hp => hn p (List.mem_cons_of_mem _ hp)) h2
    have hl : Line.isLit (.label (.block l)) = false := rfl
    simp [List.countP_append, hl, e1, e2]

/-- `emitPre` of a function without literal-pool load has no literal line. -/
theorem emitPre_lit0 {k : Nat} {af : AFunc} {pre : Array Line} (h : emitPre k af = .ok pre)
    (hn : af.NoLit) : pre.toList.countP Line.isLit = 0 := by
  obtain ⟨body, ps, hb, rfl⟩ := emitPre_ok h
  have h1 := blocksLinesE_lit0 hn hb
  have h2 := ftList_lit body.length body (Nat.le_refl _)
  have h4 : ∀ ts : List (Lbl × Clif.TrapCode),
      (ts.flatMap fun p => [Line.label p.1, Line.ins (.udf 0xc11f) (some p.2)]).countP Line.isLit = 0 := by
    intro ts; induction ts with
    | nil => rfl
    | cons p ts ih => rw [List.flatMap_cons, List.countP_append, ih]; simp [Line.isLit]
  rw [List.toList_toArray, List.countP_append, h4]
  omega

/-! ## The bound -/

/-- The code `emitFunc` produces from any allocation `rf` `lowerRFunc` lowers is at most
`8 · rfWords vc rf` bytes (4 per word; relaxation at most doubles it and the literal pool adds
12 bytes per literal load, `emitFunc_size_le`, which the load's word bound covers,
`emitPre_size_lit`). -/
theorem emitFunc_size_rf {vc : VCode} {rf : RFunc} {af : AFunc} {k : Nat} {fa : FnAsm}
    (ha : lowerRFunc vc rf = .ok af) (he : emitFunc k af = .ok fa) :
    fa.size ≤ 8 * rfWords vc rf := by
  obtain ⟨pre, hp, -⟩ := emitFunc_unfold he
  have h1 := emitFunc_size_le he hp
  have h2 := emitPre_size_lit hp
  have h3 := lowerRFunc_words ha
  simp only [linesBytes] at h2
  omega

/-- **The spill allocation's code fits the `b` range**: under the size condition
`spillSizeOkB vcp`, the code of the spill allocation is below `2 ^ 27` bytes. -/
theorem emitFunc_spill_size {vcp : VCode} {af : AFunc} {k : Nat} {fa : FnAsm}
    (hsz : spillSizeOkB vcp = true) (ha : lowerRFunc vcp (spillAlloc vcp) = .ok af)
    (he : emitFunc k af = .ok fa) : fa.size < 2 ^ 27 := by
  have h1 := emitFunc_size_rf ha he
  have h2 := spillSizeOkB_bound hsz
  unfold spillWordBound at h2
  omega

end E2E
