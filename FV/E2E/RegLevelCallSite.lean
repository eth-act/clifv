import FV.E2E.RegLevelUnwind
import FV.E2E.RegLevelNext
import FV.E2E.RegLevelCall

/-!
# The call-site pair of a register-level call (S10e)

At a `Q` state whose next item is a `call`/`tryCall`, the pc is at the item's call line `j`
(`bl`/`blr`), and `(c, lineOffset R.L j + 4)` is the pair `callSites` writes for the call
(`c = some ti` for a `tryCall`), the membership `personality_callSite` consumes.

* `L_callKeys`: the callees of the call lines of the final code are those of `af`'s calls, in
  order (`relaxLines`, `fallthrough` and the trap section add or drop no call line; each call
  emits exactly one, nothing else emits one).
* `q_callSite`: for a call in a block that is not `af`'s last one. `Q` locates the item's lines
  only by the lines that follow it; the next block's label (unique in the final code,
  `RL.label_unique`) anchors them, so the pc's call line is the call's.
* `q_callSite_last`: for the last block, nothing anchors the lines (an identical line
  sequence elsewhere also satisfies `Q`), so the decidable check `lastCallsOk` is assumed:
  every call of the last block has the handlers of every call line of `fa` with the same
  callee, unless it is a plain call followed by a trap (`nextLine?`, the `udf` after a call that
  does not return, e.g. `_Unwind_Resume`) and that call line is not followed by the trap.
-/

namespace Backend.Proof

open Backend E2E Backend.Proof.UnwindTables

/-- The call of an allocated instruction as `AFunc.calls` lists it. -/
def aCall : AInst → Option (Option TryInfo)
  | .inst (.call _) => some none
  | .inst (.tryCall _ ti) => some (some ti)
  | _ => none

/-- The calls of one block of an allocated function. -/
def blockCalls (p : Label × Array AInst) : List (Option TryInfo) := p.2.toList.filterMap aCall

/-- Since #553 `AFunc.calls` lists the calls in the emission order (`emitOrder`), so the
statement is over `emitOrder` (the old blocks-order form no longer typechecks and does not
hold when cold blocks move). -/
theorem calls_eq (af : AFunc) : af.calls = (emitOrder af).flatMap (fun e => blockCalls e.1) := by
  unfold AFunc.calls blockCalls
  congr 1

/-- The callee of a call line (`bl n` ↦ `.sym n`, `blr r` ↦ `.reg r`). -/
def _root_.Backend.Line.callKey : Line → Option CallDest
  | .ins (.bl n) _ => some (.sym n)
  | .ins (.blr r) _ => some (.reg r)
  | _ => none

/-- The callees of the call lines, in order. -/
def callKeys (L : List Line) : List CallDest := L.filterMap Line.callKey

/-- The callee of an allocated call. -/
def aKey : AInst → Option CallDest
  | .inst (.call ic) => some ic.dest
  | .inst (.tryCall ic _) => some ic.dest
  | _ => none

/-- The callees of the calls of one block. -/
def blockKeys (p : Label × Array AInst) : List CallDest := p.2.toList.filterMap aKey

theorem isCall_eq (l : Line) : l.isCall = (l.callKey).isSome := by
  rcases l with ⟨i, t⟩ | ⟨a, b⟩ | ⟨l⟩
  · cases i <;> rfl
  · rfl
  · rfl

theorem callKey_none {l : Line} (h : l.isCall = false) : l.callKey = none := by
  rw [isCall_eq] at h; simpa using h

/-- The number of call lines. -/
def nCalls (L : List Line) : Nat := L.countP Line.isCall

theorem nCalls_eq (L : List Line) : nCalls L = (callKeys L).length := by
  rw [nCalls, callKeys, List.length_filterMap_eq_countP]
  congr 1
  funext l
  exact isCall_eq l

theorem nCalls_append (A B : List Line) : nCalls (A ++ B) = nCalls A + nCalls B :=
  List.countP_append ..

theorem callKeys_append (A B : List Line) : callKeys (A ++ B) = callKeys A ++ callKeys B :=
  List.filterMap_append

theorem relaxLine_callKeys (f : Lbl → Bool) (ln : Line) :
    callKeys (relaxLine f ln) = callKeys [ln] := by
  unfold relaxLine
  split
  · rename_i c t h
    rcases ln with ⟨i, _ | _⟩ | ⟨a, b⟩ | ⟨l⟩ <;> simp [Line.relaxable?] at h
    obtain ⟨hc, rfl⟩ := h
    split <;> cases i <;> simp_all [callKeys, Insn.relaxTarget?, Insn.condTarget?, Insn.invertTo,
      Line.callKey, List.filterMap_cons, List.filterMap_nil]
  · rfl

theorem relaxLines_callKeys (f : Lbl → Bool) :
    ∀ L : List Line, callKeys (relaxLines f L) = callKeys L
  | [] => rfl
  | ln :: L => by
    rw [relaxLines_cons, callKeys_append, relaxLine_callKeys, relaxLines_callKeys f L,
      ← callKeys_append]
    rfl

theorem relaxLines_nCalls (f : Lbl → Bool) (L : List Line) : nCalls (relaxLines f L) = nCalls L := by
  rw [nCalls_eq, nCalls_eq, relaxLines_callKeys]

@[simp] theorem callKey_invertTo (c : Insn) (e : Lbl) (t : Option Clif.TrapCode) :
    (Line.ins (c.invertTo e) t).callKey = (Line.ins c t).callKey := by
  cases c <;> rfl

/-! ## The call lines under `MachBuffer`'s simplification

`MachBuffer` removes only branch lines (a `b`/`b.cond` has no callee) and retargets branches,
so the call lines and their order are kept. -/

/-- Erasing a line with no callee keeps the call lines. -/
theorem callKeys_eraseIdx : ∀ (L : List Line) (k : Nat) (ln : Line), L[k]? = some ln →
    ln.callKey = none → callKeys (L.eraseIdx k) = callKeys L
  | [], _, _, h, _ => by simp at h
  | a :: L, 0, ln, h, hk => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [List.eraseIdx, callKeys, List.filterMap_cons, hk, List.filterMap_nil]
  | a :: L, k + 1, ln, h, hk => by
    simp only [List.getElem?_cons_succ] at h
    show callKeys (a :: L.eraseIdx k) = callKeys (a :: L)
    cases ha : a.callKey with
    | none =>
      simp only [callKeys, List.filterMap_cons, ha]
      exact callKeys_eraseIdx L k ln h hk
    | some d =>
      simp only [callKeys, List.filterMap_cons, ha]
      exact congrArg (d :: ·) (callKeys_eraseIdx L k ln h hk)

/-- Setting a line with no callee to a line with no callee keeps the call lines. -/
theorem callKeys_set : ∀ (L : List Line) (p : Nat) (y : Line),
    (∀ x, L[p]? = some x → x.callKey = none) → y.callKey = none →
    callKeys (L.set p y) = callKeys L
  | [], _, _, _, _ => rfl
  | a :: L, 0, y, h, hy => by
    have h0 := h a (by simp)
    simp only [List.set_cons_zero, callKeys, List.filterMap_cons, h0, hy]
  | a :: L, p + 1, y, h, hy => by
    have ih := callKeys_set L p y (fun x hx => h x (by simpa using hx)) hy
    show callKeys (a :: L.set p y) = callKeys (a :: L)
    cases ha : a.callKey with
    | none => simp only [callKeys, List.filterMap_cons, ha]; exact ih
    | some d => simp only [callKeys, List.filterMap_cons, ha]; exact congrArg (d :: ·) ih

/-- The line `MBuf.step` considers: a branch, whose call key is none. -/
theorem callKey_of_stepLine {ln : Line}
    (ht : ((ln.ubr?).orElse fun _ => ln.cbr?).isSome = true) : ln.callKey = none := by
  cases ln with
  | ins i tc =>
    cases tc with
    | none =>
      cases i with
      | b _ => rfl
      | bcond _ _ => rfl
      | cbz _ _ _ _ => rfl
      | tbz _ _ _ _ => rfl
      | _ => simp [Line.ubr?, Line.cbr?, Insn.condTarget?] at ht
    | some _ => simp [Line.ubr?, Line.cbr?] at ht
  | _ => simp [Line.ubr?, Line.cbr?] at ht

/-- The line `MBuf.step` inverts: a conditional branch, whose call key is none. -/
theorem callKey_of_cbr {ln : Line} {ct} (h : ln.cbr? = some ct) : ln.callKey = none :=
  callKey_of_stepLine (by cases hu : ln.ubr? <;> simp [Option.orElse, hu, h])

/-- `lastCode` names an index before `n` holding a line. -/
theorem lastCode_spec (out : Array Line) : ∀ (n k : Nat), lastCode out n = some k →
    k < n ∧ ∃ ln, out[k]? = some ln
  | 0, _, h => by simp [lastCode] at h
  | n + 1, k, h => by
    unfold lastCode at h
    cases hx : out[n]? with
    | none => simp only [hx] at h; cases h
    | some ln =>
      simp only [hx] at h
      cases ln with
      | label _ =>
        obtain ⟨hlt, hk⟩ := lastCode_spec out n k h
        exact ⟨by omega, hk⟩
      | _ => simp only [Option.some.injEq] at h; subst h; exact ⟨by omega, _, hx⟩

theorem lastCode_lt (out : Array Line) (k p : Nat) (h : lastCode out k = some p) : p < k :=
  (lastCode_spec out k p h).1

/-- The line at index `p < k` is untouched by erasing `k`. -/
theorem getElem?_eraseIdx_of_lt {L : List Line} {k p : Nat} (hpk : p < k) (_hk : k ≤ L.length) :
    (L.eraseIdx k)[p]? = L[p]? :=
  List.getElem?_eraseIdx_of_lt hpk

theorem step_callKeys (allLabels : Bool) (m m' : MBuf) (h : MBuf.step allLabels m = some m') :
    callKeys m'.out.toList = callKeys m.out.toList := by
  unfold MBuf.step at h
  rcases hlc : lastCode m.out m.out.size with - | k
  · simp [hlc] at h
  obtain ⟨-, ln, hkln⟩ := lastCode_spec m.out m.out.size k hlc
  have hln : m.out[k]! = ln := by simp [getElem!_def, hkln]
  have hkl' : m.out.toList[k]? = some ln := by simpa using hkln
  rcases ht : (ln.ubr?).orElse (fun _ => ln.cbr?) with - | t
  · simp only [hlc, hln, ht, Option.bind_eq_bind, Option.bind_some, Option.bind_none] at h
    cases h
  have hbr : ln.callKey = none := callKey_of_stepLine (by rw [ht]; rfl)
  have hE : callKeys (m.erase k).toList = callKeys m.out.toList := by
    simp only [MBuf.erase, List.toList_toArray]; exact callKeys_eraseIdx _ k ln hkl' hbr
  simp only [hlc, hln, ht, Option.bind_eq_bind, Option.bind_some, Option.bind_none] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (cases h; exact hE)
    | (cases h; rfl)
    | skip
  all_goals
    rcases hpp : lastCode m.out k with - | p
    · simp only [hpp, Option.bind_none] at h; cases h
    obtain ⟨hpk, lp, hlp⟩ := lastCode_spec _ _ _ hpp
    have hlp' : m.out[p]! = lp := by simp [getElem!_def, hlp]
    simp only [hpp, hlp', Option.bind_some] at h
    split at h
    · cases h; exact hE
    rcases hct : lp.cbr? with - | ct
    · simp only [hct, Option.bind_none] at h; cases h
    simp only [hct, Option.bind_some] at h
    split at h
    · cases h
    split at h
    · rename_i c tc _
      cases h
      have hy0 : (Line.ins (Insn.invertTo t c) tc).callKey = none := by
        rw [callKey_invertTo]; exact callKey_of_cbr hct
      show callKeys ((m.erase k).set! p _).toList = _
      rw [Array.set!, Array.toList_setIfInBounds]
      refine (callKeys_set _ p _ (fun x hx => ?_) hy0).trans hE
      simp only [MBuf.erase, List.toList_toArray, List.getElem?_eraseIdx_of_lt hpk,
        Array.getElem?_toList, hlp, Option.some.injEq] at hx
      subst hx; exact callKey_of_cbr hct
    · cases h

/-- An invariant of a `forIn` in `Id`. -/
theorem mbForIn_inv {α σ : Type} (l : List α) (init : σ) (f : α → σ → Id (ForInStep σ))
    (P : σ → Prop) (h0 : P init) (hf : ∀ a s, P s → P (f a s).run.value) :
    P (forIn l init f).run := by
  induction l generalizing init with
  | nil => simpa using h0
  | cons a l ih =>
    rw [List.forIn_cons]
    have := hf a init h0
    cases hfa : f a init with
    | done b => rw [hfa] at this; simp only [Id.run_bind]; exact this
    | yield b => rw [hfa] at this; simp only [Id.run_bind]; exact ih b this

theorem optimize_callKeys (allLabels : Bool) (m : MBuf) :
    callKeys (MBuf.optimize allLabels m).out.toList = callKeys m.out.toList := by
  unfold MBuf.optimize
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  refine mbForIn_inv (P := fun m' : MBuf => callKeys m'.out.toList = callKeys m.out.toList)
    _ _ _ rfl ?_
  intro _ s hs
  split
  · rename_i m' h; exact (step_callKeys _ _ _ h).trans hs
  · exact hs

theorem fold_callKeys (g : MBuf → Line → MBuf)
    (hg : ∀ m ln, callKeys (g m ln).out.toList = callKeys m.out.toList ++ callKeys [ln]) :
    ∀ (ls : List Line) (m : MBuf),
      callKeys (ls.foldl g m).out.toList = callKeys m.out.toList ++ callKeys ls
  | [], m => by simp [callKeys]
  | ln :: ls, m => by
    rw [List.foldl_cons, fold_callKeys g hg ls, hg, List.append_assoc, ← callKeys_append]
    rfl

theorem callKeys_relabel (f : Lbl → Lbl) (ln : Line) : (ln.relabel f).callKey = ln.callKey := by
  cases ln with
  | ins i tc => cases i <;> rfl
  | _ => rfl

theorem callKeys_map_relabel (f : Lbl → Lbl) :
    ∀ L : List Line, callKeys (L.map (Line.relabel f)) = callKeys L
  | [] => rfl
  | ln :: L => by
    have ih := callKeys_map_relabel f L
    simp only [callKeys] at ih ⊢
    rw [List.map_cons, List.filterMap_cons, List.filterMap_cons, callKeys_relabel, ih]

theorem machBuf_callKeys (allLabels : Bool) (ls : List Line) :
    callKeys (machBuf allLabels ls).1 = callKeys ls := by
  unfold machBuf
  dsimp only
  rw [callKeys_map_relabel, optimize_callKeys, fold_callKeys _ ?hg]
  · simp [callKeys]
  case hg =>
    intro m ln
    split <;> simp [optimize_callKeys, Array.toList_push, callKeys_append]

theorem callKeys_nil {L : List Line} (h : ∀ l ∈ L, l.isCall = false) : callKeys L = [] :=
  List.filterMap_eq_nil_iff.2 fun l hl => callKey_none (h l hl)

theorem memFinalize_noCall {c : FnCtx} {m : AMode} {n : Nat} {v : List Line × AMode}
    (h : memFinalize c m n = .ok v) : ∀ l ∈ v.1, l.isCall = false := by
  obtain ⟨pre, m'⟩ := v
  unfold memFinalize at h
  split at h <;> simp only [pure, Except.pure, Except.ok.injEq, throw, throwThe, MonadExceptOf.throw,
    reduceCtorEq] at h
  all_goals (repeat' split at h)
  all_goals (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h)
  all_goals first | exact loadConst64_noCall _ _ | simp

theorem addOff_noCall (rd rn : Reg) (off : Int) :
    ∀ l ∈ MInst.lines.addOff rd rn off, l.isCall = false := by
  unfold MInst.lines.addOff
  repeat' split
  all_goals simp [Line.isCall, Line.insn?, callInsn?]

theorem kinsn_noCall (k : CondBrKind) (l : Lbl) (t : Option Clif.TrapCode) :
    (Line.ins (k.insn l) t).isCall = false := by
  cases k <;> rfl

theorem rmwLoopCmp_noCall (op : AtomicRmwLoopOp) (bits : Nat) (t : Option Clif.TrapCode) :
    (Line.ins (rmwLoopCmp op bits) t).isCall = false := by
  unfold rmwLoopCmp; split <;> rfl

theorem casLoopCmp_noCall (bits : Nat) (t : Option Clif.TrapCode) :
    (Line.ins (casLoopCmp bits) t).isCall = false := by
  unfold casLoopCmp; split <;> rfl

theorem rmwLoopMid_noCall (op : AtomicRmwLoopOp) (bits : Nat) :
    ∀ i ∈ rmwLoopMid op bits, (Line.ins i none).isCall = false := by
  have hs : ∀ i ∈ rmwLoopSext bits, (Line.ins i none).isCall = false := by
    unfold rmwLoopSext; split <;> simp [Line.isCall, Line.insn?, callInsn?]
  cases op <;> simp only [rmwLoopMid, List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
  all_goals intro i hi
  all_goals first
    | (rcases hi with rfl | rfl <;> first | rfl | exact rmwLoopCmp_noCall _ _ _)
    | (rcases hi with hi | rfl | rfl <;> first | exact hs i hi | rfl | exact rmwLoopCmp_noCall _ _ _)
    | (subst hi; rfl)
    | simp at hi

/-- An allocated instruction other than a call emits no call line. -/
theorem lines_noCall {c : FnCtx} {m : MInst} {ps ps' : PState} {ls : List Line}
    (h : m.lines c ps = .ok (ls, ps')) (hm : aCall (.inst m) = none) :
    ∀ l ∈ ls, l.isCall = false := by
  unfold MInst.lines at h
  split at h <;> simp only [bind, Except.bind, pure, Except.pure] at h
  all_goals (repeat' (first | (split at h) | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h)))
  all_goals (try simp only [List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
    rmwLoopLines, rmwLoopBody, casLoopLines, casLoopHead, List.cons_append,
    List.nil_append, List.append_assoc, List.mem_nil_iff, false_implies, implies_true,
    and_true])
  all_goals (repeat' apply And.intro)
  all_goals first
    | rfl
    | (simp [aCall] at hm; done)
    | exact memFinalize_noCall ‹_›
    | exact addOff_noCall _ _ _
    | exact kinsn_noCall _ _ _
    | exact casLoopCmp_noCall _ _
    | exact rmwLoopMid_noCall _ _
    | (cases h; done)
    | (simp [throw, throwThe, MonadExceptOf.throw] at h; done)
    | (intro _ _; rfl)
    | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at *; done)

theorem aKey_isSome (a : AInst) : (aKey a).isSome = (aCall a).isSome := by
  cases a with
  | inst m => cases m <;> rfl
  | _ => rfl

theorem filterMap_aKey_length (C : List AInst) :
    (C.filterMap aKey).length = (C.filterMap aCall).length := by
  rw [List.length_filterMap_eq_countP, List.length_filterMap_eq_countP]
  congr 1
  funext a
  exact aKey_isSome a

theorem flatMap_blockKeys_length : ∀ (l : List (Label × Array AInst)),
    (l.flatMap blockKeys).length = (l.flatMap blockCalls).length
  | [] => rfl
  | p :: l => by
    simp only [List.flatMap_cons, List.length_append, flatMap_blockKeys_length l, blockKeys,
      blockCalls, filterMap_aKey_length]

/-- The call lines of an allocated instruction: one `bl`/`blr` with its callee for a call, none
otherwise. -/
theorem lines_callKeys {c : FnCtx} {m : MInst} {ps ps' : PState} {ls : List Line}
    (h : m.lines c ps = .ok (ls, ps')) : callKeys ls = (aKey (.inst m)).toList := by
  by_cases hm : aCall (.inst m) = none
  · rw [callKeys_nil (lines_noCall h hm)]
    have : aKey (.inst m) = none := by
      have := aKey_isSome (.inst m); rw [hm] at this; simpa using this
    rw [this]; rfl
  · cases m with
    | call ic =>
      cases hd : ic.dest <;> simp [MInst.lines, hd, pure, Except.pure] at h <;>
        obtain ⟨h1, -⟩ := h <;> subst h1 <;> simp [callKeys, Line.callKey, aKey, hd]
    | tryCall ic ti =>
      cases hd : ic.dest <;> simp [MInst.lines, hd, pure, Except.pure] at h <;>
        obtain ⟨h1, -⟩ := h <;> subst h1 <;> simp [callKeys, Line.callKey, aKey, hd]
    | _ => simp [aCall] at hm

theorem popLines_noCall (int : Bool) (rs : List Reg) : ∀ l ∈ popLines int rs, l.isCall = false := by
  intro l hl
  unfold popLines at hl
  generalize pairsOf rs = po at hl
  obtain ⟨ps, o⟩ := po
  simp only [List.mem_append, List.mem_map] at hl
  rcases hl with ⟨p, -, rfl⟩ | hl
  · cases int <;> rfl
  · cases o with
    | none => simp at hl
    | some r => simp only [List.mem_singleton] at hl; subst hl; cases int <;> rfl

theorem epilogueLines_noCall (saves : List Reg) (size : Nat) :
    ∀ l ∈ epilogueLines saves size, l.isCall = false := by
  intro l hl
  simp only [epilogueLines, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with ((hl | hl) | hl) | (rfl | rfl)
  · exact spAdjLines_noCall false _ l hl
  · exact popLines_noCall _ _ l hl
  · exact popLines_noCall _ _ l hl
  · rfl
  · rfl

theorem ainstLines_callKeys {c : FnCtx} {af : AFunc} {a : AInst} {ps ps' : PState} {ls : List Line}
    (h : ainstLines c af a ps = .ok (ls, ps')) : callKeys ls = (aKey a).toList := by
  cases a with
  | inst m => exact lines_callKeys h
  | prologue =>
    simp only [ainstLines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    split
    · exact callKeys_nil (prologueLines_noCall _ _)
    · rfl
  | epilogueRet =>
    simp only [ainstLines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    split
    · exact callKeys_nil (epilogueLines_noCall _ _)
    · rfl

theorem codeLinesE_callKeys {c : FnCtx} {af : AFunc} :
    ∀ {code : List AInst} {ps ps' : PState} {ls : List Line},
      codeLinesE c af code ps = .ok (ls, ps') → callKeys ls = code.filterMap aKey
  | [], ps, ps', ls, h => by
    simp only [codeLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | a :: as, ps, ps', ls, h => by
    simp only [codeLinesE, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i r hr
      split at h
      · cases h
      · rename_i r2 hr2
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.1, callKeys_append, ainstLines_callKeys hr, codeLinesE_callKeys hr2,
          List.filterMap_cons]
        cases aKey a <;> rfl

theorem callKeys_label_cons (l : Lbl) (L : List Line) : callKeys (.label l :: L) = callKeys L := rfl

theorem trapLines_callKeys (ps : PState) : callKeys (trapLines ps) = [] := by
  apply callKeys_nil
  intro l hl
  simp only [trapLines, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false] at hl
  obtain ⟨p, -, rfl | rfl⟩ := hl <;> rfl

theorem dropWhile_eq_drop {α : Type} (p : α → Bool) (l : List α) :
    l.dropWhile p = l.drop (l.takeWhile p).length := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases hp : p a <;> simp [hp, ih]

/-- `splitSegs` re-splits the lines it was given. -/
theorem splitSegs_lines : ∀ (ss : List Seg) (L : List Line) (os : List (List Line)),
    splitSegs ss L = some os → segLines ss os = L
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [splitSegs] at h
  | s :: ss, .label (.block l) :: rest, os, h => by
    unfold splitSegs at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i hl hbody
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hl hbody
        subst hl
        rw [Option.map_eq_some_iff] at h
        obtain ⟨os', hm, rfl⟩ := h
        have ih := splitSegs_lines ss _ os' hm
        simp only [segLines]
        rw [ih, ← dropWhile_eq_drop, List.cons_append, List.append_assoc,
          List.takeWhile_append_dropWhile]
        conv => rhs; rw [← List.take_append_drop s.body.length rest, hbody]
  | _ :: _, [], _, h => by simp [splitSegs] at h
  | _ :: _, .ins _ _ :: _, _, h => by simp [splitSegs] at h
  | _ :: _, .word _ _ :: _, _, h => by simp [splitSegs] at h
  | _ :: _, .label (.trap _) :: _, _, h => by simp [splitSegs] at h

theorem filterMap_split {α β : Type} (f : α → Option β) (X : List α) (hX : X ≠ []) :
    X.dropLast.filterMap f ++ X.getLast?.toList.filterMap f = X.filterMap f := by
  conv => rhs; rw [← List.dropLast_concat_getLast hX]
  rw [List.getLast?_eq_some_getLast hX, List.filterMap_append]
  rfl

/-- A block's code lines: the lines but the last instruction's (`body`) and the last
instruction's (`term`), with the block's call keys. -/
theorem seg_callKeys {c : FnCtx} {af : AFunc} {l : Label} {code : Array AInst}
    {body term : List Line} {ps1 psm ps2 : PState}
    (h1 : codeLinesE c af code.toList.dropLast ps1 = .ok (body, psm))
    (h2 : codeLinesE c af code.toList.getLast?.toList psm = .ok (term, ps2)) :
    callKeys (body ++ term) = blockKeys (l, code) := by
  rw [blockKeys, callKeys_append, codeLinesE_callKeys h1, codeLinesE_callKeys h2]
  cases hc : code.toList with
  | nil => rfl
  | cons a rest => exact filterMap_split aKey (a :: rest) (by simp)

/-- The call keys of the first `i` segments' unsimplified lines: the first `i` blocks'. -/
theorem segs_callKeys_take {c : FnCtx} {af : AFunc} :
    ∀ {bs : List ((Label × Array AInst) × Nat)} {ps psF : PState} {ss : List Seg} (i : Nat),
      segsOf c af bs ps = .ok (ss, psF) →
      callKeys (segLines (ss.take i) ((ss.take i).map (·.term))) =
        (bs.take i).flatMap (fun e => blockKeys e.1)
  | [], ps, psF, ss, i, h => by
    simp only [segsOf, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [segLines, callKeys]
  | _ :: _, _, _, _, 0, _ => by simp [segLines, callKeys]
  | ((l, code), j) :: bs, ps, psF, ss, i + 1, h => by
    simp only [segsOf, bind, Except.bind] at h
    split at h
    · cases h
    rename_i r1 h1
    split at h
    · cases h
    rename_i r2 h2
    split at h
    · cases h
    rename_i r3 h3
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hs := seg_callKeys (l := l) h1 h2
    rw [callKeys_append] at hs
    simp only [List.take_succ_cons, List.map_cons, segLines, List.cons_append,
      callKeys_label_cons, callKeys_append, List.flatMap_cons]
    rw [hs, segs_callKeys_take i h3]

theorem segs_callKeys {c : FnCtx} {af : AFunc} {bs : List ((Label × Array AInst) × Nat)}
    {ps psF : PState} {ss : List Seg} (h : segsOf c af bs ps = .ok (ss, psF)) :
    callKeys (segLines ss (ss.map (·.term))) = bs.flatMap (fun e => blockKeys e.1) := by
  have := segs_callKeys_take (bs.length + ss.length) h
  rwa [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at this

/-- `machPlan`'s plan: its segments and the call keys of its final lines (the `MachBuffer`
output re-split, whose call keys are the segments' own lines'). -/
theorem machPlan_callKeys {af : AFunc} {a : Bool} {ss : List Seg} {ps : PState} {p : Plan}
    (h : machPlan af a ss ps = some p) :
    p.segs = ss ∧ callKeys (segLines ss p.outs) = callKeys (segLines ss (ss.map (·.term))) := by
  unfold machPlan at h
  simp only [bind, Option.bind] at h
  split at h
  · cases h
  rename_i os hos
  try dsimp only at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, by rw [splitSegs_lines ss _ os hos, machBuf_callKeys]⟩
  · cases h

/-- The call keys of an emission plan's final lines are those of its unsimplified lines. -/
theorem plan_outs_callKeys {k : Nat} {af : AFunc} {p : Plan} (hp : emitPlan k af = .ok p) :
    callKeys (segLines p.segs p.outs) = callKeys (segLines p.segs (p.segs.map (·.term))) := by
  unfold emitPlan at hp
  simp only [bind, Except.bind] at hp
  split at hp
  · cases hp
  rename_i r hr
  obtain ⟨ss, ps⟩ := r
  try dsimp only at hp
  split at hp
  · rename_i p1 h1
    simp only [pure, Except.pure, Except.ok.injEq] at hp
    subst hp
    have hmp : machPlan af true ss ps = some p1 ∨ machPlan af false ss ps = some p1 := by
      cases e : machPlan af true ss ps with
      | some q => rw [e] at h1; simp only [Option.orElse] at h1; exact .inl h1
      | none => rw [e] at h1; simp only [Option.orElse] at h1; exact .inr h1
    rcases hmp with hmp | hmp
    · rw [(machPlan_callKeys hmp).1]; exact (machPlan_callKeys hmp).2
    · rw [(machPlan_callKeys hmp).1]; exact (machPlan_callKeys hmp).2
  · split at hp
    · simp only [pure, Except.pure, Except.ok.injEq] at hp
      subst hp
      rfl
    · cases hp

/-- The call keys of an emission plan's lines: the blocks' call keys in emission order. -/
theorem plan_callKeys {k : Nat} {af : AFunc} {p : Plan} (hp : emitPlan k af = .ok p) :
    callKeys p.lines = (emitOrder af).flatMap (fun e => blockKeys e.1) := by
  obtain ⟨hseg, -, -, -⟩ := emitPlan_spec hp
  rw [Plan.lines, callKeys_append, trapLines_callKeys, List.append_nil, plan_outs_callKeys hp]
  exact segs_callKeys hseg

theorem flatMap_keys_length (l : List ((Label × Array AInst) × Nat)) :
    (l.flatMap (fun e => blockKeys e.1)).length =
      (l.flatMap (fun e => blockCalls e.1)).length := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, List.length_append, List.length_append, ih]
    exact congrArg (· + _) (filterMap_aKey_length _)

/-! ## The call lines of the final code are the function's calls, in order -/

/-- **The callees of the call lines of the final code are those of `af`'s calls**, in order
(`AFunc.calls` is in emission order since #553). -/
theorem L_callKeys {R : RL} (hR : R.Wf) :
    callKeys R.L = (emitOrder R.af).flatMap (fun e => blockKeys e.1) := by
  obtain ⟨p, hp, hL, -⟩ := emitFunc_ok hR.emit
  show callKeys R.fa.lines.toList = _
  rw [hL, relaxLines_callKeys]
  exact plan_callKeys hp

theorem go_absent : ∀ {L : List Line} {off : Nat} {m m' : Std.HashMap Lbl Nat} {l : Lbl},
    labelOffsets.go L off m = .ok m' → m.contains l = true → ∀ j : Nat, L[j]? ≠ some (Line.label l)
  | [], _, _, _, _, _, _, j, hj => by simp at hj
  | ln :: L, off, m, m', l, h, hc, j, hj => by
    unfold labelOffsets.go at h
    cases ln with
    | label lb =>
      by_cases hlb : m.contains lb = true
      · simp only [hlb, ite_true] at h; cases h
      · simp only [hlb, Bool.false_eq_true, ite_false] at h
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Line.label.injEq] at hj
          subst hj; exact hlb hc
        | succ j =>
          exact go_absent (l := l) h (by rw [Std.HashMap.contains_insert]; simp [hc]) j (by simpa using hj)
    | ins i t =>
      cases j with
      | zero => simp at hj
      | succ j => exact go_absent h hc j (by simpa using hj)
    | word a b =>
      cases j with
      | zero => simp at hj
      | succ j => exact go_absent h hc j (by simpa using hj)

theorem go_unique : ∀ {L : List Line} {off : Nat} {m m' : Std.HashMap Lbl Nat} {l : Lbl} {p q : Nat},
    labelOffsets.go L off m = .ok m' → L[p]? = some (.label l) → L[q]? = some (.label l) → p = q
  | [], _, _, _, _, _, _, _, hp, _ => by simp at hp
  | ln :: L, off, m, m', l, p, q, h, hp, hq => by
    unfold labelOffsets.go at h
    cases ln with
    | label lb =>
      by_cases hlb : m.contains lb = true
      · simp only [hlb, ite_true] at h; cases h
      · simp only [hlb, Bool.false_eq_true, ite_false] at h
        cases p with
        | zero =>
          cases q with
          | zero => rfl
          | succ q =>
            simp only [List.getElem?_cons_zero, Option.some.injEq, Line.label.injEq] at hp
            subst hp
            exact absurd (by simpa using hq) (go_absent h (by simp) q)
        | succ p =>
          cases q with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq, Line.label.injEq] at hq
            subst hq
            exact absurd (by simpa using hp) (go_absent h (by simp) p)
          | succ q => exact congrArg (· + 1) (go_unique h (by simpa using hp) (by simpa using hq))
    | ins i t =>
      cases p with
      | zero => simp at hp
      | succ p =>
        cases q with
        | zero => simp at hq
        | succ q => exact congrArg (· + 1) (go_unique h (by simpa using hp) (by simpa using hq))
    | word a b =>
      cases p with
      | zero => simp at hp
      | succ p =>
        cases q with
        | zero => simp at hq
        | succ q => exact congrArg (· + 1) (go_unique h (by simpa using hp) (by simpa using hq))

/-- A label line of the final code is the only line of its label. -/
theorem RL.label_unique {R : RL} (hR : R.Wf) {p q : Nat} {l : Lbl} (hp : R.L[p]? = some (.label l))
    (hq : R.L[q]? = some (.label l)) : p = q :=
  go_unique (L := R.fa.lines.toList) hR.lm hp hq

/-! ## Indices of call lines -/

theorem callIdx_at : ∀ (L : List Line) (j : Nat) (ln : Line), L[j]? = some ln → ln.isCall = true →
    (callIdx L)[nCalls (L.take j)]? = some j
  | [], _, _, h, _ => by simp at h
  | a :: L, 0, ln, h, hc => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [callIdx, hc, nCalls]
  | a :: L, j + 1, ln, h, hc => by
    have ih := callIdx_at L j ln (by simpa using h) hc
    simp only [nCalls] at ih
    by_cases ha : a.isCall = true
    · simp [callIdx, nCalls, ha, List.getElem?_map, ih]
    · simp [callIdx, nCalls, ha, List.getElem?_map, ih]

theorem callKeys_at {L : List Line} {j : Nat} {ln : Line} (h : L[j]? = some ln) :
    (callKeys L)[nCalls (L.take j)]? = ln.callKey ∨ ln.callKey = none := by
  cases hk : ln.callKey with
  | none => exact .inr rfl
  | some k =>
    left
    obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp h
    have e : callKeys L = callKeys (L.take j) ++ k :: callKeys (L.drop (j + 1)) := by
      conv => lhs; rw [← List.take_append_drop j L, List.drop_eq_getElem_cons hj]
      rw [callKeys_append]
      simp only [callKeys, List.filterMap_cons, hk]
    rw [e, nCalls_eq, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl

/-- The pair `callSites` reads for the call line `j0` of the final code, the `n`-th call line. -/
theorem mem_calls_zip {R : RL} {j0 n : Nat} {x : Insn} {c : Option TryInfo}
    (hj : R.L[j0]? = some (.ins x none)) (hx : (Line.ins x none).isCall = true)
    (hn : nCalls (R.L.take j0) = n) (hc : R.af.calls[n]? = some c) :
    (c, lineOffset R.L j0 + 4) ∈ R.af.calls.zip (scanLines R.fa.lines.toList 0 [] []).2 := by
  rw [scanLines_rets_eq]
  have hi := callIdx_at R.L j0 _ hj hx
  rw [hn] at hi
  apply List.mem_of_getElem? (i := n)
  rw [List.getElem?_zip_eq_some]
  refine ⟨hc, ?_⟩
  simp only [List.reverse_nil, List.nil_append, List.getElem?_map]
  show ((callIdx R.L)[n]?).map _ = _
  rw [hi]
  simp only [Option.map_some, Nat.zero_add]
  rfl

/-! ## The call item of a `Q` state -/

theorem flatMap_mid {α γ : Type} (f : α → List γ) (l : List α) (b : Nat) (p : α)
    (h : l[b]? = some p) :
    l.flatMap f = (l.take b).flatMap f ++ (f p ++ (l.drop (b + 1)).flatMap f) := by
  obtain ⟨hb, rfl⟩ := List.getElem?_eq_some_iff.mp h
  conv => lhs; rw [← List.take_append_drop b l, List.drop_eq_getElem_cons hb]
  simp only [List.flatMap_append, List.flatMap_cons]

theorem flatMap_take_succ {α γ : Type} (f : α → List γ) (l : List α) (b : Nat) (p : α)
    (h : l[b]? = some p) : (l.take (b + 1)).flatMap f = (l.take b).flatMap f ++ f p := by
  rw [List.take_add_one, h]
  simp [List.flatMap_append]

/-! ## The call lines of each segment's final lines -/

theorem callKey_setTarget (i : Insn) (t : Lbl) (tc : Option Clif.TrapCode) :
    (Line.ins (i.setTarget t) tc).callKey = (Line.ins i tc).callKey := by
  cases i <;> rfl

theorem codeLinesE_one {c : FnCtx} {af : AFunc} {a : AInst} {ps ps' : PState} {ls : List Line}
    (h : codeLinesE c af [a] ps = .ok (ls, ps')) : ainstLines c af a ps = .ok (ls, ps') := by
  simp only [codeLinesE, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i r hr
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, List.append_nil] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hr

/-- A last instruction's lines are its unsimplified lines (`RawTerm`). -/
theorem rawTerm_of {c : FnCtx} {af : AFunc} {a : AInst} {ps ps' : PState} {t : List Line}
    (h : ainstLines c af a ps = .ok (t, ps')) : RawTerm (some a) t := by
  cases a with
  | inst m =>
    cases m
    all_goals first
      | exact True.intro
      | (simp only [ainstLines, MInst.lines, pure, Except.pure, Except.ok.injEq,
          Prod.mk.injEq] at h
         first | exact h.1.symm | exact ⟨_, h.1.symm⟩)
  | _ => exact True.intro

/-- Lines kept or retargeted line by line (`LineOut`) have the same call keys. -/
theorem callKeys_of_lineOut {rep : Label → Nat → Bool} {idx : LabelIdx} :
    ∀ {t o : List Line}, o.length = t.length →
      (∀ (i : Nat) (x y : Line), t[i]? = some x → o[i]? = some y → LineOut rep idx x y) →
      callKeys o = callKeys t
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | x :: t, y :: o, hl, h => by
    have hxy : y.callKey = x.callKey := by
      rcases h 0 x y rfl rfl with ⟨rfl, -⟩ | ⟨l, l', -, -, rfl, -⟩
      · rfl
      · exact callKeys_relabel _ x
    have ih : callKeys o = callKeys t :=
      callKeys_of_lineOut (by simpa using hl) (fun i x' y' h1 h2 => h (i + 1) x' y' h1 h2)
    show (y :: o).filterMap Line.callKey = (x :: t).filterMap Line.callKey
    rw [List.filterMap_cons, List.filterMap_cons, hxy]
    have ih' : o.filterMap Line.callKey = t.filterMap Line.callKey := ih
    rw [ih']

/-- The final lines of a conditional branch have no call line. -/
theorem condOut_callKeys {rep : Label → Nat → Bool} {idx : LabelIdx} {s1 s2 : Label} {ci : Insn}
    {o : List Line} {nxt : Nat} (hk : (Line.ins ci none).callKey = none)
    (h : CondOut rep idx s1 s2 ci o nxt) : callKeys o = [] := by
  rcases h with ⟨c, t', e', rfl, -, rfl, -, -⟩ | ⟨c, t', rfl, -, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ | ⟨rfl, -⟩
  · simp only [callKeys, List.filterMap_cons, List.filterMap_nil, callKey_setTarget, hk]; rfl
  · simp only [callKeys, List.filterMap_cons, List.filterMap_nil, callKey_setTarget, hk]
  · simp only [callKeys, List.filterMap_cons, List.filterMap_nil, callKey_invertTo, hk]
  · rfl

/-- **`termOk` keeps the call lines** of a last instruction's unsimplified lines. -/
theorem termOk_callKeys {rep : Label → Nat → Bool} {idx : LabelIdx} {a : Option AInst}
    {t o : List Line} {nxt : Nat} (h : termOk rep idx a t o nxt = true) (hr : RawTerm a t) :
    callKeys o = callKeys t := by
  by_cases hj : ∃ x, a = some (.inst (.jump x))
  · obtain ⟨x, rfl⟩ := hj
    simp only [RawTerm] at hr
    subst hr
    rcases termOk_jump h with ⟨l', rfl, -⟩ | ⟨rfl, -⟩ <;> rfl
  by_cases hc : ∃ tl el k, a = some (.inst (.condBr tl el k))
  · obtain ⟨tl, el, k, rfl⟩ := hc
    simp only [RawTerm] at hr
    subst hr
    have hk : (Line.ins (k.insn (.block tl)) none).callKey = none := by cases k <;> rfl
    rw [condOut_callKeys hk (termOk_condBr h)]
    simp only [callKeys, List.filterMap_cons, List.filterMap_nil, hk]; rfl
  by_cases hb : ∃ k tl el rn bit, a = some (.inst (.testBitAndBranch k tl el rn bit))
  · obtain ⟨k, tl, el, rn, bit, rfl⟩ := hb
    simp only [RawTerm] at hr
    subst hr
    rw [condOut_callKeys rfl (termOk_tbz h)]
    rfl
  by_cases ht : ∃ info ti, a = some (.inst (.tryCall info ti))
  · obtain ⟨info, ti, rfl⟩ := ht
    simp only [RawTerm] at hr
    obtain ⟨cl, rfl⟩ := hr
    obtain ⟨call, b0, he, ho⟩ := termOk_tryCall h
    simp only [List.cons.injEq, and_true] at he
    obtain ⟨rfl, rfl⟩ := he
    rcases ho with ⟨l', rfl, -⟩ | ⟨rfl, -⟩ <;> rfl
  · obtain ⟨hl, hline⟩ := termOk_kept (fun x e => hj ⟨x, e⟩) (fun tl el k e => hc ⟨tl, el, k, e⟩)
      (fun k tl el rn bit e => hb ⟨k, tl, el, rn, bit, e⟩) (fun info ti e => ht ⟨info, ti, e⟩) h
    exact callKeys_of_lineOut hl hline

theorem getElem?_of_take {α : Type} {l : List α} {n i : Nat} {a : α}
    (h : (l.take n)[i]? = some a) : l[i]? = some a := by
  rw [List.getElem?_take] at h
  split at h
  · exact h
  · cases h

theorem nCalls_label_cons (l : Lbl) (L : List Line) : nCalls (.label l :: L) = nCalls L := by
  rw [nCalls_eq, nCalls_eq, callKeys_label_cons]

theorem back?_toList {α : Type} (a : Array α) : a.back? = a.toList.getLast? := by
  rw [Array.back?_eq_getElem?, List.getLast?_eq_getElem?]; simp

theorem nCalls_segLines_cons (s : Seg) (ss : List Seg) (o : List Line) (os : List (List Line)) :
    nCalls (segLines (s :: ss) (o :: os)) = nCalls s.body + nCalls o + nCalls (segLines ss os) := by
  simp only [nCalls_eq, segLines, List.cons_append, callKeys_label_cons, callKeys_append,
    List.length_append]

theorem segLines_nCalls_le : ∀ (ss : List Seg) (os : List (List Line)), os.length = ss.length →
    (∀ (i : Nat) (s : Seg) (o : List Line), ss[i]? = some s → os[i]? = some o →
      nCalls o = nCalls s.term ∨ nCalls s.term = 0) →
    nCalls (segLines ss (ss.map (·.term))) ≤ nCalls (segLines ss os)
  | [], _, _, _ => by simp [segLines, nCalls]
  | _ :: _, [], hl, _ => by simp at hl
  | s :: ss, o :: os, hl, h => by
    rw [List.map_cons, nCalls_segLines_cons, nCalls_segLines_cons]
    have h0 := h 0 s o rfl rfl
    have ih := segLines_nCalls_le ss os (by simpa using hl)
      (fun i s' o' h1 h2 => h (i + 1) s' o' h1 h2)
    omega

/-- Final lines with at least the call lines of each segment's unsimplified ones, and as many in
all, have exactly those of each segment. -/
theorem segLines_nCalls_eq : ∀ (ss : List Seg) (os : List (List Line)), os.length = ss.length →
    (∀ (i : Nat) (s : Seg) (o : List Line), ss[i]? = some s → os[i]? = some o →
      nCalls o = nCalls s.term ∨ nCalls s.term = 0) →
    nCalls (segLines ss os) = nCalls (segLines ss (ss.map (·.term))) →
    ∀ (i : Nat) (s : Seg) (o : List Line), ss[i]? = some s → os[i]? = some o →
      nCalls o = nCalls s.term
  | [], _, _, _, _, _, _, _, h1, _ => by simp at h1
  | _ :: _, [], hl, _, _, _, _, _, _, _ => by simp at hl
  | s :: ss, o :: os, hl, h, he, i, s', o', h1, h2 => by
    rw [List.map_cons, nCalls_segLines_cons, nCalls_segLines_cons] at he
    have h0 := h 0 s o rfl rfl
    have hle := segLines_nCalls_le ss os (by simpa using hl)
      (fun i s' o' h1 h2 => h (i + 1) s' o' h1 h2)
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
      subst h1 h2
      omega
    | succ i =>
      exact segLines_nCalls_eq ss os (by simpa using hl) (fun i s' o' h1 h2 => h (i + 1) s' o' h1 h2)
        (by omega) i s' o' h1 h2

theorem segLines_nCalls_congr : ∀ (ss : List Seg) (os : List (List Line)), os.length = ss.length →
    (∀ (i : Nat) (s : Seg) (o : List Line), ss[i]? = some s → os[i]? = some o →
      nCalls o = nCalls s.term) →
    nCalls (segLines ss os) = nCalls (segLines ss (ss.map (·.term)))
  | [], _, _, _ => by simp [segLines]
  | _ :: _, [], hl, _ => by simp at hl
  | s :: ss, o :: os, hl, h => by
    rw [List.map_cons, nCalls_segLines_cons, nCalls_segLines_cons, h 0 s o rfl rfl,
      segLines_nCalls_congr ss os (by simpa using hl) (fun i s' o' h1 h2 => h (i + 1) s' o' h1 h2)]

theorem segLines_split : ∀ (ss : List Seg) (os : List (List Line)) (i : Nat),
    os.length = ss.length →
    segLines ss os = segLines (ss.take i) (os.take i) ++ segLines (ss.drop i) (os.drop i)
  | [], os, _, h => by
    have : os = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst this; simp [segLines]
  | _ :: _, [], _, h => by simp at h
  | s :: ss, o :: os, 0, _ => by simp [segLines]
  | s :: ss, o :: os, i + 1, h => by
    simp only [List.take_succ_cons, List.drop_succ_cons, segLines, List.cons_append,
      List.append_assoc]
    rw [segLines_split ss os i (by simpa using h)]

/-- **Each segment's final lines have the call lines of its unsimplified ones**: `termOk`
keeps them; a forwarding block's code is one `jump` (no call line), and the `MachBuffer`
simplification keeps the call lines of the whole function (`plan_outs_callKeys`). -/
theorem plan_seg_nCalls {k : Nat} {af : AFunc} {fa : FnAsm} (h : emitFunc k af = .ok fa)
    {lm : Std.HashMap Lbl Nat} (hlm : labelOffsets fa.lines = .ok lm) {p : Plan}
    (hp : emitPlan k af = .ok p) :
    ∀ (i : Nat) (s : Seg) (o : List Line), p.segs[i]? = some s → p.outs[i]? = some o →
      nCalls o = nCalls s.term := by
  obtain ⟨hseg, hlen, hok, -⟩ := emitPlan_spec hp
  obtain ⟨-, -, hss⟩ := segsOf_spec hseg
  obtain ⟨-, -, hall⟩ := segsOk_spec hok
  have hor : ∀ (i : Nat) (s : Seg) (o : List Line), p.segs[i]? = some s → p.outs[i]? = some o →
      nCalls o = nCalls s.term ∨ nCalls s.term = 0 := by
    intro i s o hs ho
    obtain ⟨code, ps1, psm, ps2, hb, -, h2, -, -⟩ := hss i s hs
    have hab : af.blocks[s.idx]? = some (s.label, code) :=
      emitOrder_get (List.mem_of_getElem? hb)
    obtain ⟨A, -, hm⟩ := segNxts_get (n := 0) hs ho
    rcases hall _ hm with ⟨hf, -⟩ | hc
    · -- a forwarding block: its code is one `jump`, whose line is no call line
      right
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hf
      obtain ⟨b', code', hb', -, hc'⟩ := fwd?_spec hx
      obtain rfl := af_label_inj h hlm hab hb'
      rw [hab] at hb'
      simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hb'
      subst hb'
      rw [hc'] at h2
      simp only [List.getLast?_singleton, Option.toList_some] at h2
      rw [nCalls_eq, codeLinesE_callKeys h2]
      rfl
    · left
      unfold segTermOk at hc
      simp only [hab, Option.bind_some] at hc
      have hback : code.back? = code.toList.getLast? := by
        rw [Array.back?_eq_getElem?, List.getLast?_eq_getElem?]; simp
      rw [hback] at hc
      rw [nCalls_eq, nCalls_eq, termOk_callKeys hc ?_]
      cases hl : code.toList.getLast? with
      | none => exact True.intro
      | some a =>
        rw [hl] at h2
        exact rawTerm_of (codeLinesE_one h2)
  have hg := congrArg List.length (plan_outs_callKeys hp)
  rw [← nCalls_eq, ← nCalls_eq] at hg
  exact segLines_nCalls_eq p.segs p.outs hlen hor hg

theorem isCall_of_call {x : Insn} (hx : (∃ n, x = .bl n) ∨ ∃ r, x = .blr r) :
    (Line.ins x none).isCall = true := by
  rcases hx with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl

/-- **A `Q` state at a call item, taken apart**: the call line `j0` at the pc, whose index among
the call lines of the final code is the call's index in `af.calls`. (Re-stated for #553: the old
statement located the item's lines through `ftList`/`nxtOf` in block order, which the emission
plan replaced; `Q` now pins the lines after the block's segment (`segX`), so the call lines
before the pc are those of the segments before it and of the block's code before the call.) -/
theorem q_call_core {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {i : MInst}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i)
    {info : CallInfo} {c : Option TryInfo}
    (hc : (i = .call info ∧ c = none) ∨ ∃ ti, i = .tryCall info ti ∧ c = some ti) :
    ∃ j0 x, R.L[j0]? = some (.ins x none) ∧ Arm.r .PC s = R.pcOf j0 ∧
      ((∃ n, x = .bl n) ∨ ∃ r, x = .blr r) ∧ R.af.calls[nCalls (R.L.take j0)]? = some c := by
  have hcall : ∀ regs i', i.assign regs = .ok i' → (∀ ds, i' ≠ .args ds) ∧
      (∀ us, i' ≠ .rets us) ∧ aCall (.inst i') = some c ∧ ∃ x ls,
        (∀ ps, i'.lines R.ctx ps = .ok (.ins x none :: ls, ps)) ∧
        ((∃ n, x = .bl n) ∨ (∃ r, x = .blr r)) ∧ i'.callInsn? = some x := by
    intro regs i' hasg
    rcases hc with ⟨rfl, rfl⟩ | ⟨ti, rfl, rfl⟩
    · obtain ⟨hna, hnr, hx⟩ := call_hcall (ctx := R.ctx) regs i' hasg
      obtain ⟨ic, rfl⟩ := (assign_call_tryCall info regs).1 i' hasg
      exact ⟨hna, hnr, rfl, hx⟩
    · obtain ⟨hna, hnr, hx⟩ := tryCall_hcall (ctx := R.ctx) regs i' hasg
      obtain ⟨ic, rfl, -⟩ := (assign_call_tryCall info regs).2 ti i' hasg
      exact ⟨hna, hnr, rfl, hx⟩
  rcases Q.cases hq with hqs | ⟨vbf, allocsf, regsf, if_, xf, bx, hvbf, he, hits, half, hins,
    hasgf, -⟩
  rotate_left
  · -- a forwarding block: its `jump` is no call
    rw [hvb] at hvbf
    cases hvbf
    simp only [RItem.op.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hi1 := hi
    rw [hins] at hi1
    simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at hi1
    subst hi1
    obtain ⟨-, -, -, x, ls, -, -, hxi⟩ := hcall regsf (.jump xf) hasgf
    simp [MInst.callInsn?] at hxi
  obtain ⟨j0, vb0, items, pre, code, X, ps1, psm, ps2, x, hvb0, hit, hsplit, -, hcode, hX, hT,
    -, hdrop, hpc, -, hx, hsc⟩ := id hqs
  rw [hvb] at hvb0; cases hvb0
  obtain ⟨c1, c2, hc1, hc2, rfl⟩ := itemsCode_cons hcode
  obtain ⟨regs, i1, i', rfl, hi0, hasg, hc1'⟩ := itemCode_op hc1
  rw [hi] at hi0; cases hi0
  obtain ⟨hna, hnr, hcI, xI, ls, hl, hxc, hxi⟩ := hcall regs i' hasg
  obtain rfl : c1 = [.inst i'] := by
    rcases hc1' with ⟨h, -, -⟩ | ⟨ds, h, -⟩ | ⟨us, h, -⟩
    · exact h
    · exact absurd h (hna ds)
    · exact absurd h (hnr us)
  have hrel : (Line.ins xI none).relaxable? = none := by
    rcases hxc with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
  -- the emission plan and block `b`'s segment
  obtain ⟨p, hp, -, -⟩ := emitFunc_ok hR.emit
  have hPL : planLines R.fa.k R.af = p.lines := by simp [planLines, hp]
  have hRL : R.L = relaxLines R.far p.lines := by rw [RL.L_plan hR, hPL]
  rw [hPL] at hdrop
  obtain ⟨sg, o, N⟩ := x
  obtain ⟨hxm, hxb⟩ := segX_mem hp hx
  obtain ⟨i0, hs0, ho0⟩ := segNxts_mem hxm
  obtain ⟨A, hA, hxA⟩ := segX_get hp hs0 ho0
  dsimp only at hxb hs0 ho0 hT hdrop
  rw [hxb, hx] at hxA
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hxA
  subst hxA
  obtain ⟨hseg, hlen, -, -⟩ := emitPlan_spec hp
  obtain ⟨-, -, hss⟩ := segsOf_spec hseg
  obtain ⟨codeB, psB1, psBm, psB2, hbB, h1B, -, -, -⟩ := hss i0 sg hs0
  have habB : R.af.blocks[sg.idx]? = some (sg.label, codeB) :=
    emitOrder_get (List.mem_of_getElem? hbB)
  -- block `b`'s code: the code before the call item (`P`), the call, the rest (`c2`)
  obtain ⟨-, -, -, hblk⟩ := (lowerRFunc_ok hR.alloc).1
  obtain ⟨codeAll, hcodeAll, hab⟩ := hblk b vb items hvb hit
  rw [hsplit] at hcodeAll
  obtain ⟨cpre, crest, -, hcrest, rfl⟩ := itemsCode_append hcodeAll
  rw [show R.fr = RAFrame.compute R.vc R.rf from rfl] at hcode
  rw [hcode] at hcrest
  cases hcrest
  have habB2 := habB
  rw [hxb, hab] at habB2
  simp only [Option.some.injEq, Prod.mk.injEq] at habB2
  obtain ⟨-, hcodeB⟩ := habB2
  obtain ⟨P, hP⟩ : ∃ P : List AInst, P = (if b = 0 then [AInst.prologue] else []) ++ cpre :=
    ⟨_, rfl⟩
  have hcB : codeB.toList = P ++ AInst.inst i' :: c2 := by rw [← hcodeB, hP]; simp
  rw [hcB] at h1B
  -- the call lines before the pc
  have hdropL : R.L.drop j0 = relaxLines R.far (X ++ o) ++
      (relaxLines R.far p.lines).drop (rix R.far p.lines (A.length + 1 + sg.body.length + o.length)) := by
    rw [hdrop, hRL]
  have hsum : (relaxLines R.far p.lines).take j0 ++ relaxLines R.far (X ++ o) =
      relaxLines R.far (p.lines.take (A.length + 1 + sg.body.length + o.length)) := by
    have e1 := List.take_append_drop j0 (relaxLines R.far p.lines)
    rw [← hRL, hdropL, hRL, ← List.append_assoc] at e1
    have e2 : relaxLines R.far p.lines = relaxLines R.far (p.lines.take
        (A.length + 1 + sg.body.length + o.length)) ++ (relaxLines R.far p.lines).drop
        (rix R.far p.lines (A.length + 1 + sg.body.length + o.length)) := by
      rw [relax_drop, ← relax_split]
    exact List.append_cancel_right (e1.trans e2)
  have htakeN : p.lines.take (A.length + 1 + sg.body.length + o.length) =
      A ++ .label (.block sg.label) :: (sg.body ++ o) := by
    have e : p.lines = (A ++ .label (.block sg.label) :: (sg.body ++ o)) ++
        (segLines (p.segs.drop (i0 + 1)) (p.outs.drop (i0 + 1)) ++ trapLines p.ps) := by
      rw [hA]; try simp only [List.append_assoc, List.cons_append]
    have hlenT : (A ++ .label (.block sg.label) :: (sg.body ++ o)).length =
        A.length + 1 + sg.body.length + o.length := by
      simp only [List.length_append, List.length_cons]; omega
    rw [e, ← hlenT, List.take_left]
  have hAeq : A = segLines (p.segs.take i0) (p.outs.take i0) := by
    have e := segLines_split p.segs p.outs i0 hlen
    rw [List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.mp hs0).1,
      List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.mp ho0).1] at e
    have hs0' : p.segs[i0]'(List.getElem?_eq_some_iff.mp hs0).1 = sg :=
      (List.getElem?_eq_some_iff.mp hs0).2
    have ho0' : p.outs[i0]'(List.getElem?_eq_some_iff.mp ho0).1 = o :=
      (List.getElem?_eq_some_iff.mp ho0).2
    rw [hs0', ho0', segLines] at e
    have e3 := hA
    rw [Plan.lines, e] at e3
    simp only [List.append_assoc, List.cons_append] at e3
    exact (List.append_cancel_right (by simpa only [List.append_assoc, List.cons_append] using e3)).symm
  have hnA : nCalls A = (((emitOrder R.af).take i0).flatMap
      (fun e : (Label × Array AInst) × Nat => blockCalls e.1)).length := by
    rw [hAeq, segLines_nCalls_congr _ _ (by rw [List.length_take, List.length_take, hlen])
      (fun i s o h1 h2 => plan_seg_nCalls hR.emit hR.lm hp i s o (getElem?_of_take h1)
        (getElem?_of_take h2)), nCalls_eq,
      segs_callKeys_take i0 hseg, flatMap_keys_length]
  -- the call lines of the block's code before the call
  have hX' : codeLinesE R.ctx R.af (AInst.inst i' :: c2).dropLast ps1 = .ok (X, psm) := hX
  have hbodyX : nCalls sg.body = (P.filterMap aKey).length + nCalls X := by
    rw [List.dropLast_append_of_ne_nil (by simp)] at h1B
    rw [nCalls_eq, nCalls_eq, codeLinesE_callKeys h1B, codeLinesE_callKeys hX',
      List.filterMap_append, List.length_append]
  have hcnt : nCalls (R.L.take j0) = nCalls A + (P.filterMap aKey).length := by
    have e := congrArg nCalls hsum
    rw [htakeN, ← hRL] at e
    simp only [nCalls_append, relaxLines_nCalls, nCalls_label_cons, hbodyX] at e
    omega
  -- the call's index in `af.calls`
  have hbc : blockCalls (sg.label, codeB) = P.filterMap aCall ++ c :: c2.filterMap aCall := by
    simp only [blockCalls]
    rw [hcB, List.filterMap_append, List.filterMap_cons, hcI]
  have hidx : nCalls (R.L.take j0) = ((((emitOrder R.af).take i0).flatMap
      (fun e => blockCalls e.1)) ++ P.filterMap aCall).length := by
    rw [hcnt, hnA, List.length_append, filterMap_aKey_length]
  have hcalls : R.af.calls[nCalls (R.L.take j0)]? = some c := by
    rw [hidx, calls_eq, flatMap_mid _ _ i0 _ hbB]
    dsimp only
    rw [hbc]
    simp only [List.append_assoc, List.cons_append]
    rw [← List.append_assoc]
    exact getElem?_mid _ _ _
  -- the call line at the pc
  have hj : R.L[j0]? = some (.ins xI none) := by
    by_cases hc2 : c2 = []
    · subst hc2
      simp only [List.append_nil, List.dropLast_singleton, List.getLast?_singleton,
        Option.toList_some] at hX hT
      simp only [codeLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hX
      obtain ⟨rfl, -⟩ := hX
      have hT' := codeLinesE_single hT
      rw [hl] at hT'
      simp only [Except.ok.injEq, Prod.mk.injEq] at hT'
      obtain ⟨hterm0, -⟩ := hT'
      obtain ⟨x', hx', hok'⟩ := hsc
      rw [hx] at hx'
      cases hx'
      unfold segTermOk at hok'
      dsimp only at hok'
      rw [habB, Option.bind_some, back?_toList, hcB] at hok'
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or] at hok'
      have hno : Line.target? (.ins xI none) = none := by
        rcases hxc with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
      have h0 := termOk_call_head (ls := ls) hxi (by rw [← hterm0]; rfl) hno hok'
      cases o with
      | nil => simp at h0
      | cons a o' =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
        subst h0
        rw [List.nil_append, relaxLines_cons, relaxLine_of_none hrel, List.singleton_append,
          List.cons_append] at hdrop
        exact drop_get hdrop
    · have hX2 : codeLinesE R.ctx R.af ([AInst.inst i'] ++ c2.dropLast) ps1 = .ok (X, psm) := by
        rwa [List.dropLast_append_of_ne_nil hc2] at hX
      obtain ⟨ls1, X'', psm', h1, -, rfl⟩ := codeLinesE_append _ _ _ _ _ hX2
      have h1' := codeLinesE_single h1
      rw [hl] at h1'
      simp only [Except.ok.injEq, Prod.mk.injEq] at h1'
      obtain ⟨rfl, -⟩ := h1'
      rw [List.cons_append, List.cons_append, relaxLines_cons, relaxLine_of_none hrel,
        List.singleton_append, List.cons_append] at hdrop
      exact drop_get hdrop
  exact ⟨j0, xI, hj, hpc, hxc, hcalls⟩

/-! ## The call-site pair of a `Q` state's call -/

/-- **The call-site pair of a call** (S10e, #553): at a `Q` state whose next item is a
`call`/`tryCall` of block `b`, the pc is at the call line `j` (`bl`/`blr`), and
`(c, lineOffset R.L j + 4)` is the pair `callSites` writes for this call (`c = some ti` for a
`tryCall`), as `personality_callSite` consumes it. `Q` pins the lines after the block's segment
in the emission plan, so no block needs to follow (`q_callSite`) and no check is needed for the
last block (`q_callSite_last`). -/
theorem q_callSite_any {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {i : MInst}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i)
    {info : CallInfo} {c : Option TryInfo}
    (hc : (i = .call info ∧ c = none) ∨ ∃ ti, i = .tryCall info ti ∧ c = some ti) :
    ∃ j x, R.L[j]? = some (.ins x none) ∧ Arm.r .PC s = R.pcOf j ∧
      ((∃ n, x = .bl n) ∨ ∃ r, x = .blr r) ∧
      (c, lineOffset R.L j + 4) ∈ R.af.calls.zip (scanLines R.fa.lines.toList 0 [] []).2 := by
  obtain ⟨j0, x, hj, hpc, hx, hn⟩ := q_call_core hR hq hvb hi hc
  exact ⟨j0, x, hj, hpc, hx, mem_calls_zip hj (isCall_of_call hx) rfl hn⟩

/-- **The call-site pair of a call in a block that is not the last one** (S10e): at a `Q` state
whose next item is a `call`/`tryCall` of block `b` (not `af`'s last block), the pc is at the call
line `j` (`bl`/`blr`), and `(c, lineOffset R.L j + 4)` is the pair `callSites` writes for this
call (`c = some ti` for a `tryCall`), as `personality_callSite` consumes it. (Since #553
`q_callSite_any` holds for every block; `hnl` is no longer needed.) -/
theorem q_callSite {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {i : MInst}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i)
    {info : CallInfo} {c : Option TryInfo}
    (hc : (i = .call info ∧ c = none) ∨ ∃ ti, i = .tryCall info ti ∧ c = some ti)
    (hnl : (R.af.blocks[b + 1]?).isSome) :
    ∃ j x, R.L[j]? = some (.ins x none) ∧ Arm.r .PC s = R.pcOf j ∧
      ((∃ n, x = .bl n) ∨ ∃ r, x = .blr r) ∧
      (c, lineOffset R.L j + 4) ∈ R.af.calls.zip (scanLines R.fa.lines.toList 0 [] []).2 := by
  exact q_callSite_any hR hq hvb hi hc

/-! ## Calls of the last block -/

/-- The line the code after a plain call starts with, where the emitter's state does not matter:
a trap (`udf`, the code after a call that does not return). -/
def nextLine? : List AInst → Option (Insn × Option Clif.TrapCode)
  | .inst (.udf code) :: _ => some (.udf 0xc11f, some code)
  | _ => none

/-- The line is the instruction line `l`. -/
def lineIs : Option Line → Insn × Option Clif.TrapCode → Bool
  | some (.ins i t), l => decide ((i, t) = l)
  | _, _ => false

/-- The line the code after a plain call starts with, where the emitter's state does not matter:
a register move (`mov`, e.g. of the call's result: one line, no branch, not relaxed), the `adrp`
of a GOT load (`loadExtNameGot`, e.g. of `_Unwind_Resume` after a cleanup pad's call), else
`nextLine?`. -/
def afterLine? : List AInst → Option (Insn × Option Clif.TrapCode)
  | .inst (.mov s rd rm) :: _ =>
    some (if rm == .sp then .mov true rd rm else .mov s.is64 rd rm, none)
  | .inst (.loadExtNameGot rd n) :: _ => some (.adrpGot rd n, none)
  | c => nextLine? c

/-- The calls of a block's code: the call's index among the block's calls, its handlers, and the
code after it. -/
def codeCalls (code : List AInst) : List (Nat × Option TryInfo × List AInst) :=
  (List.range code.length).filterMap fun q => match code[q]? with
    | some a => (aCall a).map fun c => (((code.take q).filterMap aCall).length, c, code.drop (q + 1))
    | none => none

/-- **The check for the calls of the last block** (decidable, on `af` and its final code `fa`):
for every call of the last block and every call line of `fa` with the same callee, the call line
is a call with the same handlers (`Option TryInfo`), or the call of the last block is a plain
call followed by a line (`afterLine?`) the call line is not followed by. -/
def lastCallsOk (af : AFunc) (fa : FnAsm) : Bool :=
  let L := fa.lines.toList
  let code := (af.blocks.back?.map (·.2.toList)).getD []
  let base := af.calls.length - (code.filterMap aCall).length
  (codeCalls code).all fun q =>
    (callIdx L).zipIdx.all fun p =>
      decide ((callKeys L)[p.2]? ≠ (callKeys L)[base + q.1]?) ||
        decide (af.calls[p.2]? = some q.2.1) ||
        (q.2.1.isNone && match afterLine? q.2.2 with
          | some l => !lineIs L[p.1 + 1]? l
          | none => false)

theorem mem_codeCalls {P c2 : List AInst} {a : AInst} {c : Option TryInfo} (ha : aCall a = some c) :
    ((P.filterMap aCall).length, c, c2) ∈ codeCalls (P ++ a :: c2) := by
  simp only [codeCalls, List.mem_filterMap, List.mem_range]
  refine ⟨P.length, by simp, ?_⟩
  simp [ha, List.take_left']

theorem nextLine?_some {c : List AInst} {l : Insn × Option Clif.TrapCode} (h : nextLine? c = some l) :
    ∃ code c3, c = .inst (.udf code) :: c3 ∧ l = (.udf 0xc11f, some code) := by
  unfold nextLine? at h
  split at h
  · exact ⟨_, _, rfl, (Option.some.inj h).symm⟩
  · cases h

theorem afterLine?_some {c : List AInst} {l : Insn × Option Clif.TrapCode}
    (h : afterLine? c = some l) :
    (∃ code c3, c = .inst (.udf code) :: c3 ∧ l = (.udf 0xc11f, some code)) ∨
    (∃ s rd rm c3, c = .inst (.mov s rd rm) :: c3 ∧
      l = (if rm == .sp then .mov true rd rm else .mov s.is64 rd rm, none)) ∨
    ∃ rd n c3, c = .inst (.loadExtNameGot rd n) :: c3 ∧ l = (.adrpGot rd n, none) := by
  unfold afterLine? at h
  split at h
  · exact .inr (.inl ⟨_, _, _, _, rfl, (Option.some.inj h).symm⟩)
  · exact .inr (.inr ⟨_, _, _, rfl, (Option.some.inj h).symm⟩)
  · exact .inl (nextLine?_some h)

/-- Witness: the move of a call's result after the call (`mov x0, x19`) is a line `afterLine?`
names, as in the last block of `gimli::read::abbrev::…::parse` (std, T3). -/
example : afterLine? [.inst (.mov .size64 (.x 0) (.x 19)), .epilogueRet] =
    some (.mov true (.x 0) (.x 19), none) := rfl

/-- Witness: the GOT load of `_Unwind_Resume` after a cleanup pad's call is a line `afterLine?`
names (its `adrp`), as in the last block of three `regex` functions (deps). -/
example : afterLine? [.inst (.loadExtNameGot (.x 8) "_Unwind_Resume"), .epilogueRet] =
    some (.adrpGot (.x 8) "_Unwind_Resume", none) := rfl

/-- **The call-site pair of a call in the last block** (S10e): as `q_callSite`, for `af`'s last
block, under `lastCallsOk`. (Since #553 `q_callSite_any` holds for every block: `Q` pins the
lines after the block's segment in the emission plan, so `hlast` and `hok` are no longer
needed; the statement is kept for its callers.) -/
theorem q_callSite_last {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {i : MInst}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i)
    {info : CallInfo} {c : Option TryInfo}
    (hc : (i = .call info ∧ c = none) ∨ ∃ ti, i = .tryCall info ti ∧ c = some ti)
    (hlast : R.af.blocks[b + 1]? = none) (hok : lastCallsOk R.af R.fa = true) :
    ∃ j x, R.L[j]? = some (.ins x none) ∧ Arm.r .PC s = R.pcOf j ∧
      ((∃ n, x = .bl n) ∨ ∃ r, x = .blr r) ∧
      (c, lineOffset R.L j + 4) ∈ R.af.calls.zip (scanLines R.fa.lines.toList 0 [] []).2 := by
  exact q_callSite_any hR hq hvb hi hc

end Backend.Proof
