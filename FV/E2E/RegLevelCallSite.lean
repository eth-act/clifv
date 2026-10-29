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

theorem calls_eq (af : AFunc) : af.calls = af.blocks.toList.flatMap blockCalls := by
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
  rcases l with ⟨i, t⟩ | ⟨a, b⟩ | ⟨w⟩ | ⟨l⟩
  · cases i <;> rfl
  · rfl
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

theorem ftStep_callKeys (ln : Line) (rest : List Line) :
    callKeys (ftStep ln rest[0]? rest[1]?).1 =
      callKeys ((ln :: rest).take (ftStep ln rest[0]? rest[1]?).2) := by
  rcases rest with _ | ⟨x, _ | ⟨y, r⟩⟩
  all_goals
    simp only [List.getElem?_nil, List.getElem?_cons_zero, List.getElem?_cons_succ]
    unfold ftStep
    repeat' split
  all_goals simp_all [callKeys, List.filterMap_cons]
  all_goals simp_all [Line.callKey]

theorem ftList_callKeys : ∀ (n : Nat) (L : List Line), L.length ≤ n →
    callKeys (ftList L) = callKeys L
  | _, [], _ => by simp [ftList, callKeys]
  | 0, _ :: _, h => by simp at h
  | n + 1, ln :: rest, h => by
    have hp := (ftStep_pos ln rest[0]? rest[1]?).1
    rw [ftList_cons]
    rw [callKeys_append, ftStep_callKeys, ftList_callKeys n _ (by simp at h ⊢; omega),
      ← callKeys_append, List.take_append_drop]

theorem callKeys_ftList (L : List Line) : callKeys (ftList L) = callKeys L :=
  ftList_callKeys _ L (Nat.le_refl _)

theorem nCalls_ftList (L : List Line) : nCalls (ftList L) = nCalls L := by
  rw [nCalls_eq, nCalls_eq, callKeys_ftList]

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

theorem blocksLinesE_callKeys {c : FnCtx} {af : AFunc} :
    ∀ {bs : List (Label × Array AInst)} {ps ps' : PState} {body : List Line},
      blocksLinesE c af bs ps = .ok (body, ps') → callKeys body = bs.flatMap blockKeys
  | [], ps, ps', body, h => by
    simp only [blocksLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | (l0, code0) :: bs, ps, ps', body, h => by
    simp only [blocksLinesE, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i r hr
      split at h
      · cases h
      · rename_i r2 hr2
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.1, List.cons_append, callKeys_label_cons, callKeys_append, codeLinesE_callKeys hr,
          blocksLinesE_callKeys hr2, List.flatMap_cons]
        rfl

/-- Block `b`'s label in the lines before `fallthrough`, with the callees before it. -/
theorem blocksLinesE_at {c : FnCtx} {af : AFunc} :
    ∀ {bs : List (Label × Array AInst)} {ps psF : PState} {body : List Line} {b : Nat}
      {l : Label} {code : Array AInst},
      blocksLinesE c af bs ps = .ok (body, psF) → bs[b]? = some (l, code) →
      ∃ pre post, body = pre ++ .label (.block l) :: post ∧
        callKeys pre = (bs.take b).flatMap blockKeys
  | [], _, _, _, _, _, _, _, hb => by simp at hb
  | (l0, code0) :: bs, ps, psF, body, b, l, code, h, hb => by
    simp only [blocksLinesE, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i r hr
      split at h
      · cases h
      · rename_i r2 hr2
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        cases b with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          exact ⟨[], r.1 ++ r2.1, by simp, rfl⟩
        | succ b =>
          simp only [List.getElem?_cons_succ] at hb
          obtain ⟨pre, post, hbody, hk⟩ := blocksLinesE_at hr2 hb
          refine ⟨.label (.block l0) :: r.1 ++ pre, post, by rw [hbody]; simp, ?_⟩
          rw [List.cons_append, callKeys_label_cons, callKeys_append, codeLinesE_callKeys hr, hk,
            List.take_succ_cons, List.flatMap_cons]
          rfl

theorem trapLines_callKeys (ts : List (Lbl × Clif.TrapCode)) : callKeys (trapLines ts) = [] := by
  apply callKeys_nil
  intro l hl
  simp only [trapLines, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false] at hl
  obtain ⟨p, -, rfl | rfl⟩ := hl <;> rfl

/-- The literal pool has no call lines (#565). -/
theorem emitPool_callKeys (c : FnCtx) (af : AFunc) : callKeys (emitPool c af) = [] := by
  simp only [callKeys, List.filterMap_eq_nil_iff]
  intro ln hln
  rcases emitPool_mem hln with ⟨w, rfl⟩ | ⟨n, rfl⟩ <;> rfl

/-! ## The call lines of the final code are the function's calls, in order -/

/-- **The callees of the call lines of the final code are those of `af`'s calls**, in order. -/
theorem L_callKeys {R : RL} (hR : R.Wf) : callKeys R.L = R.af.blocks.toList.flatMap blockKeys := by
  obtain ⟨body, ps, hb, hL, -⟩ := emitFunc_ok hR.emit
  show callKeys R.fa.lines.toList = _
  rw [hL, callKeys_append, emitPool_callKeys, List.append_nil, relaxLines_callKeys, callKeys_append,
    callKeys_ftList, trapLines_callKeys, List.append_nil]
  exact blocksLinesE_callKeys hb

/-- Block `b'`'s label line in the final code, with the callees of the call lines before it. -/
theorem label_at {R : RL} (hR : R.Wf) {b' : Nat} {l' : Label} {code' : Array AInst}
    (h : R.af.blocks[b']? = some (l', code')) :
    ∃ J, R.L[J]? = some (.label (.block l')) ∧
      callKeys (R.L.take J) = (R.af.blocks.toList.take b').flatMap blockKeys := by
  obtain ⟨body, ps, hb, hL, -⟩ := emitFunc_ok hR.emit
  obtain ⟨pre, post, rfl, hk⟩ := blocksLinesE_at hb (by simpa using h)
  obtain ⟨Z, hZ⟩ := ftList_snoc_label (.block l') pre
  have hsplit := ftList_label_split (.block l') post pre
  rw [hZ] at hsplit
  generalize emitFar ⟨R.fa.k, R.af.slotBase⟩ R.af = F at hL
  have hL' : R.L = relaxLines F Z ++ (Line.label (.block l') ::
      (relaxLines F (ftList post ++ trapLines ps.traps.toList) ++ emitPool ⟨R.fa.k, R.af.slotBase⟩ R.af)) := by
    show R.fa.lines.toList = _
    rw [hL, hsplit, List.append_assoc, List.append_assoc, relaxLines_append, List.singleton_append,
      relaxLines_cons, relaxLine_label, List.singleton_append, List.append_assoc, List.cons_append]
  have hZk : callKeys Z = callKeys pre := by
    have := callKeys_ftList (pre ++ [.label (.block l')])
    rw [hZ, callKeys_append, callKeys_append] at this
    simpa [callKeys, Line.callKey] using this
  refine ⟨(relaxLines F Z).length, ?_, ?_⟩
  · rw [hL']; simp
  · rw [hL', List.take_left, relaxLines_callKeys, hZk, hk]

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
    | data w =>
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
    | data w =>
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

theorem itemsCode_append {fr : RAFrame} {vb : VBlock} :
    ∀ {A B : List RItem} {code : List AInst}, itemsCode fr vb (A ++ B) = .ok code →
      ∃ ca cb, itemsCode fr vb A = .ok ca ∧ itemsCode fr vb B = .ok cb ∧ code = ca ++ cb
  | [], B, code, h => ⟨[], code, rfl, h, rfl⟩
  | a :: A, B, code, h => by
    obtain ⟨c1, c2, h1, h2, rfl⟩ := itemsCode_cons h
    obtain ⟨ca, cb, ha, hb, rfl⟩ := itemsCode_append h2
    refine ⟨c1 ++ ca, cb, ?_, hb, by simp⟩
    simp [itemsCode, h1, ha, bind, Except.bind, pure, Except.pure]

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

theorem getElem?_mid {α : Type} (X : List α) (a : α) (Z : List α) {n : Nat} (hn : n = X.length) :
    (X ++ a :: Z)[n]? = some a := by
  subst hn; simp

/-- **A `Q` state at a call item, taken apart**: the call line `j0` at the pc, the lines `ls` of
the block's remaining code after it, and the call's index `n` in `af.calls` (with its callee,
the call line's, at index `n` of the callees), between the calls of the blocks before `b` and
those of blocks `0..b`; the block's code around the call (`P ++ a :: c2`), and for a plain call
the lines `ls` = the call line, then the lines of `c2`. -/
theorem q_call_core {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {i : MInst}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i)
    {info : CallInfo} {c : Option TryInfo}
    (hc : (i = .call info ∧ c = none) ∨ ∃ ti, i = .tryCall info ti ∧ c = some ti) :
    ∃ j0 x ls T n, R.L[j0]? = some (.ins x none) ∧ Arm.r .PC s = R.pcOf j0 ∧
      ((∃ n, x = .bl n) ∨ ∃ r, x = .blr r) ∧
      R.L.drop j0 = relaxLines R.far (ftList (ls ++ nxtOf R.af b)) ++ T ∧
      R.af.calls[n]? = some c ∧
      (R.af.blocks.toList.flatMap blockKeys)[n]? = (Line.ins x none).callKey ∧
      (∃ p, R.af.blocks[b]? = some p) ∧
      ((R.af.blocks.toList.take b).flatMap blockCalls).length ≤ n ∧
      n + nCalls ls = ((R.af.blocks.toList.take (b + 1)).flatMap blockCalls).length ∧
      ∃ (P : List AInst) (a : AInst) (c2 : List AInst) (ls2 : List Line) (ps ps' : PState),
        R.af.blocks[b]? = some (vb.label, (P ++ a :: c2).toArray) ∧ aCall a = some c ∧
        n = ((R.af.blocks.toList.take b).flatMap blockCalls).length + (P.filterMap aCall).length ∧
        codeLinesE R.ctx R.af c2 ps = .ok (ls2, ps') ∧ (c = none → ls = .ins x none :: ls2) := by
  obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops, hal, hit, hsplit,
    hasg, hc1, -, -, -, hc2, h1, h2, -, hdrop, hpc, -⟩ := q_op hq hvb hi
  -- the allocated call
  obtain ⟨ic, hic⟩ : ∃ ic, (i' = .call ic ∧ c = none) ∨ ∃ ti, i' = .tryCall ic ti ∧ c = some ti := by
    rcases hc with ⟨rfl, rfl⟩ | ⟨ti, rfl, rfl⟩
    · obtain ⟨ic, rfl⟩ := (assign_call_tryCall info regs).1 i' hasg
      exact ⟨ic, .inl ⟨rfl, rfl⟩⟩
    · obtain ⟨ic, rfl, -⟩ := (assign_call_tryCall info regs).2 ti i' hasg
      exact ⟨ic, .inr ⟨ti, rfl, rfl⟩⟩
  have hna : ∀ ds, i' ≠ .args ds := by
    rcases hic with ⟨rfl, -⟩ | ⟨_, rfl, -⟩ <;> intro _ h <;> cases h
  have hnr : ∀ us, i' ≠ .rets us := by
    rcases hic with ⟨rfl, -⟩ | ⟨_, rfl, -⟩ <;> intro _ h <;> cases h
  have hcI : aCall (.inst i') = some c := by
    rcases hic with ⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩ <;> rfl
  have hkI : aKey (.inst i') = some ic.dest := by
    rcases hic with ⟨rfl, -⟩ | ⟨_, rfl, -⟩ <;> rfl
  obtain rfl : c1 = [.inst i'] := by
    rcases hc1 with ⟨h, -, -⟩ | ⟨ds, h, -⟩ | ⟨us, h, -⟩
    · exact h
    · exact absurd h (hna ds)
    · exact absurd h (hnr us)
  have hl1 := codeLinesE_single h1
  have hk1 : callKeys ls1 = [ic.dest] := by rw [lines_callKeys hl1, hkI]; rfl
  -- the call line
  obtain ⟨x, rest1, rfl, hx, hkx⟩ : ∃ x rest1, ls1 = .ins x none :: rest1 ∧
      ((∃ n, x = .bl n) ∨ ∃ r, x = .blr r) ∧ (Line.ins x none).callKey = some ic.dest := by
    rcases hic with ⟨rfl, -⟩ | ⟨ti, rfl, -⟩ <;> cases hd : ic.dest <;>
      simp [MInst.lines, hd, pure, Except.pure] at hl1 <;> obtain ⟨e1, -⟩ := hl1 <;> subst e1 <;>
      exact ⟨_, _, rfl, by simp, by simp [Line.callKey]⟩
  have hdrop0 := hdrop
  rw [List.cons_append, ftList_cons, ftStep_call hx] at hdrop0
  simp only [List.drop_one, List.tail_cons, List.cons_append] at hdrop0
  rw [relaxLines_cons, relaxLine_of_none (by rcases hx with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl),
    List.singleton_append, List.cons_append] at hdrop0
  have hj : R.L[j0]? = some (.ins x none) := drop_get (Z := []) (by rw [hdrop0]; rfl)
  -- the block's code
  obtain ⟨-, -, -, hblk⟩ := (lowerRFunc_ok hR.alloc).1
  obtain ⟨code, hcode, hab⟩ := hblk b vb items hvb hit
  rw [hsplit] at hcode
  obtain ⟨cpre, crest, -, hcrest, rfl⟩ := itemsCode_append hcode
  obtain ⟨c1a, c2a, hc1a, hc2a, rfl⟩ := itemsCode_cons hcrest
  rw [show R.fr = RAFrame.compute R.vc R.rf from rfl] at hc2
  rw [hc2] at hc2a
  cases hc2a
  obtain ⟨regs', i0, i2, hal', hi0, hasg', hc1b⟩ := itemCode_op hc1a
  obtain rfl := regsArr_of_map (hal'.symm.trans hal)
  rw [hi] at hi0; cases hi0
  rw [hasg] at hasg'; cases hasg'
  obtain rfl : c1a = [.inst i'] := by
    rcases hc1b with ⟨h, -, -⟩ | ⟨ds, h, -⟩ | ⟨us, h, -⟩
    · exact h
    · exact absurd h (hna ds)
    · exact absurd h (hnr us)
  -- the calls
  obtain ⟨P, hP⟩ : ∃ P : List AInst, P = (if b = 0 then [AInst.prologue] else []) ++ cpre :=
    ⟨_, rfl⟩
  have hab' : R.af.blocks.toList[b]? = some (vb.label, (P ++ AInst.inst i' :: c2).toArray) := by
    rw [Array.getElem?_toList, hab, hP]; simp
  have hbc : blockCalls (vb.label, (P ++ AInst.inst i' :: c2).toArray) =
      P.filterMap aCall ++ c :: c2.filterMap aCall := by
    simp [blockCalls, List.filterMap_append, hcI]
  have hbk : blockKeys (vb.label, (P ++ AInst.inst i' :: c2).toArray) =
      P.filterMap aKey ++ ic.dest :: c2.filterMap aKey := by
    simp [blockKeys, List.filterMap_append, hkI]
  refine ⟨j0, x, .ins x none :: rest1 ++ ls2, T,
    ((R.af.blocks.toList.take b).flatMap blockCalls).length + (P.filterMap aCall).length,
    hj, hpc, hx, by rw [hdrop, List.append_assoc], ?_, ?_, ⟨_, hab⟩, by omega, ?_, ?_⟩
  · rw [calls_eq, flatMap_mid _ _ b _ hab', hbc, List.append_assoc, ← List.append_assoc]
    exact getElem?_mid _ _ _ (by simp)
  · rw [flatMap_mid _ _ b _ hab', hbk, List.append_assoc, ← List.append_assoc, hkx]
    exact getElem?_mid _ _ _ (by rw [List.length_append, flatMap_blockKeys_length, filterMap_aKey_length])
  · rw [flatMap_take_succ _ _ b _ hab', hbc, nCalls_eq, callKeys_append, hk1,
      codeLinesE_callKeys h2]
    simp [filterMap_aKey_length]
    omega
  · refine ⟨P, .inst i', c2, ls2, psm, ps2, by rw [hab, hP]; simp, hcI, rfl, h2, fun hc0 => ?_⟩
    rcases hic with ⟨rfl, -⟩ | ⟨ti, -, hti⟩
    · have : rest1 = [] := by
        cases hd : ic.dest <;> simp [MInst.lines, hd, pure, Except.pure] at hl1 <;> simp [hl1]
      subst this; rfl
    · rw [hc0] at hti; cases hti

/-! ## The call-site pair of a `Q` state's call -/

theorem isCall_of_call {x : Insn} (hx : (∃ n, x = .bl n) ∨ ∃ r, x = .blr r) :
    (Line.ins x none).isCall = true := by
  rcases hx with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl

/-- **The call-site pair of a call in a block that is not the last one** (S10e): at a `Q` state
whose next item is a `call`/`tryCall` of block `b` (not `af`'s last block), the pc is at the call
line `j` (`bl`/`blr`), and `(c, lineOffset R.L j + 4)` is the pair `callSites` writes for this
call (`c = some ti` for a `tryCall`), as `personality_callSite` consumes it. The block after `b`
anchors the pc's line: `Q` locates the item's lines only up to the lines that follow it, and
the next block's label is unique (`RL.label_unique`). -/
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
  obtain ⟨j0, x, ls, T, n, hj, hpc, hx, hdrop, hcn, -, -, -, hn, -⟩ := q_call_core hR hq hvb hi hc
  obtain ⟨⟨l', code'⟩, hb1⟩ := Option.isSome_iff_exists.mp hnl
  obtain ⟨J, hJ, hJk⟩ := label_at hR hb1
  have hnxt : nxtOf R.af b = [.label (.block l')] := by simp [nxtOf, hb1]
  rw [hnxt] at hdrop
  obtain ⟨Z, hZ⟩ := ftList_snoc_label (.block l') ls
  rw [hZ, relaxLines_append] at hdrop
  have hdrop' : R.L.drop j0 = relaxLines R.far Z ++ (.label (.block l') :: T) := by
    rw [hdrop]; simp [relaxLines, relaxLine, Line.relaxable?]
  have hJ0 : R.L[j0 + (relaxLines R.far Z).length]? = some (.label (.block l')) := by
    have := congrArg (·[(relaxLines R.far Z).length]?) hdrop'
    simpa [List.getElem?_drop] using this
  have hJeq : j0 + (relaxLines R.far Z).length = J := RL.label_unique hR hJ0 hJ
  have htake : R.L.take J = R.L.take j0 ++ relaxLines R.far Z := by
    rw [← hJeq, List.take_add, hdrop', List.take_left]
  have hZn : nCalls Z = nCalls ls := by
    have := nCalls_ftList (ls ++ [.label (.block l')])
    rw [hZ, nCalls_append, nCalls_append] at this
    simpa [nCalls, Line.isCall, Line.insn?, callInsn?] using this
  have hcount : nCalls (R.L.take J) =
      ((R.af.blocks.toList.take (b + 1)).flatMap blockCalls).length := by
    rw [nCalls_eq, hJk, flatMap_blockKeys_length]
  rw [htake, nCalls_append, relaxLines_nCalls, hZn] at hcount
  exact ⟨j0, x, hj, hpc, hx, mem_calls_zip hj (isCall_of_call hx) (by omega) hcn⟩

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

/-- A line that is no branch stays as it is (`ftStep`). -/
theorem ftStep_plainIns (x : Insn) (hc : x.condTarget? = none) (hb : ∀ y, x ≠ .b y)
    (n1 n2 : Option Line) : ftStep (.ins x none) n1 n2 = ([.ins x none], 1) := by
  unfold ftStep
  split
  · rename_i h
    simp only [Line.ins.injEq] at h
    exact absurd h.1 (hb _)
  · split
    · rename_i heq _
      simp only [Line.ins.injEq] at heq
      obtain ⟨rfl, -⟩ := heq
      simp [hc]
    · rfl

theorem ftStep_mov (x : Insn) (hx : ∃ b rd rm, x = .mov b rd rm) (n1 n2 : Option Line) :
    ftStep (.ins x none) n1 n2 = ([.ins x none], 1) := by
  have hc : x.condTarget? = none := by obtain ⟨_, _, _, rfl⟩ := hx; rfl
  have hb : ∀ y, x ≠ .b y := by obtain ⟨_, _, _, rfl⟩ := hx; intro y h; cases h
  unfold ftStep
  split
  · rename_i h
    simp only [Line.ins.injEq] at h
    exact absurd h.1 (hb _)
  · split
    · rename_i heq _
      simp only [Line.ins.injEq] at heq
      obtain ⟨rfl, -⟩ := heq
      simp [hc]
    · rfl

/-- Witness: the move of a call's result after the call (`mov x0, x19`) is a line `afterLine?`
names, as in the last block of `gimli::read::abbrev::…::parse` (std, T3). -/
example : afterLine? [.inst (.mov .size64 (.x 0) (.x 19)), .epilogueRet] =
    some (.mov true (.x 0) (.x 19), none) := rfl

/-- Witness: the GOT load of `_Unwind_Resume` after a cleanup pad's call is a line `afterLine?`
names (its `adrp`), as in the last block of three `regex` functions (deps). -/
example : afterLine? [.inst (.loadExtNameGot (.x 8) "_Unwind_Resume"), .epilogueRet] =
    some (.adrpGot (.x 8) "_Unwind_Resume", none) := rfl

theorem ftStep_trap (i : Insn) (t : Clif.TrapCode) (n1 n2 : Option Line) :
    ftStep (.ins i (some t)) n1 n2 = ([.ins i (some t)], 1) := by
  unfold ftStep
  split <;> simp_all

/-- **The call-site pair of a call in the last block** (S10e): as `q_callSite`, for `af`'s last
block, under `lastCallsOk`. `Q` does not locate the item's lines there (nothing follows them in
the block lines), but every call line with the call's callee is a call with the same handlers,
or not followed by the line that follows this (plain) call in `Q`'s lines. -/
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
  obtain ⟨j0, x, ls, T, n, hj, hpc, hx, hdrop, hcn, hkn, -, -, hn, P, a, c2, ls2, ps, ps', hp, haC,
    hnP, hc2, hls⟩ := q_call_core hR hq hvb hi hc
  have hxc := isCall_of_call hx
  obtain ⟨kd, hkd⟩ : ∃ kd, (Line.ins x none).callKey = some kd := by
    rcases hx with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> exact ⟨_, rfl⟩
  have hkeys := L_callKeys hR
  have hlen : (callKeys R.L).length = R.af.calls.length := by
    rw [hkeys, flatMap_blockKeys_length, calls_eq]
  -- b is the last block
  have hb : b + 1 = R.af.blocks.size := by
    have h1 := (Array.getElem?_eq_some_iff.mp hp).1
    have h2 := Array.getElem?_eq_none_iff.mp hlast
    omega
  have hback : R.af.blocks.back? = some (vb.label, (P ++ a :: c2).toArray) := by
    rw [Array.back?_eq_getElem?, show R.af.blocks.size - 1 = b by omega, hp]
  have hpL : R.af.blocks.toList[b]? = some (vb.label, (P ++ a :: c2).toArray) := by
    rw [Array.getElem?_toList, hp]
  have hall : (R.af.blocks.toList.take (b + 1)) = R.af.blocks.toList :=
    List.take_of_length_le (by simp; omega)
  have hk : R.af.calls.length = ((R.af.blocks.toList.take b).flatMap blockCalls).length +
      ((P ++ a :: c2).filterMap aCall).length := by
    have h := flatMap_take_succ blockCalls _ b _ hpL
    rw [hall] at h
    rw [calls_eq, h, List.length_append]
    simp [blockCalls]
  -- the call line `j0` is the `n0`-th call line
  have hk0 : (callKeys R.L)[nCalls (R.L.take j0)]? = some kd := by
    rcases callKeys_at hj with h | h
    · rw [h, hkd]
    · rw [hkd] at h; cases h
  have hn0lt : nCalls (R.L.take j0) < R.af.calls.length := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hk0).1
  obtain ⟨c0, hc0⟩ : ∃ c0, R.af.calls[nCalls (R.L.take j0)]? = some c0 :=
    ⟨_, List.getElem?_eq_getElem hn0lt⟩
  have hkn' : (callKeys R.L)[n]? = some kd := by rw [hkeys, hkn, hkd]
  -- the check at this call and the pc's call line
  simp only [lastCallsOk, hback, Option.map_some, Option.getD_some, List.all_eq_true,
    ] at hok
  have h1 := hok _ (mem_codeCalls (P := P) (c2 := c2) haC) (j0, nCalls (R.L.take j0))
    (List.mem_zipIdx_iff_getElem?.mpr (callIdx_at R.L j0 _ hj hxc))
  have hbase : R.af.calls.length - ((P ++ a :: c2).filterMap aCall).length +
      (P.filterMap aCall).length = n := by omega
  simp only [hbase, show R.fa.lines.toList = R.L from rfl, hk0, hkn', ne_eq, not_true_eq_false,
    decide_false, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
    Option.isNone_iff_eq_none] at h1
  rcases h1 with h1 | ⟨rfl, h1⟩
  · rw [hc0] at h1
    obtain rfl := Option.some.inj h1
    exact ⟨j0, x, hj, hpc, hx, mem_calls_zip hj hxc rfl hc0⟩
  · -- a plain call followed by a trap or a move: the pc's call line is followed by that line
    exfalso
    obtain ⟨l, hl, h1⟩ : ∃ l, afterLine? c2 = some l ∧ lineIs R.L[j0 + 1]? l = false := by
      revert h1; cases afterLine? c2 <;> simp
    have hnx : nxtOf R.af b = [] := by simp [nxtOf, hlast]
    rcases afterLine?_some hl with ⟨code, c3, rfl, rfl⟩ | ⟨s', rd, rm, c3, rfl, rfl⟩ |
      ⟨rd, nm, c3, rfl, rfl⟩
    · simp only [codeLinesE, bind, Except.bind, ainstLines, MInst.lines, pure, Except.pure] at hc2
      split at hc2
      · cases hc2
      · rename_i r hr
        simp only [Except.ok.injEq, Prod.mk.injEq] at hc2
        obtain ⟨rfl, -⟩ := hc2
        rw [hls rfl, hnx, List.append_nil, List.singleton_append, ftList_cons, ftStep_call hx] at hdrop
        simp only [List.drop_one, List.tail_cons, List.singleton_append] at hdrop
        rw [ftList_cons, ftStep_trap] at hdrop
        simp only [List.drop_one, List.tail_cons, List.singleton_append] at hdrop
        rw [relaxLines_cons, relaxLine_of_none (by rcases hx with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl),
          relaxLines_cons, relaxLine_of_none rfl, List.singleton_append, List.singleton_append,
          List.cons_append, List.cons_append] at hdrop
        simp [drop_get1 hdrop, lineIs] at h1
    · generalize hy : (if rm == .sp then Insn.mov true rd rm else .mov s'.is64 rd rm) = y at h1
      have hym : ∃ b rd rm, y = .mov b rd rm := by
        subst hy; split <;> exact ⟨_, _, _, rfl⟩
      have hl1 : ∀ ps0, MInst.lines R.ctx (.mov s' rd rm) ps0 = .ok ([.ins y], ps0) := by
        intro ps0; subst hy; rfl
      simp only [codeLinesE, bind, Except.bind, ainstLines, hl1] at hc2
      split at hc2
      · cases hc2
      · rename_i r hr
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hc2
        obtain ⟨rfl, -⟩ := hc2
        rw [hls rfl, hnx, List.append_nil, List.singleton_append, ftList_cons, ftStep_call hx] at hdrop
        simp only [List.drop_one, List.tail_cons, List.singleton_append] at hdrop
        rw [ftList_cons, ftStep_mov y hym] at hdrop
        simp only [List.drop_one, List.tail_cons, List.singleton_append] at hdrop
        rw [relaxLines_cons, relaxLine_of_none (by rcases hx with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl),
          relaxLines_cons, relaxLine_of_none (by obtain ⟨_, _, _, rfl⟩ := hym; rfl),
          List.singleton_append, List.singleton_append, List.cons_append, List.cons_append] at hdrop
        simp [drop_get1 hdrop, lineIs] at h1
    · have hl1 : ∀ ps0, MInst.lines R.ctx (.loadExtNameGot rd nm) ps0 =
          .ok ([.ins (.adrpGot rd nm), .ins (.ldrGotLo12 rd rd nm)], ps0) := fun _ => rfl
      simp only [codeLinesE, bind, Except.bind, ainstLines, hl1] at hc2
      split at hc2
      · cases hc2
      · rename_i r hr
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hc2
        obtain ⟨rfl, -⟩ := hc2
        rw [hls rfl, hnx, List.append_nil, List.cons_append, List.cons_append, ftList_cons,
          ftStep_call hx] at hdrop
        simp only [List.drop_one, List.tail_cons, List.singleton_append] at hdrop
        rw [ftList_cons, ftStep_plainIns _ rfl (fun _ h => by cases h)] at hdrop
        simp only [List.drop_one, List.tail_cons, List.singleton_append] at hdrop
        rw [relaxLines_cons, relaxLine_of_none (by rcases hx with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl),
          relaxLines_cons, relaxLine_of_none rfl,
          List.singleton_append, List.singleton_append, List.cons_append, List.cons_append] at hdrop
        simp [drop_get1 hdrop, lineIs] at h1

end Backend.Proof
