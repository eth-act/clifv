import FV.E2E.RegLevelUTry
import FV.E2E.EmitPreOk
import FV.E2E.EmitLabels

/-!
# Completeness of the per-function unwinding checks (S10g, #404)

`unwFnsB` (FV/Link/UnwFns.lean) decides, per compiled function, the checks the unwinding theorem
consumes. Here: they pass for what the pipeline produces.

* `callSites_complete`: `callSites af fa` succeeds for the emitted code `fa` of `af`
  (`emitFunc`) when every handler of `af`'s `try_call`s is a cleanup (tag 0) or catch (tag 1)
  handler whose landing pad is a block of `af`.
-/

namespace Link.EhCheck.Complete

set_option autoImplicit false

open Backend Backend.Proof Backend.Proof.UnwindTables E2E

/-! ## The emitted code's calls and labels -/

/-- The callees of the call lines of the emitted code are those of `af`'s calls, in order. -/
theorem callKeys_emit {k : Nat} {af : AFunc} {fa : FnAsm} (h : emitFunc k af = .ok fa) :
    callKeys fa.lines.toList = af.blocks.toList.flatMap blockKeys := by
  obtain ⟨body, ps, hb, hL, -⟩ := emitFunc_ok h
  rw [hL, relaxLines_callKeys, callKeys_append, callKeys_ftList, trapLines_callKeys,
    List.append_nil]
  exact blocksLinesE_callKeys hb

theorem callIdx_length : ∀ L : List Line, (callIdx L).length = nCalls L
  | [] => rfl
  | ln :: L => by
    simp only [callIdx, List.length_append, List.length_map, callIdx_length L, nCalls,
      List.countP_cons]
    split <;> simp_all <;> omega

/-- The emitted code has one call line per call of `af`. -/
theorem nCalls_emit {k : Nat} {af : AFunc} {fa : FnAsm} (h : emitFunc k af = .ok fa) :
    nCalls fa.lines.toList = af.calls.length := by
  rw [nCalls_eq, callKeys_emit h, flatMap_blockKeys_length, calls_eq]

/-- Block `b`'s label is a line of the emitted code. -/
theorem label_mem_emit {k : Nat} {af : AFunc} {fa : FnAsm} (h : emitFunc k af = .ok fa)
    {b : Nat} {l : Label} {code : Array AInst} (hb : af.blocks[b]? = some (l, code)) :
    Line.label (.block l) ∈ fa.lines.toList := by
  obtain ⟨body, ps, hbl, hL, -⟩ := emitFunc_ok h
  obtain ⟨pre, post, rfl, -⟩ := blocksLinesE_at hbl (by simpa using hb)
  obtain ⟨Z, hZ⟩ := ftList_snoc_label (.block l) pre
  have hsplit := ftList_label_split (.block l) post pre
  rw [hZ] at hsplit
  rw [hL, hsplit, List.append_assoc, List.append_assoc, relaxLines_append, List.singleton_append,
    relaxLines_cons, relaxLine_label]
  simp

/-- A label line of `L` is found by `scanLines`' label list. -/
theorem scanLines_lookup_isSome : ∀ (L : List Line) (off : Nat) (labs : List (Label × Nat))
    (rets : List Nat) (l : Label),
    ((labs.lookup l).isSome ∨ Line.label (.block l) ∈ L) →
      ((scanLines L off labs rets).1.lookup l).isSome
  | [], _, labs, _, l, h => by
    simp only [List.not_mem_nil, or_false] at h
    simpa [scanLines] using h
  | ln :: L, off, labs, rets, l, h => by
    simp only [scanLines]
    apply scanLines_lookup_isSome
    rcases h with h | h
    · left
      unfold labsAfter
      split
      · rename_i l' _
        simp only [List.lookup_cons]
        split <;> simp_all
      · exact h
    · rcases List.mem_cons.1 h with h | h
      · left
        subst h
        simp [labsAfter]
      · exact .inr h

/-! ## `callSites` -/

/-- `mapM` in `Except` succeeds when every element's step does. -/
theorem mapM_ok_of {ε α β : Type} (f : α → Except ε β) :
    ∀ {l : List α}, (∀ a ∈ l, ∃ b, f a = .ok b) → ∃ bs, l.mapM f = .ok bs
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a (by simp)
    obtain ⟨bs, hbs⟩ := mapM_ok_of f (l := l) fun x hx => h x (by simp [hx])
    exact ⟨b :: bs, by simp [List.mapM_cons, hb, hbs, bind, Except.bind, pure, Except.pure]⟩

/-- The handlers of `af`'s `try_call`s. -/
def HandlersOk (af : AFunc) : Prop :=
  ∀ ti, some ti ∈ af.calls → ∀ h ∈ ti.handlers,
    (∃ n l, h = .tag n l ∧ n ≤ 1) ∧
      ∃ (b : Nat) (code : Array AInst), af.blocks[b]? = some (h.label, code)

/-- **`callSites` succeeds on the emitted code** when the handlers are cleanup/catch handlers
whose landing pads are blocks of `af`. -/
theorem callSites_complete {k : Nat} {af : AFunc} {fa : FnAsm} (he : emitFunc k af = .ok fa)
    (hh : HandlersOk af) : ∃ l, callSites af fa = .ok l := by
  unfold callSites
  by_cases hany : af.calls.any (·.isSome) = true
  · simp only [hany, Bool.not_true, Bool.false_eq_true, ite_false]
    have hlen : (scanLines fa.lines.toList 0 [] []).2.length = af.calls.length := by
      rw [scanLines_rets_eq]
      simp [callIdx_length, nCalls_emit he]
    simp only [hlen, bne_self_eq_false, Bool.false_eq_true, ite_false]
    -- every call's entries succeed
    have hent : ∀ p ∈ af.calls.zip (scanLines fa.lines.toList 0 [] []).2,
        ∃ es, siteEntries (scanLines fa.lines.toList 0 [] []).1 p = .ok es := by
      rintro ⟨c, ret⟩ hp
      have hc := (List.of_mem_zip hp).1
      simp only [siteEntries]
      split
      · exact ⟨_, rfl⟩
      · cases c with
        | none => simp [handlersOf] at *
        | some ti =>
          have hall : ∀ h ∈ ti.handlers, ∃ e, handlerEntry
              (scanLines fa.lines.toList 0 [] []).1 ret h = .ok e := by
            intro h hmem
            obtain ⟨⟨n, l, rfl, hn⟩, b, code, hb⟩ := hh ti hc h hmem
            have hs := scanLines_lookup_isSome fa.lines.toList 0 [] [] l
              (.inr (label_mem_emit he hb))
            obtain ⟨pad, hpad⟩ := Option.isSome_iff_exists.1 hs
            simp only [TryHandler.label] at hb
            rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn with rfl | rfl <;>
              exact ⟨_, by simp only [handlerEntry, TryHandler.label, hpad]; rfl⟩
          exact mapM_ok_of (handlerEntry (scanLines fa.lines.toList 0 [] []).1 ret) hall
    obtain ⟨sites, hs⟩ := mapM_ok_of _ hent
    exact ⟨some sites.flatten, by simp [hs, bind, Except.bind, pure, Except.pure]⟩
  · simp only [Bool.not_eq_true] at hany
    exact ⟨none, by simp [hany, pure, Except.pure]⟩

end Link.EhCheck.Complete

namespace Link.EhCheck.Complete

open Backend Backend.Proof Backend.Proof.UnwindTables E2E

/-! ## The entry block of the emitted code -/

theorem noTrap_nextS {c : FnCtx} {af : AFunc} {c2 : List AInst} {psm ps2 : PState}
    {ls2 : List Line} {b : Nat} (h2 : codeLinesE c af c2 psm = .ok (ls2, ps2)) :
    ∀ n, (ls2 ++ nxtOf af b)[1]? ≠ some (.label (.trap n)) := by
  intro n e
  have hm := List.mem_of_getElem? e
  rcases List.mem_append.1 hm with hm | hm
  · exact codeLinesE_noTrap _ _ _ _ h2 _ hm n rfl
  · simp only [nxtOf] at hm
    split at hm <;> simp at hm

/-- **The entry block in the emitted code** (`RegLevelFrame.entry_block` without the
activation): its label at line 0, then the prologue, then the `fallthrough` of its items'
lines. -/
theorem entry_static {vc : VCode} {rf : RFunc} {af : AFunc} {k : Nat} {fa : FnAsm}
    (halloc : lowerRFunc vc rf = .ok af) (hemit : emitFunc k af = .ok fa) {vb : VBlock}
    {items : Array RItem} (hvb : vc.blocks[0]? = some vb) (hit : rf.blocks[0]? = some items) :
    ∃ code ls ps1 ps2 T, itemsCode (RAFrame.compute vc rf) vb items.toList = .ok code ∧
      af.blocks[0]? = some (vb.label, (AInst.prologue :: code).toArray) ∧
      codeLinesE ⟨k, af.slotBase⟩ af code ps1 = .ok (ls, ps2) ∧
      fa.lines.toList[0]? = some (.label (.block vb.label)) ∧
      fa.lines.toList.drop 1 = prologueLines af.saves af.frameSize ++
        (relaxLines (emitFar ⟨k, af.slotBase⟩ af) (ftList (ls ++ nxtOf af 0)) ++ T) := by
  have hframe := lowerRFunc_frame halloc
  obtain ⟨⟨-, -, -, hbl⟩, -⟩ := lowerRFunc_ok halloc
  obtain ⟨code, hcode, haf⟩ := hbl 0 vb items hvb hit
  obtain ⟨body, psF, hb, -, hblk⟩ := emit_block hemit
  obtain ⟨j0, lsA, ps1, ps2, T, hj0, hdrop, hls, -, hj⟩ := hblk 0 _ _ haf
  obtain rfl := hj rfl
  simp only [ite_true] at hls
  obtain ⟨ls1, ls2, psm, h1, h2, rfl⟩ := codeLinesE_append _ _ _ _ _ hls
  simp only [codeLinesE, ainstLines, hframe, ite_true, bind, Except.bind, pure, Except.pure,
    List.append_nil, Except.ok.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  refine ⟨code, ls2, _, ps2, T, hcode, by simpa using haf, h2, hj0, ?_⟩
  show List.drop (0 + 1) fa.lines.toList = _
  rw [hdrop, List.append_assoc, ftR_plain_append _ _ _
    (fun ln h => by obtain ⟨_, _, _, hp⟩ := prologueLines_ins _ _ ln h; exact hp)
    (noTrap_nextS h2), List.append_assoc]

/-! ## `padsNonzeroB` -/

/-- `labelOffsets` keeps the labels found so far. -/
theorem go_mono : ∀ {L : List Line} {off : Nat} {m lm : Std.HashMap Lbl Nat},
    labelOffsets.go L off m = .ok lm → ∀ (l : Lbl) (v : Nat), m[l]? = some v → lm[l]? = some v
  | [], off, m, lm, h, l, v, hv => by
    simp only [labelOffsets.go, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact hv
  | ln :: L, off, m, lm, h, l, v, hv => by
    unfold labelOffsets.go at h
    cases ln with
    | label l' =>
      by_cases hc : m.contains l' = true
      · simp only [hc, ite_true] at h; cases h
      · simp only [hc, Bool.false_eq_true, ite_false] at h
        refine go_mono h l v ?_
        rw [Std.HashMap.getElem?_insert]
        split
        · rename_i heq
          exfalso; apply hc
          rw [beq_iff_eq] at heq; subst heq
          rw [Std.HashMap.contains_eq_isSome_getElem?, hv]; rfl
        · exact hv
    | ins i t => exact go_mono h l v hv
    | word a b => exact go_mono h l v hv

/-- `labelOffsets` gives a label first defined after byte offset `off` an offset ≥ `off`. -/
theorem go_ge : ∀ {L : List Line} {off : Nat} {m lm : Std.HashMap Lbl Nat} {l : Lbl} {v : Nat},
    labelOffsets.go L off m = .ok lm → m[l]? = none → lm[l]? = some v → off ≤ v
  | [], off, m, lm, l, v, h, hn, hv => by
    simp only [labelOffsets.go, pure, Except.pure, Except.ok.injEq] at h
    subst h; rw [hn] at hv; cases hv
  | ln :: L, off, m, lm, l, v, h, hn, hv => by
    unfold labelOffsets.go at h
    cases ln with
    | label l' =>
      by_cases hc : m.contains l' = true
      · simp only [hc, ite_true] at h; cases h
      · simp only [hc, Bool.false_eq_true, ite_false] at h
        by_cases he : l' = l
        · subst he
          have hlm := go_mono h l' off (by simp)
          rw [hlm] at hv; cases hv; exact Nat.le_refl _
        · exact go_ge h (by rw [Std.HashMap.getElem?_insert]; simp [he, hn]) hv
    | ins i t => exact Nat.le_trans (Nat.le_add_right _ _) (go_ge h hn hv)
    | word a b => exact Nat.le_trans (Nat.le_add_right _ _) (go_ge h hn hv)

/-- The emitted code: the entry label, the prologue's `stp`/`mov`, the rest. -/
theorem lines_head {vc : VCode} {rf : RFunc} {af : AFunc} {k : Nat} {fa : FnAsm}
    (halloc : lowerRFunc vc rf = .ok af) (hemit : emitFunc k af = .ok fa) {vb : VBlock}
    {items : Array RItem} (hvb : vc.blocks[0]? = some vb) (hit : rf.blocks[0]? = some items) :
    ∃ R, fa.lines.toList = .label (.block vb.label) ::
      .ins (.stp Reg.fp Reg.lr (.spPreIndexed (-16))) :: .ins (.mov true Reg.fp .sp) :: R := by
  obtain ⟨code, ls, ps1, ps2, T, hcode, haf, hcl, h0, hd⟩ := entry_static halloc hemit hvb hit
  rw [prologueLines_eq] at hd
  generalize fa.lines.toList = L at h0 hd ⊢
  cases L with
  | nil => cases h0
  | cons x xs =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
    simp only [List.drop_succ_cons, List.drop_zero] at hd
    subst h0
    exact ⟨_, by rw [hd]; rfl⟩

/-- Every label but the entry block's is at byte offset ≥ 8 (after the prologue's
`stp`/`mov`). -/
theorem label_off_ge {vc : VCode} {rf : RFunc} {af : AFunc} {k : Nat} {fa : FnAsm}
    (halloc : lowerRFunc vc rf = .ok af) (hemit : emitFunc k af = .ok fa) {vb : VBlock}
    {items : Array RItem} (hvb : vc.blocks[0]? = some vb) (hit : rf.blocks[0]? = some items)
    {lm : Std.HashMap Lbl Nat} (hlm : labelOffsets fa.lines = .ok lm) {l : Label} {v : Nat}
    (hl : l ≠ vb.label) (hv : lm[Lbl.block l]? = some v) : 8 ≤ v := by
  obtain ⟨R, hR⟩ := lines_head halloc hemit hvb hit
  unfold labelOffsets at hlm
  rw [hR] at hlm
  unfold labelOffsets.go at hlm
  simp only [Std.HashMap.contains_empty, Bool.false_eq_true, ite_false] at hlm
  unfold labelOffsets.go at hlm
  unfold labelOffsets.go at hlm
  simp only [Line.size] at hlm
  exact go_ge hlm (by rw [Std.HashMap.getElem?_insert]; simp [Ne.symm hl]) hv

/-- The `try_call` handlers' landing pads: at least one handler, none at the entry block. -/
def PadsOk (af : AFunc) (l0 : Label) : Prop :=
  ∀ ti, some ti ∈ af.calls → ti.handlers ≠ [] ∧ ∀ h ∈ ti.handlers, h.label ≠ l0

/-- **`padsNonzeroB` holds for the emitted code** when every `try_call` has a handler and no
handler's landing pad is the entry block. -/
theorem padsNonzero_complete {vc : VCode} {rf : RFunc} {af : AFunc} {k : Nat} {fa : FnAsm}
    {fb : FnBin} (halloc : lowerRFunc vc rf = .ok af) (hemit : emitFunc k af = .ok fa)
    (hlay : fa.layout = .ok fb) {vb : VBlock} {items : Array RItem}
    (hvb : vc.blocks[0]? = some vb) (hit : rf.blocks[0]? = some items) (hp : PadsOk af vb.label) :
    padsNonzeroB af fa = true := by
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hlay
  unfold padsNonzeroB
  rw [List.all_eq_true]
  rintro ⟨c, ret⟩ hmem
  cases c with
  | none => rfl
  | some ti =>
    obtain ⟨hne, hlab⟩ := hp ti (List.of_mem_zip hmem).1
    obtain ⟨h, hs, hh⟩ : ∃ h hs, ti.handlers = h :: hs := by
      cases hti : ti.handlers with
      | nil => exact absurd hti hne
      | cons h hs => exact ⟨h, hs, rfl⟩
    have hl := hlab h (by rw [hh]; simp)
    have hE : ∀ e, entryFor (scanLines fa.lines.toList 0 [] []).1 (some ti, ret) = some e →
        e.pad ≠ 0 := by
      intro e he
      simp only [entryFor, handlersOf, hh, handlerEntry?] at he
      cases hlk : (scanLines fa.lines.toList 0 [] []).1.lookup h.label with
      | none => rw [hlk] at he; cases he
      | some v =>
        have h8 := label_off_ge halloc hemit hvb hit hlm hl (scanLines_labelOffsets hlm hlk)
        rw [hlk, Option.bind_some] at he
        split at he <;> cases he <;> simp <;> omega
    cases hq : entryFor (scanLines fa.lines.toList 0 [] []).1 (some ti, ret) with
    | none => simp
    | some e => simpa [hq] using hE e hq

/-! ## `unwindRows` -/

/-- **`unwindRows` succeeds on the emitted code** when the code is below 4 GiB: the code starts
with the entry label and the prologue (`entry_static`), and the rows are the prologue's and the
pushes' (`prologueRows`, `pushRows`). -/
theorem unwindRows_complete {vc : VCode} {rf : RFunc} {af : AFunc} {k : Nat} {fa : FnAsm}
    {fb : FnBin} (halloc : lowerRFunc vc rf = .ok af) (hemit : emitFunc k af = .ok fa)
    (hlay : fa.layout = .ok fb) (hsz : 4 * fb.words.size < 2 ^ 32) {vb : VBlock}
    {items : Array RItem} (hvb : vc.blocks[0]? = some vb) (hit : rf.blocks[0]? = some items) :
    unwindRows af fa = .ok (prologueRows ++ pushRows af.saves 8) := by
  have hframe := lowerRFunc_frame halloc
  obtain ⟨code, ls, ps1, ps2, T, -, haf, -, h0, hd⟩ := entry_static halloc hemit hvb hit
  generalize hP : prologueLines af.saves af.frameSize = P at hd
  have hins : ∀ ln ∈ P, ∃ i t, ln = .ins i t := by
    intro ln hln
    rw [← hP] at hln
    obtain ⟨x, rfl, -⟩ := prologueLines_ins _ _ ln hln
    exact ⟨_, _, rfl⟩
  have hgot : (fa.lines.toList.drop 1).take P.length = P := by
    rw [hd, List.take_left]
  have hpre : P <+: fa.lines.toList.drop 1 := by
    rw [hd]; exact List.prefix_append _ _
  have hsum := layout_sum hlay
  have hle : 4 * P.length < 2 ^ 32 := by
    have h1 : ∀ L : List Line, (∀ ln ∈ L, ∃ i t, ln = .ins i t) →
        (L.map Line.size).sum = 4 * L.length := by
      intro L hL
      induction L with
      | nil => rfl
      | cons x xs ih =>
        obtain ⟨i, t, rfl⟩ := hL x (by simp)
        have := ih (fun y hy => hL y (by simp [hy]))
        simp only [List.map_cons, List.sum_cons, Line.size, List.length_cons]
        omega
    have hA := h1 P hins
    generalize fa.lines.toList = L at hpre hsum
    have e := congrArg (fun L => (L.map Line.size).sum) (List.take_append_drop 1 L)
    simp only [List.map_append, List.sum_append] at e
    obtain ⟨tl, htl⟩ := hpre
    have h3 := congrArg (fun L => (L.map Line.size).sum) htl
    simp only [List.map_append, List.sum_append] at h3
    omega
  have hle' : ¬ (4 * P.length ≥ 2 ^ 32) := by omega
  have h0' : fa.lines[0]? = some (.label (.block vb.label)) := by simpa using h0
  unfold unwindRows
  simp only [hframe, Bool.not_true, Bool.false_eq_true, ite_false, haf, bind, Except.bind]
  have hb : (some AInst.prologue != some AInst.prologue) = false := rfl
  simp only [List.head?_cons, List.toList_toArray, hb, Bool.false_eq_true, ite_false, hP]
  rw [if_neg hle']
  simp only [h0', hgot]
  simp only [pure, Except.pure]
  simp
  exact fun x hx => by obtain ⟨i, t, rfl⟩ := hins x hx; simp [Line.insn?]

/-! ## The `try_call` premises from the prepared code -/

/-- **The `try_call`s of the prepared code `vc`** have at least one handler; each a cleanup or
catch tag (0 or 1) whose landing pad is a block of `vc` other than the entry block (decidable,
`tryInfoOkB`). -/
def TryInfoOk (vc : VCode) : Prop :=
  ∀ vb ∈ vc.blocks.toList, ∀ c ti, MInst.tryCall c ti ∈ vb.insts.toList → ti.handlers ≠ [] ∧
    ∀ h ∈ ti.handlers, (∃ n l, h = .tag n l ∧ n ≤ 1) ∧
      (∃ vb' ∈ vc.blocks.toList, vb'.label = h.label) ∧ (vc.blocks[0]?.map (·.label)) ≠ some h.label

/-- `TryInfoOk`, decided. -/
def tryInfoOkB (vc : VCode) : Bool :=
  vc.blocks.toList.all fun vb => vb.insts.toList.all fun
    | .tryCall _ ti => !ti.handlers.isEmpty && ti.handlers.all fun h =>
        (match h with | .tag n _ => decide (n ≤ 1) | .default _ => false) &&
          vc.blocks.toList.any (·.label == h.label) && (vc.blocks[0]?.map (·.label)) != some h.label
    | _ => true

theorem tryInfoOk_of {vc : VCode} (h : tryInfoOkB vc = true) : TryInfoOk vc := by
  intro vb hvb c ti hi
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 h vb hvb) _ hi
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true,
    List.any_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h1
  refine ⟨h1.1, fun hd hhd => ?_⟩
  obtain ⟨⟨htag, hex⟩, hne⟩ := h1.2 hd hhd
  refine ⟨?_, hex, hne⟩
  cases hd with
  | tag n l => exact ⟨n, l, rfl, by simpa using htag⟩
  | default l => cases htag

/-- Substituting an allocation keeps a `try_call`'s handlers: a `try_call` result comes from a
`try_call` with the same `TryInfo`. -/
theorem tryCall_visit (regs : Array Reg) (i : MInst) :
    E2E.PutPost (MInst.visitOperands (putOp regs) i)
      (fun m => ∀ c ti, m = .tryCall c ti → ∃ c0, i = .tryCall c0 ti) := by
  cases i
  case call info =>
    obtain ⟨d, us, ds⟩ := info
    cases d <;> simp only [MInst.visitOperands, pure_bind] <;>
      repeat' first | (with_reducible apply E2E.putPost_bind); intro _ | (with_reducible apply E2E.putPost_pure)
    all_goals intro c ti h; cases h
  case tryCall info ti =>
    obtain ⟨d, us, ds⟩ := info
    cases d <;> simp only [MInst.visitOperands, pure_bind] <;>
      repeat' first | (with_reducible apply E2E.putPost_bind); intro _ | (with_reducible apply E2E.putPost_pure)
    all_goals intro c ti' h; cases h; exact ⟨_, rfl⟩
  all_goals
    simp only [MInst.visitOperands]
    repeat' first | (with_reducible apply E2E.putPost_bind); intro _ | (with_reducible apply E2E.putPost_pure)
  all_goals intro c ti h; cases h

theorem tryCall_assign {i : MInst} {regs : Array Reg} {c : CallInfo} {ti : TryInfo}
    (h : i.assign regs = .ok (.tryCall c ti)) : ∃ c0, i = .tryCall c0 ti :=
  E2E.assign_post h (tryCall_visit regs i) c ti rfl

/-- A `try_call` of the allocated function is a `try_call` of the prepared code with the same
handlers. -/
theorem tryCall_of_af {vc : VCode} {rf : RFunc} {af : AFunc} (halloc : lowerRFunc vc rf = .ok af)
    {ti : TryInfo} (h : some ti ∈ af.calls) :
    ∃ vb ∈ vc.blocks.toList, ∃ c, MInst.tryCall c ti ∈ vb.insts.toList := by
  obtain ⟨⟨-, -, hsz, hbl⟩, -⟩ := lowerRFunc_ok halloc
  rw [calls_eq, List.mem_flatMap] at h
  obtain ⟨⟨l, code⟩, hp, hc⟩ := h
  obtain ⟨b, hb⟩ := List.mem_iff_getElem?.1 hp
  have hb' : af.blocks[b]? = some (l, code) := by simpa using hb
  have hlt : b < af.blocks.size := (Array.getElem?_eq_some_iff.1 hb').1
  rw [hsz, Array.size_zip] at hlt
  obtain ⟨vb, hvb⟩ : ∃ vb, vc.blocks[b]? = some vb :=
    ⟨_, Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨items, hit⟩ : ∃ items, rf.blocks[b]? = some items :=
    ⟨_, Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨code', hcode, haf⟩ := hbl b vb items hvb hit
  rw [hb'] at haf
  simp only [Option.some.injEq, Prod.mk.injEq] at haf
  obtain ⟨-, rfl⟩ := haf
  simp only [blockCalls, List.mem_filterMap] at hc
  obtain ⟨a, ha, hac⟩ := hc
  simp only [List.toList_toArray, List.mem_append] at ha
  rcases ha with ha | ha
  · split at ha <;> simp at ha; subst ha; cases hac
  obtain ⟨it, -, c1, hit1, hac1⟩ := mem_itemsCode hcode ha
  cases a with
  | inst m =>
    cases m with
    | tryCall c' ti' =>
      simp only [aCall, Option.some.injEq] at hac
      subst hac
      cases it with
      | move src dst =>
        have := EmitLabels.moveInsts_targets (itemCode_move_ok hit1) _ hac1
        simp [MInst.targets] at this
      | op k allocs =>
        obtain ⟨regs, i, i', -, hi, hasg, hcases⟩ := itemCode_op hit1
        have hi' : i' = .tryCall c' ti' := by
          rcases hcases with ⟨rfl, -, -⟩ | ⟨ds, -, rfl⟩ | ⟨us, -, rfl⟩
          · simp only [List.mem_singleton, AInst.inst.injEq] at hac1; exact hac1.symm
          · cases hac1
          · simp at hac1
        subst hi'
        refine ⟨vb, by simpa using Array.mem_of_getElem? hvb, ?_⟩
        obtain ⟨c0, rfl⟩ := tryCall_assign hasg
        exact ⟨c0, by simpa using Array.mem_of_getElem? hi⟩
    | _ => simp [aCall] at hac
  | _ => simp [aCall] at hac

/-- **`HandlersOk` of the allocated function** from `TryInfoOk` of the prepared code. -/
theorem handlersOk_of_tryInfo {vc : VCode} {rf : RFunc} {af : AFunc}
    (halloc : lowerRFunc vc rf = .ok af) (hsize : rf.blocks.size = vc.blocks.size)
    (ht : TryInfoOk vc) : HandlersOk af := by
  obtain ⟨⟨-, -, hsz, hbl⟩, -⟩ := lowerRFunc_ok halloc
  intro ti hti h hh
  obtain ⟨vb, hvb, c, hc⟩ := tryCall_of_af halloc hti
  obtain ⟨-, hall⟩ := ht vb hvb c ti hc
  obtain ⟨htag, ⟨vb', hvb', hl⟩, -⟩ := hall h hh
  refine ⟨htag, ?_⟩
  obtain ⟨b, hb⟩ := List.mem_iff_getElem?.1 hvb'
  have hb' : vc.blocks[b]? = some vb' := by simpa using hb
  have hlt : b < vc.blocks.size := (Array.getElem?_eq_some_iff.1 hb').1
  have hlt' : b < rf.blocks.size := by omega
  obtain ⟨items, hit⟩ : ∃ items, rf.blocks[b]? = some items :=
    ⟨_, Array.getElem?_eq_getElem hlt'⟩
  obtain ⟨code, -, haf⟩ := hbl b vb' items hb' hit
  exact ⟨b, _, by rw [haf, hl]⟩

/-- **`PadsOk` of the allocated function** (at the entry block's label) from `TryInfoOk` of the
prepared code. -/
theorem padsOk_of_tryInfo {vc : VCode} {rf : RFunc} {af : AFunc}
    (halloc : lowerRFunc vc rf = .ok af) (ht : TryInfoOk vc) {vb0 : VBlock}
    (h0 : vc.blocks[0]? = some vb0) : PadsOk af vb0.label := by
  intro ti hti
  obtain ⟨vb, hvb, c, hc⟩ := tryCall_of_af halloc hti
  obtain ⟨hne, hall⟩ := ht vb hvb c ti hc
  refine ⟨hne, fun h hh he => ?_⟩
  obtain ⟨-, -, hn⟩ := hall h hh
  rw [h0] at hn
  exact hn (by simp [he])

end Link.EhCheck.Complete
