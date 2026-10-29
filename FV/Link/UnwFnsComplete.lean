import FV.Link.UnwFns
import FV.E2E.EmitPreOk
import FV.E2E.EmitLabels
import FV.Link.EntryLines

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

/-- The callees of the call lines of the emitted code are those of `af`'s calls, in emission
order (`emitOrder`). -/
theorem callKeys_emit {k : Nat} {af : AFunc} {fa : FnAsm} (h : emitFunc k af = .ok fa) :
    callKeys fa.lines.toList = (emitOrder af).flatMap (fun e => blockKeys e.1) := by
  obtain ⟨p, hp, hL, -⟩ := emitFunc_ok h
  rw [hL, relaxLines_callKeys]
  exact plan_callKeys hp

theorem callIdx_length : ∀ L : List Line, (callIdx L).length = nCalls L
  | [] => rfl
  | ln :: L => by
    simp only [callIdx, List.length_append, List.length_map, callIdx_length L, nCalls,
      List.countP_cons]
    split <;> simp_all <;> omega

/-- The emitted code has one call line per call of `af`. -/
theorem nCalls_emit {k : Nat} {af : AFunc} {fa : FnAsm} (h : emitFunc k af = .ok fa) :
    nCalls fa.lines.toList = af.calls.length := by
  rw [nCalls_eq, callKeys_emit h, flatMap_keys_length, calls_eq]

/-- Block `b`'s label is a line of the emitted code. -/
theorem label_mem_emit {k : Nat} {af : AFunc} {fa : FnAsm} (h : emitFunc k af = .ok fa)
    {b : Nat} {l : Label} {code : Array AInst} (hb : af.blocks[b]? = some (l, code)) :
    Line.label (.block l) ∈ fa.lines.toList := by
  obtain ⟨p, hp, hL, hseg⟩ := emit_seg h
  obtain ⟨i, s, o, j, ps1, psm, ps2, -, -, -, -, -, hj, -⟩ := hseg b l code hb
  exact List.mem_of_getElem? hj

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
    -- every call's entries succeed (landing pads looked up in the alias-extended labels)
    have hor : ∀ (o : Option Nat) (a : Nat), ∃ p, o.or (some a) = some p :=
      fun o a => by cases o <;> exact ⟨_, rfl⟩
    have hent : ∀ p ∈ af.calls.zip (scanLines fa.lines.toList 0 [] []).2,
        ∃ es, siteEntries (siteLabs fa) p = .ok es := by
      rintro ⟨c, ret⟩ hp
      have hc := (List.of_mem_zip hp).1
      simp only [siteEntries]
      split
      · exact ⟨_, rfl⟩
      · cases c with
        | none => simp [handlersOf] at *
        | some ti =>
          have hall : ∀ h ∈ ti.handlers, ∃ e, handlerEntry (siteLabs fa) ret h = .ok e := by
            intro h hmem
            obtain ⟨⟨n, l, rfl, hn⟩, b, code, hb⟩ := hh ti hc h hmem
            have hs := scanLines_lookup_isSome fa.lines.toList 0 [] [] l
              (.inr (label_mem_emit he hb))
            obtain ⟨pad, hpad⟩ := Option.isSome_iff_exists.1 hs
            obtain ⟨pad', hpad'⟩ : ∃ p, (siteLabs fa).lookup l = some p := by
              rw [siteLabs, Backend.Proof.lookup_append, hpad]; exact hor _ _
            simp only [TryHandler.label] at hb
            rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn with rfl | rfl <;>
              exact ⟨_, by simp only [handlerEntry, TryHandler.label, hpad']; rfl⟩
          exact mapM_ok_of (handlerEntry (siteLabs fa) ret) hall
    obtain ⟨sites, hs⟩ := mapM_ok_of _ hent
    exact ⟨some sites.flatten, by simp [siteLabs] at hs; simp [hs, bind, Except.bind, pure, Except.pure]⟩
  · simp only [Bool.not_eq_true] at hany
    exact ⟨none, by simp [hany, pure, Except.pure]⟩

end Link.EhCheck.Complete

namespace Link.EhCheck.Complete

open Backend Backend.Proof Backend.Proof.UnwindTables E2E

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
  obtain ⟨code, -, -, h0, hd⟩ := entry_static halloc hemit hvb hit
  rw [prologueLines_eq] at hd
  generalize fa.lines.toList = L at h0 hd ⊢
  cases L with
  | nil => cases h0
  | cons x xs =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
    simp only [List.drop_succ_cons, List.drop_zero] at hd
    subst h0
    obtain ⟨tl, htl⟩ := hd
    exact ⟨_, by rw [← htl]; rfl⟩

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

/-- No block-label alias of the emitted code resolves to the entry block (decidable): a landing
pad `callSites` resolves through an alias (`siteLabs`) is then at a label other than the
entry's, at offset ≥ 8. (Since #553 `callSites` reads `MachBuffer`'s aliases `fa.alias`; an
alias to the entry block would need a forwarding block `b <entry>`. On the pipeline's output
there is none (`alias_ne_entry` with `fwd_ne_entry_input`, FV/Link/UnwTryIn.lean): this check is
the premise of the generic `padsNonzero_complete` only, where `vc` is arbitrary.) -/
def aliasEntryOkB (af : AFunc) (fa : FnAsm) : Bool :=
  fa.alias.all fun p => some p.2 != af.blocks[0]?.map (·.1)

/-! ## No alias to the entry block -/

/-- `relaxLine` keeps a line or makes it two instructions. -/
private theorem relaxLine_cases (F : Lbl → Bool) (x : Line) :
    relaxLine F x = [x] ∨ ∃ c t, relaxLine F x = [.ins c none, .ins (.b t) none] := by
  unfold relaxLine
  split
  · split
    · exact .inr ⟨_, _, rfl⟩
    · exact .inl rfl
  · exact .inl rfl

/-- The emission plan's lines start with the entry block's label, then a line that is no label
(the prologue's `stp`; `lines_head` through the relaxation). -/
private theorem plan_head {vc : VCode} {rf : RFunc} {af : AFunc} {k : Nat} {fa : FnAsm}
    (halloc : lowerRFunc vc rf = .ok af) (hemit : emitFunc k af = .ok fa) {vb : VBlock}
    {items : Array RItem} (hvb : vc.blocks[0]? = some vb) (hit : rf.blocks[0]? = some items)
    {p : Plan} (hp : emitPlan k af = .ok p) :
    p.lines[0]? = some (.label (.block vb.label)) ∧ ∀ l, p.lines[1]? ≠ some (.label l) := by
  obtain ⟨R, hR⟩ := lines_head halloc hemit hvb hit
  obtain ⟨p', hp', hL, -⟩ := emitFunc_ok hemit
  rw [hp] at hp'
  cases hp'
  rw [hL] at hR
  generalize emitFar ⟨k, af.slotBase⟩ af = F at hR
  cases hpl : p.lines with
  | nil => rw [hpl] at hR; simp [relaxLines] at hR
  | cons x0 xs =>
    rw [hpl, relaxLines_cons] at hR
    rcases relaxLine_cases F x0 with h0 | ⟨c, t, h0⟩
    · rw [h0, List.singleton_append, List.cons.injEq] at hR
      obtain ⟨rfl, hR⟩ := hR
      refine ⟨rfl, fun l hl => ?_⟩
      cases xs with
      | nil => simp at hl
      | cons x1 ys =>
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hl
        subst hl
        rw [relaxLines_cons, relaxLine_label] at hR
        simp at hR
    · rw [h0] at hR
      simp at hR

/-- The first label line of block `e` is line 0 when `L` starts with `e`'s label. -/
private theorem blockLabelIdx_head {L : List Line} {e : Label}
    (h : L[0]? = some (.label (.block e))) : (blockLabelIdx L)[e]? = some 0 := by
  cases L with
  | nil => simp at h
  | cons x xs =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [blockLabelIdx, List.zipIdx_cons]

/-- Line 1, no label, represents no block. -/
private theorem repAt_one {af : AFunc} {own : Label → Bool} {L : List Line}
    (h1 : ∀ l, L[1]? ≠ some (.label l)) : ∀ fuel s, repAt af own L.toArray fuel s 1 = false
  | 0, _ => by simp [repAt]
  | fuel + 1, s => by
    have ih := repAt_one (af := af) (own := own) h1 fuel
    rw [repAt]
    simp only [List.getElem?_toArray]
    cases hL : L[1]? with
    | none => cases af.fwd? s <;> simp [ih]
    | some ln =>
      cases ln with
      | label l => exact absurd hL (h1 l)
      | ins i t => cases af.fwd? s <;> simp [ih]
      | word a b => cases af.fwd? s <;> simp [ih]

/-- Line 0, the entry label followed by no label, represents only the entry block when no
block forwards to the entry. -/
private theorem repAt_zero {af : AFunc} {own : Label → Bool} {L : List Line} {e : Label}
    (h0 : L[0]? = some (.label (.block e))) (h1 : ∀ l, L[1]? ≠ some (.label l))
    (hfw : ∀ s x, af.fwd? s = some x → x ≠ e) :
    ∀ fuel s, s ≠ e → repAt af own L.toArray fuel s 0 = false
  | 0, _, _ => by simp [repAt]
  | fuel + 1, s, hs => by
    rw [repAt]
    simp only [List.getElem?_toArray, h0, repAt_one h1, Bool.or_false]
    cases hf : af.fwd? s with
    | none => simp [Ne.symm hs]
    | some x => simp [Ne.symm hs, repAt_zero h0 h1 hfw fuel x (hfw s x hf)]

/-- **No alias of a label other than the entry's resolves to the entry block** when no block
forwards (`AFunc.fwd?`) to the entry: every alias is justified by `aliasOk`, and line 0 of the
plan (the entry label, followed by the prologue) represents no other block. -/
theorem alias_ne_entry {vc : VCode} {rf : RFunc} {af : AFunc} {k : Nat} {fa : FnAsm}
    (halloc : lowerRFunc vc rf = .ok af) (hemit : emitFunc k af = .ok fa) {vb : VBlock}
    {items : Array RItem} (hvb : vc.blocks[0]? = some vb) (hit : rf.blocks[0]? = some items)
    (hfw : ∀ s x, af.fwd? s = some x → x ≠ vb.label) :
    ∀ q ∈ fa.alias, q.1 ≠ vb.label → q.2 ≠ vb.label := by
  intro q hq hq1 hq2
  obtain ⟨p, hp, -, -⟩ := emitFunc_ok hemit
  rw [emitFunc_alias hemit] at hq
  have hq' : q ∈ p.alias := by simpa [emitAlias, hp] using hq
  have hok := (emitPlan_spec hp).2.2.2 q hq'
  obtain ⟨h0, h1⟩ := plan_head halloc hemit hvb hit hp
  unfold aliasOk at hok
  rw [hq2, blockLabelIdx_head h0] at hok
  simp only [repOn] at hok
  rw [repAt_zero h0 h1 hfw _ _ hq1] at hok
  cases hok

/-- **`padsNonzeroB` holds for the emitted code** when every `try_call` has a handler, no
handler's landing pad is the entry block, and no alias of another label resolves to the entry
block (#553: `callSites` resolves landing pads through `MachBuffer`'s aliases). -/
theorem padsNonzero_complete_of {vc : VCode} {rf : RFunc} {af : AFunc} {k : Nat} {fa : FnAsm}
    {fb : FnBin} (halloc : lowerRFunc vc rf = .ok af) (hemit : emitFunc k af = .ok fa)
    (hlay : fa.layout = .ok fb) {vb : VBlock} {items : Array RItem}
    (hvb : vc.blocks[0]? = some vb) (hit : rf.blocks[0]? = some items) (hp : PadsOk af vb.label)
    (hal : ∀ q ∈ fa.alias, q.1 ≠ vb.label → q.2 ≠ vb.label) :
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
    -- the pad's label offset: through an alias to a non-entry label, or the handler's own
    have h8 : ∀ v, (siteLabs fa).lookup h.label = some v → 8 ≤ v := by
      intro v hv
      rw [siteLabs, Backend.Proof.lookup_append] at hv
      cases hA : (fa.alias.filterMap (fun l =>
          ((scanLines fa.lines.toList 0 [] []).1.lookup l.2).map fun x => (l.1, x))).lookup
          h.label with
      | some v' =>
        rw [hA] at hv
        cases hv
        obtain ⟨x, hxm, hxl⟩ := lookup_aliasLabs fa.alias hA
        exact label_off_ge halloc hemit hvb hit hlm (hal _ hxm hl) (scanLines_labelOffsets hlm hxl)
      | none =>
        rw [hA] at hv
        exact label_off_ge halloc hemit hvb hit hlm hl (scanLines_labelOffsets hlm hv)
    have hE : ∀ e, entryFor (siteLabs fa) (some ti, ret) = some e → e.pad ≠ 0 := by
      intro e he
      simp only [entryFor, handlersOf, hh, handlerEntry?] at he
      cases hlk : (siteLabs fa).lookup h.label with
      | none => rw [hlk] at he; cases he
      | some v =>
        have h8v := h8 v hlk
        rw [hlk, Option.bind_some] at he
        split at he <;> cases he <;> simp <;> omega
    cases hq : entryFor (siteLabs fa) (some ti, ret) with
    | none => simp
    | some e => simpa [hq] using hE e hq

/-- **`padsNonzeroB` holds for the emitted code** when every `try_call` has a handler, no
handler's landing pad is the entry block, and no alias resolves to the entry block
(`aliasEntryOkB`; #553: `callSites` resolves landing pads through `MachBuffer`'s aliases; on the
pipeline's output `padsNonzero_complete_input` needs no such check). -/
theorem padsNonzero_complete {vc : VCode} {rf : RFunc} {af : AFunc} {k : Nat} {fa : FnAsm}
    {fb : FnBin} (halloc : lowerRFunc vc rf = .ok af) (hemit : emitFunc k af = .ok fa)
    (hlay : fa.layout = .ok fb) {vb : VBlock} {items : Array RItem}
    (hvb : vc.blocks[0]? = some vb) (hit : rf.blocks[0]? = some items) (hp : PadsOk af vb.label)
    (hal : aliasEntryOkB af fa = true) :
    padsNonzeroB af fa = true := by
  refine padsNonzero_complete_of halloc hemit hlay hvb hit hp fun p hpm _ he => ?_
  obtain ⟨⟨-, -, -, hbl⟩, -⟩ := lowerRFunc_ok halloc
  obtain ⟨code, -, haf⟩ := hbl 0 vb items hvb hit
  have := List.all_eq_true.1 hal p hpm
  rw [haf, he] at this
  simp at this

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
  obtain ⟨code, -, haf, h0, hd⟩ := entry_static halloc hemit hvb hit
  generalize hP : prologueLines af.saves af.frameSize = P at hd
  have hins : ∀ ln ∈ P, ∃ i t, ln = .ins i t := by
    intro ln hln
    rw [← hP] at hln
    obtain ⟨x, rfl, -⟩ := prologueLines_ins _ _ ln hln
    exact ⟨_, _, rfl⟩
  have hgot : (fa.lines.toList.drop 1).take P.length = P :=
    (List.prefix_iff_eq_take.mp hd).symm
  have hpre : P <+: fa.lines.toList.drop 1 := hd
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
  obtain ⟨⟨⟨l, code⟩, b⟩, hp, hc⟩ := h
  have hb' : af.blocks[b]? = some (l, code) := by
    have hm := (emitOrder_perm af).mem_iff.mp hp
    rw [List.mem_zipIdx_iff_getElem?] at hm
    simpa using hm
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
