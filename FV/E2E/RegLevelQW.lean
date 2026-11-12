import FV.E2E.RegLevelSegAlign
import FV.E2E.RegLevelOp
import FV.E2E.RegLevelBranch

/-!
# `QW` taken apart and put together (SEM1 #537, item (3), route (a))

The bookkeeping lemmas of `RegLevelMove.lean`/`RegLevelBranch.lean` on `QW`: `QW` at an item is
`Qs` at the witness (`QW.qws`, `QW.qws_op`, `QW.qws_lt`) unless the item is a forwarding block's
`jump` entered without a step (`QW.fwd`); `Qs` at a witness taken apart (`qWs_split`,
`qWs_term`) and put together at the next item at the straight witness (`qWs_next`); the entry
witnesses of a block at the lines representing it (`RL.entryWit_of_rep`, `qW_entry`); and no
block label among a block's lines (`NoBlockLbl`, `RL.noBlock_drop`), so no line inside them
represents a block (`RL.entryWit_ne`).
-/

namespace Backend.Proof

open Backend E2E

theorem relaxLines_single_ne (f : Lbl → Bool) (ln : Line) : (relaxLines f [ln]).length ≠ 0 := by
  simp only [relaxLines, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  unfold relaxLine
  split
  · split <;> simp
  · simp

/-! ## No block label among a block's lines -/

/-- A line that is no block label. -/
def NoBlockLbl (ln : Line) : Prop := ∀ l, ln ≠ .label (.block l)

theorem lines_noBlock {c : FnCtx} {m : MInst} {ps ps' : PState} {ls : List Line}
    (h : m.lines c ps = .ok (ls, ps')) : ∀ ln ∈ ls, NoBlockLbl ln := by
  have hmf : ∀ mm b pre am, memFinalize c mm b = .ok (pre, am) → ∀ ln ∈ pre, NoBlockLbl ln := by
    intro mm b pre am hm ln hln n e
    subst e
    unfold memFinalize at hm
    have hfin : ∀ (base : Reg) (off : Int) pre am,
        (match simm9? off with
          | some s => (([] : List Line), AMode.unscaled base s)
          | none => match uimm12Scaled? off b with
            | some o => ([], .unsignedOffset base o)
            | none => (loadConst64 (.x 16) (u64 off), .regExtended base (.x 16) .sxtx)) = (pre, am) →
        Line.label (.block n) ∉ pre := by
      intro base off pre am e hin
      split at e
      · cases e; simp at hin
      · split at e
        · cases e; simp at hin
        · cases e
          obtain ⟨i, t, hi⟩ := loadConst64_ins _ _ _ hin
          cases hi
    split at hm <;> simp only [pure, Except.pure, Except.ok.injEq] at hm <;>
      first | exact hfin _ _ _ _ hm hln | (cases hm; simp at hln) | cases hm
  have hmf' : ∀ mm b v, memFinalize c mm b = .ok v → ∀ ln ∈ v.1, NoBlockLbl ln :=
    fun mm b v hv => hmf mm b v.1 v.2 hv
  unfold MInst.lines at h
  split at h <;> simp only [bind, Except.bind, pure, Except.pure] at h
  all_goals (repeat' (first | (split at h) | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h)))
  all_goals first | cases h | (simp [throw, throwThe, MonadExceptOf.throw] at h) | skip
  all_goals intro ln hln n e; subst e
  all_goals simp [MInst.lines.addOff, rmwLoopLines, rmwLoopBody, casLoopLines, casLoopHead] at hln
  all_goals first
    | exact hmf' _ _ _ ‹memFinalize _ _ _ = _› _ hln _ rfl
    | (rcases hln with hln | hln
       · exact hmf' _ _ _ ‹memFinalize _ _ _ = _› _ hln _ rfl
       · first
          | ((repeat' (split at hln)) <;> simp at hln; done)
          | (simp [throw, throwThe, MonadExceptOf.throw] at *; done))

theorem codeLinesE_noBlock {c : FnCtx} {af : AFunc} :
    ∀ (code : List AInst) (ps ps' : PState) (ls : List Line),
      codeLinesE c af code ps = .ok (ls, ps') → ∀ ln ∈ ls, NoBlockLbl ln
  | [], ps, ps', ls, h => by
    simp only [codeLinesE, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h; simp
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
        intro ln hln
        rcases List.mem_append.1 hln with hln | hln
        · cases a with
          | inst m => exact lines_noBlock hr ln hln
          | prologue =>
            simp only [ainstLines, pure, Except.pure, Except.ok.injEq] at hr
            subst hr
            intro n e; subst e
            split at hln
            · obtain ⟨_, _, h⟩ := prologueLines_isIns _ _ _ hln; cases h
            · simp at hln
          | epilogueRet =>
            simp only [ainstLines, pure, Except.pure, Except.ok.injEq] at hr
            subst hr
            intro n e; subst e
            split at hln
            · obtain ⟨_, _, h⟩ := epilogueLines_isIns _ _ _ hln; cases h
            · simp at hln
        · exact codeLinesE_noBlock as _ _ _ hr2 ln hln

theorem relaxLines_noBlock {F : Lbl → Bool} {ls : List Line} (h : ∀ ln ∈ ls, NoBlockLbl ln) :
    ∀ ln ∈ relaxLines F ls, NoBlockLbl ln := by
  intro ln hln
  simp only [relaxLines, List.mem_flatMap] at hln
  obtain ⟨a, ha, hm⟩ := hln
  unfold relaxLine at hm
  split at hm
  · split at hm
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl <;> intro l e <;> cases e
    · simp only [List.mem_singleton] at hm; subst hm; exact h _ ha
  · simp only [List.mem_singleton] at hm; subst hm; exact h _ ha

/-- **No block label in the run of lines `A` at line `j0`.** -/
theorem RL.noBlock_drop {R : RL} {j0 : Nat} {A rest : List Line} (hd : R.L.drop j0 = A ++ rest)
    (hA : ∀ ln ∈ A, NoBlockLbl ln) :
    ∀ k l, j0 < k → k < j0 + A.length → R.L[k]? ≠ some (.label (.block l)) := by
  intro k l h1 h2 e
  have : (R.L.drop j0)[k - j0]? = some (.label (.block l)) := by
    rw [List.getElem?_drop, show j0 + (k - j0) = k by omega]; exact e
  rw [hd, List.getElem?_append_left (by omega)] at this
  exact hA _ (List.mem_of_getElem? this) l rfl

/-- Lines with the same tail from `j` and `r` have the same pc. -/
theorem RL.pcOf_of_drop {R : RL} {j r : Nat} (h : R.L.drop j = R.L.drop r) :
    R.pcOf j = R.pcOf r := by
  have hl := congrArg List.length h
  simp only [List.length_drop] at hl
  by_cases hj : j ≤ R.L.length <;> by_cases hr : r ≤ R.L.length
  · rw [show j = r by omega]
  all_goals
    simp only [RL.pcOf, lineOffset]
    rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

/-! ## `Qs` at a witness -/

/-- **`QWs` at an item with more items after it**, taken apart (`qs_split` at the witness). -/
theorem qWs_split {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j : Nat} {ps1 : PState} {b : Nat}
    {it : RItem} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : QWs R s j ps1 b (it :: its) m w) (hne : its ≠ []) :
    ∃ vb items pre c1 c2 ls1 X' psm psm' ps2, ∃ x : Seg × List Line × Nat,
      R.vc.blocks[b]? = some vb ∧ R.rf.blocks[b]? = some items ∧
      items.toList = pre ++ it :: its ∧ ItemsChecked R vb (it :: its) ∧
      itemCode R.fr vb it = .ok c1 ∧ itemsCode R.fr vb its = .ok c2 ∧
      codeLinesE R.ctx R.af c1 ps1 = .ok (ls1, psm) ∧
      codeLinesE R.ctx R.af c2.dropLast psm = .ok (X', psm') ∧
      codeLinesE R.ctx R.af c2.getLast?.toList psm' = .ok (x.1.term, ps2) ∧
      ps2.traps.toList <+: R.psF.traps.toList ∧
      R.L.drop j = relaxLines R.far ls1 ++ (relaxLines R.far (X' ++ x.2.1) ++
        R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2)) ∧
      Arm.r .PC s = R.pcOf j ∧ StRel R s m w ∧ segX R.fa.k R.af b = some x ∧
      SegChecked R.fa.k R.af b := by
  obtain ⟨vb, items, pre, code, X, psm', ps2, x, hvb, hit, hsplit, hchk, hcode, hX, hT,
    htr, hdrop, hpc, hst, hx, hsc⟩ := hq
  obtain ⟨c1, c2, hc1, hc2, rfl⟩ := itemsCode_cons hcode
  have hc2ne : c2 ≠ [] := by
    obtain ⟨cc, k, a, out, -, -, hrun⟩ := hchk
    obtain ⟨c0, ins, _, hc0, -⟩ := hR.check
    obtain ⟨preds, hcfg⟩ := hc0.cfg
    have hrun' : ∃ k' a', cc.runItems vb k' its a' = .ok out := by
      cases it with
      | move src dst => exact ⟨_, _, (runItems_move hrun).2⟩
      | op k1 al =>
        obtain ⟨-, -, -, -, a', -, -, -, h⟩ := runItems_op hrun
        exact ⟨_, _, h⟩
    obtain ⟨k', a', hrun'⟩ := hrun'
    exact itemsCode_ne_nil hcfg hvb hrun' hne hc2
  rw [List.dropLast_append_of_ne_nil hc2ne] at hX
  have hlast : (c1 ++ c2).getLast? = c2.getLast? := by
    rw [List.getLast?_append, List.getLast?_eq_getLast hc2ne]
    simp
  rw [hlast] at hT
  obtain ⟨ls1, X', psm, h1, h2, rfl⟩ := codeLinesE_append _ _ _ _ _ hX
  refine ⟨vb, items, pre, c1, c2, ls1, X', psm, psm', ps2, x, hvb, hit, hsplit, hchk, hc1,
    hc2, h1, h2, hT, htr, ?_, hpc, hst, hx, hsc⟩
  rw [hdrop, List.append_assoc, relaxLines_append, List.append_assoc]

/-- **`QWs` at the next item**, at the straight witness, after the item's lines `ls1` ran
(`qs_next` at the witness). -/
theorem qWs_next {R : RL} {s : Arm.ArmState} {b : Nat} {it : RItem} {its : List RItem}
    {m : Loc → CV} {w : Arm.ArmState} {vb : VBlock} {items : Array RItem} {pre : List RItem}
    {c2 : List AInst} {ls1 X' : List Line} {psm psm' ps2 : PState} {x : Seg × List Line × Nat}
    {j : Nat} (hvb : R.vc.blocks[b]? = some vb) (hit : R.rf.blocks[b]? = some items)
    (hsplit : items.toList = pre ++ it :: its) (hchk : ItemsChecked R vb its)
    (hc2 : itemsCode R.fr vb its = .ok c2)
    (h2 : codeLinesE R.ctx R.af c2.dropLast psm = .ok (X', psm'))
    (h3 : codeLinesE R.ctx R.af c2.getLast?.toList psm' = .ok (x.1.term, ps2))
    (htr : ps2.traps.toList <+: R.psF.traps.toList)
    (hdrop : R.L.drop j = relaxLines R.far ls1 ++ (relaxLines R.far (X' ++ x.2.1) ++
        R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2)))
    (hpc : Arm.r .PC s = R.pcOf (j + (relaxLines R.far ls1).length)) (hst : StRel R s m w)
    (hx : segX R.fa.k R.af b = some x) (hsc : SegChecked R.fa.k R.af b) :
    QWs R s (j + (relaxLines R.far ls1).length) psm b its m w :=
  ⟨vb, items, pre ++ [it], c2, X', psm', ps2, x, hvb, hit, by rw [hsplit]; simp, hchk, hc2, h2,
    h3, htr, by rw [← List.drop_drop, hdrop, List.drop_left], hpc, hst, hx, hsc⟩

/-- **`QWs` at the last item**, taken apart (`qs_term` at the witness). -/
theorem qWs_term {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j : Nat} {ps1 : PState} {b : Nat}
    {it : RItem} {m : Loc → CV} {w : Arm.ArmState} (hq : QWs R s j ps1 b [it] m w) :
    ∃ vb items pre c1 X psm ps2, ∃ x : Seg × List Line × Nat, R.vc.blocks[b]? = some vb ∧
      R.rf.blocks[b]? = some items ∧ items.toList = pre ++ [it] ∧ ItemsChecked R vb [it] ∧
      itemCode R.fr vb it = .ok c1 ∧ codeLinesE R.ctx R.af c1.dropLast ps1 = .ok (X, psm) ∧
      codeLinesE R.ctx R.af c1.getLast?.toList psm = .ok (x.1.term, ps2) ∧
      ps2.traps.toList <+: R.psF.traps.toList ∧
      R.L.drop j = relaxLines R.far (X ++ x.2.1) ++
        R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2) ∧
      Arm.r .PC s = R.pcOf j ∧ StRel R s m w ∧
      termOk (planRep R.fa.k R.af) (blockLabelIdx (planLines R.fa.k R.af)) c1.getLast? x.1.term
        x.2.1 x.2.2 = true := by
  obtain ⟨vb, items, pre, code, X, psm, ps2, x, hvb, hit, hsplit, hchk, hcode, hX, hT, htr,
    hdrop, hpc, hst, hx, hsc⟩ := hq
  obtain ⟨c1, c2, h1, h2, rfl⟩ := itemsCode_cons hcode
  obtain rfl : c2 = [] := by simpa [itemsCode, pure, Except.pure] using h2.symm
  rw [List.append_nil] at hX hT
  refine ⟨vb, items, pre, c1, X, psm, ps2, x, hvb, hit, hsplit, hchk, h1, hX, hT, htr,
    hdrop, hpc, hst, ?_⟩
  -- `c1` is not empty
  have hne : c1 ≠ [] := by
    obtain ⟨cc, k, a, out, -, -, hrun⟩ := hchk
    obtain ⟨c0, ins, _, hc0, -⟩ := hR.check
    obtain ⟨preds, hcfg⟩ := hc0.cfg
    have := itemsCode_ne_nil hcfg hvb hrun (by simp) hcode
    simpa using this
  obtain ⟨y, hy⟩ : ∃ y, c1.getLast? = some y := ⟨_, List.getLast?_eq_getLast hne⟩
  -- the branch check of the block's segment
  obtain ⟨x', hx', hok⟩ := hsc
  rw [hx] at hx'
  cases hx'
  obtain ⟨p, hp, -⟩ := hR.psF
  obtain ⟨-, hidx⟩ := segX_mem hp hx
  unfold segTermOk at hok
  rw [hidx] at hok
  obtain ⟨⟨-, -, -, hbl⟩, -⟩ := lowerRFunc_ok hR.alloc
  obtain ⟨codeF, hcF, haf⟩ := hbl b vb items hvb hit
  rw [hsplit] at hcF
  obtain ⟨ca, cb, -, hcb, rfl⟩ := itemsCode_append hcF
  change itemsCode R.fr vb [it] = .ok cb at hcb
  rw [hcode, List.append_nil] at hcb
  cases hcb
  rw [haf] at hok
  rw [hy]
  have hb : (((if b = 0 then [AInst.prologue] else []) ++ (ca ++ c1)).toArray).back? = some y := by
    rw [Array.back?_eq_getElem?]
    simp only [List.size_toArray, List.getElem?_toArray]
    rw [← List.getLast?_eq_getElem?, ← List.append_assoc, List.getLast?_append, hy]
    rfl
  simpa [hb] using hok

/-! ## `QW` at an item -/

theorem QEWst.items {R : RL} {j : Nat} {ps1 : PState} {b : Nat} (h : QEWst R j ps1 b) :
    ∃ items, R.rf.blocks[b]? = some items := by
  cases h with
  | std hit _ => exact ⟨_, hit⟩
  | fwd _ _ hit _ _ _ _ _ _ _ _ _ _ => exact ⟨_, hit⟩

/-- **A block entered at a witness has an entry witness at its pc**, given a line representing
the block there. -/
theorem QEWst.entryWit {R : RL} {j : Nat} {ps1 : PState} {bx : Nat} (h : QEWst R j ps1 bx)
    {vbx : VBlock} (hvbx : R.vc.blocks[bx]? = some vbx) {jl : Nat}
    (hrep : RepL R.af (planOwn R.fa.k R.af) R.L vbx.label jl) (hpc : R.pcOf jl = R.pcOf j) :
    ∃ T, R.EntryWit bx (R.pcOf j) (j, ps1, T) := by
  cases h with
  | std hit hq =>
    refine ⟨[], rfl, ⟨vbx, jl, hvbx, hrep, hpc⟩, fun items' hit' => .inl ⟨rfl, ?_⟩⟩
    rw [hit] at hit'; cases hit'; exact hq
  | fwd hvb hx hit hil hal hins hasg hsucc hvbx' hlx hrep' hpc' hq =>
    refine ⟨[.label .skip], rfl, ⟨vbx, jl, hvbx, hrep, hpc⟩, fun items' hit' => .inr ⟨by simp, ?_⟩⟩
    rw [hit] at hit'; cases hit'
    exact ⟨_, _, _, _, _, _, _, _, _, hvb, hx, hit, rfl, hil, hal, hins, hasg, hsucc, hvbx', hlx,
      hrep', hpc', hq⟩

/-- `QW` at an item that is no `op` of instruction 0 is `Qs` at the witness. -/
theorem QW.qws {R : RL} {s : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line} {b : Nat}
    {it : RItem} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (h : QW R s j ps1 T (.run ⟨b, it :: its, m, w⟩)) (hit : ∀ allocs, it ≠ .op 0 allocs) :
    T = [] ∧ QWs R s j ps1 b (it :: its) m w := by
  rcases h with h | ⟨-, ⟨_, _, _, items, allocs, _, _, _, _, -, -, -, hits, hil, -⟩, -⟩
  · exact h
  · rw [← hits] at hil
    simp only [List.cons.injEq] at hil
    exact (hit allocs hil.1).elim

/-- `QW` at an `op` whose instruction branches nowhere is `Qs` at the witness. -/
theorem QW.qws_op {R : RL} {s : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line}
    {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (h : QW R s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {i : MInst}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i) (ht : i.targets = []) :
    T = [] ∧ QWs R s j ps1 b (.op k allocs :: its) m w := by
  rcases h with h | ⟨-, ⟨vb', _, _, items, allocs', regs, i', _, _, hvb', -, -, hits, hil, -, hins,
    hasg, -⟩, -⟩
  · exact h
  · rw [hvb] at hvb'
    cases hvb'
    rw [← hits] at hil
    simp only [List.cons.injEq, RItem.op.injEq] at hil
    obtain ⟨⟨rfl, -⟩, -⟩ := hil
    rw [hins] at hi
    simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    have := (assign_shape hasg).1
    rw [ht] at this
    cases this

/-- `QW` at an `op` of an instruction before the block's last is `Qs` at the witness. -/
theorem QW.qws_lt {R : RL} {s : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line}
    {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (h : QW R s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock}
    (hvb : R.vc.blocks[b]? = some vb) (hk : k + 1 < vb.insts.size) :
    T = [] ∧ QWs R s j ps1 b (.op k allocs :: its) m w := by
  rcases h with h | ⟨-, ⟨vb', _, _, items, allocs', regs, i', _, _, hvb', -, -, hits, hil, -, hins,
    -⟩, -⟩
  · exact h
  · rw [hvb] at hvb'
    cases hvb'
    rw [← hits] at hil
    simp only [List.cons.injEq, RItem.op.injEq] at hil
    obtain ⟨⟨rfl, -⟩, -⟩ := hil
    rw [hins] at hk
    simp at hk

/-- **`QW` at a forwarding block's `jump` entered without a step** (`T ≠ []`): its only item,
an `op` of its only instruction, a `jump x` to its successor `bx`, which has an entry witness at
the witness's pc. -/
theorem QW.fwd {R : RL} {s : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line} {b : Nat}
    {it : RItem} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (h : QW R s j ps1 T (.run ⟨b, it :: its, m, w⟩)) (hT : T ≠ []) :
    ∃ vb allocs regs i x bx itx, R.vc.blocks[b]? = some vb ∧ it = .op 0 allocs ∧ its = [] ∧
      allocs = regs.map Loc.reg ∧ vb.insts = #[i] ∧ i.assign regs = .ok (.jump x) ∧
      succOf R.vc b 0 = some bx ∧ R.rf.blocks[bx]? = some itx ∧
      (∃ items : Array RItem, R.rf.blocks[b]? = some items ∧ items.toList = [.op 0 allocs]) ∧
      (∃ W, R.EntryWit bx (R.pcOf j) W) ∧ Arm.r .PC s = R.pcOf j ∧ StRel R s m w := by
  rcases h with ⟨h0, -⟩ | ⟨-, ⟨vb, vbx, x, items, allocs, regs, i, bx, jl, hvb, -, hit, hits, hil,
    hal, hins, hasg, hsucc, hvbx, hlx, hrep, hpcj, hqe⟩, hpc, hst⟩
  · exact (hT h0).elim
  rw [← hits] at hil
  simp only [List.cons.injEq] at hil
  obtain ⟨rfl, rfl⟩ := hil
  obtain ⟨itx, hitx⟩ := hqe.items
  obtain ⟨T', hW⟩ := hqe.entryWit hvbx (by rw [hlx]; exact hrep) hpcj
  exact ⟨vb, allocs, regs, i, x, bx, itx, hvb, rfl, rfl, hal, hins, hasg, hsucc, hitx,
    ⟨items, hit, hits.symm⟩, ⟨_, hW⟩, hpc, hst⟩

/-- A line representing a block is no instruction line. -/
theorem RL.not_ins_of_repL {R : RL} {own : Label → Bool} {x : Label} {j : Nat}
    (h : RepL R.af own R.L x j) : ∀ x' t', R.L[j]? ≠ some (.ins x' t') := by
  intro x' t' e
  obtain ⟨k, l, hk, hkl, hrun⟩ := repL_run h
  rcases Nat.eq_or_lt_of_le hk with hk | hk
  · subst hk; rw [hkl] at e; cases e
  · obtain ⟨l', hl'⟩ := hrun j (Nat.le_refl _) hk
    rw [hl'] at e; cases e

/-- **`QW` at an `op` of an instruction before the block's last**, taken apart (`q_op` at the
witness, with the item's code). -/
theorem qW_op {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line}
    {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : QW R s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {i : MInst} (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i)
    (hk : k + 1 < vb.insts.size) :
    T = [] ∧ ∃ items pre regs i' c1 c2 X' ls1 psm psm' ps2, ∃ x : Seg × List Line × Nat,
      ∃ (cc : CheckCtx) (wh : String) (ops : Array Operand),
      itemCode R.fr vb (.op k allocs) = .ok c1 ∧
      allocs = regs.map Loc.reg ∧ R.rf.blocks[b]? = some items ∧
      items.toList = pre ++ .op k allocs :: its ∧ i.assign regs = .ok i' ∧
      ((c1 = [AInst.inst i'] ∧ (∀ ds, i' ≠ .args ds) ∧ (∀ us, i' ≠ .rets us)) ∨
        (∃ ds, i' = .args ds ∧ c1 = []) ∨ (∃ us, i' = .rets us ∧ c1 = [AInst.epilogueRet])) ∧
      i.operands = .ok ops ∧ cc.checkStatic wh ops (regs.map Loc.reg) i.clobbers = .ok () ∧
      ItemsChecked R vb its ∧ itemsCode R.fr vb its = .ok c2 ∧
      codeLinesE R.ctx R.af c1 ps1 = .ok (ls1, psm) ∧
      codeLinesE R.ctx R.af c2.dropLast psm = .ok (X', psm') ∧
      codeLinesE R.ctx R.af c2.getLast?.toList psm' = .ok (x.1.term, ps2) ∧
      ps2.traps.toList <+: R.psF.traps.toList ∧
      R.L.drop j = relaxLines R.far ls1 ++ (relaxLines R.far (X' ++ x.2.1) ++
        R.L.drop (rix R.far (planLines R.fa.k R.af) x.2.2)) ∧
      Arm.r .PC s = R.pcOf j ∧ StRel R s m w ∧
      segX R.fa.k R.af b = some x ∧ SegChecked R.fa.k R.af b := by
  obtain ⟨hT0, hq'⟩ := hq.qws_lt hvb hk
  refine ⟨hT0, ?_⟩
  obtain ⟨vb0, items, pre, code, X, psX, ps2, x, hvb0, hit, hsplit, hchk, hcode, hX, hT,
    htr, hdrop, hpc, hst, hx, hsc⟩ := hq'
  rw [hvb] at hvb0; cases hvb0
  obtain ⟨c1, c2, hc1, hc2, rfl⟩ := itemsCode_cons hcode
  have hc1o := hc1
  obtain ⟨regs, i0, i', rfl, hi0, hasg, hc1'⟩ := itemCode_op hc1
  rw [hi] at hi0; cases hi0
  obtain ⟨cc, wh, i2, ops, hi2, hops, hstat, hchk'⟩ := op_checked hchk
  rw [hi] at hi2; cases hi2
  have hne : its ≠ [] := by
    obtain ⟨c, k0, a, out, -, -, hrun⟩ := hchk
    obtain ⟨-, rfl, _, _, _, _, _, _, h'⟩ := runItems_op hrun
    rintro rfl
    have := (runItems_nil h').1
    omega
  obtain ⟨c, ins, _, hc, -⟩ := hR.check
  obtain ⟨preds, hcfg⟩ := hc.cfg
  obtain ⟨c0, k0, a0, out0, -, -, hrun'⟩ := id hchk'
  have hc2ne : c2 ≠ [] := itemsCode_ne_nil hcfg hvb hrun' hne hc2
  rw [List.dropLast_append_of_ne_nil hc2ne] at hX
  obtain ⟨ls1, X', psm, h1, h2, rfl⟩ := codeLinesE_append _ _ _ _ _ hX
  have hlast : (c1 ++ c2).getLast?.toList = c2.getLast?.toList := by
    rw [List.getLast?_append, List.getLast?_eq_getLast hc2ne]
    simp
  rw [hlast] at hT
  exact ⟨items, pre, regs, i', c1, c2, X', ls1, psm, psX, ps2, x, cc, wh, ops, hc1o, rfl, hit,
    hsplit, hasg, hc1', hops, hstat, hchk', hc2, h1, h2, hT, htr,
    by rw [hdrop]; simp only [List.append_assoc, relaxLines_append], hpc, hst, hx, hsc⟩

/-! ## Entry witnesses -/

/-- **At the label line of a block** (other than the entry) whose segment was checked: the
block's items at a witness at the label's pc (`qs_entry`'s code part). -/
theorem qWst_entry {R : RL} (hR : R.Wf) {t : Nat} {vb : VBlock} {items : Array RItem} (ht : t ≠ 0)
    (hvb : R.vc.blocks[t]? = some vb) (hit : R.rf.blocks[t]? = some items)
    (ho : (R.af.fwd? vb.label).isNone = true ∨ planOwn R.fa.k R.af vb.label = true)
    {jl : Nat} (hjl : R.L[jl]? = some (.label (.block vb.label))) :
    ∃ j ps1, R.pcOf j = R.pcOf jl ∧ QWst R j ps1 t items.toList := by
  obtain ⟨⟨-, -, -, hbl⟩, -⟩ := lowerRFunc_ok hR.alloc
  obtain ⟨code, hcode, haf⟩ := hbl t vb items hvb hit
  obtain ⟨p, hp, hL, hseg⟩ := emit_seg hR.emit
  obtain ⟨i, sg, o, -, ps1, psm, ps2, hs, ho', hidx, hlab, -, -, -, e1, e2, hpre, -⟩ :=
    hseg t _ _ haf
  simp only [ht, ite_false, List.nil_append, List.toList_toArray] at e1 e2
  obtain ⟨A, hA, hX⟩ := segX_get hp hs ho'
  rw [hidx] at hX
  obtain ⟨p', hp', hps⟩ := hR.psF
  rw [hp] at hp'
  cases hp'
  have hPL : planLines R.fa.k R.af = p.lines := by simp [planLines, hp]
  have hRL : R.L = relaxLines R.far p.lines := hL
  -- the block's label line
  have e : p.lines = (A ++ [Line.label (.block sg.label)] ++ (sg.body ++ o)) ++
      (segLines (p.segs.drop (i + 1)) (p.outs.drop (i + 1)) ++ trapLines p.ps) := by
    rw [hA]; simp
  have hlbl : p.lines[A.length]? = some (.label (.block vb.label)) := by
    rw [hA, ← hlab, List.append_assoc, List.cons_append]; exact getElem?_mid _ _ _
  have r1 := relax_label (F := R.far) hlbl
  rw [← hRL] at r1
  have hj : jl = rix R.far p.lines A.length := labelOffsets_uniq hR.lm hjl r1.1
  subst hj
  refine ⟨rix R.far p.lines (A.length + 1), ps1, ?_, vb, items, [], code, sg.body, psm, ps2,
    (sg, o, A.length + 1 + sg.body.length + o.length), hvb, hit, rfl,
    itemsChecked_block hR hvb hit, hcode, e1, e2, by rw [← hps]; exact hpre, ?_, hX,
    segChecked_of hp hX (by rw [hlab]; exact ho)⟩
  · rw [r1.2]
    simp only [RL.pcOf]
    rw [lineOffset_succ _ _ _ r1.1]
    simp [Line.size]
  · have d1 : p.lines.drop (A.length + 1) = (sg.body ++ o) ++
        (segLines (p.segs.drop (i + 1)) (p.outs.drop (i + 1)) ++ trapLines p.ps) := by
      rw [e, List.append_assoc]; exact List.drop_left' (by simp)
    have d2 : p.lines.drop (A.length + 1 + sg.body.length + o.length) =
        segLines (p.segs.drop (i + 1)) (p.outs.drop (i + 1)) ++ trapLines p.ps := by
      rw [e]; exact List.drop_left' (by simp; omega)
    rw [hPL, hRL, relax_drop, relax_drop, d1, d2, relaxLines_append]

/-- **Every block but the entry has an entry witness at each line representing it**
(`qe_entry`'s code part). -/
theorem RL.entryWit_of_rep {R : RL} (hR : R.Wf) {l : Label} {jl : Nat}
    (hrep : RepL R.af (planOwn R.fa.k R.af) R.L l jl) :
    ∀ {t : Nat} {vb : VBlock} {items : Array RItem}, t ≠ 0 → R.vc.blocks[t]? = some vb →
      vb.label = l → R.rf.blocks[t]? = some items → ∃ W, R.EntryWit t (R.pcOf jl) W := by
  induction hrep with
  | here ho hL =>
    intro t vb items ht hvb hl hit
    subst hl
    obtain ⟨j, ps1, hpj, hq⟩ := qWst_entry hR ht hvb hit ho hL
    refine ⟨(j, ps1, []), hpj, ⟨vb, _, hvb, .here ho hL, rfl⟩, fun items' hit' => .inl ⟨rfl, ?_⟩⟩
    rw [hit] at hit'; cases hit'; exact hq
  | @skip l j l' ho hL hr ih =>
    intro t vb items ht hvb hl hit
    obtain ⟨W, hW1, -, hW3⟩ := ih ht hvb hl hit
    have hp : R.pcOf (j + 1) = R.pcOf j := by
      simp only [RL.pcOf]
      rw [lineOffset_succ _ _ _ hL]
      simp [Line.size]
    exact ⟨W, hW1.trans hp, ⟨vb, j, hvb, by rw [hl]; exact .skip ho hL hr, rfl⟩, hW3⟩
  | @fwd l x j hx hr ih =>
    intro t vb items ht hvb hl hit
    obtain ⟨b', vb', items', allocs, regs, i, bx, vbx, itx, hvb', hl', hit', -, hil, hal, hins,
      hasg, hsucc, hvbx, hlx, hitx, hbx0⟩ := RL.fwd_block hR hx
    obtain rfl : t = b' := RL.label_inj hR hvb hit hvb' hit' (hl.trans hl'.symm)
    rw [hvb] at hvb'; cases hvb'
    rw [hit] at hit'; cases hit'
    obtain ⟨W, hW1, -, hW3⟩ := ih hbx0 hvbx hlx hitx
    have hqe : QEWst R W.1 W.2.1 bx := by
      rcases hW3 itx hitx with ⟨-, h⟩ | ⟨-, ⟨vb2, vbx2, x2, items2, allocs2, regs2, i2, bx2, jl2,
        h1, h2, h3, -, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩⟩
      · exact .std hitx h
      · exact .fwd h1 h2 h3 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    refine ⟨(W.1, W.2.1, [.label .skip]), hW1, ⟨vb, j, hvb, by rw [hl]; exact .fwd hx hr, rfl⟩,
      fun items' hit' => .inr ⟨by simp, ?_⟩⟩
    rw [hit] at hit'; cases hit'
    exact ⟨vb, vbx, x, items, allocs, regs, i, bx, j, hvb, by rw [hl]; exact hx, hit, rfl, hil,
      hal, hins, hasg, hsucc, hvbx, hlx, hr, hW1.symm, hqe⟩

/-- **Entering a block** (other than the entry) at a line representing it (`q_entry` at the
chosen entry witness of the arrival pc). -/
theorem qW_entry {R : RL} (hR : R.Wf) {t : Nat} {vb : VBlock} {items : Array RItem} (ht : t ≠ 0)
    (hvb : R.vc.blocks[t]? = some vb) (hit : R.rf.blocks[t]? = some items)
    {s : Arm.ArmState} {m : Loc → CV} {w : Arm.ArmState} {jl : Nat}
    (hrep : RepL R.af (planOwn R.fa.k R.af) R.L vb.label jl) (hpc : Arm.r .PC s = R.pcOf jl)
    (hst : StRel R s m w) :
    (∃ W, R.EntryWit t (Arm.r .PC s) W) ∧
      QW R s (R.entryW t (Arm.r .PC s)).1 (R.entryW t (Arm.r .PC s)).2.1
        (R.entryW t (Arm.r .PC s)).2.2 (.run ⟨t, items.toList, m, w⟩) := by
  have hE : ∃ W, R.EntryWit t (Arm.r .PC s) W := by
    rw [hpc]; exact RL.entryWit_of_rep hR hrep ht hvb rfl hit
  exact ⟨hE, (RL.entryW_spec hE).qW hit rfl hst⟩

/-- **Entering a block at a pc with an entry witness**: `QW` at the chosen one. -/
theorem qW_entryW {R : RL} {t : Nat} {items : Array RItem} (hit : R.rf.blocks[t]? = some items)
    {s : Arm.ArmState} {m : Loc → CV} {w : Arm.ArmState}
    (hE : ∃ W, R.EntryWit t (Arm.r .PC s) W) (hst : StRel R s m w) :
    QW R s (R.entryW t (Arm.r .PC s)).1 (R.entryW t (Arm.r .PC s)).2.1
      (R.entryW t (Arm.r .PC s)).2.2 (.run ⟨t, items.toList, m, w⟩) :=
  (RL.entryW_spec hE).qW hit rfl hst

end Backend.Proof
