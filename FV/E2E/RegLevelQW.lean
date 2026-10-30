import FV.E2E.RegLevelSegAlign
import FV.E2E.RegLevelOp
import FV.E2E.RegLevelBranch

/-!
# `q_op`, `q_next`, `q_entry` at a witness (SEM1 #537, item (3), route (a))

The bookkeeping lemmas of `RegLevelNext.lean`/`RegLevelBranch.lean` on `QW`: taking `QW` at an
instruction item apart (`qW_op`, which also names the item's code), putting it together at the
next item at the straight witness (`qW_next`), and the entry witnesses of blocks
(`RL.entryWit_exists`, `qW_entry`).
-/

namespace Backend.Proof

open Backend E2E

theorem relaxLines_single_ne (f : Lbl → Bool) (ln : Line) : (relaxLines f [ln]).length ≠ 0 := by
  simp only [relaxLines, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  unfold relaxLine
  split
  · split <;> simp
  · simp

/-- `QW` at an instruction item, taken apart (`q_op`). -/
theorem qW_op {R : RL} {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc} {its : List RItem}
    {m : Loc → CV} {w : Arm.ArmState} {j0 : Nat} {ps1 : PState} {T : List Line}
    (hq : QW R s j0 ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {i : MInst} (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i) :
    ∃ items pre regs i' c1 c2 ls1 ls2 psm ps2, ∃ (cc : CheckCtx) (wh : String) (ops : Array Operand),
      itemCode R.fr vb (.op k allocs) = .ok c1 ∧
      allocs = regs.map Loc.reg ∧ R.rf.blocks[b]? = some items ∧
      items.toList = pre ++ .op k allocs :: its ∧ i.assign regs = .ok i' ∧
      ((c1 = [AInst.inst i'] ∧ (∀ ds, i' ≠ .args ds) ∧ (∀ us, i' ≠ .rets us)) ∨
        (∃ ds, i' = .args ds ∧ c1 = []) ∨ (∃ us, i' = .rets us ∧ c1 = [AInst.epilogueRet])) ∧
      i.operands = .ok ops ∧ cc.checkStatic wh ops (regs.map Loc.reg) i.clobbers = .ok () ∧
      ItemsChecked R vb its ∧ itemsCode R.fr vb its = .ok c2 ∧
      codeLinesE R.ctx R.af c1 ps1 = .ok (ls1, psm) ∧ codeLinesE R.ctx R.af c2 psm = .ok (ls2, ps2) ∧
      ps2.traps.toList <+: R.psF.traps.toList ∧
      R.L.drop j0 = relaxLines R.far (ftList (ls1 ++ (ls2 ++ nxtOf R.af b))) ++ T ∧
      Arm.r .PC s = R.pcOf j0 ∧ StRel R s m w := by
  obtain ⟨vb0, items, pre, code, ls, ps2, hvb0, hit, hsplit, hchk, hcode, hls, htr, hdrop,
    hpc, hst⟩ := hq
  rw [hvb] at hvb0; cases hvb0
  obtain ⟨c1, c2, hc1, hc2, rfl⟩ := itemsCode_cons hcode
  have hc1o := hc1
  obtain ⟨regs, i0, i', rfl, hi0, hasg, hc1'⟩ := itemCode_op hc1
  rw [hi] at hi0; cases hi0
  obtain ⟨cc, wh, i2, ops, hi2, hops, hstat, hchk'⟩ := op_checked hchk
  rw [hi] at hi2; cases hi2
  obtain ⟨ls1, ls2, psm, h1, h2, rfl⟩ := codeLinesE_append _ _ _ _ _ hls
  exact ⟨items, pre, regs, i', c1, c2, ls1, ls2, psm, ps2, cc, wh, ops, hc1o, rfl, hit, hsplit,
    hasg, hc1', hops, hstat, hchk', hc2, h1, h2, htr, by rw [hdrop, List.append_assoc], hpc, hst⟩

/-- `QW` at the next item, at the straight witness, after the item's lines `ls1` ran
(`q_next`). -/
theorem qW_next {R : RL} {s : Arm.ArmState} {b : Nat} {it : RItem} {its : List RItem}
    {m : Loc → CV} {w : Arm.ArmState} {vb : VBlock} {items : Array RItem} {pre : List RItem}
    {c2 : List AInst} {ls1 ls2 : List Line} {psm ps2 : PState} {T : List Line} {j0 : Nat}
    (hvb : R.vc.blocks[b]? = some vb) (hit : R.rf.blocks[b]? = some items)
    (hsplit : items.toList = pre ++ it :: its) (hchk : ItemsChecked R vb its)
    (hc2 : itemsCode R.fr vb its = .ok c2) (h2 : codeLinesE R.ctx R.af c2 psm = .ok (ls2, ps2))
    (htr : ps2.traps.toList <+: R.psF.traps.toList)
    (hdrop : R.L.drop j0 = relaxLines R.far (ftList (ls1 ++ (ls2 ++ nxtOf R.af b))) ++ T)
    (hft : ftList (ls1 ++ (ls2 ++ nxtOf R.af b)) = ls1 ++ ftList (ls2 ++ nxtOf R.af b))
    (hpc : Arm.r .PC s = R.pcOf (j0 + (relaxLines R.far ls1).length)) (hst : StRel R s m w) :
    QW R s (j0 + (relaxLines R.far ls1).length) psm T (.run ⟨b, its, m, w⟩) := by
  have hdrop' : R.L.drop j0 =
      relaxLines R.far ls1 ++ (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T) := by
    rw [hdrop, hft, relaxLines_append, List.append_assoc]
  refine ⟨vb, items, pre ++ [it], c2, ls2, ps2, hvb, hit, by rw [hsplit]; simp, hchk, hc2, h2, htr,
    ?_, hpc, hst⟩
  rw [← List.drop_drop, hdrop', List.drop_left]

/-- **Every block but the entry has an entry witness** (`q_entry`). -/
theorem RL.entryWit_exists {R : RL} (hR : R.Wf) {t : Nat} {vb : VBlock} {items : Array RItem}
    (ht : t ≠ 0) (hvb : R.vc.blocks[t]? = some vb) (hit : R.rf.blocks[t]? = some items) :
    ∃ W, R.EntryWit t W := by
  obtain ⟨⟨-, -, -, hbl⟩, -⟩ := lowerRFunc_ok hR.alloc
  obtain ⟨code, hcode, haf⟩ := hbl t vb items hvb hit
  obtain ⟨body, psF, hb, -, hblk⟩ := emit_block hR.emit
  obtain ⟨body', hb'⟩ := hR.psF
  have hk : R.ctx = ⟨R.fa.k, R.af.slotBase⟩ := rfl
  rw [hk, hb] at hb'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hb'
  obtain ⟨-, rfl⟩ := hb'
  obtain ⟨j0, ls, ps1, ps2, T, hj0, hdrop, hls, htr, -⟩ := hblk t _ _ haf
  simp only [ht, ite_false, List.nil_append, List.toList_toArray] at hls
  refine ⟨(j0 + 1, ps1, T), fun vb' jl hvb' hjl => ?_, fun items' hit' => ?_⟩
  · rw [hvb] at hvb'; cases hvb'
    simp only [RL.pcOf, RL.L]
    rw [lineOffset_succ _ _ _ hj0]
    have e1 := labelOffsets_label hR.lm hj0
    have e2 := labelOffsets_label hR.lm hjl
    rw [e1] at e2
    simp only [Option.some.injEq] at e2
    simp only [Line.size, Nat.add_zero, RL.L] at e2 ⊢
    rw [e2]
  · rw [hit] at hit'; cases hit'
    exact ⟨vb, code, ls, ps2, hvb, itemsChecked_block hR hvb hit, hcode, hls, htr, hdrop⟩

/-- **Entering a block at the chosen entry witness** (`q_entry`). -/
theorem qW_entry {R : RL} (hR : R.Wf) {t : Nat} {vb : VBlock} {items : Array RItem} (ht : t ≠ 0)
    (hvb : R.vc.blocks[t]? = some vb) (hit : R.rf.blocks[t]? = some items)
    {s : Arm.ArmState} {m : Loc → CV} {w : Arm.ArmState} {jl : Nat}
    (hjl : R.L[jl]? = some (.label (.block vb.label))) (hpc : Arm.r .PC s = R.pcOf jl)
    (hst : StRel R s m w) :
    Arm.r .PC s = R.pcOf (R.entryW t).1 ∧
      QW R s (R.entryW t).1 (R.entryW t).2.1 (R.entryW t).2.2 (.run ⟨t, items.toList, m, w⟩) := by
  have hW := RL.entryW_spec (RL.entryWit_exists hR ht hvb hit)
  have hp : Arm.r .PC s = R.pcOf (R.entryW t).1 := hpc.trans (hW.1 vb jl hvb hjl)
  obtain ⟨vb', code, ls, ps2, hvb', hchk, hcode, hls, htr, hdrop⟩ := hW.2 items hit
  exact ⟨hp, vb', items, [], code, ls, ps2, hvb', hit, rfl, hchk, hcode, hls, htr, hdrop, hp, hst⟩

end Backend.Proof
