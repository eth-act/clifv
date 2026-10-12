import FV.E2E.DeadCleanupAlloc
import FV.E2E.DeadCleanupEmit

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.DeadCleanup

theorem spill_inst_cases_cleanup {f : Clif.Function} {vc vcp : VCode} {af : AFunc}
    (hs : lowerScopeB f = true) (hl : lowerFunction f = .ok vc) (hp : Backend.prepare (prune vc) = .ok vcp)
    (ha : lowerRFunc vcp (spillAlloc vcp) = .ok af)
    {b : Nat} {l : Label} {code : Array AInst} {m : MInst}
    (hb : af.blocks[b]? = some (l, code)) (hm : AInst.inst m ∈ code.toList) :
    ∃ vb, vcp.blocks[b]? = some vb ∧
      ((∃ (src dst : Loc) (ms : List AInst), MoveOk src dst ∧
          (RAFrame.compute vcp (spillAlloc vcp)).moveInsts src dst = .ok ms ∧ AInst.inst m ∈ ms) ∨
       (∃ (kk : Nat) (i : MInst) (regs : Array Reg), vb.insts[kk]? = some i ∧ i.assign regs = .ok m ∧
          (∀ ops, i.operands = .ok ops → regs.map Loc.reg = spillLocs ops i.clobbers) ∧
          (∀ ds, m ≠ .args ds) ∧ (∀ us, m ≠ .rets us))) := by
  have hS := lowerScope_of hs
  obtain ⟨ss, ps, hcfg⟩ := Spill.cfg_ok_of_prepare hp (prune_prepDomain (prepDomain_of_lower hS hl hS.nonempty))
  obtain ⟨⟨-, -, hsz, hbl⟩, -, -⟩ := lowerRFunc_ok ha
  have hlt : b < (vcp.blocks.zip (spillAlloc vcp).blocks).size := by
    rw [← hsz]; exact (Array.getElem?_eq_some_iff.mp hb).1
  rw [Array.size_zip] at hlt
  obtain ⟨vb, hvb⟩ : ∃ vb, vcp.blocks[b]? = some vb :=
    ⟨_, Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨items, hit⟩ : ∃ items, (spillAlloc vcp).blocks[b]? = some items :=
    ⟨_, Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨cd, hcd, hb'⟩ := hbl b vb items hvb hit
  rw [hb] at hb'
  simp only [Option.some.injEq, Prod.mk.injEq] at hb'
  obtain ⟨-, rfl⟩ := hb'
  have hm' : AInst.inst m ∈ cd := by
    rcases List.mem_append.mp hm with h | h
    · split at h <;> simp at h
    · exact h
  obtain ⟨it, hitm, c1, hc1, hmc⟩ := mem_itemsCode hcd hm'
  have hok := itemOk_spillAlloc hcfg hvb hit it hitm
  refine ⟨vb, hvb, ?_⟩
  cases it with
  | move src dst => exact .inl ⟨src, dst, c1, hok, itemCode_move_ok hc1, hmc⟩
  | op kk allocs =>
    obtain ⟨regs, i, i', rfl, hi, hasg, hcase⟩ := itemCode_op hc1
    obtain ⟨i0, hi0, hloc⟩ := hok
    rw [hi] at hi0
    cases hi0
    rcases hcase with ⟨rfl, hna, hnr⟩ | ⟨ds, -, rfl⟩ | ⟨us, -, rfl⟩
    · simp only [List.mem_singleton, AInst.inst.injEq] at hmc
      subst hmc
      exact .inr ⟨kk, i, regs, hi, hasg, hloc, hna, hnr⟩
    · cases hmc
    · simp at hmc

/-! ## `emitPre` succeeds when every instruction expands -/

theorem emitPre_spill_cleanup_ok {p : Clif.Program} {f : Clif.Function} {vc vcp : VCode} {af : AFunc}
    (hsub : InSubset p f) (hd : dominatedB f = true) (hs : lowerScopeB f = true)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare (prune vc) = .ok vcp)
    (ha : lowerRFunc vcp (spillAlloc vcp) = .ok af) : ∀ k, ∃ pre, emitPre k af = .ok pre := by
  intro k
  have hcov := formsCovered_cleanup_complete (lowerScope_of hs) hl hp ⟨k, af.slotBase⟩
  obtain ⟨hins, -⟩ := ctlInsts_cleanup_pipeline hsub (dominated_of hd) (lowerScope_of hs) hl hp
  apply emitPre_of
  apply blocksLinesE_total
  intro x hx a ha' ps
  obtain ⟨b, hb⟩ := List.mem_iff_getElem?.mp hx
  obtain ⟨l, code⟩ := x
  cases a with
  | prologue => exact ⟨_, rfl⟩
  | epilogueRet => exact ⟨_, rfl⟩
  | inst m =>
    obtain ⟨vb, hvb, hcase⟩ := spill_inst_cases_cleanup hs hl hp ha (by simpa using hb) ha'
    rcases hcase with ⟨src, dst, ms, -, hmv, hmm⟩ | ⟨kk, i, regs, hi, hasg, hloc, hna, hnr⟩
    · exact moveInsts_total _ hmv m hmm ps
    · exact op_total (hcov b vb kk i hvb hi) (hins b vb kk i hvb hi) hloc hasg hna hnr ps

theorem emitReady_spill_cleanup {p : Clif.Program} {f : Clif.Function} {vc vcp : VCode} {af : AFunc}
    (hsub : InSubset p f) (hd : dominatedB f = true) (hs : lowerScopeB f = true)
    (har : Spill.arityOkB f = true)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare (prune vc) = .ok vcp)
    (hem : emitCondsB vcp = true) (ha : lowerRFunc vcp (spillAlloc vcp) = .ok af) :
    emitReady af = true := by
  simp only [emitCondsB, Bool.and_eq_true] at hem
  obtain ⟨⟨⟨hsz, himm⟩, hna⟩, htg⟩ := hem
  obtain ⟨pre, hpre⟩ := emitPre_spill_cleanup_ok hsub hd hs hl hp ha 0
  obtain ⟨fa, he⟩ := emitFunc_of_emitPre hpre
  obtain ⟨hlab, hdef⟩ := emitFunc_labels_lowerRFunc
    (prepare_labels_nodup hp (prune_prepDomain
      (prepDomain_of_lower (lowerScope_of hs) hl (lowerScope_of hs).nonempty)))
    htg (Nat.le_of_eq (spillAlloc_size vcp).symm) ha he
  unfold emitReady
  rw [he]
  exact FnAsm.layoutReadyB_of hlab hdef
    (emitFunc_encodable_of
      (spillAccepted_cleanup hsub (Spill.arityOk_of har) (dominated_of hd)
        (lowerScope_of hs) hl hp)
      (formsCovered_cleanup_complete (lowerScope_of hs) hl hp default) himm ha he)
    (emitFunc_spill_near hna ha he) (emitFunc_spill_size hsz ha he)

end E2E
