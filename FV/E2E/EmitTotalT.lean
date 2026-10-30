import FV.E2E.EmitTotal
import FV.E2E.EmitCondsDefs
import FV.Backend.Proof.SpillLocalPipeT

/-!
# Allocation, emission and layout are total on the typed scope (S11e5 Stage C, slice 8)

`backend_correct_final_total_emit`'s totality half (`AllocTotal`, `EmitTotal`) over the typed
movement scope `LowerScopeT`. The emission proofs (`emitPre`, labels, encodability, branch reach,
size) are about the prepared VCode and its spill allocation only; they need, besides the
decidable `emitCondsB`, that `prepare`'s input is in its domain (`Prep.PrepDomain`, typed:
`prepDomain_ofT`), that the spill allocation is accepted (`AllocChecked`, typed: slice 6's
`spillAcceptedT`), that every form is covered (`FormsCovered`) and that every instruction meets
the control check `ctlInstOk` with `Args` first in block 0 (the integer proof of the latter,
`ctlInsts_pipeline`, rests on the integer control-shape analysis; here it is a premise, decided
by `ctlInstsB` in the typed input scope).

* `spill_inst_cases_of`, `emitPre_spill_of`, `emitReady_spill_of`: `emitPre_spill_ok`,
  `emitReady_spill` from those facts (no CLIF function);
* `lowerAlloc_of_spill`, `lowerAllocReady_emit_of`: whatever the untrusted allocator answers,
  `lowerAllocReady`, `emitFunc` and `layout` succeed once the spill allocation is lowered and its
  code is ready;
* `lowerRFunc_spillAllocT`: `lowerRFunc` lowers the spill allocation on the typed pipeline's
  output (`lowerRFunc_spillAlloc`, typed);
* `backend_total_emitT`: the typed pipeline's allocation, emission and layout succeed.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill

/-- `FormsCovered` does not depend on the function context (`FormOk` ignores it). -/
theorem formsCovered_ctx {c : FnCtx} {vc : VCode} (h : FormsCovered c vc) (c' : FnCtx) :
    FormsCovered c' vc := h

/-- `ctlInstOk` everywhere in `vc` and block 0 starting with `Args` followed by an instruction:
the instruction part of `ctlCheck` (`ctlInsts_pipeline`'s conclusion). -/
def CtlInsts (vc : VCode) : Prop :=
  (∀ (b : Nat) (vb : VBlock) (k : Nat) (i : MInst), vc.blocks[b]? = some vb →
      vb.insts[k]? = some i → ctlInstOk b k i = true) ∧
    ∃ vb0 ds, vc.blocks[0]? = some vb0 ∧ vb0.insts[0]? = some (.args ds) ∧ 1 < vb0.insts.size

/-- **The instructions of the spill allocation's code** (`spill_inst_cases` from `prepare`'s
domain alone). -/
theorem spill_inst_cases_of {vc vcp : VCode} {af : AFunc} (hdom : Prep.PrepDomain vc)
    (hp : Backend.prepare vc = .ok vcp) (ha : lowerRFunc vcp (spillAlloc vcp) = .ok af)
    {b : Nat} {l : Label} {code : Array AInst} {m : MInst}
    (hb : af.blocks[b]? = some (l, code)) (hm : AInst.inst m ∈ code.toList) :
    ∃ vb, vcp.blocks[b]? = some vb ∧
      ((∃ (src dst : Loc) (ms : List AInst), MoveOk src dst ∧
          (RAFrame.compute vcp (spillAlloc vcp)).moveInsts src dst = .ok ms ∧ AInst.inst m ∈ ms) ∨
       (∃ (kk : Nat) (i : MInst) (regs : Array Reg), vb.insts[kk]? = some i ∧ i.assign regs = .ok m ∧
          (∀ ops, i.operands = .ok ops → regs.map Loc.reg = spillLocs ops i.clobbers) ∧
          (∀ ds, m ≠ .args ds) ∧ (∀ us, m ≠ .rets us))) := by
  obtain ⟨ss, ps, hcfg⟩ := Spill.cfg_ok_of_prepare hp hdom
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

/-- **`emitPre` succeeds on the spill allocation** (`emitPre_spill_ok` from `prepare`'s domain,
the covered forms and the control check). -/
theorem emitPre_spill_of {vc vcp : VCode} {af : AFunc} (hdom : Prep.PrepDomain vc)
    (hp : Backend.prepare vc = .ok vcp) (hcov : FormsCovered default vcp) (hctl : CtlInsts vcp)
    (ha : lowerRFunc vcp (spillAlloc vcp) = .ok af) : ∀ k, ∃ pre, emitPre k af = .ok pre := by
  intro k
  have hcov' : FormsCovered ⟨k, af.slotBase⟩ vcp := formsCovered_ctx hcov _
  apply emitPre_of
  apply blocksLinesE_total
  intro x hx a ha' ps
  obtain ⟨b, hb⟩ := List.mem_iff_getElem?.mp hx
  obtain ⟨l, code⟩ := x
  cases a with
  | prologue => exact ⟨_, rfl⟩
  | epilogueRet => exact ⟨_, rfl⟩
  | inst m =>
    obtain ⟨vb, hvb, hcase⟩ := spill_inst_cases_of hdom hp ha (by simpa using hb) ha'
    rcases hcase with ⟨src, dst, ms, -, hmv, hmm⟩ | ⟨kk, i, regs, hi, hasg, hloc, hna, hnr⟩
    · exact moveInsts_total _ hmv m hmm ps
    · exact op_total (hcov' b vb kk i hvb hi) (hctl.1 b vb kk i hvb hi) hloc hasg hna hnr ps

/-- **The spill allocation's code is ready** under `emitCondsB` (`emitReady_spill` from
`prepare`'s domain, the spill allocation's acceptance, the covered forms and the control
check). -/
theorem emitReady_spill_of {vc vcp : VCode} {af : AFunc} (hdom : Prep.PrepDomain vc)
    (hp : Backend.prepare vc = .ok vcp) (hacc : AllocChecked vcp (spillAlloc vcp))
    (hcov : FormsCovered default vcp) (hctl : CtlInsts vcp) (hem : emitCondsB vcp = true)
    (ha : lowerRFunc vcp (spillAlloc vcp) = .ok af) : emitReady af = true := by
  simp only [emitCondsB, Bool.and_eq_true] at hem
  obtain ⟨⟨⟨hsz, himm⟩, hna⟩, htg⟩ := hem
  obtain ⟨pre, hpre⟩ := emitPre_spill_of hdom hp hcov hctl ha 0
  obtain ⟨fa, he⟩ := emitFunc_of_emitPre hpre
  obtain ⟨hlab, hdef⟩ := emitFunc_labels_lowerRFunc (prepare_labels_nodup hp hdom) htg
    (Nat.le_of_eq (E2E.spillAlloc_size vcp).symm) ha he
  unfold emitReady
  rw [he]
  exact FnAsm.layoutReadyB_of hlab hdef (emitFunc_encodable_of hacc hcov himm ha he)
    (emitFunc_spill_near hna ha he) (emitFunc_spill_size hsz ha he)

/-- **`lowerAlloc` succeeds whatever the allocator answered** once the spill allocation is
lowered (`lowerAlloc_total`'s case analysis). -/
theorem lowerAlloc_of_spill {vcp : VCode} (hsp : ∃ af, lowerRFunc vcp (spillAlloc vcp) = .ok af)
    (ra : Except String RFunc) : ∃ af, lowerAlloc vcp ra = .ok af := by
  rw [lowerAlloc_eq_lowerRFunc]
  unfold allocResult
  cases ra with
  | error e => exact hsp
  | ok rf =>
    simp only
    by_cases hc : (checkAlloc vcp rf).isOk = true
    · simp only [hc, ite_true]
      cases hlr : lowerRFunc vcp rf with
      | ok af => exact ⟨af, hlr⟩
      | error e => exact hsp
    · simp only [hc]; exact hsp

/-- **`lowerAllocReady`, emission and layout succeed** whatever the allocator answered, once
the spill allocation is lowered and its code is ready. -/
theorem lowerAllocReady_emit_of {vcp : VCode} (hsp : ∃ af, lowerRFunc vcp (spillAlloc vcp) = .ok af)
    (hready : ∀ af, lowerRFunc vcp (spillAlloc vcp) = .ok af → emitReady af = true)
    (ra : Except String RFunc) (k : Nat) :
    ∃ af, lowerAllocReady vcp ra = .ok af ∧ ∃ fa fb, emitFunc k af = .ok fa ∧ fa.layout = .ok fb := by
  obtain ⟨af, ha⟩ := lowerAlloc_of_spill hsp (readyAnswer vcp ra)
  obtain ⟨fa, fb, he, hla⟩ := emit_of_emitReady (emitReady_lowerAllocReady hready ha) k
  exact ⟨af, (lowerAllocReady_eq vcp ra).trans ha, fa, fb, he, hla⟩

/-- **`lowerRFunc` lowers the spill allocation of the typed pipeline's output**
(`lowerRFunc_spillAlloc` over `LowerScopeT`; the local facts of `spillLocalOk_of_pipelineT`
with its run-time premises, the control check `CtlInsts`). -/
theorem lowerRFunc_spillAllocT {f : Clif.Function} {vc vcp : VCode} (hd : Dominated f)
    (hs : LowerScopeT f) (har : ArityOk f) (htc : Compile.tryArgClassOk f = true)
    (hrc : ResClassOk f) (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (hsc : ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, i.isCtl = true → SpillInstOk i)
    (hcov : FormsCovered default vcp) (hctl : CtlInsts vcp) :
    ∃ af, lowerRFunc vcp (spillAlloc vcp) = .ok af := by
  obtain ⟨ss, ps, hcfg⟩ := Spill.cfg_ok_of_prepare hp (prepDomain_ofT hd hs hl)
  exact lowerRFunc_spill_of hcfg (spillLocalOk_of_pipelineT hd hs har htc hrc hl hp hsc hcov)
    hctl.1 hctl.2

/-- **The typed pipeline's allocation, emission and layout succeed** (the totality half of
`backend_correct_final_total_emit` over `LowerScopeT`): for a function in the typed scope whose
lowering and prepared code meet the typed spill chain's run-time facts (control forms `hsc`,
covered forms `hcov`, definitions before kills `hk`), the control check (`hctl`) and the emission
conditions (`hem`), and every answer `ra` of the untrusted allocator, `lowerAllocReady`,
`emitFunc` and `layout` succeed, and the allocation lowered (`allocResult`) is `AllocChecked`. -/
theorem backend_total_emitT {f : Clif.Function} {vc vcp : VCode} (hd : Dominated f)
    (hs : LowerScopeT f) (har : ArityOk f) (htc : Compile.tryArgClassOk f = true)
    (hrc : ResClassOk f) (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (hsc : ∀ vb ∈ vc.blocks.toList, ∀ i ∈ vb.insts.toList, i.isCtl = true → SpillInstOk i)
    (hcov : FormsCovered default vcp) (hk : killFreeB vcp = true) (hctl : CtlInsts vcp)
    (hem : emitCondsB vcp = true) (ra : Except String RFunc) (k : Nat) :
    AllocChecked vcp (allocResult vcp (readyAnswer vcp ra)) ∧
    ∃ af, lowerAllocReady vcp ra = .ok af ∧ ∃ fa fb, emitFunc k af = .ok fa ∧ fa.layout = .ok fb := by
  have hdom := prepDomain_ofT hd hs hl
  have hacc := spillAcceptedT hd hs har htc hrc hl hp hsc hcov hk
  refine ⟨allocChecked_allocResultT hd hs har htc hrc hl hp hsc hcov hk _,
    lowerAllocReady_emit_of (lowerRFunc_spillAllocT hd hs har htc hrc hl hp hsc hcov hctl)
      (fun af ha => emitReady_spill_of hdom hp hacc hcov hctl hem ha) ra k⟩

end E2E
