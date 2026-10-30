import FV.E2E.EmitTotalIn
import FV.E2E.SizeVC
import FV.E2E.SizeLower
import FV.Backend.Proof.IselSzDriver
import FV.Backend.Proof.FormsCoverComplete

/-!
# The size bound from the input (V6c)

`backend_correct_final_total_emit_in` (`EmitTotalIn`) still assumed the size bound
`spillSizeOkB vcp` on the prepared VCode: the words of the spill allocation's code below `2 ^ 24`.
Here it follows from the decidable input condition `sizeOkB f` (`SizeDefs`: a word bound
`sizeBoundIn f` summed over `f`'s blocks, statements and terminators below `2 ^ 24`):

* the ISLE runs of the driver are bounded (`IselSz f`, `Driver.iselSz`): a cost analysis on V3's
  abstract interpreter (`IselSzSound`, tables `IselSzTab`), the call, `try_call` and `br_table`
  rules by hand (`IselSzCall`, `IselSzBrTable`);
* `lowerFunction`'s output is within `vcIn`/`tgIn` of the input (`size_lower`, `SizeLower`);
* `prepare` adds at most one edge block per branch target (`vcW_prepare`, `SizeVC`), and the spill
  allocation's words are within the VCode measure (`spillWordBound_le`).

* `spillSizeOkB_of_sizeOkB`: `spillSizeOkB vcp` for the pipeline's output from in-scope input.
* `backend_correct_final_total_emit_input`: `backend_correct_final_total_emit_in` with
  `spillSizeOkB vcp` replaced by `sizeOkB f`: every premise on the code is an input condition.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- The spill allocation's words are within the input-side bound, given the ISLE contract. -/
theorem spillWordBound_le_sizeBoundIn {f : Clif.Function} {vc vcp : VCode} (hI : IselSz f)
    (hE : Compile.functionE f = true) (hl : lowerFunction f = .ok vc)
    (hp : Backend.prepare vc = .ok vcp) : spillWordBound vcp ≤ sizeBoundIn f := by
  obtain ⟨hM, hW, hT⟩ := size_lower hI hE hl
  have h1 := spillWordBound_le vcp
  have h2 := vcW_mono (Nat.le_trans (maxRC_prepare hp) hM) vcp
  have h3 := vcW_prepare hp (mIn f)
  have h4 : jumpBW (mIn f) * vcTg vc ≤ jumpBW (mIn f) * tgIn f := Nat.mul_le_mul_left _ hT
  unfold sizeBoundIn
  omega

/-- A control form or a `FormOk` form is not a literal-pool load (#565). -/
theorem isLitLoad_of_covered2 {i : MInst} (h : i.isCtl = true ∨ FormOk default i = true) :
    i.isLitLoad = false := by
  cases hl : i.isLitLoad with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨sz, rd, c, fl, rfl⟩ : ∃ sz rd c fl, i = .fpuLoad sz rd (.const c) fl := by
      unfold MInst.isLitLoad at hl
      split at hl
      · exact ⟨_, _, _, _, rfl⟩
      · cases hl
    rcases h with h | h
    · cases h
    · unfold FormOk at h
      split at h <;> simp_all [memOk]
      -- the float `fpuLoad` arm: its addressing modes exclude `AMode.const`
      all_goals
        obtain ⟨-, -, rfl, -⟩ := ‹_ ∧ _ ∧ AMode.const _ = _ ∧ _›
        simp at h

/-- **Subset E has no literal-pool load**: the integer analysis's coverage is two-way
(`Driver.FormsCovered2`, #565). -/
theorem noPoolB_of_formsCovered2 {vcp : VCode} (h : FormsCovered2 vcp) : vcp.noPoolB = true := by
  unfold VCode.noPoolB
  rw [List.all_eq_true]
  intro vb hvb
  rw [List.all_eq_true]
  intro i hi
  obtain ⟨b, hb⟩ := List.mem_iff_getElem?.mp hvb
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
  rw [Array.getElem?_toList] at hb hk
  rw [isLitLoad_of_covered2 (h b vb k i hb hk)]
  rfl

/-- **The size bound from the input**: for a function in the lowering's scope (`lowerScopeB`) with
`sizeOkB f`, the prepared VCode meets `spillSizeOkB` (its `poolReachB` part since subset E has no
literal-pool load, `noPoolB_of_formsCovered2`). -/
theorem spillSizeOkB_of_sizeOkB {f : Clif.Function} {vc vcp : VCode}
    (hs : lowerScopeB f = true) (hsz : sizeOkB f = true)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp) : spillSizeOkB vcp = true := by
  have hI := iselSz (lowerScope_of hs)
  have h := spillWordBound_le_sizeBoundIn hI (lowerScope_of hs).subsetE hl hp
  unfold sizeOkB at hsz
  have := of_decide_eq_true hsz
  exact spillSizeOkB_of (by omega)
    (poolReachB_of_noPool (noPoolB_of_formsCovered2 (formsCovered2_complete (lowerScope_of hs) hl hp)))

set_option linter.unusedVariables false in -- the conclusion's premises are named for readability
/-- **The backend's end-to-end theorem, total including emission and layout, with every premise
on the code an input condition** (V6c): for every in-scope function (`InSubset`, `dominatedB`,
`lowerScopeB`, `arityOkB`) whose extends widen (`extendsWidenB`) and which meets the size bound
`sizeOkB`, and every answer `ra` of the untrusted allocator, the backend's allocation
`lowerAllocReady`, emission and layout succeed, and the machine code refines the CLIF run under
`backend_correct_final`'s contract, link-time and run premises. Compared with
`backend_correct_final_total_emit_in`, `spillSizeOkB vcp` is proven from `sizeOkB f`. -/
theorem backend_correct_final_total_emit_input {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} (hsub : InSubset p f) (hd : dominatedB f = true) (hs : lowerScopeB f = true)
    (har : Spill.arityOkB f = true) (hw : extendsWidenB f = true) (hsz : sizeOkB f = true)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (ra : Except String RFunc) :
    ∃ af, lowerAllocReady vcp ra = .ok af ∧
      ∃ fa fb, emitFunc k af = .ok fa ∧ fa.layout = .ok fb ∧
      ∀ {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
        {K : Nat},
      ∀
        (hC : ∀ s, CalleeOk
          (frameW K (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).intBase
            (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).size af s) K X H
            vcp.CallSite)
        (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
          (frameW K (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).intBase
            (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).size af s) X H
            vcp.TrySite)
        (hTls : hasTls f = true → ∀ s, TlsOk
          (frameW K (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).intBase
            (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).size af s) K X H)
        (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
          Rel.holds ⟨frameW K (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).intBase
            (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).size af s, syms,
            slotOff, (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).intBase⟩
            f sl cm w) X)
        (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
          Rel.holds ⟨frameW K (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).intBase
            (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).size af s, syms,
            slotOff, (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).intBase⟩
            f sl cm w) X)
        (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
        (hslot : af.slotBase = slotOff)
        {base ra' : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
        (hent : AbiEntry fb base ra' s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
        (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
        (hrel : Rel.holds ⟨frameW K
            (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).intBase
            (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).size af s,
          syms, slotOff, (RAFrame.compute vcp (allocResult vcp (readyAnswer vcp ra))).intBase⟩
          f cs.frame.slots cs.mem w₀)
        (htr : TrapsExplicit env p cs) (fuel : Nat),
      ArmRefines fb base ra' (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) :=
  backend_correct_final_total_emit_in hsub hd hs har hw hl hp
    (spillSizeOkB_of_sizeOkB hs hsz hl hp) ra

/-- **Non-vacuity of `backend_correct_final_total_emit_input`**: `lowerWitness` (whose other
input conditions `backend_correct_final_total_emit_in_witness` and
`backend_correct_final_total_witness` discharge) meets the size bound. -/
theorem backend_correct_final_total_emit_input_witness :
    extendsWidenB lowerWitness = true ∧ sizeOkB lowerWitness = true := by
  refine ⟨backend_correct_final_total_emit_in_witness.1, ?_⟩
  native_decide

end E2E
