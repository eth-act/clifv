import FV.E2E.RelaxTotal
import FV.E2E.EmitReady
import FV.Backend.AllocReady
import FV.E2E.EmitPreOk
import FV.E2E.EmitEnc
import FV.E2E.EmitLabels
import FV.E2E.EmitNear
import FV.E2E.EmitSize

/-!
# Emission and layout are total (V6b)

`backend_correct_final_total_relaxed` (V6) still assumed that `emitPre` succeeds and that the
emitted code passes `layoutReadyB`. Both premises are discharged here, for the backend's
`lowerAllocReady` (`FV/Backend/AllocReady.lean`): regalloc2's lowered function is kept only if it
is `emitReady`, else the spill allocation is lowered — and for in-scope input the spill
allocation's code is ready (`emitReady_spill`) under four decidable conditions on the prepared
VCode (`emitCondsB`), each counted by `lean-e2e-check` (1149 of 1149):

* `spillSizeOkB` (`FV/E2E/EmitSize.lean`): a word bound of the spill code below 2^24 — the size
  input condition (genuinely needed: a large enough function exceeds the 128 MiB reach of `b`);
* `immsOkB` (`FV/E2E/EmitEnc.lean`): instruction selection's immediates are in the encoder's
  ranges (and an indirect call target is an int vreg);
* `noAlwaysB` (`FV/E2E/EmitNear.lean`): no `condBr`/`trapIf` with condition `al`/`nv` (those are
  not relaxed);
* `branchTargetsOkB` (`FV/E2E/EmitLabels.lean`): every branch target is a block label.

The last three are facts about `lowerFunction`'s output, proven from the ISLE rule data in
`FV/E2E/EmitTotalIn.lean` (V6c: `backend_correct_final_total_emit_in`, under the input condition
`extendsWidenB`); everything else (`emitPre` success, labels distinct and defined, register
encodability, the atomic-loop/jump-table forms in reach) is proven.

* `emitPre_index`, `emitFunc_index`: the function index only names labels in the text.
* `emit_of_emitReady`: an `emitReady` function emits and lays out at every index.
* `backend_correct_final_total_ready`: the end-to-end theorem for `lowerAllocReady`, given that
  the spill allocation's code is ready.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

theorem MInst.lines_index (m : MInst) (k sb : Nat) (ps : PState) :
    m.lines { k, slotBase := sb } ps = m.lines { k := 0, slotBase := sb } ps := by
  cases m <;> rfl

/-- `emitPre` does not depend on the function index. -/
theorem emitPre_index (k : Nat) (af : AFunc) : emitPre k af = emitPre 0 af := by
  unfold emitPre
  simp only [MInst.lines_index _ k]

/-- `emitFunc` depends on the function index only through the `k` field. -/
theorem emitFunc_index (k : Nat) (af : AFunc) :
    emitFunc k af = (emitFunc 0 af).map fun fa => { fa with k } := by
  unfold emitFunc
  rw [emitPre_index k af]
  cases emitPre 0 af with
  | error e => rfl
  | ok pre =>
    simp only [bind, Except.bind, Except.map]
    split <;> rfl

/-- An `emitReady` function emits and lays out at every function index. -/
theorem emit_of_emitReady {af : AFunc} (h : emitReady af = true) (k : Nat) :
    ∃ fa fb, emitFunc k af = .ok fa ∧ fa.layout = .ok fb := by
  unfold emitReady at h
  cases h0 : emitFunc 0 af with
  | error e => simp [h0] at h
  | ok fa0 =>
    rw [h0] at h
    have hk : emitFunc k af = .ok { fa0 with k } := by rw [emitFunc_index, h0]; rfl
    obtain ⟨fb, hfb⟩ := emitFunc_layout_ready hk h
    exact ⟨_, fb, hk, hfb⟩

/-- `emitReady` of `lowerAllocReady`'s function: regalloc2's by the check, else the spill
allocation's (`hspill`). -/
theorem emitReady_lowerAllocReady {vcp : VCode} {ra : Except String RFunc} {af : AFunc}
    (hspill : ∀ af, lowerRFunc vcp (spillAlloc vcp) = .ok af → emitReady af = true)
    (ha : lowerAlloc vcp (readyAnswer vcp ra) = .ok af) : emitReady af = true := by
  unfold readyAnswer at ha
  cases h : lowerAlloc vcp ra with
  | ok af0 =>
    rw [h] at ha
    simp only at ha
    split at ha
    · rename_i hr
      rw [h] at ha
      cases ha
      exact hr
    · exact hspill af ha
  | error e =>
    rw [h] at ha
    exact hspill af ha

set_option linter.unusedVariables false in -- the conclusion's premises are named for readability
/-- **The end-to-end theorem for the backend's allocation `lowerAllocReady`**, given that the
spill allocation's code is ready (`hspill`): allocation, lowering, emission and layout succeed
and the machine code refines the CLIF run. The frame is that of the allocation `lowerAllocReady`
lowers, `allocResult vcp (readyAnswer vcp ra)`. -/
theorem backend_correct_final_total_ready {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} (hsub : InSubset p f) (hd : dominatedB f = true) (hs : lowerScopeB f = true)
    (har : Spill.arityOkB f = true)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (hspill : ∀ af, lowerRFunc vcp (spillAlloc vcp) = .ok af → emitReady af = true)
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
      ArmRefines fb base ra' (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) := by
  obtain ⟨af, ha, hcor⟩ :=
    backend_correct_final_total (k := k) hsub hd hs har hl hp (readyAnswer vcp ra)
  obtain ⟨fa, fb, he, hla⟩ := emit_of_emitReady (emitReady_lowerAllocReady hspill ha) k
  exact ⟨af, (lowerAllocReady_eq vcp ra).trans ha, fa, fb, he, hla, hcor he hla⟩

/-- The decidable conditions on the prepared VCode under which the spill allocation's code is
ready (`emitReady_spill`). -/
def emitCondsB (vcp : VCode) : Bool :=
  spillSizeOkB vcp && immsOkB vcp && vcp.noAlwaysB && branchTargetsOkB vcp

/-- **The spill allocation's code is ready** for in-scope input under `emitCondsB`. -/
theorem emitReady_spill {p : Clif.Program} {f : Clif.Function} {vc vcp : VCode} {af : AFunc}
    (hsub : InSubset p f) (hd : dominatedB f = true) (hs : lowerScopeB f = true)
    (har : Spill.arityOkB f = true)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (hem : emitCondsB vcp = true) (ha : lowerRFunc vcp (spillAlloc vcp) = .ok af) :
    emitReady af = true := by
  simp only [emitCondsB, Bool.and_eq_true] at hem
  obtain ⟨⟨⟨hsz, himm⟩, hna⟩, htg⟩ := hem
  obtain ⟨pre, hpre⟩ := emitPre_spill_ok hsub hd hs hl hp ha 0
  obtain ⟨fa, he⟩ := emitFunc_of_emitPre hpre
  obtain ⟨hlab, hdef⟩ := emitFunc_spill_labels hs hl hp htg ha he
  unfold emitReady
  rw [he]
  exact FnAsm.layoutReadyB_of hlab hdef
    (emitFunc_spill_encodable hsub hd hs har hl hp himm ha he)
    (emitFunc_spill_near hna ha he) (emitFunc_spill_size hsz ha he)

set_option linter.unusedVariables false in -- the conclusion's premises are named for readability
/-- **The backend's end-to-end theorem, total including emission and layout** (V6b): for every
in-scope function (`InSubset`, `dominatedB`, `lowerScopeB`, `arityOkB`) whose prepared VCode
meets `emitCondsB` (the size bound and three facts about instruction selection's output), and
every answer `ra` of the untrusted allocator, the backend's allocation `lowerAllocReady`,
emission and layout succeed, and the machine code refines the CLIF run under
`backend_correct_final`'s contract, link-time and run premises. Compared with
`backend_correct_final_total_relaxed`, the premises `∃ pre, emitPre k af = .ok pre` and
`∀ fa, emitFunc k af = .ok fa → fa.layoutReadyB = true` are gone. -/
theorem backend_correct_final_total_emit {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} (hsub : InSubset p f) (hd : dominatedB f = true) (hs : lowerScopeB f = true)
    (har : Spill.arityOkB f = true)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (hem : emitCondsB vcp = true)
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
  backend_correct_final_total_ready hsub hd hs har hl hp
    (fun _ ha => emitReady_spill hsub hd hs har hl hp hem ha) ra

/-- `emitCondsB` of `lowerWitness`'s prepared VCode. -/
def lowerWitnessEmitCondsB : Bool :=
  match lowerFunction lowerWitness with
  | .error _ => false
  | .ok vc => match Backend.prepare vc with
    | .error _ => false
    | .ok vcp => emitCondsB vcp && match lowerRFunc vcp (spillAlloc vcp) with
      | .ok af => emitReady af
      | .error _ => false

/-- **Non-vacuity of `backend_correct_final_total_emit`**: on `lowerWitness` (whose other input
conditions `backend_correct_final_total_witness` discharges) the prepared VCode meets
`emitCondsB`, and `lowerAllocReady` succeeds with regalloc2 absent (its spill allocation's code is
`emitReady`, decided). -/
theorem backend_correct_final_total_emit_witness :
    ∃ vc vcp af, lowerFunction lowerWitness = .ok vc ∧ Backend.prepare vc = .ok vcp ∧
      emitCondsB vcp = true ∧ lowerAllocReady vcp (.error "regalloc2 absent") = .ok af := by
  obtain ⟨-, -, -, vc, vcp, af, hl, hp, ha⟩ := backend_correct_final_total_witness
  have h : lowerWitnessEmitCondsB = true := by native_decide
  have ha' : lowerRFunc vcp (spillAlloc vcp) = .ok af := ha
  simp only [lowerWitnessEmitCondsB, hl, hp, ha', Bool.and_eq_true] at h
  refine ⟨vc, vcp, af, hl, hp, h.1, ?_⟩
  simp [lowerAllocReady, ha, h.2]

end E2E
