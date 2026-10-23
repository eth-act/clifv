import FV.Link.UnwCondIn
import FV.Backend.Proof.IselOutBoundRun

/-!
# The outgoing bound as an input condition (S10g, #404)

`unwCondInB` (`FV/Link/UnwCondIn.lean`) still decides the outgoing area of the compiled code
(`a.vcp.outgoing ≤ 32560`). It now follows from the input condition `outBoundB` on the call
signatures (`Backend.Proof.OutBound.lowerFunction_outgoing_le`, carried through `prune` and
`prepare`: **`vcp_outgoing_le`**). **`unwCondIn2B`** is `unwCondInB` with `outBoundB g` in place
of the decided bound; **`unwCondInB_of_in2`** gives `unwCondInB` from it,
**`unwCondsInB_of_in2`** lifts this to every compiled function of an input in `InScopeIn`, and
**`compileExeU_total_ldCond2`** is `compileExeU_total_ldCond` on these conditions.
-/

namespace Link.EhCheck.Complete

set_option autoImplicit false

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.OutBound E2E E2E.LinkCheck

/-- **The per-function unwinding conditions, the outgoing bound an input condition**:
`unwCondInB` with `outBoundB g` in place of `a.vcp.outgoing ≤ 32560`. -/
def unwCondIn2B (g : Clif.Function) (a : Art) : Bool :=
  tryTablesB g && tryRetsB g && lastCallsOk a.af a.fa && outBoundB g &&
    leadOkB a.rf a.af && decide (4 * a.fb.words.size < 2 ^ 32)

/-- `unwCondIn2B` of every compiled function of `R`. -/
def unwCondsIn2B (R : Res) : Bool := (progOf R).funcs.all fun g => unwCondIn2B g (artOf R g)

/-- **The prepared VCode's outgoing area is at most 32560 bytes** on `LowerScope` input with
`outBoundB`: `lowerFunction_outgoing_le`, and `prune` and `prepare` keep the outgoing area. -/
theorem vcp_outgoing_le {g : Clif.Function} {k : Nat} {base : BitVec 64} {o : Lean.Json} {a : Art}
    (hpipe : pipeCleanupT g k base o = .ok a) (hs : LowerScope g) (hob : outBoundB g = true) :
    a.vcp.outgoing ≤ 32560 := by
  obtain ⟨hl, hp, -⟩ := pipeCleanupT_spec hpipe
  rw [Prep.prepare_outgoing hp (DeadCleanup.prune_prepDomain (Driver.prepDomain_of hs hl)),
    DeadCleanup.prune_outgoing]
  exact lowerFunction_outgoing_le hs hob hl

/-- **`unwCondInB` from `unwCondIn2B`** on a function of `fnScopeB` whose cleanup pipeline
succeeded: the outgoing bound by `vcp_outgoing_le`. -/
theorem unwCondInB_of_in2 {g : Clif.Function} {k : Nat} {base : BitVec 64} {o : Lean.Json}
    {a : Art} (hpipe : pipeCleanupT g k base o = .ok a) (hsc : fnScopeB g = true)
    (hc : unwCondIn2B g a = true) : unwCondInB g a = true := by
  simp only [unwCondIn2B, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨ht, hr⟩, hlc⟩, hob⟩, hlead⟩, hcode⟩ := hc
  obtain ⟨-, -, -, -, -, -, -, -, hs, -, -⟩ := fnScope_parts hsc
  have hout := vcp_outgoing_le hpipe (lowerScope_of hs) hob
  simp [unwCondInB, ht, hr, hlc, hout, hlead, hcode]

/-- **`unwCondsInB` from `unwCondsIn2B`** on an input in `InScopeIn`. -/
theorem unwCondsInB_of_in2 {I : LinkInput} (hin : InScopeIn I = true)
    (hc : unwCondsIn2B (Link.DeadCleanup.parResultsCleanupT I) = true) :
    unwCondsInB (Link.DeadCleanup.parResultsCleanupT I) = true := by
  have hin' := hin
  simp only [InScopeIn, progScopeInB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    at hin'
  obtain ⟨⟨⟨hn, -⟩, -⟩, hfs⟩ := hin'
  have hok := resultsCleanupT_ok_input hin
  rw [Link.DeadCleanup.parResultsCleanupT_eq] at hc ⊢
  have hprog : (progOf I.resultsCleanupT).funcs = I.prog.funcs := by
    simp [progOf, LinkInput.resultsCleanupT, LinkInput.prog, Function.comp_def]
  have hnR : ((progOf I.resultsCleanupT).funcs.map (·.name)).Nodup := by rw [hprog]; exact hn
  rw [unwCondsInB, List.all_eq_true]
  intro g hg
  obtain ⟨e, he, rfl, ha⟩ := artOf_spec hnR hg
  obtain ⟨fi, hfi, rfl⟩ := List.mem_map.1 he
  have hok' := List.all_eq_true.1 hok _ he
  cases hpc : pipeCleanupT fi.func fi.k (BitVec.ofNat 64 (I.baseOf fi.func.name)) (raJ fi.ra fi.j)
    with
  | error _ => simp [hpc, Except.toBool] at hok'
  | ok a =>
    have haa : artOf I.resultsCleanupT fi.func = a := by rw [ha, hpc]; rfl
    rw [haa]
    have hsc := fnScopeB_of_input (hfs fi.func (by rw [← hprog]; exact hg))
    have hcg := List.all_eq_true.1 hc fi.func hg
    rw [haa] at hcg
    exact unwCondInB_of_in2 hpc hsc hcg

end Link.EhCheck.Complete

namespace Link.DeadCleanup

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend LinkSpec Ld

/-- **`compileExeU_total_ldCond` with the outgoing bound an input condition** (`unwCondsIn2B`:
`outBoundB` on the call signatures, no decision on the compiled code's outgoing area). -/
theorem compileExeU_total_ldCond2 {S : LinkSpec} {o : Opts} {ins : List Input} {st : St}
    {g : GcOut}
    (hres : resolve (o.entry :: o.undefs) ins = .ok st)
    (hgc : st.gc (o.entry :: o.undefs) o.gc = .ok g)
    (hrefs : layRefsB o st g = true) (hrels : relsInB o st g = true) (hfit : fitsB o st g = true)
    (hsp : specPreB (ldSpec S o st g) o st g = true)
    (hin : InScopeIn (ldSpec S o st g).input0 = true) (hl : (ldSpec S o st g).layoutOkB = true)
    (hreach : (ldSpec S o st g).reachOkB = true)
    (hU : EhCheck.Complete.unwCondsIn2B (parResultsCleanupT (ldSpec S o st g).input0) = true) :
    ∃ r, link o ins = .ok r ∧
      compileExe (ldSpec S o st g) r.img.write =
        .ok (patch r.img.write (offsetOf r.img.phs (ldSpec S o st g).R)
          (regionOf (ldSpec S o st g) (tpOff r.img.phs))) ∧
      (EhCheck.ehOkR (parResultsCleanupT (ldSpec S o st g).input0)
          (patch r.img.write (offsetOf r.img.phs (ldSpec S o st g).R)
            (regionOf (ldSpec S o st g) (tpOff r.img.phs))) = true →
        compileExeU (ldSpec S o st g) r.img.write =
          .ok (patch r.img.write (offsetOf r.img.phs (ldSpec S o st g).R)
            (regionOf (ldSpec S o st g) (tpOff r.img.phs)))) :=
  compileExeU_total_ldCond hres hgc hrefs hrels hfit hsp hin hl hreach
    (EhCheck.Complete.unwCondsInB_of_in2 hin hU)

end Link.DeadCleanup
