import FV.Link.ExeULdIn
import FV.Link.UnwCheckIn

/-!
# The unwinding conditions left after `unwCheck_complete` (S10g, #404)

`unwCondB` (`FV/Link/UnwFnIn.lean`) still lists `unwCheck`, now a theorem: `unwCheck_complete`
(from `Dominated`, `LowerScope`, `tryTablesB` and the input condition `tryRetsB`).
**`unwCondInB`** lists what is left per function: the input conditions `tryTablesB` and
`tryRetsB` and the code size (Cranelift's frame, #549, made the saves' rows unconditional, so
the frame conditions `saveFrameB`/`leadOkB` are gone; `lastCallsOk` is no longer needed since
#622; since #553 `callSites` reads the emitter's aliases, and no alias resolves to the entry
block on the pipeline's output: `fwd_ne_entry_input`).
**`unwCondB_of_in`** gives `unwCondB` from it; **`unwCondsB_of_in`** lifts this to every
compiled function of an input in `InScopeIn`, and **`compileExeU_total_ldCond`** is
`compileExeU_total_ldIn` on these conditions.
-/

namespace Link.EhCheck.Complete

set_option autoImplicit false

open Backend Backend.Proof Backend.Proof.Driver E2E E2E.LinkCheck

/-- **The per-function unwinding conditions left** (see the module doc). -/
def unwCondInB (g : Clif.Function) (a : Art) : Bool :=
  tryTablesB g && tryRetsB g && decide (4 * a.fb.words.size < 2 ^ 32)

/-- `unwCondInB` of every compiled function of `R`. -/
def unwCondsInB (R : Res) : Bool := (progOf R).funcs.all fun g => unwCondInB g (artOf R g)

/-- **`unwCondB` from `unwCondInB`**: on a function of `fnScopeB` whose cleanup pipeline
succeeded, `unwCheck` holds by `unwCheck_complete`. -/
theorem unwCondB_of_in {g : Clif.Function} {k : Nat} {base : BitVec 64} {o : Lean.Json} {a : Art}
    (hpipe : pipeCleanupT g k base o = .ok a) (hsc : fnScopeB g = true)
    (hc : unwCondInB g a = true) : unwCondB g a = true := by
  simp only [unwCondInB, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨ht, hr⟩, hcode⟩ := hc
  obtain ⟨hl, -⟩ := pipeCleanupT_spec hpipe
  obtain ⟨-, -, -, -, -, -, -, hd, hs, -, -⟩ := fnScope_parts hsc
  have hu := unwCheck_complete (dominated_of hd) (lowerScope_of hs) ht hr hl
  simp [unwCondB, ht, hu, hcode]

/-- **`unwCondsB` from `unwCondsInB`** on an input in `InScopeIn`. -/
theorem unwCondsB_of_in {I : LinkInput} (hin : InScopeIn I = true)
    (hc : unwCondsInB (Link.DeadCleanup.parResultsCleanupT I) = true) :
    unwCondsB (Link.DeadCleanup.parResultsCleanupT I) = true := by
  have hin' := hin
  simp only [InScopeIn, progScopeInB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    at hin'
  obtain ⟨⟨⟨hn, -⟩, -⟩, hfs⟩ := hin'
  have hok := resultsCleanupT_ok_input hin
  rw [Link.DeadCleanup.parResultsCleanupT_eq] at hc ⊢
  have hprog : (progOf I.resultsCleanupT).funcs = I.prog.funcs := by
    simp [progOf, LinkInput.resultsCleanupT, LinkInput.prog, Function.comp_def]
  have hnR : ((progOf I.resultsCleanupT).funcs.map (·.name)).Nodup := by rw [hprog]; exact hn
  rw [unwCondsB, List.all_eq_true]
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
    exact unwCondB_of_in hpc hsc hcg

end Link.EhCheck.Complete

namespace Link.DeadCleanup

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend LinkSpec Ld

/-- **`compileExeU_total_ldIn` on the remaining conditions `unwCondsInB`** (no `unwCheck`). -/
theorem compileExeU_total_ldCond {S : LinkSpec} {o : Opts} {ins : List Input} {st : St}
    {g : GcOut}
    (hres : resolve (o.entry :: o.undefs) ins = .ok st)
    (hgc : st.gc (o.entry :: o.undefs) o.gc = .ok g)
    (hrefs : layRefsB o st g = true) (hrels : relsInB o st g = true) (hfit : fitsB o st g = true)
    (hsp : specPreB (ldSpec S o st g) o st g = true)
    (hin : InScopeIn (ldSpec S o st g).input0 = true) (hl : (ldSpec S o st g).layoutOkB = true)
    (hreach : (ldSpec S o st g).reachOkB = true)
    (hU : EhCheck.Complete.unwCondsInB (parResultsCleanupT (ldSpec S o st g).input0) = true) :
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
  compileExeU_total_ldIn hres hgc hrefs hrels hfit hsp hin hl hreach
    (EhCheck.Complete.unwCondsB_of_in hin hU)

end Link.DeadCleanup
