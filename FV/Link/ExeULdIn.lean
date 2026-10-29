import FV.Link.ExeLdIn
import FV.Link.ExeUCompile
import FV.Link.UnwFnIn

/-! # The executable compiler with unwinding on `lean-ld`'s inputs: what is left (S10g, #404)

`compileExeU S file0` is `compileExe` followed by `unwOkB` on the written executable: the
executable's unwind tables are the compiled functions' (`ehOkR`) and the per-function unwinding
checks hold (`unwFnsB`). **`compileExeU_total_ldIn`**: under `compileExe_total_ldIn`'s premises
(decided on `lean-ld`'s inputs) and `unwCondsB` of the compiled functions
(`Link.EhCheck.Complete.unwFnsB_of_conds`: the input condition `tryTablesB`, the code below
4 GiB, and the check without a completeness proof yet, `unwCheck`;
`lastCallsOk` is no longer needed since #622),
`lean-ld` links, `compileExe` succeeds,
and `compileExeU` succeeds as soon as the written executable passes `ehOkR` (the tables `lean-ld`
merged from the region object's `.eh_frame`; not yet derived from the inputs).
-/

namespace Link.DeadCleanup

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend LinkSpec Ld

/-- **The executable compiler with unwinding on `lean-ld`'s output, from the input conditions
and the remaining unwinding conditions**: `compileExe_total_ldIn`, and `compileExeU` succeeds
when the written executable's unwind tables pass `ehOkR`. -/
theorem compileExeU_total_ldIn {S : LinkSpec} {o : Opts} {ins : List Input} {st : St}
    {g : GcOut}
    (hres : resolve (o.entry :: o.undefs) ins = .ok st)
    (hgc : st.gc (o.entry :: o.undefs) o.gc = .ok g)
    (hrefs : layRefsB o st g = true) (hrels : relsInB o st g = true) (hfit : fitsB o st g = true)
    (hsp : specPreB (ldSpec S o st g) o st g = true)
    (hin : InScopeIn (ldSpec S o st g).input0 = true) (hl : (ldSpec S o st g).layoutOkB = true)
    (hreach : (ldSpec S o st g).reachOkB = true)
    (hU : EhCheck.Complete.unwCondsB (parResultsCleanupT (ldSpec S o st g).input0) = true) :
    ∃ r, link o ins = .ok r ∧
      compileExe (ldSpec S o st g) r.img.write =
        .ok (patch r.img.write (offsetOf r.img.phs (ldSpec S o st g).R)
          (regionOf (ldSpec S o st g) (tpOff r.img.phs))) ∧
      (EhCheck.ehOkR (parResultsCleanupT (ldSpec S o st g).input0)
          (patch r.img.write (offsetOf r.img.phs (ldSpec S o st g).R)
            (regionOf (ldSpec S o st g) (tpOff r.img.phs))) = true →
        compileExeU (ldSpec S o st g) r.img.write =
          .ok (patch r.img.write (offsetOf r.img.phs (ldSpec S o st g).R)
            (regionOf (ldSpec S o st g) (tpOff r.img.phs)))) := by
  obtain ⟨r, hlk, hc⟩ := compileExe_total_ldIn hres hgc hrefs hrels hfit hsp hin hl hreach
  refine ⟨r, hlk, hc, fun heh => ?_⟩
  have hu := EhCheck.Complete.unwFnsB_of_conds hin hU
  unfold compileExeU
  rw [hc]
  simp [unwOkB, heh, hu]

end Link.DeadCleanup
