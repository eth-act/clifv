import FV.Concurrency
import FVTest.Concurrency.Litmus

-- the memory-model layer (T2, #38; docs/plans/atomics.md)
#print axioms Concurrency.Armv8.atomics_sc
#print axioms Concurrency.Armv8.ob_dmb
#print axioms Concurrency.Armv8.hb_shape
#print axioms Concurrency.Armv8.coherence
#print axioms Concurrency.Armv8.atomicity
#print axioms Concurrency.ClifMM.drf_sc
#print axioms Concurrency.Mapping.armv8_to_clif
#print axioms Concurrency.Mapping.armv8_drf_sc
#print axioms Concurrency.Exec.sc_interleaving
#print axioms Concurrency.Mapping.armv8_interleaving
#print axioms Concurrency.Code.lines_kinds
#print axioms Concurrency.Code.ordered_only_atomic
#print axioms Concurrency.Code.memInsns_rmwLoopLines
#print axioms Concurrency.Code.memInsns_casLoopLines
#print axioms Concurrency.Code.kinds_prologueLines
#print axioms Concurrency.Code.kinds_epilogueLines
#print axioms Concurrency.Code.kinds_relaxLines
-- non-vacuity witnesses
#print axioms Concurrency.Witness.incX_premises
#print axioms Concurrency.Witness.incX_conclusions
#print axioms Concurrency.Witness.incX_interleaving
#print axioms Concurrency.Witness.mp_premises
#print axioms Concurrency.Witness.mp_sc
#print axioms Concurrency.Code.lines_kinds_witness
-- litmus tests (herd7 verdicts)
#print axioms Concurrency.Litmus.mp_rel_acq
#print axioms Concurrency.Litmus.mp_plain
#print axioms Concurrency.Litmus.mp_rel
#print axioms Concurrency.Litmus.mp_dmbs
#print axioms Concurrency.Litmus.sb_rel_acq
#print axioms Concurrency.Litmus.sb_plain
#print axioms Concurrency.Litmus.sb_dmbs
#print axioms Concurrency.Litmus.lb_acq_rel
#print axioms Concurrency.Litmus.lb_plain
#print axioms Concurrency.Litmus.w22_rels
#print axioms Concurrency.Litmus.w22_plain
#print axioms Concurrency.Litmus.iriw_acqs
#print axioms Concurrency.Litmus.iriw_plain
#print axioms Concurrency.Litmus.corr
#print axioms Concurrency.Litmus.corr_wf
#print axioms Concurrency.Litmus.inc_both0_a
#print axioms Concurrency.Litmus.inc_both0_b
#print axioms Concurrency.Litmus.inc_wf
#print axioms Concurrency.Litmus.inc_ok
