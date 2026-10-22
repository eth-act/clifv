import FV.Backend.Proof.LowerTotalT
import FV.Backend.Proof.IselPrgCtorSoundT
import FV.Backend.Proof.IselPrgCoverTermT
import FV.Backend.Proof.IselPrgHandT
import FV.Backend.Proof.IselPrgTabF64

-- S11 (#35) slice 8 totality: typed ISLE progress (driver totality, extern-helper model,
-- context invariant, roots, hand-checked rules, the `f64const` sub-table)
#print axioms Backend.Proof.Driver.buildCtx_okT
#print axioms Backend.Proof.Driver.lowerFunction_okT
#print axioms Backend.Proof.Prg.aextT_sound
#print axioms Backend.Proof.Prg.actorT_sound
#print axioms Backend.Proof.Prg.aidata_soundT
#print axioms Backend.Proof.Prg.pinv_buildT
#print axioms Backend.Proof.Prg.pinv_termCtxT
#print axioms Backend.Proof.Prg.pinv_tryCtxT
#print axioms Backend.Proof.Prg.stmt_rootT
#print axioms Backend.Proof.Prg.term_rootT
#print axioms Backend.Proof.Prg.try_rootT
#print axioms Backend.Proof.Prg.handRules_okT
#print axioms Backend.Proof.Prg.f64Tab_ok

-- non-vacuity witnesses
#print axioms Backend.Proof.Driver.buildCtx_okT_witness
