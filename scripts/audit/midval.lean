import FV.Opt.Proof.MidValMem
import FV.Opt.Proof.MidValMemWitness
import FV.Opt.Proof.SemSimMU
import FV.Opt.Proof.SemSimMWitness

-- #1119 (c) stage 1: the memory facts of the mid-end validator `Opt.MidVal.check`
#print axioms Clif.Mem.readFold_spec
#print axioms Clif.Mem.readFold_some
#print axioms Clif.Mem.writeBits_bytes
#print axioms Clif.Mem.readBits_writeBits
#print axioms Clif.Mem.checkAccess_ok_valid
#print axioms Clif.Mem.checkAccess_of_valid
#print axioms Clif.Mem.load_of_store
#print axioms Clif.Mem.load_of_load
#print axioms Clif.Mem.MidValWitness.store_ok
#print axioms Clif.Mem.MidValWitness.store_ok_big
#print axioms Clif.Mem.MidValWitness.fwd_lemma
#print axioms Clif.Mem.MidValWitness.fwd_big_lemma
#print axioms Clif.Mem.MidValWitness.fwd
#print axioms Clif.Mem.MidValWitness.fwd_big
#print axioms Clif.Mem.MidValWitness.rle_lemma
#print axioms Clif.Mem.MidValWitness.rle

-- (3) the memory-aware simulation `FunSimMU` and its program-level lifting
#print axioms Opt.IsSimM.star
#print axioms Opt.ContM.comp
#print axioms Opt.ContM.mono
#print axioms Opt.IsSimM.comp
#print axioms Opt.TryOkMU.toTryOkM
#print axioms Opt.TContM.comp
#print axioms Opt.TContM.mono
#print axioms Opt.HContM.comp
#print axioms Opt.HContM.mono
#print axioms Opt.IsSimMU.comp
#print axioms Opt.Cont.toM
#print axioms Opt.TCont.toM
#print axioms Opt.HCont.toM
#print axioms Opt.IsSimU.toMU
#print axioms Opt.FunSimU.toMU
#print axioms Opt.FunSimMU.refl
#print axioms Opt.FunSimMU.trans
#print axioms Opt.FunsSimMU.map
#print axioms Opt.FunsSimU.toMU
#print axioms Opt.FunsSimMU.findP
#print axioms Opt.FunsSimMU.externNames
#print axioms Opt.GRMU.of
#print axioms Opt.TContM.toContMU
#print axioms Opt.TabRelM.none'
#print axioms Opt.TabRelM.ofH
#print axioms Opt.TabRelM.bt
#print axioms Opt.CallersRelMU.length
#print axioms Opt.GRU.toMU
#print axioms Opt.TabRel.toM
#print axioms Opt.CallersRelU.toMU
#print axioms Opt.SRU.toMU
#print axioms Opt.XStepRelMU.stuck'
#print axioms Opt.XStepRelMU.trapped'
#print axioms Opt.XStepRelMU.done'
#print axioms Opt.XStepRelMU.same'
#print axioms Opt.XStepRelMU.push'
#print axioms Opt.XStepRelMU.pop'
#print axioms Opt.funSimMU_entry
#print axioms Opt.returnValues_relMU
#print axioms Opt.callCont_relMU
#print axioms Opt.tailCont_relMU
#print axioms Opt.ciCont_relMU
#print axioms Opt.sim_step_lstepMU
#print axioms Opt.sim_stepMU_core
#print axioms Opt.extRaise_congrMU
#print axioms Opt.indRaise_congrMU
#print axioms Opt.unwindFrom_relMU
#print axioms Opt.raiseIn_relMU
#print axioms Opt.sim_raiseMU
#print axioms Opt.XStepRelMU.toStepX
#print axioms Opt.sim_stepMU
#print axioms Opt.runLoopX_refinesSRMU
#print axioms Opt.runLoopX_refinesMU
-- (3) witnesses (native_decide of ConstPhiWitness only)
#print axioms Opt.SemSimMWitness.fwd_simMU -- witness: native_decide
#print axioms Opt.SemSimMWitness.fwd_simMU_trans -- witness: native_decide
#print axioms Opt.SemSimMWitness.pq_simMU -- witness: native_decide
#print axioms Opt.SemSimMWitness.entry_sru -- witness: native_decide
#print axioms Opt.SemSimMWitness.fwd_refinesMU -- witness: native_decide
#print axioms Opt.SemSimMWitness.p_returns
#print axioms Opt.SemSimMWitness.q_returns -- witness: native_decide
-- (no axioms at all: last, so the audit's parser does not join them with the next line)
#print axioms Opt.SemSimMWitness.keeps
#print axioms Opt.SemSimMWitness.fwd_entry
