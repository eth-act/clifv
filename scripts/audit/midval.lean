import FV.Opt.Proof.MidValMem
import FV.Opt.Proof.MidValMemWitness

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
