import FV.Link.ConstPhiSrcScopeWitness

-- #1042: constant-phi removal and the source domain (the shape lean-link's `--verified` gate
-- handles: the bundle's program in `SrcScopeB`, the compiled input's source program not)
#print axioms Link.ConstPhiSrcScopeWitness.cp_changed -- witness: native_decide
#print axioms Link.ConstPhiSrcScopeWitness.src_in -- witness: native_decide
#print axioms Link.ConstPhiSrcScopeWitness.cp_src_out -- witness: native_decide
#print axioms Link.ConstPhiSrcScopeWitness.cp_prog_declSig -- witness: native_decide
