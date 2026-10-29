module

public import FV.Backend.Proof.IselExcl
public import FV.Backend.Proof.DriverCheckSound

@[expose] public section

/-! Axiom audit of the excluded root rules (`ExcludedUnmatchable program`). -/

#print axioms Backend.Proof.excludedUnmatchable
#print axioms Backend.Proof.fails_sound
#print axioms Backend.Proof.Driver.ctxOk_sound
