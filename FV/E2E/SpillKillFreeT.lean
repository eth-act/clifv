import FV.Backend.Proof.RegallocOperands
import FV.E2E.RegLevelPush
import FV.Backend.Proof.KillPrep
import FV.Backend.Proof.KillDriverT
import FV.Backend.Proof.KillTryDefsT
import FV.Backend.Proof.KillAssembleT
import FV.E2E.LinkScopeT
import FV.Backend.Proof.LowerDecide
import FV.Backend.Proof.SpillArity

/-!
# `killFreeB` on the typed scope, proven (S11 slice 8, totality half)

`spillKillFreeT`: on `Dominated`, `LowerScopeT`, `AbiSigsOk`, `ArityOk`, `tryArgClassOk` input,
`prepare (lowerFunction f)` passes `Spill.killFreeB` (`spillKillFree` over the typed scope):

* `Kill.killRunsHypT` (`KillDriverT.lean`): the killed-vreg analysis of the ISLE runs is a
  uniform invariant over every root rule of the exported program, so it holds over
  float-capable contexts; only the two rule exclusions it used (`nop`, I128) are re-proven over
  `CtxInvT`;
* `Kill.tryDefsExactT` (`KillTryDefsT.lean`): a `try_call`'s call defines exactly its result
  vregs (its operands are integer-position values, `termIntPos_of`);
* `Kill.killFreeB_lowerT` (`KillAssembleT.lean`): the driver's typed VCode passes `killFreeB`;
* `Spill.killFreeB_prepare` with the typed CFG facts `Spill.lowOk_ofT`: `prepare` keeps it.

No premise names the float roots: a newly proven root needs no new proof here.

`LinkCheck.killFreeB_of_scopeT`: the same from the decided conjuncts of `fnScopeInTB`
(`dominatedB`, `lowerScopeTB`, the ABI checks, `arityOkB`, `tryArgClassOk`), so `lowerOutTB`'s
`Spill.killFreeB` conjunct follows from the rest of the typed input scope
(`LinkCheck.killFreeB_of_fnScopeInT`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **`killFreeB` on the typed scope**: the prepared VCode of every `Dominated`, `LowerScopeT`
function (with its ABI, arity and `try_call`-argument class conditions) passes
`Spill.killFreeB`. -/
theorem spillKillFreeT {f : Clif.Function} {vc vcp : VCode} (hd : Dominated f)
    (hs : LowerScopeT f) (ha : Spill.AbiSigsOk f) (har : Spill.ArityOk f)
    (htc : Compile.tryArgClassOk f = true) (hl : lowerFunction f = .ok vc)
    (hp : Backend.prepare vc = .ok vcp) : Spill.killFreeB vcp = true :=
  Spill.killFreeB_prepare (Spill.lowOk_ofT hd hs har htc hl)
    (Kill.killFreeB_lowerT Kill.killRunsHypT Kill.tryDefsExactT hd hs ha har htc hl) hp

/-- **`killFreeB` on the float scope**: `spillKillFreeT` over `LowerScopeTF`. -/
theorem spillKillFreeTF {f : Clif.Function} {vc vcp : VCode} (hd : Dominated f)
    (hs : LowerScopeTF f) (ha : Spill.AbiSigsOk f) (har : Spill.ArityOk f)
    (htc : Compile.tryArgClassOk f = true) (hl : lowerFunction f = .ok vc)
    (hp : Backend.prepare vc = .ok vcp) : Spill.killFreeB vcp = true :=
  Spill.killFreeB_prepare (Spill.lowOk_ofTF hd hs har htc hl)
    (Kill.killFreeB_lowerTF Kill.killRunsHypTF Kill.tryDefsExactTF hd hs ha har htc hl) hp

/-- `AbiSigsOk` from its decided conjuncts (`sigAbiOk`, `indSigsOk`). -/
theorem abiSigsOk_of_checks {g : Clif.Function} (h1 : sigAbiOk g.sig = true)
    (h2 : g.externs.all (fun e => sigAbiOk e.2.sig) = true) (h3 : indSigsOk g = true) :
    Spill.AbiSigsOk g := by
  simp only [indSigsOk, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h2 h3
  exact ⟨⟨h1, h2⟩, fun s hs => (h3 s hs).2⟩

namespace LinkCheck

/-- **Completeness of `killFreeB` on the typed scope, from decided input conditions**: the
conjuncts of `fnScopeInTB` other than `lowerOutTB` give `Spill.killFreeB` of every prepared
lowering. -/
theorem killFreeB_of_scopeT {g : Clif.Function} {vc vcp : VCode} (hd : dominatedB g = true)
    (hs : lowerScopeTB g = true) (habi : sigAbiOk g.sig = true)
    (hext : g.externs.all (fun e => sigAbiOk e.2.sig) = true) (hind : indSigsOk g = true)
    (har : Spill.arityOkB g = true) (htc : Compile.tryArgClassOk g = true)
    (hl : lowerFunction g = .ok vc) (hp : Backend.prepare vc = .ok vcp) :
    Spill.killFreeB vcp = true :=
  spillKillFreeT (dominated_of hd) (lowerScopeT_of hs) (abiSigsOk_of_checks habi hext hind)
    (Spill.arityOk_of har) htc hl hp

end LinkCheck

end E2E
