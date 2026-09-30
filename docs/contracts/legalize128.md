# `Opt.Legalize128` and its validator (`Opt.Legal.check`)

Status: **validator landed and exercised; refinement proof in progress — legalised functions
are still flagged unverified** (`i128 legalized (outside backend_correct)`).

## Design (validator with fallback)

`Opt.Legalize128.function128Cert f` (untrusted, `FV/Opt/Legalize128.lean`) returns the
legalised function `g` and a certificate `Cert` (the `(lo, hi)` pair of every `i128` value,
the shared zero of the pad values). `Opt.Legal.check f g cert : Bool` (`FV/Opt/Legal.lean`)
re-derives, statement by statement, the segment of `g` each statement of `f` must be
rewritten to (`planOf` → `Plan`: `same`, a renamed instance of a canonical *pure pattern*,
two `i64` loads/stores, a `__*ti3` helper call, an ABI-expanded call, a condition pattern +
`trapz`/`trapnz`), and checks the terminators, block parameters (AAPCS64 pads), signature,
value-id layout (values of `f` `< T0 = maxValueId f`; pair components and zero distinct and
`≥ T0`; temporaries/pads fresh) and unique definitions.
`lean-backend` (`Opt.Legalize128.parsedFile128`) runs the check on every legalised function;
until the refinement theorem is complete, *accepted and rejected* functions are both flagged
unverified (accepted: `i128 legalized (outside backend_correct)`; rejected: `…: Opt.Legal.check
rejects`). Flipping the accepted case to "verified" is one line in `parsedFile128`, to be done
together with `E2E.backend_correct_legal`.

Measured: the check accepts all **203** legalised functions of the survey `g_u128` crates
(debug/release/release-oc) and the i128 Cranelift runtests, including all **189** functions
that would otherwise be inside `InSubset`/`lowerCheck` (31 survey + 158 runtest); it rejects
all **1197** single-statement mutants of those outputs (`/tmp` harness, not committed).

## Legaliser changes (required for provability / correctness)

* `iconcat`, `isplit.i128`, `ireduce.i64` of `i128`, `bitcast.i128` emit copies (`bor x, x`)
  instead of aliasing a pair: distinct source values never share a target value, so the value
  relation needs no dominance argument. Constant shift amounts through `iconcat` are still
  folded (`St.concatLo`).
* Shift-amount constants are folded by their **unsigned** value (`constOfDef` used `Int.toNat`
  of the signed immediate: `ishl x, iconst.i8 -1` shifted by 0 instead of 127 — a miscompile).
* `umulhi`/`smulhi` at `i128` are no longer legalised (the expansion returned
  `(0, low64(high half))`, wrong in general, e.g. `umulhi(2^64, 2^64) = 1`); such functions stay
  unsupported.
* `Clif.Rust.env`: `__*ti3` return with the caller's memory (was `Mem.empty`), and the
  `sdiv(i128::MIN, -1)` overflow test examines the dividend (it tested the divisor twice and never
  fired).
Differential after the changes: `clif-filetest --legalize128` over the 64 i128 runtest files:
legal pass 973 / fail 7 / agree 980 / **disagree 0** (the 7 fails are original-program failures
in `i128-load-store.clif`, agreed by the legalised form).

## Proven so far (no `sorry`; axioms: propext, Classical.choice, Quot.sound, `_native`
bv_decide certificates)

* `FV/Opt/Proof/LegalPat.lean`: `runPat_lstar`, `pureOk_run` — a `pureOk` segment executes
  (as `lstep`s) its canonical pattern: outputs at `outs`, every non-fresh value outside `outs`
  unchanged (injectivity/freshness from the check).
* `FV/Opt/Proof/LegalArith.lean`: every canonical pattern computes the `Clif.Sem` operation at
  `i128` on the halves (`Out128`): `pat_unary` (all 9 ops), `pat_binary` (bitwise, add, sub,
  min/max), `pat_imul` (`mul128`, toNat arithmetic), `pat_icmp` (10 condition codes), `pat_cond`,
  selects, `pat_bitselect`, `bmask` (3 shapes), extends, `ireduce`, copies,
  `pat_shiftNarrow`, `pat_constShift` (all amounts `< 128`, 4 normalised ops),
  `pat_varShift64/8/16/32` (5 ops each, incl. `rotr` normalisation).
* `FV/Opt/Proof/LegalBase.lean`: `check_good` (facts of an accepted check), value images and
  their disjointness, `VRel`/`RelV` with the general update lemma, `SrcInv` definitions.
* `FV/Opt/Proof/LegalSem.lean`: `evalInst_same`, `evalInst_types`, `evalInst_allocs`.

## Remaining (see `docs/DEFERRED.md`)

Plan-level step simulation (source statement ↔ segment, per plan kind; memory lemmas for the
split `i128` load/store; helper/extern-call env contracts `HelperOk`/`ExtLegal` and their proofs
for `Clif.Rust.env`), block entry / terminators, the fuel-induction refinement theorem
(original ↔ legalised under `Clif.runLoop`, returns related by the ABI expansion, traps equal,
premises: source `TrapsExplicit`, bounded allocations), and `E2E.backend_correct_legal`
composing it with `backend_correct_final`.
