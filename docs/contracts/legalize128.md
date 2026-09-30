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

## Proven (no `sorry`; axioms: propext, Classical.choice, Quot.sound, `_native` bv_decide certificates)

**`Opt.Legal.check_refines`** (`FV/Opt/Proof/LegalSim.lean`): for `check C.f C.g C.cert = true`,
from entry states of `f` on `args` and of `g` on `args'` (`ExpRel (groups f.sig.params) args
args'`: `i128` arguments as `(lo, hi)` `i64` pairs, pads any `i64`; same slots and memory), if
`Clif.runLoop env p fuel` of `f` returns `vals` with memory `m1`, then `runLoop env p' k` of `g`
returns `vals'` with `ExpRel (groups f.sig.returns) vals vals'` and the same `m1` for some `k`;
if it traps with `c`, `g` traps with `c`. Premises:
* `EnvOk env C p p'`: externs called by `f`/`g` are not functions of `p`/`p'`; `HelperOk env`
  (the `__*ti3` helpers compute `Sem.div` at `i128` on the halves, trapping where it traps);
  `ExtLegal env` (an extern called with arguments expanded by its signature's groups returns the
  expanded results, traps where the original traps); `EnvKeepsAllocs env`;
* `MemBounded m` (valid ranges below `2^64`; the backend's `MemRel.valid` gives it);
* `NoMemTrap env p` of the source run: no reachable source step traps at a load/store. Chosen
  over an alignment/in-slot check: a 16-byte access whose two 8-byte halves are valid in two
  adjacent allocations traps while the split access does not; excluding memory traps of the
  source is exactly what `E2E.TrapsExplicit` (already a premise of `backend_correct_final`)
  states, so it costs nothing at the E2E level.

Layers: `LegalShift*` (variable shifts/rotates: 7-bit amounts for shifts, bit-level halves
lemmas `rotl_lo/hi` and an opaque-amount rotate core; each module < 20 s, < 2 GB — the old
128-bit-amount `bv_decide` goals ran out of 20 GB), `LegalMem` (split load/store), `LegalExt`
(ABI expansion `ExpRel`, contracts), `LegalPlan` (`pure_step`: every pure plan), `LegalSim`
(block entry `enter_sim`, statements `sim_same/pure/load/store/div/call/trap`, terminators
`sim_term`, `step_sim`, fuel induction `sim_run`, entry `check_refines`).

## Remaining

* `HelperOk`, `ExtLegal`, `EnvKeepsAllocs` proven for `Clif.Rust.env` (stated in `LegalExt`;
  the `div128` pair arithmetic vs `BitVec.sdiv/srem` via `toInt_sdiv`/`toInt_srem` is the
  main work).
* `E2E.backend_correct_legal` (FV/E2E/Legal.lean): compose `check_refines` with
  `backend_correct_final` at `g` (`MemBounded` from `Rel.holds`, `NoMemTrap` from the source's
  `TrapsExplicit`, `EnvOk.src/tgt` from `InSubset` of `g` in the legalised program).
* Until then legalised functions stay flagged unverified in `parsedFile128`.
