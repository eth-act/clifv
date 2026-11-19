# Contract: the mid-end validator `Opt.MidVal` (#1119, option (c))

Status: **stage 1, in progress.** The checker is an executable definition (`FV/Opt/MidVal.lean`,
`lake exe midval-check`) measured on real dump pairs; the memory facts it relies on are proved
(`FV/Opt/Proof/MidValMem.lean`); the soundness theorem below is not proved yet, and no tool uses
the checker (no verdict, report or link input mentions it).

## What it is for

In builds whose Cranelift `opt_level` is not `none` (`cargo fv --release`, crates raising
`opt-level` in a profile), cg_clif compiles Cranelift's optimised function `g` while `cargo fv`
compiles the unoptimised dump `f`; their bytes then differ (23.1 % parity on 9 release crates).
The validator decides, per function, whether `g` may be compiled in place of `f` while the
theorem stays about `f`; Cranelift's mid-end stays outside the trusted base, and a rejected
function is compiled from `f` as today.

## The check (`Opt.MidVal.check f g norm`)

`f` is the unoptimised dump after `Opt.ConstPhi.run` (Cranelift's own unreachable-code and
constant-phi removal, which run before the e-graph), `g` the optimised dump. Same header and
`sigDecls`, both well-formed (`Opt.check`), the same blocks in the same order with the same
parameter types, the same dominator tree.

* **Terms.** Every value gets a hash-consed term: `param b i`, `res b k j` (result `j` of `f`'s
  statement `k` of block `b`, a skeleton statement), `node i` (a pure node with term operands,
  passed through the normaliser `norm`). Renaming, aliases, GVN, dead pure nodes and any
  placement of pure nodes are invisible.
* **Pure nodes** (`pureK`): `Opt.isPure`, `func_addr`, `tls_value`, the non-trapping float ops.
  `g` may evaluate one where `f` does not, so each must be total on its checked operand types:
  `Opt.check` types the `isPure` ones, `floatTyped` the float ones; `symbol_value`, `func_addr`
  and `tls_value` (`stuck` on a symbol missing from the image) are accepted in `g` only where `f`
  evaluated the same term no later.
* **Skeleton** (everything else) is matched in order, statement by statement, with term operands;
  terminators likewise. A skeleton statement of `f` without a counterpart is accepted only as: a
  load whose location is known (same memory version, address term, offset, type, access kind,
  explicit byte order; from a dominating store or load); a store of the value already known at
  its location; a `notrap` load (its value becomes an opaque term no compared position may
  contain); a trapping instruction with idempotent effects equal to a dominating one.
* **Memory versions**: Cranelift 0.135.0's `LastStores` with one region (cg_clif sets no alias
  region): every store, call, `call_indirect`, atomic, `fence` and `try_call` starts a version, a
  join of different versions starts one; explicit traps keep it.
* **Normaliser seam** (`Norm`): `Norm.id` in stage 1. A stage-2 rewrite (constant evaluation,
  a proven `simplify` rule) is one more `Norm` with a lemma that it preserves the value under
  `Clif.evalInst`. `evalConst` (constant evaluation) exists for measurement only
  (`midval-check --fold`).

Rejected, with a reason: ISLE rewrites (`rewrite:*`), dead-store elimination (`alias:store`),
moved `can_move` loads, the two checker gaps below.

## Soundness (to be proved; names are new, nothing existing changes)

* `Opt.FunSimMU f g`: the simulation of `Opt.FunSimU` with the frame relation over memory
  (`Frame → Frame → Mem → Prop`); `FunSimU` cannot express load removal because memory is
  quantified away at every step. With `FunSimU.toMU`, `FunSimMU.trans` and the program-level
  lifting `runLoopX_refinesMU`, whose conclusion is that of `Opt.runLoopX_refinesU`.
* `Opt.MidVal.check_sound : checkCert f g norm cert = true → NormSound norm → FunSimMU f g`, where
  `checkCert` re-checks the certificate the executable checker emits (terms, versions, the
  alignment script, known values and their sites) and `NormSound` says the normaliser preserves
  values.
* Refinement: `OutcomeRefines` (same return values and final memory, same trap code; nothing
  claimed for a `stuck` or out-of-fuel source run). A removed load never removes a trap: its
  location was accessed successfully at the same version, so `f`'s load succeeds or is `stuck`
  (`Clif.Mem.load_of_store`, `Clif.Mem.load_of_load`); a dead load is removed only if `notrap`
  (`Clif.run` is `stuck`, never trapped, on a bad `notrap` access).

## Proof modules (plan)

1. `FV/Opt/Proof/MidValMem.lean` — **done**: store-to-load and load-to-load facts in either byte
   order, never a trap (`load_of_store`, `load_of_load`; witnesses `MidValMemWitness.lean`).
2. `FV/Opt/MidValCert.lean`: the certificate and `checkCert` (lists and arrays, no hash maps in
   what the proof reads), emitted by `check`; the measurement must give the same verdicts.
3. `FV/Opt/Proof/SemSimM*.lean`: `IsSimM`/`FunSimMU`, `toMU`, `trans`, `runLoopX_refinesMU`
   (the lifting of `SemSim`/`SemSimX`/`SemSimU` with memory threaded through the relation).
4. `FV/Opt/Proof/MidValTerm.lean`: term evaluation, `NormSound`, totality of typed pure nodes.
5. `FV/Opt/Proof/MidValSim.lean`: the relation (a valuation of the atoms; registers are the
   terms' values; the known values hold in memory at the current version), step lemmas, block
   entry, `check_sound`; a positive witness on a real pair of the measured crates and the
   negative pairs of `FVTest/Opt/midval/`.
6. Plumbing (separate PR): per-function theorem about `f` through the validator, `lean-backend`
   naming it only when `checkCert` is decided, `cargo fv` passing the `.opt.clif` when the dump's
   `opt_level` is not `none`, `lean-link`/`link-check` re-deciding the check per pair
   (`Link.cpSource` pattern), a gate line. crypto-bigint's executables first need #1122.

## Measured (2026-11-19, 9 release crates, 121,879 dump pairs)

Accepted 73,703 (60.5 %); of those, 72,862 / 73,695 (98.9 %) are byte-identical to stock when
compiled from `g` (ReleaseScope1's opt-input run); projected release parity 60.1 % (today 23.1 %);
with constant evaluation 63.3 % accepted. Rejections: ISLE rewrites 37.3 %, `call_indirect`
result types in `Opt.check` 1.5 % and `bitcast` typing 0.2 % (checker gaps, follow-up), symbol
placement 0.3 %, dead-store elimination 5 functions. fv-demo debug: 1,342 / 1,378 accepted, the
rest the two checker gaps. Details and per-crate tables: #1119 issuecomment-7009839377.
