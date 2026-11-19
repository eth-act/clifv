# Contract: the mid-end validator `Opt.MidVal` (#1119, option (c))

Status: **stage 1: checker measured, soundness proved.** The checker is an executable definition
(`FV/Opt/MidVal.lean`, `lake exe midval-check`) measured on real dump pairs; on acceptance it
emits a certificate that `Opt.MidVal.checkCert` re-checks (`FV/Opt/MidValCert.lean`), and
**`Opt.MidVal.check_sound : checkCert f g cert = true → Opt.FunSimMU f g`** is proved with the
standard axioms (`FV/Opt/Proof/MidValSim.lean`; audit `scripts/audit/midval.lean`). No tool uses
the checker yet (no verdict, report or link input mentions it): that is the plumbing PR.

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
parameter types (the entry block: the same parameters, ids included, since it receives the
function's arguments), the same dominator tree.

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

## Soundness (proved; names are new, nothing existing changes)

* `Opt.FunSimMU f g`: the simulation of `Opt.FunSimU` with the frame relation over memory
  (`Frame → Frame → Mem → Prop`); `FunSimU` cannot express load removal because memory is
  quantified away at every step. With `FunSimU.toMU`, `FunSimMU.trans` and the program-level
  lifting `runLoopX_refinesMU`, whose conclusion is that of `Opt.runLoopX_refinesU`.
* `Opt.MidVal.check_sound : checkCert f g cert = true → FunSimMU f g` (stage 1, `Norm.id`; with a
  normaliser: `check_sound_norm : checkCert f g cert norm = true → NormSound norm →
  FunSimMU f g`), where `checkCert` re-checks the certificate the executable checker emits
  (`Opt.MidVal.emit`: the term table with a dominance site per term, the term of every value of
  `f` and `g`, the facts at each block's entry) and `NormSound` says the normaliser preserves
  values (`normSound_id`).
* Programs: `Opt.MidVal.validated_refines` — if every function of `q` is the one of `p` or a `g`
  with `checkCert (ConstPhi.run f) g cert = true` (`Validated`), then `∀ n xs xs', SRU syms xs xs'
  → ∃ n', XOutcomeRefines (runLoopX env p n xs) (runLoopX env q n' xs')` (same return values and
  final memory, same trap code, same exception; nothing claimed for a `stuck` or out-of-fuel
  source run). A removed load never removes a trap: its location holds a memory fact (accessed
  successfully, no writer since), so `f`'s load succeeds with the fact's value or is `stuck`
  (`evalInst_load_of_holds`); a dead load is removed only if `notrap` (`Clif.run` is `stuck`,
  never trapped, on a bad `notrap` access).
* Witnesses: `FVTest/Opt/MidValWitness.lean` decides `checkCert` (`native_decide`) on a real pair of
  the measured crates (memchr 2.8.3, `find_raw_impl`: two stores forwarded to loads, one across
  blocks, `stack_addr`s merged) and instantiates `check_sound` and `validated_refines` on it;
  `FVTest/Opt/MidValNegWitness.lean` shows `¬ FunSimMU f g` for three negative pairs (`neg_deadload`,
  `neg_stuckpure`, `neg_hoist`), hence `checkCert … cert = false` for **every** certificate.

## Proof modules (plan)

1. `FV/Opt/Proof/MidValMem.lean` — **done**: store-to-load and load-to-load facts in either byte
   order, never a trap (`load_of_store`, `load_of_load`; witnesses `MidValMemWitness.lean`).
2. `FV/Opt/MidValCert.lean` — **done**: the certificate `Cert` and `checkCert` (lists and arrays,
   structurally recursive; it reads `Opt.check`'s info of `f` and `g`), emitted by `emit` from
   `check`'s final state. Memory versions are not in the certificate: a writer drops every memory
   fact (one alias region), and each block's entry facts must be among the facts at the end of
   every predecessor (`CC.blockOk`), so the proof needs no dataflow fixpoint. Measured below:
   the same verdict as `check` on every pair.
3. `FV/Opt/Proof/SemSimM*.lean` — **done**: `ContM`, `IsSimM`, `CIOkM`, `TContM`, `HContM`,
   `TryOkMU`, `IsSimMU`, `FunSimMU` (the frame relation `R : Frame → Frame → Mem → Prop`; each
   local step matched from the same memory; after a call, a `try_call` return or at a handler the
   relation holds for every memory with the same symbols), `IsSimU.toMU`, `FunSimU.toMU`,
   `FunSimMU.refl`, `FunSimMU.trans`, `FunsSimMU`, the state relation `SRMU` with `SRU.toMU`,
   `runLoopX_refinesSRMU` and **`runLoopX_refinesMU`** (from `FunsSimMU p.funcs q.funcs`, exactly
   the conclusion of `runLoopX_refinesU`: `∀ n xs xs', SRU syms xs xs' → ∃ n',
   XOutcomeRefines …`); witness `SemSimMWitness.lean` (the ConstPhi witness pair, run to a return).
4. `FV/Opt/Proof/MidValTerm.lean` — **done**: term values `tmVal` (atoms read `f`'s registers, nodes
   are `evalNode` of earlier terms), stability (`tmVal_congr`), node terms (`tmVal_mapOperands`),
   `NormSound`/`normSound_id`; `MidValFloat.lean`: totality of the checker's pure nodes
   (`evalInst_pureK_total`, floats typed by `floatTyped`); `MidValFacts.lean`: the memory facts
   (`MemHolds`; load from a fact, fact from a load/store, idempotent store, `mergeK` memory
   independence); the `symbol_value`/`func_addr`/`tls_value` placement rule is the `defd` fact.
5. `FV/Opt/Proof/MidVal{Spec,Walk,Rel,Entry,Prefix,FStep,Match,Termin,Sim,Prog}.lean` — **done**:
   `checkCert_spec`, the walk case lemmas, the relation `Rel`/`MR` (positions in the same block, the
   rest of the walk succeeds, registers of both sides hold their terms' values, facts hold) and
   `MRW` (with equal register windows from the fresh values on), `g`'s pure prefix (`gPre_run`),
   steps of `f` alone (`rel_nop`, `rel_pure`, `rel_remove`), matched statements (`rel_matched`),
   terminators and `try_call` edges (`rel_term`, `rel_try`, `rel_enter`), `isSimMU`,
   **`check_sound`**, `validated_refines`; witnesses above.
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

**Re-check (`midval-check --cert`, 2026-11-19, the same 121,879 pairs regenerated):** every pair
gets the same verdict and reason as `check` (10 autocfg probes differ only in their per-build
symbol hash); `checkCert (emit f g)` is `true` on all 73,703 accepted pairs. Time per accepted
pair: `check` median 91 µs (mean 157, p99 924, max 159 ms), `checkCert` median 33 µs (mean 56,
p99 320, max 54 ms; 4.1 s in total; second run, with the static site check `CC.sitesOk`). The 12
hand-made pairs: the 4 positive ones re-check `ok`, the 8 negative ones are rejected by `check`
(no certificate).

## Follow-up: the checker gaps (2026-11-19, agent MidendGaps1)

* **`call_indirect` and `bitcast`**: `checkCert` and `check` run `Opt.MidVal.wfCheck` instead of
  `Opt.check` (unchanged): `call_indirect` result types from the function's `sigDecls`
  (`sigDeclOf`), `bitcast` typed by width as `Clif.evalInst` evaluates it (`pureTypedM`). Proof
  side: `WfM` (`FV/Opt/Proof/MidValWf.lean`, `wfM_of_wfCheck`, the `DomInv` lemmas restated),
  `evalInst_pureK_totalM`, and the `call_indirect` step proved (`matched_ci`: same signature,
  callee and argument terms, memory reset at the call).
* **Hoisted `symbol_value`/`tls_value`/`func_addr`**: a separate mode, `checkCertSyms`
  (`check … (hoist := true)`, `midval-check --hoist`): `g` may evaluate such a node of `f` before
  `f` does. Theorem `check_soundSyms : checkCertSyms f g cert = true → globalsResolve f syms = true
  → FunSimMUAt syms f g` (`globalsResolve`: every such instruction of `f` names a symbol `syms`
  defines; decidable from the function and the symbol table, for link-check); program level
  `validated_refines_syms` (`ValidatedSyms syms`), through `runLoopX_refinesMUAt` (the
  `SemSimMU` chain restated for `FunsSimMUAt syms`, the old statements its instances).
  `checkCert` itself does not accept hoisting.
* **Negative witnesses**: `neg_call`, `neg_merge`, `neg_endian`, `neg_readonly`: `¬ FunSimMU`, so
  every certificate is rejected; `neg_type` is a true simulation (little-endian `load.i32` of a
  stored `i64` = `ireduce`), the checker is conservative there (`ty_check_rejects`).
* **Measured** (the 121,879 pairs regenerated; the stage-1 binary on the same dumps: 73,703):
  items 1+2 74,462 (61.1 %; +613 `call_indirect`, +146 `bitcast`; 1,210 former `call_indirect`
  pairs now fail on a rewrite), hoisting mode 74,477 (+15; 388 former placement pairs now fail on
  a rewrite). Every accepted pair re-checks `ok`. Newly accepted, compiled from `g` in
  ReleaseScope1's counterfactual: 1,079 / 1,086 identical to stock (items 1+2), 3 / 15 (hoisting).
  Witnesses on real pairs: `FVTest/Opt/MidValGapWitness.lean`.
