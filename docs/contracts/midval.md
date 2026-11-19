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
* **Normaliser seam** (`Norm`): `Norm.id` in stage 1; the default is now `Norm.stdT f` (stage 2,
  below: `Norm.std`, then the typed rules). A stage-2 rewrite is one more `Norm` with a lemma that
  it preserves the value under `Clif.evalInst` (`NormSound`, or `NormSoundT f` for a rule that
  reads an atom's type). `midval-check --norm-id` measures with stage 1's `Norm.id`,
  `--norm-const` with family 1 alone (`evalConst`), `--norm-std` without the typed rules.

Rejected, with a reason: ISLE rewrites (`rewrite:*`), dead-store elimination (`alias:store`),
moved `can_move` loads, the two checker gaps below.

## Soundness (proved; names are new, nothing existing changes)

* `Opt.FunSimMU f g`: the simulation of `Opt.FunSimU` with the frame relation over memory
  (`Frame → Frame → Mem → Prop`); `FunSimU` cannot express load removal because memory is
  quantified away at every step. With `FunSimU.toMU`, `FunSimMU.trans` and the program-level
  lifting `runLoopX_refinesMU`, whose conclusion is that of `Opt.runLoopX_refinesU`.
* `Opt.MidVal.check_sound : checkCert f g cert = true → FunSimMU f g` (with the default
  normaliser `Norm.stdT f`; for any normaliser: `check_sound_norm : checkCert f g cert norm = true →
  NormSound norm → FunSimMU f g`), where `checkCert` re-checks the certificate the executable
  checker emits (`Opt.MidVal.emit`: the term table with a dominance site per term, the term of
  every value of `f` and `g`, the facts at each block's entry) and `NormSound` says the
  normaliser preserves values (`normSound_id`, `normSound_std`).
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

## Stage 2: rewrites through the normaliser (agents MidendNorm1, MidendNorm2)

The default normaliser of `check`, `emit`, `checkCert` and `checkCertSyms` (`Norm.std`, since
the typed seam `Norm.stdT f`) grows one proved family at a time; `check_sound`'s text is
unchanged (`check_sound_normT h normSoundT_stdT`).

| family | normaliser step | proof | accepted (121,879 pairs) | accepted: identical to stock from `g` | projected release parity |
|---|---|---|---|---|---|
| stage 1 + gaps (`--norm-id`) | none | `normSound_id` | 74,462 (61.1 %) | 73,597 / 74,437 (98.9 %) | 60.5 % |
| 1: constant evaluation | `evalConst` | `normSound_evalConst` | 77,905 (63.9 %) | 76,767 / 77,880 (98.6 %) | 63.1 % |
| 2: single-node algebraic rules, first set | `Norm.alg` after `evalConst` | `normSound_alg` | 87,451 (71.8 %) | 80,622 / 87,406 (92.2 %) | 66.2 % |
| 2: second set | `Norm.alg2` before `Norm.alg` | `normSound_alg2`, `normSound_std` | 88,966 (73.0 %) | 81,681 / 88,921 (91.9 %) | 67.1 % |
| 3: branch conditions (`checkCertC`, hints) | none (`condPrep g hints` re-check) | `condPrep_simU`, `check_soundC` | 91,948 (75.4 %) | 84,317 / 91,898 (91.8 %) | 69.3 % |

(Projected release parity: functions byte-identical to stock if every accepted function is
compiled from `g` and every rejected one from `f`, over the 121,750 functions of the
counterfactual.)

* **Family 1, constant evaluation** (`Opt.MidVal.evalConst`, `FV/Opt/Proof/MidValNormConst.lean`):
  an `isPure`, non-partial node with at least one operand, every operand an `iconst` term (floats
  included: `f32const`/`f64const` are `iconst` at a float type), is the constant `Clif.evalInst`
  gives it in a frame holding those constants. No rewrite rule is involved: wrap-around, shift
  amounts ≥ width, signedness, `i128` and float bit patterns are `evalInst`'s by construction, and a
  node `evalInst` does not evaluate to one value is left alone. Proof:
  `normSound_evalConst : NormSound evalConst` (a pure node with operands reads neither the frame's
  function nor its slots, `evalInst_isPure_frame`; nor memory, `evalNode_pureK_mem`; its
  operands' term values are the collected constants, `mapM_lookup`, `tmVal_of_constOf`).
  Measured (2026-11-19, the 121,879 pairs regenerated, the same binary with and without
  `--norm-id`): +3,443 accepted, 0 lost, every accepted pair re-checks `ok`; all 3,443 newly
  accepted functions are Lean-compiled and verified from `g` in ReleaseScope1's counterfactual,
  3,170 of them byte-identical to stock. Hoisting mode: 74,477 → 77,932. Witnesses
  (`FVTest/Opt/MidValNormWitness.lean`): a real pair (crypto-bigint's `criterion`
  `InsertionHole<f64>::drop`, `imul 1, 8` → `iconst 8` passed to `memcpy`: rejected by `Norm.id`,
  `checkCert` decided, `real_simMU`, `real_refines`); `ishl.i32 1, 33 = 2` (the amount is taken
  modulo the width) and `sshr.i8 -128, 1 = -64` accepted, the look-alike folds to `0` and `64`
  rejected and shown to be no simulation, so every certificate is rejected (`shift_rejected`,
  `sshr_rejected`).
* **Family 2, single-node algebraic rules** (`Opt.MidVal.Norm.alg` = `Norm.guard algStep`,
  `FV/Opt/Proof/MidValNormAlg.lean`), tried where `evalConst` leaves the node alone
  (`Norm.std = Norm.orElse evalConst (Norm.orElse Norm.alg2 Norm.alg)`, second set below).
  Each rule maps a node to a node over existing terms with the same value under
  `Clif.evalInst` in every frame, ill-typed operands included (no
  typing premise): it reads an operand's structure only through `nodeAt` (a node whose operands
  are earlier) and `constAt` (a constant of the given type), and `Norm.guard` keeps a result only
  if every occurrence of it in the table has its operands earlier.
  - `selIcmp`: `select ty c 1 0` with `c` an `icmp` is `c` at `i8` and `uextend ty c` at a wider
    type; `select ty c 0 1` is the same of the inverted `icmp` (`IntCC.inv`, interned first by
    `auxTms`). Not for a `c` that is not an `icmp` (it need not be 0/1).
  - `mulPow2`: `imul ty x c` (either operand order) with `c` the constant `2^k` of type `ty`,
    `0 < k < width`, is `ishl ty x k` (the amount a constant of type `ty`, interned first).
  - `addStack`: `iadd ty s c` (either order) with `s` a `stack_addr ty slot off` and `c` a
    constant of type `ty` is `stack_addr ty slot (off + c)`, `c` read as signed (the address is
    taken modulo `2^width` on both sides).
  - `redExt`: `ireduce ty (extend op uty x)` with `x` a node whose result type `xt` is known
    (`nodeTy`), `xt` and `ty` narrower than `uty`: `x` if `xt = ty`, `extend op ty x` if `xt` is
    narrower, `ireduce ty x` if wider. Not for an atom `x` (a parameter, load or call result):
    its type is not in the table, and for an operand of another width the rewrite is false.

  These mirror Cranelift's mid-end rewrites seen in the dumps (`select`-of-`icmp` in
  `opts/selects.isle`, `imul` by a power of two in `opts/arithmetic.isle`, `ireduce`-of-extend in
  `opts/extends.isle`, and the `stack_addr` offset fold), and are proved directly against
  `Clif.evalInst`: `FV/Opt`'s proven 0.136.1 `simplify` rules carry a forward, typed obligation
  (`SimplifySound`: under a typed `GraphModel`, a candidate has the value the node has, if it has
  one), not the every-frame equality `NormSound` needs. Proof: `ruleSound_selIcmp`,
  `ruleSound_mulPow2`, `ruleSound_addStack`, `ruleSound_redExt`, `normSound_alg`, `normSound_std`.
  Measured (2026-11-19, the same 121,879 pairs; #1136's binary against this one): 77,905 → 87,451
  (+9,546), 0 lost, every accepted pair re-checks `ok`; 9,526 of the newly accepted functions are
  Lean-compiled and verified from `g` in ReleaseScope1's counterfactual (20 have no record there),
  3,855 of them byte-identical to stock (compiled from `f` today, they are not). Hoisting mode:
  77,932 → 87,518. Witnesses (`FVTest/Opt/MidValAlgWitness.lean`): per rule a hand-made pair
  accepted and rejected by family 1 alone, and a look-alike rejected (`select` of a non-`icmp`
  condition and the wrong extension in `redExt`'s place shown to be no simulation); three real
  pairs (`imul v1, 4` → `ishl v1, 2`; `iadd (stack_addr ss0), (imul 0, 8)` → `stack_addr ss0`;
  `select (icmp eq x, -1), 0, 1` and its `ireduce.i32` → `uextend` of `icmp ne x, -1`), each
  rejected by family 1 alone, `checkCert` decided, simulation and program refinement.
* **Family 2, second set** (`Opt.MidVal.Norm.alg2` = `Norm.guard algStep2`,
  `FV/Opt/Proof/MidValNormAlg2.lean`), tried before the first set; the same discipline (every
  frame, no typing premise). Cranelift's canonical forms:
  - `icmpSwap`: `icmp cc ty a b` with `a` a constant and `b` not is `icmp (swap cc) ty b a`;
  - `icmpBool`: with `u` an `icmp` (at `i8`) or its `uextend` to a type wider than `i8`,
    `icmp eq u 1` / `icmp ne u 0` is that `icmp`, `icmp eq u 0` / `icmp ne u 1` its inversion;
  - `icmpUnit`: `icmp ult x 1` is `icmp eq x 0`, `icmp uge x 1` is `icmp ne x 0` (the `0`
    interned first), `icmp ugt x 0` is `icmp ne x 0`, `icmp ule x 0` is `icmp eq x 0`;
  - `subNeg`: `isub 0 x` is `ineg x`; `mulTwo`: `imul x 2` (either order) is `iadd x x`, and
    `shlOne`: `ishl x c` with a constant amount `c ≡ 1` modulo the width is `iadd x x` too (so that
    `g`'s shift by one still meets the first set's former normal form);
  - `bmaskBool`: `bmask.i8 c` with `c` an `icmp` is `ineg.i8 c`; `xorNot`: `bxor x -1` (either
    order) is `bnot x`.

  Proof: `ns_icmpSwap`, `ns_icmpBool` (`boolAt_val`), `ns_icmpUnit`, `ns_subNeg`, `ns_mulTwo`,
  `ns_shlOne`, `ns_xorNot`, `ns_bmaskBool`, `ruleSound_algStep2`, `normSound_alg2`,
  `normSound_std`. Measured (2026-11-19, the same pairs; the first set's binary against this one):
  87,451 → 88,966 (+1,515), 0 lost, every accepted pair re-checks `ok`; all 1,515 newly accepted
  functions are Lean-compiled and verified from `g`, 1,059 byte-identical to stock. Hoisting
  mode: 87,518 → 89,065. (Without `shlOne`, 17 pairs the first set accepted were lost: `imul x 2`
  became `iadd x x` while `g`'s `ishl x 1` stayed.) Witnesses
  (`FVTest/Opt/MidValAlg2Witness.lean`): per rule a hand-made pair accepted and rejected without
  the second set, and a look-alike rejected (an `icmp` compared with `2`, `icmp ult x 2` against
  `icmp eq x 0`, and `bmask` of a non-`icmp` shown to be no simulation); five real pairs (`isub 0,
  x`; `imul x, 2`; `icmp ule 48, x`; `icmp ult x, 1`; `icmp eq (select (icmp eq x, -1), 0, 1), 1`),
  each rejected without the second set, `checkCert` decided, simulation and program refinement.
* **Family 3, branch conditions** (`Opt.MidVal.checkCertC`, `FV/Opt/MidValCond.lean`; proofs
  `FV/Opt/Proof/MidValCondSim.lean`, `FV/Opt/Proof/MidValCondProg.lean`). Cranelift's mid-end
  drops the zero test of a `brif` condition: `f` branches on `icmp ne x, 0` (or `icmp ugt x, 0`,
  `icmp ult 0, x`, an `uextend`/`sextend` of the condition, or a chain of these) where `g` branches
  on `x`. These are not value rewrites (`icmp ne x, 0` is `0`/`1`, `x` is not), so they are not a
  `Norm` rule; they hold only where the value is used as a branch condition (`brif` takes its
  `then` successor iff the value is non-zero). The validator does not relax the terminator
  comparison of `checkCert`. Instead:
  - `condPrep g hints` is `g` with, in each hinted block whose terminator is `brif c t e` with `c`
    below `g.freshValue`, fresh statements appended that rebuild `f`'s wrapper chain on `c`
    (`z = iconst ty 0; r = icmp ne c, z`, `r = uextend.ty c`, …, values numbered from
    `g.freshValue` on) and the terminator `brif r t e`. Only wrappers that keep the condition's
    truth whenever they evaluate are inserted (`Wrap.ok`: `icmp ne` with `0` on either side,
    `icmp ugt y, 0`, `icmp ult 0, y`, `extend`); any other hint leaves the block unchanged. A
    hint is a block id with a wrapper chain: it is untrusted (computed by `checkC`, the relaxed
    executable check), `condPrep` is built from `g` and the hints only, so a wrong hint can only
    make the re-check reject.
  - `refsOk g` (side condition, checked in `checkCertC`): every operand of every statement and
    terminator of `g` is below `g.freshValue`. `g.freshValue` is computed from the values `g`
    defines (block parameters, results), not from those it reads; without the test a statement
    of `g` could read a value numbered at or above it, which the inserted statements of
    `condPrep` write, so `g` and the copy would read different registers there (the proof's
    frame relation equates them only below `g.freshValue`).
  - `checkCertC f g cert hints` = `checkCert f g cert` for no hints, else `refsOk g &&
    checkCert f (condPrep g hints) cert`; `checkCertSymsC` the same for the hoisting mode. The
    compiled function stays `g`: the copy exists only inside the check, and the inserted values
    are read only by the copied `brif` (so the zero / non-zero equivalence is used only at that
    branch, never where a value is observed).

  Theorems (new names; nothing on main restated): `condPrep_simU : refsOk g = true → FunSimU
  (condPrep g hints) g` (the inserted statements are stuttering steps that write only values
  `g` never reads; both take the same successor at the `brif`, `prepChain_ok`),
  `check_soundC_norm`, `check_soundC` (`checkCertC f g cert hints = true → FunSimMU f g`, by
  `check_sound_norm` and `FunSimMU.trans`), `check_soundSymsC`, `checkedC_simMU`,
  `ValidatedC`/`ValidatedSymsC` (every `Validated` list is one: `Validated.toC`),
  `validatedC_refines`, `validatedC_refines_syms` (the conclusions of `validated_refines`/
  `validated_refines_syms`). Measured (2026-11-19, the same 121,879 pairs, `midval-check --cond
  --cert`; #1138's binary against this one): 88,966 → 91,948 (+2,982), 0 lost, every accepted
  pair re-checks `ok` with `checkCertC` and the emitted hints; 2,977 of the newly accepted
  functions are Lean-compiled and verified from `g` (5 have no record), 2,636 byte-identical to
  stock. Hoisting mode: 89,065 → 92,096. Witnesses (`FVTest/Opt/MidValCondWitness.lean`): `brif (icmp
  ne x, 0)` and `brif (uextend.i64 x)` against `brif x` accepted and rejected without hints; the
  look-alikes `brif (icmp eq x, 1)` and `brif (icmp ugt x, 1)` against `brif x` rejected, shown to
  be no simulation (`eq_not_sim`, `ugt1_not_sim`), so every certificate with every hint list is
  rejected (`eq_rejected`, `ugt1_rejected`); two real pairs (crypto-bigint: `brif (uextend.i64
  (load.i8 …))` → `brif (load.i8 …)`; `brif (icmp ne …, 0)` in a proptest runner with
  `try_call`s), each rejected without hints, `checkCertC` decided, simulation and program
  refinement.
* **Typed seam** (agent MidendNorm4; design: #1119 issuecomment-7024569975). Two rewrites seen
  in the dumps depend on an atom's width, which the term table does not hold; in an arbitrary
  frame an atom's register may hold a value of any type, so no every-frame equality (`NormSound`)
  covers them. The seam:
  - Compiler side (`FV/Opt/MidVal.lean`): `atomTy f` is the static type of an atom of `f` (block
    parameters' declared types; statement results' `Inst.resultTypes`, calls through the extern
    signatures, `call_indirect` through `sigDeclOf`; `none` for `poison`); `tyAt` gives a term's
    type (a node's `nodeTy`, an atom's `atomTy`). `selTyped`: `select ty c 1 0` / `select ty c 0
    1` with `c` an integer-typed term that is not an `icmp` is `icmp ne/eq tc c 0` at `i8`, its
    `uextend ty` wider (the `0` and the comparison are looked up with `findTm`; the untrusted
    `intern` interns them first, `internSelAux`). `redTyped`: `ireduce ty (extend op uty x)` with
    `x` an atom of static type `xt`, both narrower than `uty`: `x`, `extend op ty x` or
    `ireduce ty x` (as `redExt` for a node `x`). `Norm.stdT f = Norm.orElse Norm.std (Norm.guard
    (typedStep (atomTy f)))` is the default of `check`, `emit`, `checkCert`, `checkCertSyms`,
    `checkCertC`, `checkC`, `emitC` (a default that reads `f`), and of `midval-check`.
  - Obligation (`FV/Opt/Proof/MidValTerm.lean`): `AtomsTyped f tms fr mem i` (every atom reachable
    from `i`'s operands through node operands, `TmReach`, that has a static type holds a value of
    it in `fr`) and `NormSoundT f norm` (the normalised term has the node's value in every frame
    where `AtomsTyped` holds); `NormSound.toT`. The simulation evaluates a normalised node only in
    `f`'s frame at a point where its operands' sites are no later, so every atom below it is
    available there and typed by the run-time invariant (`Inv.regs`) and `wfCheck`'s typing
    (`atomTy_tm`, `reach_site`, `atomsTyped_of`, `FV/Opt/Proof/MidValTyped.lean`).
  - `HypT` is `Hyp` with `NormSoundT f norm` (`Hyp.toT`); the simulation lemmas taking `Hyp` have
    `…T` versions taking `HypT` (the two that use the normaliser, `TV_pureOkT` and `gStmtT`, get
    `AtomsTyped` from `HypT.atomsTyped`), and the old names are corollaries with their text.
    Theorems (new names): `check_sound_normT : checkCert f g cert norm = true → NormSoundT f norm →
    FunSimMU f g`, `check_soundSyms_normT`, `check_soundC_normT`; `check_sound`, `check_soundSyms`,
    `check_soundC` keep their text and are proved by them with `normSoundT_stdT : NormSoundT f
    (Norm.stdT f)` (`ruleSoundT_selTyped`, `ruleSoundT_redTyped`, `normSoundT_typed`,
    `FV/Opt/Proof/MidValNormTyped.lean`).
  - Witnesses (`FVTest/Opt/MidValTypedWitness.lean`): `select (icmp eq x, 0), 0, 1` against
    `select x, 1, 0` (`x` an `i32` parameter) and `ireduce.i16 (uextend.i64 x)` against `x`,
    `uextend.i16 x`, `ireduce.i16 x` (`x` of `i16`, `i8`, `i32`) accepted and rejected by
    `Norm.std`; the look-alikes `uextend.i64 (icmp ne x, 0)` against `select x, 0, 1` and the
    `i16` pair with an `i32` atom rejected, shown to be no simulation, so every certificate is
    rejected (`sel_rejected`, `red_rejected`); two real pairs (clap_builder in crypto-bigint's
    test build: `br_table (ireduce.i32 (uextend.i64 (load.i8 …)))` → `br_table (uextend.i32
    (load.i8 …))`; `select (icmp eq (load.i64 …), 0), 0, 1` → `select (load.i64 …), 1, 0`), each
    rejected by `Norm.std`, `checkCert` decided, simulation and program refinement. The design's
    prototype of the same rules measured 91,948 → 103,615 accepted (`--cond`, the same 121,879
    pairs, 0 lost); the landed binary is not measured here.
