# Two-block Stock production

Implementation `5f35e773` extends main `efe8b677` with the first general direct
CFG production class. The default compiler, checker, verified linker and emitted
proof consumers select the actual Stock result for a two-block function whose
entry contains constants/nops and jumps to a scalar/division/mask return block.
New entry results are forwarded as successor arguments; inherited entry values
remain available. The class includes narrow integer widths and nine-argument
ABI inputs with a stack-passed argument and placed stack slots.

The proof executes the ABI prelude on the same canonical core as the source
body, branch, selected successor copies and return. It uses the original general
`SourceEntry` contract, including placed slots. Computed source availability and
assembly derive inherited/new-value coverage and the correspondence between
per-edge copies and legacy single-successor semantics. Nonempty copies are
supported. Source return and genuine division-trap contracts retain their
original fuel, ABI pins, memory deallocation and trap codes.

The additive CFG ABI-read model permits goto, derives absence of entry
predecessors from the actual code, and requires reference-world equality only
at true function entry. Paired physical return correctness follows through the
existing prepared/allocated/encoded pipeline. The old ABI-read models, theorem
variants and input conditions remain. No runtime check is accepted as a new
public source premise.

The new route retries the previous complete Scalar pipeline with the original
source, allocator and settings on candidate failure. Retained artifact indices
0–4 keep their meanings; the CFG route is appended. Actual byte reconstruction
records explicit index0 where the old default differs from the new default.
Optimizer and tail-call routes remain available.

A real mixed-program gate found that the verified CLI's global try-call guard
bypassed the new provider. On the same captured fv-demo images, the CFG provider
passed, while the prior Scalar provider required a differently sized region and
failed placement/region checks. The CLI now permits the checked CFG route when
a new-class function is present alongside retained try-call functions. Programs
without the new class retain their prior exception selection. The existing
`SemanticCompilerWith.attempt_correct_source` and peak theorem justify the
actual checked mixed result. No exception model or theorem premise changed.

## Validation

- Full FV/FVTest: 4041/4041. Final implementation replay rebuilt only the two
  edited IO leaves; the earlier complete replay checked all current keys.
- All89 axiom audit files pass: 3637 reports,3486 distinct roots. All3425
  previous required axiom sets are exact. Six compatible declaration-owner
  partitions cover every changed/new Lean module, including executable leaves.
  General declarations use only standard axioms; fixed witnesses admit only
  the three precise input-check/dominance facts recorded in the audit receipt.
- All16 old theorem headers in eight changed existing Lean modules are exact;
  the other3987 baseline Lean files are byte-identical. Two bundled transitive
  MCP reviews are clear; their proof sources are unchanged by later IO fixes.
- Integration:34 checks,14 generated roots, both allocators/cleanup modes,
  strict/fallback and retained routes, ordinary CLI proof reconstruction,
  verified linking and generated-proof axioms. Added mixed CFG/retained-try
  cases preserve the previous12 fixture roots.
- Native execution:24 objects,2880 Lean byte executions against360 Cranelift
  reference executions, zero disagreements. All96 final exported object,
  source, table and case files are byte-identical to the executed inputs.
- Runtime: corpus114/114, extra22/22, runtests5755 passes and zero failures or
  disagreements. The7 existing non-runnable runtest cases remain reported
  separately. Encoder:1398 identical functions,zero differences.
- Both E2E cleanup modes:1159 accepted,zero rejected. All1150 original and1159
  prior identities preserve their exact ordered stages.
- Verified fv-demo:21 matching tests,two verified executables. Verified survey:
  53 matching tests,18 verified executables. Actual crate-proofs default build
  passes:93 crate modules,649 recorded build/check steps.
- Fresh actual-crate comparison:4543 paired symbols,900 exact. A separate same-input current-main replay compares all4543 captured
  functions/settings:887→900 exact,13 gains,zero losses. Rebuilt baseline
  objects use the actual decoded compiler inputs, original order, gap words and
  symbol renaming. The historical report alone was not used to claim a gain.

Successful and failed attempts have separate receipts under
`/tmp/stock-cfg-production-*`. Terminal JSON records source hashes, binary
hashes, input equivalence, exact axiom/header preservation, comparison identities
and the remote recovery evidence. No emitted-code-shape native fact is added:
`StockCfgReadFixture` checks its actual compiler execution in the kernel.

## Remaining original goal

This is an incremental production expansion, not completion of #140. Internal
candidate rejection and legacy fallback preserve acceptance; they do not prove
Stock-only success or downstream completeness. Remaining work includes broader
entry bodies and block graphs, conditional/table/critical edges and loops,
uncovered rule/helper families, omitted/sunk effects, memory, calls and
exceptions, original-domain whole-driver simulation, and Stock-only lowering,
preparation/allocation/checking/physical/encoding/production completeness.
Retire rollout fallback only where those proofs justify it. Preserve old
variants, axioms, accepted identities and successful stages throughout.
