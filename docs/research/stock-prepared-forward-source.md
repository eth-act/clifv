# Checked preparation and forward realization

The indexed preparation relation describes every retained instruction and each
actual selected copy. Direct edges retain their original outgoing vector and
target parameters. A new synthetic edge has an empty first copy, then its real
jump applies the original vector to the parameterized original target. The old
single-vector argument-empty restriction is not used.

PerEdgePrepareSound proves structural decoding, one/two-step and whole-running
prefix preservation, full returns and halts including the terminal instruction,
and the original typed return/trap observations, generic over world types and
DriverSemG. The actual prepareAt_fields theorem also proves preservation of
name, class table, slot bytes, outgoing area and fired-rule metadata directly
from successful execution of the existing preparation implementation.

The actual indexed runtime adapter now calls prepareCheckedAt. Its successful
result internally establishes that relation. PerEdgeRegallocFwd ports the
original deterministic virtual-step and Realizes/iterN forward proofs, including
advancement past pending moves. PerEdgePreparedDriverSound composes actual
preparation and allocation/lowering success: an original indexed VCode return
or halt is realized by a machine implementing the selected allocation, with
equal returned values/world, the trace invariant and callee-saved parts. The
caller does not supply a preparation or allocation checker verdict.

Complete original LowerScope+Dominated Stock conditional and trap programs
inhabit that composition under actual csem from function entry. The chosen
spill allocation and its lowering are real computed outputs. A deterministic
valid-MStep successor selector realizes the allocated model and is proved to
satisfy Realizes, so the witness assumes no external realization certificate.
The return witness also reaches the real first opcode after callee-save moves;
the trap witness includes the actual source Clif trap and its coded virtual
trap observation. This is an allocated-model witness, not an Arm instruction/
encoded-byte realization proof. The previously added QEMU byte regression
continues to pass real oracle and unavailable-oracle fallback paths.

A separate actual filtering/splitting/RPO fixture executes its real csem
conditional through a newly introduced critical-edge jump. Its target has a
nonempty parameter list; the selected arbitrary CV value is preserved. This
inhabits the split-route decoder and one/two-step proof rather than testing only
already-split Stock graphs.

All prior preparation, single-vector semantics/checkers, M6 proofs and original
input-condition definitions remain unchanged. The existing indexed adapter
change is exactly one import and its two prepareAt calls becoming
prepareCheckedAt calls. Runtime allocation selection, fallback and instruction
lowering bodies are unchanged. Source preservation is checked against the
verified f1d1e0aa92 recovery snapshot, beyond the smaller recovery-source manifest.

The fresh complete Stock comparison is identical to the previous report for
all4,501 function identity/status/full-artifact records and all1,302 inventory
entries. All1,202 exact matches remain (including all671 production/#179 baseline
matches), zero gains/losses/rejections; counters unchanged. Exit10 means completed
measurement with global artifact equivalence false. The delta tool exits1 solely
because its improvement predicate requires a gain. The existing throw.clif
nonrepeatable reference-stage gap remains. No source-program changes, setting
changes, byte masking or normalization were introduced.

Still required: derive the structural relation/completeness from every actual
prepareAt filtering/splitting/RPO execution under original Stock inputs, prove
indexed fallback acceptance/totality/lowering/emission readiness, instantiate
Arm/bytes/compiler/linker/generated-proof realization consumers, and finish the
original source/block/whole-driver simulation and completeness across all
remaining rule families/effects/calls/try/traps/sinking. Internal checking and
finite witnesses do not prove those universal obligations. Production remains
legacy and full#140 remains active/incomplete. Final cutover still requires all
original accepted-input/theorem/axiom/identity/stage/#179 gates and a new complete
Stock measurement after production integration.
