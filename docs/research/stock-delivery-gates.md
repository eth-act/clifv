# Stock delivery gate receipts

Use `python3 scripts/stock-delivery-gates.py plan MANIFEST --out /tmp/NEW-DIRECTORY`
to inspect required gates, `run` to execute, `resume` to retain intact successful
checks, and `report` to independently reconstruct the summary without executing
commands. `--root` selects the checkout. Output must be outside it. Run requires
a fresh directory; resume serializes access to the existing directory.

The JSON manifest supplies packet/base/candidate, explicit argv arrays for each
gate, optional regex requires/forbids, input globs, output globs, tool executables,
environment overrides and baselines. Paths in argv/env/globs may use `{root}` and
`{out}`. Declare every external data file, tool and imported build artifact not
covered by the checkout or underlying normal Lake dependency-key check. Input
patterns matching no files fail before execution. `complete_inputs` defaults to
false: without a complete dependency declaration every resume reruns that gate.

The runner fingerprints all tracked and unignored working files, its own source,
manifest, declared files, tool executable bytes and effective environment value hashes (excluding shell nesting/last-command and the
Codex tool-call tracing identifier).
Input snapshots retain per-file hashes; environment values are not dumped.
Completed attempts keep original commit/command/timestamps/log/output hashes.
Changed inputs, logs or outputs invalidate reuse. Unknown dependency closure must
leave `complete_inputs` false. Use normal Lake keys; do not substitute saved
oleans under manually edited keys. Broad source invalidation is conservative;
this repair deliberately adds no dependency inference engine.

Commands run sequentially through memcap. OMP/Lean/Cargo workers are bounded at2;
memcaps cannot exceed16GiB, and the existing Lake scheduler is bounded to16GiB/
2jobs/max-cap16GiB. No healthy proof timeout or termination policy is added.
Exit-zero commands still must pass their explicit output assertions and must not
print the known initializer panic. Generated imports/layout and class-specific
checks remain owned by the existing integration scripts.

Each completed gate is committed atomically before final reporting. A reporting
failure can be repaired with report/resume while keeping truthful failed command
records and preserving earlier attempt logs. Historical receipts are separately
hashed references and never satisfy a current gate. No gate selection or CI/merge
policy changes: the packet manifest must name every applicable author gate from
TO-PROVE section7 and the Stock activation/identity/trust requirements.

Example manifest: scripts/fixtures/stock-delivery-runner.json. It runs the runner
regression checks and references the landed Mixed evidence as historical only.
Next delivery is logical production support, not further tooling expansion.
