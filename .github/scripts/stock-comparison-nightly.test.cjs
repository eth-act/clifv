const assert = require('node:assert/strict');
const { test } = require('node:test');
const { execFileSync } = require('node:child_process');
const n = require('./stock-comparison-nightly.cjs');
const EXACT = 'identical_code_artifact', DIFFERENT = 'different_code_artifact', UNSUPPORTED = 'lean_unsupported';
const repo = { owner: 'eth-act', repo: 'clifv' };
const bot = { login: 'github-actions[bot]', type: 'Bot' };
const context = { repo, runId: 900 };
process.env.GITHUB_RUN_ATTEMPT = '1';
function run(id = 10, changes = {}) {
  return { id, run_attempt: 1, head_sha: id.toString(16).padStart(40, '0'), head_branch: 'main',
    event: 'push', path: n.WORKFLOW, status: 'completed', conclusion: 'success',
    created_at: '2026-10-05T01:00:00Z', updated_at: '2026-10-05T02:00:00Z', ...changes };
}
function report(statuses = [EXACT, DIFFERENT, UNSUPPORTED, 'expected_stock_rejection_no_binary']) {
  const counts = {};
  for (const status of statuses) counts[status] = (counts[status] ?? 0) + 1;
  return { schema: 1, progress: 'finished', target: 'aarch64-unknown-linux-gnu', upstream_commit: 'a'.repeat(40),
    actual_ci_execution: false, execution_performed: false, binary_normalization: false, configuration_overrides: [],
    full_artifact_equivalence_verified: false, official_test_files: 2,
    inventory: [{ test: 'a.clif' }, { test: 'b.clif' }],
    source_hashes: Object.fromEntries(['FVTest/Backend/StockConfig.lean', 'FVTest/Backend/Main.lean',
      'tools/prejit-export/src/main.rs', 'tools/prejit-export/Cargo.lock', 'scripts/patches/prejit-export.patch',
      'scripts/stock-compiler-compare.py'].map(file => [file, 'b'.repeat(64)])),
    dependency_provenance: { version: 'pinned' },
    tests: [{ test: 'a.clif', source_sha256: 'c'.repeat(64), status: 'binary_test', variants: [{
      stage: 'compile', isa_index: 0, command_index: 0, target: 'aarch64-unknown-linux-gnu',
      reference_repeat_verified: true,
      flags: { opt_level: 'none' }, isa_flags: { has_lse: false },
      functions_compared: statuses.map((status, i) => ({ name: `%f${i}`, status })) }] },
    { test: 'b.clif', status: 'non_binary_test', variants: [] }],
    totals: { official_test_files: 2, inventoried_test_files: 2, files_with_compared_function_outputs: 1,
      files_all_aarch64_code_artifacts_identical: statuses.every(s => s === EXACT) ? 1 : 0,
      test_function_compilations: statuses.length, exact_code_artifacts: counts[EXACT] ?? 0,
      failed_stock_compile_assertions: 0, source_files_modified: 0, nonrepeatable_reference_stages: 0,
      function_statuses: counts, file_statuses: { binary_test: 1, non_binary_test: 1 } } };
}
function plan(changes = {}) {
  return { schema: 1, since: '2026-10-04T08:00:00.000Z', through: '2026-10-05T08:00:00.000Z',
    previous: null, snapshot_run_id: 900, snapshot_attempt: 1, initial: null,
    latest: { exact: 1, outputs: 3, sha: run().head_sha, totals: report().totals }, rows: [], ...changes };
}
function zipState(saved) {
  return execFileSync('python3', ['-c', 'import io,sys,zipfile\nb=io.BytesIO()\nwith zipfile.ZipFile(b,"w") as z: z.writestr("state.json",sys.stdin.buffer.read())\nsys.stdout.buffer.write(b.getvalue())'],
    { input: JSON.stringify(saved) });
}
function fixture(options = {}) {
  const calls = [], issue = { body: options.body ?? 'Human introduction.' };
  const saved = options.saved ?? { schema: 1, through: plan().through, baseline: n.snapshot(report(), run()) };
  const currentRun = run(900, { event: 'schedule', path: n.NIGHTLY, ...options.runChanges });
  let reads = 0;
  const github = { rest: {
    actions: { listWorkflowRuns: 'runs', listWorkflowRunArtifacts: 'artifacts',
      getWorkflowRun: async args => ({ data: args.run_id === 900 ? currentRun : run(args.run_id, { path: n.NIGHTLY, event: 'schedule' }) }),
      downloadArtifact: async () => ({ data: zipState(saved) }) },
    issues: { get: async () => {
      reads++;
      if (options.humanEdit && reads === 2) issue.body += '\nNew human note.';
      if (options.failConfirmation && reads === 3) return { data: { body: 'Unexpected body' } };
      return { data: { ...issue } };
    }, listComments: 'comments',
      createComment: async args => { calls.push(['create', args]); if (options.failCreate) throw new Error('create failed');
        return { data: { id: 99, user: bot, body: args.body, html_url: 'https://example.com/comment/99' } }; },
      update: async args => { calls.push(['update', args]); if (options.failUpdate) throw new Error('update failed'); issue.body = args.body; },
      deleteComment: async args => { calls.push(['delete', args]); if (options.failDelete) throw new Error('delete failed'); } },
  }, paginate: async method => {
    if (method === 'runs') return options.runs ?? [];
    if (method === 'artifacts') return [{ id: 50, name: 'stock-nightly-state-1', size_in_bytes: 512, expired: false }];
    if (method === 'comments') return options.comments ?? [];
    throw new Error('Unexpected pagination');
  }, request: async (_route, args) => ({ data: { status: options.historyStatus ?? 'ahead',
    commits: args.page === 1 ? [{ sha: run(11).head_sha, author: options.author ?? { login: 'contributor' },
      commit: { author: { name: 'Contributor' }, message: 'Fix operation\n\nDetails' } }] : [] } }) };
  return { github, context, issueNumber: 46, core: { info() {}, warning(message) { calls.push(['warning', message]); } }, calls, issue };
}
function oldComment(id, changes = {}) {
  return { id, user: bot, body: n.render(plan({ snapshot_run_id: id, ...changes })).body };
}

test('offsetting gains cannot hide a lost exact match', () => {
  const old = n.snapshot(report([EXACT, DIFFERENT]), run());
  const next = n.snapshot(report([DIFFERENT, EXACT]), run(11));
  const d = n.difference(old, next);
  assert.equal(old.totals.exact_code_artifacts, next.totals.exact_code_artifacts);
  assert.equal(d.gained.length, 1); assert.equal(d.lost.length, 1);
  assert.ok(d.lost[0].includes('%f0'));
});
test('unsupported transitions and removed identities remain distinct', () => {
  const old = n.snapshot(report([EXACT, DIFFERENT, UNSUPPORTED]), run());
  const next = n.snapshot(report([UNSUPPORTED, EXACT]), run(11));
  const d = n.difference(old, next);
  assert.equal(d.lost.length, 1); assert.equal(d.supportLost.length, 1);
  assert.equal(d.removed.length, 1); assert.equal(d.gained.length, 1);
});
test('reference and harness changes are incomparable, compiler driver changes are not', () => {
  for (const change of [r => r.upstream_commit = 'd'.repeat(40),
    r => r.source_hashes['scripts/stock-compiler-compare.py'] = 'd'.repeat(64),
    r => r.source_hashes['FVTest/Backend/StockConfig.lean'] = 'd'.repeat(64)]) {
    const next = report([DIFFERENT]); change(next);
    assert.equal(n.difference(n.snapshot(report([EXACT]), run()), n.snapshot(next, run(11))).comparable, false);
  }
  const next = report(); next.source_hashes['FVTest/Backend/Main.lean'] = 'd'.repeat(64);
  assert.equal(n.difference(n.snapshot(report(), run()), n.snapshot(next, run(11))).comparable, true);
});
test('changed stock input or settings do not become false regressions', () => {
  for (const change of [r => r.tests[0].source_sha256 = 'd'.repeat(64),
    r => r.tests[0].variants[0].flags.opt_level = 'speed']) {
    const next = report([DIFFERENT]); change(next);
    const d = n.difference(n.snapshot(report([EXACT]), run()), n.snapshot(next, run(11)));
    assert.equal(d.changedInput.length, 1); assert.equal(d.lost.length, 0);
  }
});
test('nonrepeatable reference artifacts are excluded from regression attribution', () => {
  const old = report([EXACT]); old.tests[0].variants[0].reference_repeat_verified = false;
  const d = n.difference(n.snapshot(old, run()), n.snapshot(report([DIFFERENT]), run(11)));
  assert.equal(d.unstableReference.length, 1); assert.equal(d.lost.length, 0);
});
test('snapshots reject partial reports, invalid inventory/counts, missing provenance', () => {
  for (const change of [r => r.progress = 'running', r => r.tests.pop(),
    r => r.inventory[1].test = 'a.clif',
    r => r.totals.exact_code_artifacts++, r => delete r.source_hashes]) {
    const data = report(); change(data); assert.throws(() => n.snapshot(data, run()));
  }
  const data = n.snapshot(report(), run()); data.entries[0][2] = 'invented';
  assert.throws(() => n.validateSnapshot(data));
});
test('repeated function names retain separate reported occurrences', () => {
  const data = report([EXACT, DIFFERENT]);
  data.tests[0].variants[0].functions_compared[1].name = '%f0';
  const saved = n.snapshot(data, run());
  assert.equal(saved.entries.length, 2);
  assert.notEqual(saved.entries[0][0], saved.entries[1][0]);
  assert.deepEqual(saved.entries.map(e => JSON.parse(e[0])[5]), [0, 1]);
});
test('collect establishes an initial baseline, compares subsequent main runs, excludes unfinished runs', async () => {
  const f = fixture({ runs: [run(10), run(11, { created_at: '2026-10-05T03:00:00Z', updated_at: '2026-10-05T04:00:00Z' }),
    run(12, { status: 'in_progress' })] });
  const result = await n.collect({ ...f, now: new Date(plan().through),
    loadReport: async r => r.id === 10 ? report([EXACT, DIFFERENT]) : report([DIFFERENT, EXACT]) });
  assert.equal(result.plan.rows.length, 2);
  assert.equal(result.plan.rows[0].initial, true);
  assert.equal(result.plan.rows[1].delta.lost.length, 1);
  assert.deepEqual(result.plan.rows[1].range.authors, ['@contributor']);
  assert.equal(result.saved.baseline.run.id, 11);
});
test('previous baseline, late completions, failed runs and reruns are handled without resetting to failures', async () => {
  const previous = { through: '2026-10-05T00:00:00.000Z', snapshot_run_id: 800, snapshot_attempt: 1, archived_through: 0 };
  const baseline = n.snapshot(report([EXACT]), run(9));
  const f = fixture({ body: `${n.STATE}${JSON.stringify(previous)} -->`, runs: [
    run(10, { created_at: '2026-10-04T20:00:00Z' }), run(11, { conclusion: 'failure' })] });
  const result = await n.collect({ ...f, now: new Date(plan().through),
    loadState: async () => ({ schema: 1, through: previous.through, baseline }), loadReport: async () => report([DIFFERENT]) });
  assert.equal(result.plan.rows[0].delta.lost.length, 1);
  assert.ok(result.plan.rows[1].problem.includes('failure'));
  assert.equal(result.saved.baseline.run.id, 10);
  assert.equal(result.plan.since, previous.through);
});
test('out-of-order historical reruns never replace the forward baseline', async () => {
  const previous = { through: '2026-10-05T00:00:00.000Z', snapshot_run_id: 800, snapshot_attempt: 1 };
  const baseline = n.snapshot(report([EXACT]), run(20));
  const f = fixture({ body: `${n.STATE}${JSON.stringify(previous)} -->`, runs: [run(10)], historyStatus: 'behind' });
  const result = await n.collect({ ...f, now: new Date(plan().through),
    loadState: async () => ({ schema: 1, through: previous.through, baseline }), loadReport: async () => report([DIFFERENT]) });
  assert.equal(result.saved.baseline.run.id, 20); assert.ok(result.plan.rows[0].problem.includes('not a forward'));
});
test('quiet nights carry the snapshot forward; invalid snapshots do not advance state', async () => {
  const previous = { through: '2026-10-05T00:00:00.000Z', snapshot_run_id: 800, snapshot_attempt: 1 };
  const baseline = n.snapshot(report(), run());
  const f = fixture({ body: `${n.STATE}${JSON.stringify(previous)} -->` });
  const options = { ...f, now: new Date(plan().through), loadState: async () => ({ schema: 1, through: previous.through, baseline }) };
  const result = await n.collect(options);
  assert.deepEqual(result.saved.baseline, baseline); assert.equal(result.plan.rows.length, 0);
  await assert.rejects(n.collect({ ...options, loadState: async () => ({ schema: 1, through: 'wrong', baseline }) }));
});
test('render is one table with the change since the previous report in each row', () => {
  const before = report([EXACT, DIFFERENT, UNSUPPORTED, UNSUPPORTED]).totals;
  const after = report([EXACT, EXACT, DIFFERENT, UNSUPPORTED]).totals;
  const { body, compact } = n.render(plan({ initial: { exact: 1, outputs: 4, sha: run().head_sha, totals: before },
    latest: { exact: 2, outputs: 4, sha: run(11).head_sha, totals: after }, compare: 'https://example.com/compare' }));
  assert.ok(body.includes('| Check | Result | Change |'));
  assert.ok(body.includes('| Exact function outputs | 2 / 4 (50.0%) | +1 |'));
  assert.ok(body.includes('| Different function outputs | 1 | 0 |'));
  assert.ok(body.includes('| Rejected for an unsupported operation | 1 | \u22121 |'));
  assert.ok(body.includes('https://example.com/compare'));
  assert.equal(body.match(/^\| Check/gm).length, 1);
  assert.ok(compact.includes('2/4 exact (+1)'));
});
test('render marks a changed total and a first measurement', () => {
  const before = report([EXACT, DIFFERENT]).totals;
  const after = report([EXACT, DIFFERENT, DIFFERENT]).totals;
  let { body } = n.render(plan({ initial: { exact: 1, outputs: 2, sha: run().head_sha, totals: before },
    latest: { exact: 1, outputs: 3, sha: run(11).head_sha, totals: after } }));
  assert.ok(body.includes('| Exact function outputs | 1 / 3 (33.3%) | 0 (of +1) |'));
  ({ body } = n.render(plan()));
  assert.ok(body.includes('No earlier measurement'));
  assert.ok(body.includes('| Exact function outputs | 1 / 3 (33.3%) | \u2014 |'));
});
test('render names lost matches with their commit range and author, and unmeasured commits', () => {
  const row = { run: run(11), url: 'https://example.com/run', exact: 0, outputs: 1,
    range: { authors: ['@contributor'], commits: [{ sha: run(11).head_sha, title: 'Change lowering' }], url: 'https://example.com/range' },
    delta: n.difference(n.snapshot(report([EXACT]), run()), n.snapshot(report([UNSUPPORTED]), run(11))) };
  const failed = { run: run(12), url: 'https://example.com/failed', problem: 'measurement failure' };
  const { body, compact } = n.render(plan({ rows: [row, failed] }));
  for (const value of ['**Lost exact matches** (1)', 'a.clif %f0', 'https://example.com/range', 'Not compared:', 'measurement failure']) {
    assert.ok(body.includes(value), value);
  }
  assert.ok(compact.includes('Lost at'));
  assert.ok(compact.includes('@contributor'));
  assert.ok(compact.includes('a.clif %f0'));
});
test('compaction archives before deletion and preserves humans and unrelated bots', async () => {
  const f = fixture({ comments: [oldComment(10), oldComment(11),
    { ...oldComment(12), user: { login: 'human', type: 'User' } },
    { id: 13, user: bot, body: 'Unrelated bot comment' }] });
  await n.publish({ ...f, plan: plan(), keep: 1 });
  assert.deepEqual(f.calls.map(c => c[0]), ['create', 'update', 'delete', 'delete']);
  assert.deepEqual(f.calls.filter(c => c[0] === 'delete').map(c => c[1].comment_id), [10, 11]);
  assert.ok(f.issue.body.includes('Human introduction.'));
  assert.ok(f.issue.body.includes('2026-10-05: 1/3 exact at'));
  assert.equal(n.marker(f.issue.body, n.STATE).archived_through, 11);
});
test('regressions and attribution survive comment compaction', async () => {
  const before = n.snapshot(report([EXACT]), run());
  const after = n.snapshot(report([DIFFERENT]), run(11));
  const old = oldComment(10, { rows: [{ run: run(11), url: 'https://example.com/run',
    range: { url: 'https://example.com/commits', authors: ['@contributor'], commits: [] }, delta: n.difference(before, after) }] });
  const f = fixture({ comments: [old] });
  await n.publish({ ...f, plan: plan(), keep: 1 });
  assert.ok(f.issue.body.includes('a.clif %f0')); assert.ok(f.issue.body.includes('@contributor'));
});
test('publication failure cannot erase comments or advance an unconfirmed archive', async () => {
  for (const failure of ['failCreate', 'failUpdate']) {
    const f = fixture({ comments: [oldComment(10)], [failure]: true });
    await assert.rejects(n.publish({ ...f, plan: plan(), keep: 1 }));
    assert.equal(f.calls.some(c => c[0] === 'delete'), false);
  }
});
test('stale cursor and mismatched uploaded snapshot cannot publish', async () => {
  for (const options of [{ body: `${n.STATE}${JSON.stringify({ through: 'later' })} -->` },
    { saved: { schema: 1, through: 'wrong', baseline: null } }]) {
    const f = fixture(options); await assert.rejects(n.publish({ ...f, plan: plan() }));
    assert.deepEqual(f.calls, []);
  }
});
test('only main scheduled/manual workflows can publish', async () => {
  for (const runChanges of [{ head_branch: 'feature' }, { event: 'pull_request' }, { path: n.WORKFLOW }]) {
    const f = fixture({ runChanges }); await assert.rejects(n.publish({ ...f, plan: plan() }));
    assert.deepEqual(f.calls, []);
  }
});
test('concurrent human edits are preserved and prevent compaction writes', async () => {
  const f = fixture({ humanEdit: true, comments: [oldComment(10)] });
  await assert.rejects(n.publish({ ...f, plan: plan(), keep: 1 }), /preserve human edits/);
  assert.ok(f.issue.body.includes('New human note.'));
  assert.deepEqual(f.calls.map(c => c[0]), ['create']);
});
test('unconfirmed issue updates never permit comment deletion', async () => {
  const f = fixture({ failConfirmation: true, comments: [oldComment(10)] });
  await assert.rejects(n.publish({ ...f, plan: plan(), keep: 1 }), /not confirmed/);
  assert.deepEqual(f.calls.map(c => c[0]), ['create', 'update']);
});
test('already archived comments are deleted without duplicating compacted history', async () => {
  const previous = { through: '2026-10-04T08:00:00.000Z', snapshot_run_id: 800, snapshot_attempt: 1, archived_through: 10 };
  const body = `${n.START}\n<!-- clifv-nightly-archive:start -->\n- Retained finding.\n<!-- clifv-nightly-archive:end -->\n${n.STATE}${JSON.stringify(previous)} -->\n${n.END}`;
  const f = fixture({ body, comments: [oldComment(10)] });
  await n.publish({ ...f, plan: plan({ previous }), keep: 1 });
  assert.equal(f.issue.body.includes('Retained finding.'), true);
  assert.equal(f.issue.body.includes('2026-10-05: 1/3 exact at'), false);
  assert.equal(f.calls.filter(c => c[0] === 'delete').length, 1);
});
test('full archive preserves comments instead of losing evidence', async () => {
  const previous = { through: '2026-10-04T08:00:00.000Z', snapshot_run_id: 800, snapshot_attempt: 1, archived_through: 0 };
  const body = `${n.START}\n<!-- clifv-nightly-archive:start -->\n${'x'.repeat(58000)}\n<!-- clifv-nightly-archive:end -->\n${n.STATE}${JSON.stringify(previous)} -->\n${n.END}`;
  const f = fixture({ body, comments: [oldComment(10, { rows: [{ run: run(11), url: 'https://example.com/run', problem: 'y'.repeat(500) }] }),
    oldComment(11, { rows: [{ run: run(11), url: 'https://example.com/run', problem: 'y'.repeat(500) }] }),
    oldComment(12, { rows: [{ run: run(11), url: 'https://example.com/run', problem: 'y'.repeat(500) }] })] });
  await n.publish({ ...f, plan: plan({ previous }), keep: 1 });
  assert.ok(f.calls.some(c => c[0] === 'warning'));
  assert.equal(f.calls.some(c => c[0] === 'delete'), false);
});
