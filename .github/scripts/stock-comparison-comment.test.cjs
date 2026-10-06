const assert = require('node:assert/strict');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const { test } = require('node:test');
const { execFileSync } = require('node:child_process');
const { validate, render, prepare, post, readSummary } = require('./stock-comparison-comment.cjs');

const sha = 'a'.repeat(40);
const run = { id: 123, run_attempt: 2, head_sha: sha, head_repository: { id: 10 },
  event: 'pull_request', path: '.github/workflows/stock-compiler-comparison.yml', status: 'completed', conclusion: 'success' };
const repo = { owner: 'eth-act', repo: 'clifv' };
const entry = (position, name = '%f', test = 'isa/aarch64/a.clif') => [test, 0, 'compile', position, name];
function data() {
  return { schema: 2, measurement_complete: true, head_sha: sha, run_id: 123, run_attempt: 2,
    target: 'aarch64-unknown-linux-gnu', elapsed_seconds: 42, cpu_seconds: 70,
    peak_runner_memory_used_bytes: 2 ** 30, pipeline_exit_code: 10, full_artifact_equivalence_verified: false,
    matched: Array.from({ length: 425 }, (_, i) => entry(i)),
    harness_sha256: { 'scripts/stock-compiler-compare.py': 'c'.repeat(64) },
    baseline_comparison: { available: true, run_id: 37262606411, run_attempt: 1, head_sha: 'b'.repeat(40),
      baseline_exact_code_artifacts: 424, gained_count: 2, lost_count: 1,
      gained: [entry(1), entry(2)], lost: [entry(500, '%g')], harness_changed: [] },
    totals: { official_test_files: 1302, inventoried_test_files: 1302,
      files_with_compared_function_outputs: 116, files_all_aarch64_code_artifacts_identical: 19,
      test_function_compilations: 4501, exact_code_artifacts: 425, failed_stock_compile_assertions: 0,
      source_files_modified: 0, nonrepeatable_reference_stages: 1,
      file_statuses: { binary_test: 484, no_lean_target: 630, non_binary_test: 180, stock_parser_warning_skip: 8 },
      function_statuses: { identical_code_artifact: 425, different_code_artifact: 983,
        unsupported_configuration: 1176, lean_unsupported: 1871, expected_stock_rejection_no_binary: 46 } } };
}
const bot = { login: 'github-actions[bot]', type: 'Bot' };
function fixture({ comments = [], failCreate = false, head = sha, jobSucceeded = true, fork = false, largeArtifact = false } = {}) {
  const mutations = [];
  const pr = { number: 3, state: 'open', head: { sha: head, repo: { id: 10 } }, base: { repo: { full_name: 'eth-act/clifv' } } };
  const github = { rest: {
    actions: { getWorkflowRun: async () => ({ data: run }), listJobsForWorkflowRun: 'jobs', listWorkflowRunArtifacts: 'artifacts' },
    pulls: { get: async () => ({ data: pr }), list: 'pulls' },
    issues: { listComments: 'comments',
      createComment: async args => { mutations.push(['create', args]); if (failCreate) throw new Error('API failure'); return { data: { id: 99, html_url: 'new-comment' } }; },
      deleteComment: async args => mutations.push(['delete', args]) },
  }, paginate: async method => {
    if (method === 'jobs') return [{ name: 'Build and compare', conclusion: jobSucceeded ? 'success' : 'failure' }];
    if (method === 'artifacts') return [{ name: 'stock-comparison-summary-2', id: 50, expired: false, size_in_bytes: largeArtifact ? 2 ** 22 : 512 }];
    if (method === 'pulls') return [pr];
    if (method === 'comments') return comments;
    throw new Error('Unexpected API call');
  } };
  return { github, context: { repo, runId: 123, payload: fork ? { workflow_run: run } : { pull_request: { number: 3 } } },
    core: { info() {} }, mutations };
}
process.env.GITHUB_RUN_ATTEMPT = '2';
async function publish(f, summary = data()) {
  const temp = fs.mkdtempSync(path.join(os.tmpdir(), 'stock-comment-test-'));
  const file = path.join(temp, 'summary.json');
  fs.writeFileSync(file, JSON.stringify(summary));
  try { return await post({ ...f, summaryPath: file }); }
  finally { fs.rmSync(temp, { recursive: true }); }
}

test('render distinguishes coverage, output agreement, and complete-file agreement', () => {
  const body = render(data(), repo, run);
  for (const expected of ['116 / 484 (24.0%)', '425 / 4,455 (9.5%)', '19 / 484 (3.9%)', 'Rejected for a setting | 1,176',
    'Rejected for an unsupported operation | 1,871', 'including the OS',
    'Rust toolchain setup is included', 'Lean installation and cache transfers are outside']) assert.ok(body.includes(expected), expected);
});
test('render compares with the main baseline and lists lost matches first', () => {
  const body = render(data(), repo, run);
  for (const expected of ['`main` at `bbbbbbbbbbbb`', 'actions/runs/37262606411/attempts/1', '**+2 / \u22121**',
    '(424 \u2192 425)', '**Lost matches** (1):\n- `isa/aarch64/a.clif` `%g` (compile, variant 0, function 500)',
    'New matches (2):']) assert.ok(body.includes(expected), expected);
  assert.ok(body.indexOf('Lost matches') < body.indexOf('New matches'));
  assert.ok(!body.includes('measuring code changed'));
});
test('render flags harness changes and bounds long lists', () => {
  const summary = data(); const b = summary.baseline_comparison;
  b.harness_changed = ['FVTest/Backend/StockConfig.lean'];
  b.gained_count = 300; b.gained = Array.from({ length: 200 }, (_, i) => entry(1000 + i));
  b.baseline_exact_code_artifacts = 126; summary.totals.exact_code_artifacts = 425;
  const body = render(summary, repo, run);
  assert.ok(body.includes('measuring code changed since then: `FVTest/Backend/StockConfig.lean`'));
  assert.ok(body.includes('... and 290 more'));
});
test('render explains a missing baseline without trusting its text', () => {
  const summary = data();
  summary.baseline_comparison = { available: false, failed: false, reason: 'no run @someone [x](http://e) `code`' };
  const body = render(summary, repo, run);
  assert.ok(body.includes('No `main` baseline to compare with: no run ?someone ?x?(http://e) ?code?.'));
});
test('render says when the baseline could not be retrieved', () => {
  const summary = data();
  summary.baseline_comparison = { available: false, failed: true, reason: 'baseline lookup failed: CalledProcessError' };
  const body = render(summary, repo, run);
  assert.ok(body.includes('could not be retrieved or read:** baseline lookup failed: CalledProcessError. The lost-match check fails'));
});
test('invalid, partial, or mismatched reports cannot publish', () => {
  for (const edit of [d => d.measurement_complete = false, d => d.head_sha = 'b'.repeat(40),
    d => d.run_attempt = 1, d => d.totals.exact_code_artifacts = -1,
    d => d.totals.function_statuses.lean_unsupported = '<script>',
    d => d.totals.file_statuses.harness_error = 1,
    d => d.totals.source_files_modified = 1, d => d.schema = 1, d => d.pipeline_exit_code = 1,
    d => d.matched.pop(), d => d.matched[0][4] = '%f @someone', d => d.matched[0][0] = '[x](http://e).clif',
    d => d.matched[0][2] = 'test', d => d.harness_sha256 = ['c'.repeat(64)],
    d => d.baseline_comparison.lost_count = 2, d => d.baseline_comparison.lost[0][4] = '`%g`',
    d => d.baseline_comparison.head_sha = 'main', d => d.baseline_comparison.harness_changed = ['../x\n'],
    d => d.baseline_comparison = { available: false, failed: false, reason: 'x'.repeat(301) },
    d => d.baseline_comparison = { available: false, reason: 'no failure flag' }, d => delete d.baseline_comparison]) {
    const summary = data(); edit(summary); assert.throws(() => validate(summary, run));
  }
});
test('successful rerun creates replacement then deletes only marked bot comments', async () => {
  const f = fixture({ comments: [
    { id: 1, user: bot, body: '<!-- clifv-stock-comparison:v1 run=123 attempt=1 --> old result' },
    { id: 2, user: { login: 'author', type: 'User' }, body: '<!-- clifv-stock-comparison:v1 user text' },
    { id: 3, user: bot, body: 'Unrelated bot comment' }] });
  await publish(f);
  assert.deepEqual(f.mutations.map(m => m[0]), ['create', 'delete']);
  assert.equal(f.mutations[1][1].comment_id, 1);
});
test('comment creation failure keeps previous result', async () => {
  const f = fixture({ failCreate: true, comments: [{ id: 1, user: bot, body: '<!-- clifv-stock-comparison:v1 run=123 attempt=1 -->' }] });
  await assert.rejects(publish(f), /API failure/);
  assert.deepEqual(f.mutations.map(m => m[0]), ['create']);
});
test('failed measurement keeps previous comment', async () => {
  const f = fixture({ jobSucceeded: false });
  await assert.rejects(publish(f), /did not succeed/); assert.deepEqual(f.mutations, []);
});
test('stale commit cannot replace a current result', async () => {
  const f = fixture({ head: 'b'.repeat(40) });
  assert.equal(await publish(f), null); assert.deepEqual(f.mutations, []);
});
test('rerunning the publisher is idempotent', async () => {
  const f = fixture({ comments: [{ id: 1, user: bot, body: '<!-- clifv-stock-comparison:v1 run=123 attempt=2 -->' }] });
  assert.equal((await publish(f)).id, 1); assert.deepEqual(f.mutations, []);
});
test('older runs cannot replace newer results', async () => {
  const f = fixture({ comments: [{ id: 1, user: bot, body: '<!-- clifv-stock-comparison:v1 run=124 attempt=1 -->' }] });
  await publish(f); assert.deepEqual(f.mutations, []);
});
test('fork publisher finds the PR from trusted API data', async () => {
  const f = fixture({ fork: true }); const ready = await prepare(f);
  assert.equal(ready.number, 3); assert.equal(ready.artifactId, 50);
  await publish(f); assert.equal(f.mutations[0][0], 'create');
});
test('oversized artifact is rejected before downloading or posting', async () => {
  const f = fixture({ largeArtifact: true });
  await assert.rejects(prepare(f), /oversized/); assert.deepEqual(f.mutations, []);
});
test('tampered summary cannot remove old comments', async () => {
  const f = fixture(); const summary = data(); summary.run_id = 999;
  await assert.rejects(publish(f, summary), /does not belong/); assert.deepEqual(f.mutations, []);
});
test('archive reader reads JSON without extracting any files', () => {
  const temp = fs.mkdtempSync(path.join(os.tmpdir(), 'stock-zip-test-'));
  try {
    const archive = path.join(temp, 'summary.zip');
    execFileSync('python3', ['-c', 'import sys,zipfile\nwith zipfile.ZipFile(sys.argv[1],"w") as z: z.writestr("ci-comparison.ci-summary.json",sys.argv[2])', archive, JSON.stringify(data())]);
    assert.deepEqual(readSummary(temp), data());
    assert.deepEqual(fs.readdirSync(temp), ['summary.zip']);
  } finally { fs.rmSync(temp, { recursive: true }); }
});
test('archive path traversal payload is rejected without extraction', () => {
  const temp = fs.mkdtempSync(path.join(os.tmpdir(), 'stock-zip-test-'));
  try {
    const archive = path.join(temp, 'summary.zip');
    execFileSync('python3', ['-c', 'import sys,zipfile\nwith zipfile.ZipFile(sys.argv[1],"w") as z: z.writestr("../execute.cjs","malicious code")', archive]);
    assert.throws(() => readSummary(temp), /unexpected archive contents/);
    assert.deepEqual(fs.readdirSync(temp), ['summary.zip']);
  } finally { fs.rmSync(temp, { recursive: true }); }
});
