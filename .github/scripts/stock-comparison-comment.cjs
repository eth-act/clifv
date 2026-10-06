// Publisher input is data only. Never execute scripts from a fork artifact.
const fs = require('node:fs');
const path = require('node:path');
const { execFileSync } = require('node:child_process');
const MARKER = '<!-- clifv-stock-comparison:v1';
const WORKFLOW = '.github/workflows/stock-compiler-comparison.yml';

function count(value, label) {
  if (!Number.isSafeInteger(value) || value < 0 || value > 1e9) throw new Error(`Invalid ${label}`);
  return value;
}

// Entries name stock tests and functions; anything else (markdown, mentions) is rejected.
const TEST = /^[A-Za-z0-9_][A-Za-z0-9_.\/-]{0,200}\.clif$/;
const FUNCTION = /^%?[A-Za-z0-9_.$:-]{1,200}$/;
const PATH = /^[A-Za-z0-9_.][A-Za-z0-9_.\/-]{0,200}$/;
const SHA = /^[0-9a-f]{40}$/;
const LISTED = 200;

function entries(value, label, max) {
  if (!Array.isArray(value) || value.length > max) throw new Error(`Invalid ${label}`);
  for (const e of value) {
    if (!Array.isArray(e) || e.length !== 5 || typeof e[0] !== 'string' || !TEST.test(e[0]) ||
        !['compile', 'run'].includes(e[2]) || typeof e[4] !== 'string' || !FUNCTION.test(e[4])) {
      throw new Error(`Invalid ${label} entry`);
    }
    count(e[1], `${label} variant`); count(e[3], `${label} position`);
  }
  return value;
}

function paths(value, label) {
  if (!Array.isArray(value) || value.length > 200 || value.some(p => typeof p !== 'string' || !PATH.test(p))) {
    throw new Error(`Invalid ${label}`);
  }
  return value;
}

function validateBaseline(b, matched) {
  if (b === null || typeof b !== 'object' || typeof b.available !== 'boolean') throw new Error('Invalid baseline comparison');
  if (!b.available) {
    if (typeof b.failed !== 'boolean') throw new Error('Invalid baseline failure flag');
    if (typeof b.reason !== 'string' || b.reason.length > 300) throw new Error('Invalid baseline reason');
    return;
  }
  if (!Number.isSafeInteger(b.run_id) || b.run_id <= 0) throw new Error('Invalid baseline run');
  for (const key of ['run_attempt', 'baseline_exact_code_artifacts', 'gained_count', 'lost_count']) count(b[key], key);
  if (typeof b.head_sha !== 'string' || !SHA.test(b.head_sha)) throw new Error('Invalid baseline commit');
  entries(b.gained, 'gained', LISTED); entries(b.lost, 'lost', LISTED);
  paths(b.harness_changed, 'harness_changed');
  if (b.gained.length !== Math.min(b.gained_count, LISTED) || b.lost.length !== Math.min(b.lost_count, LISTED) ||
      b.baseline_exact_code_artifacts - b.lost_count + b.gained_count !== matched) {
    throw new Error('Inconsistent baseline comparison');
  }
}

// The measurement: complete, consistent totals for this run and commit. The nightly digest
// checks full reports with it; `validate` adds the CI summary's own fields.
function validateMeasurement(data, run) {
  if (data.measurement_complete !== true || data.target !== 'aarch64-unknown-linux-gnu') {
    throw new Error('Invalid or incomplete measurement');
  }
  if (data.run_id !== run.id || data.run_attempt !== run.run_attempt || data.head_sha !== run.head_sha) {
    throw new Error('Report does not belong to this run and commit');
  }
  const t = data.totals;
  for (const key of ['official_test_files', 'inventoried_test_files', 'files_with_compared_function_outputs',
    'files_all_aarch64_code_artifacts_identical', 'test_function_compilations', 'exact_code_artifacts',
    'failed_stock_compile_assertions', 'source_files_modified', 'nonrepeatable_reference_stages']) count(t[key], key);
  const f = t.function_statuses;
  const statuses = ['identical_code_artifact', 'different_code_artifact', 'unsupported_configuration',
    'lean_unsupported', 'expected_stock_rejection_no_binary'];
  if (Object.keys(f).some(key => !statuses.includes(key))) throw new Error('Unexpected function status');
  for (const key of statuses) count(f[key] ?? 0, key);
  const files = t.file_statuses;
  const fileStatuses = ['binary_test', 'non_binary_test', 'no_lean_target', 'stock_parser_warning_skip'];
  if (Object.keys(files).some(key => !fileStatuses.includes(key))) throw new Error('Unexpected file status');
  for (const key of fileStatuses) count(files[key] ?? 0, key);
  const scope = files.binary_test ?? 0;
  if (!t.official_test_files || t.inventoried_test_files !== t.official_test_files ||
      Object.values(files).reduce((a, b) => a + b, 0) !== t.official_test_files ||
      statuses.reduce((sum, key) => sum + (f[key] ?? 0), 0) !== t.test_function_compilations ||
      t.exact_code_artifacts !== (f.identical_code_artifact ?? 0) ||
      t.files_with_compared_function_outputs > scope ||
      t.files_all_aarch64_code_artifacts_identical > t.files_with_compared_function_outputs ||
      t.failed_stock_compile_assertions || t.source_files_modified) throw new Error('Inconsistent report totals');
  for (const key of ['elapsed_seconds', 'cpu_seconds', 'peak_runner_memory_used_bytes']) {
    if (!Number.isFinite(data[key]) || data[key] < 0 || data[key] > 2 ** 40) throw new Error(`Invalid ${key}`);
  }
  if (typeof data.full_artifact_equivalence_verified !== 'boolean') throw new Error('Invalid completion state');
  return data;
}

function validate(data, run) {
  if (data.schema !== 2) throw new Error('Invalid or incomplete measurement');
  const t = validateMeasurement(data, run).totals;
  if (data.pipeline_exit_code !== 10) throw new Error('Invalid completion state');
  if (entries(data.matched, 'matched', 1e5).length !== t.exact_code_artifacts) throw new Error('Inconsistent matched outputs');
  const harness = data.harness_sha256;
  if (harness === null || typeof harness !== 'object' || Array.isArray(harness)) throw new Error('Invalid harness hashes');
  paths(Object.keys(harness), 'harness files');
  if (Object.values(harness).some(h => typeof h !== 'string' || !/^[0-9a-f]{64}$/.test(h))) throw new Error('Invalid harness hashes');
  validateBaseline(data.baseline_comparison, t.exact_code_artifacts);
  return data;
}

function entry(e) {
  return `\`${e[0]}\` \`${e[4]}\` (${e[2]}, variant ${e[1]}, function ${e[3]})`;
}

function listed(items, total, shown) {
  const lines = items.slice(0, shown).map(e => `- ${entry(e)}`);
  if (total > lines.length) lines.push(`- ... and ${(total - lines.length).toLocaleString('en-US')} more (summary artifact)`);
  return lines.join('\n');
}

function baselineSection(b, repo) {
  if (!b.available) {
    // The reason is plain text from the CI scripts; keep it inert.
    const reason = b.reason.replace(/[^A-Za-z0-9 .,:;()/_=+-]/g, '?');
    if (b.failed) {
      return `**The \`main\` baseline could not be retrieved or read:** ${reason}. ` +
        'The lost-match check fails until a re-run retrieves it.\n';
    }
    return `No \`main\` baseline to compare with: ${reason}.\n`;
  }
  const url = `https://github.com/${repo.owner}/${repo.repo}/actions/runs/${b.run_id}/attempts/${b.run_attempt}`;
  const now = b.baseline_exact_code_artifacts - b.lost_count + b.gained_count;
  let text = `Compared with \`main\` at \`${b.head_sha.slice(0, 12)}\` ([run](${url})): ` +
    `**+${b.gained_count.toLocaleString('en-US')} / \u2212${b.lost_count.toLocaleString('en-US')}** exact outputs ` +
    `(${b.baseline_exact_code_artifacts.toLocaleString('en-US')} \u2192 ${now.toLocaleString('en-US')}).\n`;
  if (b.harness_changed.length) {
    text += `\nThe measuring code changed since then: ${b.harness_changed.map(p => `\`${p}\``).join(', ')}. ` +
      'Changed numbers may come from the measurement, not the compiler.\n';
  }
  if (b.lost_count) text += `\n**Lost matches** (${b.lost_count.toLocaleString('en-US')}):\n${listed(b.lost, b.lost_count, 30)}\n`;
  if (b.gained_count) text += `\nNew matches (${b.gained_count.toLocaleString('en-US')}):\n${listed(b.gained, b.gained_count, 10)}\n`;
  return text;
}

function fraction(numerator, denominator) {
  return `${numerator.toLocaleString('en-US')} / ${denominator.toLocaleString('en-US')}` +
    (denominator ? ` (${(100 * numerator / denominator).toFixed(1)}%)` : '');
}

// The rows of the results table. The nightly digest shows the same rows with a change column.
function totalsRows(t) {
  const f = t.function_statuses;
  const scope = t.file_statuses.binary_test ?? 0;
  const stockOutputs = t.test_function_compilations - (f.expected_stock_rejection_no_binary ?? 0);
  return [
    ['Official CLIF test inventory', t.inventoried_test_files, t.official_test_files, ' files'],
    ['AArch64 files with outputs compared', t.files_with_compared_function_outputs, scope],
    ['Exact function outputs', t.exact_code_artifacts, stockOutputs],
    ['Files with every AArch64 output matching', t.files_all_aarch64_code_artifacts_identical, scope],
    ['Different function outputs', f.different_code_artifact ?? 0],
    ['Rejected for a setting', f.unsupported_configuration ?? 0],
    ['Rejected for an unsupported operation', f.lean_unsupported ?? 0],
  ].map(([label, value, total, unit = '']) => ({ label, value, total,
    text: (total === undefined ? value.toLocaleString('en-US') : fraction(value, total)) + unit }));
}

function render(data, repo, run) {
  validate(data, run);
  const url = `https://github.com/${repo.owner}/${repo.repo}/actions/runs/${run.id}/attempts/${run.run_attempt}`;
  return `${MARKER} run=${run.id} attempt=${run.run_attempt} -->
### Stock Cranelift / Lean comparison

Commit: \`${run.head_sha.slice(0, 12)}\`. [Run and artifacts](${url}).

| Check | Result |
| --- | --- |
${totalsRows(data.totals).map(row => `| ${row.label} | ${row.text} |`).join('\n')}
| Complete compiler metadata agreement | ${data.full_artifact_equivalence_verified ? 'Established' : 'Not established'} |
| Compiled test functions executed | No |

Exact matches require identical bytes, relocations, alignment, and trap records.
Rejected outputs do not pass. Expected stock failures without code are excluded from the output total.

${baselineSection(data.baseline_comparison, repo)}
Pipeline time: **${data.elapsed_seconds.toFixed(1)} seconds** (build, validation, artifact generation, and comparison).
Peak runner memory used: **${(data.peak_runner_memory_used_bytes / 2 ** 30).toFixed(2)} GiB**, sampled every 0.1 seconds, including the OS.
This job uses two comparison workers. Rust toolchain setup is included in the pipeline time.
Lean installation and cache transfers are outside the pipeline time.

A successful measurement job means the measurement completed, not that both compilers fully agree.
The "Check lost matches" job fails when an output that matched on that \`main\` commit no longer matches.
The label \`stock-comparison-accept-losses\` accepts intended losses on a pull request.
`;
}

async function prepare({ github, context }) {
  const { owner, repo } = context.repo;
  const event = context.payload.workflow_run;
  const id = event ? event.id : context.runId;
  const run = (await github.rest.actions.getWorkflowRun({ owner, repo, run_id: id })).data;
  const expectedAttempt = event ? event.run_attempt : Number(process.env.GITHUB_RUN_ATTEMPT);
  if (run.run_attempt !== expectedAttempt) return null;
  if (run.event !== 'pull_request' || run.path.split('@')[0] !== WORKFLOW || !/^[0-9a-f]{40}$/.test(run.head_sha)) {
    throw new Error('Unexpected source workflow');
  }
  // A run whose lost-match job failed still has a valid measurement (checked below).
  if (event && (run.status !== 'completed' || !['success', 'failure'].includes(run.conclusion))) return null;
  const jobs = await github.paginate(github.rest.actions.listJobsForWorkflowRun,
    { owner, repo, run_id: id, filter: 'latest', per_page: 100 });
  if (!jobs.some(job => job.name === 'Build and compare' && job.conclusion === 'success')) {
    throw new Error('The measurement job did not succeed');
  }
  let number = context.payload.pull_request?.number;
  if (!number) {
    const pulls = await github.paginate(github.rest.pulls.list, { owner, repo, state: 'open', per_page: 100 });
    const matches = pulls.filter(pr => pr.head.sha === run.head_sha && pr.head.repo?.id === run.head_repository.id);
    if (matches.length !== 1) return null;
    number = matches[0].number;
  }
  const pr = (await github.rest.pulls.get({ owner, repo, pull_number: number })).data;
  if (pr.state !== 'open' || pr.head.sha !== run.head_sha || pr.head.repo?.id !== run.head_repository.id ||
      pr.base.repo.full_name !== `${owner}/${repo}`) return null;
  const artifacts = await github.paginate(github.rest.actions.listWorkflowRunArtifacts,
    { owner, repo, run_id: id, per_page: 100 });
  const matches = artifacts.filter(a => a.name === `stock-comparison-summary-${run.run_attempt}` && !a.expired);
  if (matches.length !== 1 || matches[0].size_in_bytes > 1024 * 1024) throw new Error('Missing or oversized summary artifact');
  return { run, number, artifactId: matches[0].id };
}

function readSummary(summaryPath) {
  if (fs.statSync(summaryPath).isDirectory()) {
    const entries = fs.readdirSync(summaryPath);
    if (entries.length !== 1 || !entries[0].endsWith('.zip')) throw new Error('Expected one summary archive');
    const archive = path.join(summaryPath, entries[0]);
    if (fs.statSync(archive).size > 1024 * 1024) throw new Error('Oversized archive');
    // Read one bounded JSON member without extracting paths or executing code.
    const source = `import sys,zipfile
with zipfile.ZipFile(sys.argv[1]) as archive:
    entries=archive.infolist()
    assert len(entries)==1 and entries[0].filename=='ci-comparison.ci-summary.json', 'unexpected archive contents'
    assert entries[0].file_size<=1024*1024, 'oversized summary'
    sys.stdout.buffer.write(archive.read(entries[0]))
`;
    return JSON.parse(execFileSync('python3', ['-c', source, archive], { encoding: 'utf8', maxBuffer: 1024 * 1024 }));
  }
  if (fs.statSync(summaryPath).size > 1024 * 1024) throw new Error('Oversized report');
  return JSON.parse(fs.readFileSync(summaryPath, 'utf8'));
}

async function post({ github, context, core, summaryPath = 'report' }) {
  const ready = await prepare({ github, context });
  if (!ready) { core.info('No current successful PR measurement to publish'); return null; }
  const data = validate(readSummary(summaryPath), ready.run);
  const { owner, repo } = context.repo;
  const comments = await github.paginate(github.rest.issues.listComments,
    { owner, repo, issue_number: ready.number, per_page: 100 });
  const previous = comments.filter(c => c.user?.login === 'github-actions[bot]' && c.user?.type === 'Bot' &&
    c.body?.startsWith(MARKER));
  for (const comment of previous) {
    const match = comment.body.match(/^<!-- clifv-stock-comparison:v1 run=(\d+) attempt=(\d+) -->/);
    if (match && (Number(match[1]) > ready.run.id ||
        Number(match[1]) === ready.run.id && Number(match[2]) >= ready.run.run_attempt)) {
      core.info('This result or a newer result is already published'); return comment;
    }
  }
  // Create first: an API failure must not erase the last successful result.
  const current = await github.rest.issues.createComment({ owner, repo, issue_number: ready.number,
    body: render(data, context.repo, ready.run) });
  for (const comment of previous) await github.rest.issues.deleteComment({ owner, repo, comment_id: comment.id });
  core.info(`Published ${current.data.html_url}`);
  return current.data;
}

module.exports = { validate, validateMeasurement, totalsRows, render, prepare, post, readSummary };
if (require.main === module) {
  const data = JSON.parse(fs.readFileSync(process.argv[2], 'utf8'));
  const [owner, repo] = process.env.GITHUB_REPOSITORY.split('/');
  process.stdout.write(render(data, { owner, repo }, { id: data.run_id, run_attempt: data.run_attempt, head_sha: data.head_sha }));
}
