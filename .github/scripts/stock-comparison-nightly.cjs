// Trusted main reports are data, never executable input. No compiler rebuilds here.
const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');
const zlib = require('node:zlib');
const { execFileSync } = require('node:child_process');
const { validateMeasurement, totalsRows, fraction } = require('./stock-comparison-comment.cjs');

const WORKFLOW = '.github/workflows/stock-compiler-comparison.yml';
const NIGHTLY = '.github/workflows/stock-comparison-nightly.yml';
// Crate parity, the second parity metric: the full gate's `cargo fv` job measures these crates.
const GATE = '.github/workflows/full-gate.yml';
const CRATES = ['fv-demo', 'survey'];
const CRATE_RUNS = 20;
const START = '<!-- clifv-nightly-summary:start -->';
const END = '<!-- clifv-nightly-summary:end -->';
const STATE = '<!-- clifv-nightly-state:v1 ';
const COMMENT = '<!-- clifv-nightly-digest:v1 ';
const COMPACT = '<!-- clifv-nightly-compact:v1 ';
const DAY = 86400000;
const LIMIT = 60000;
const EXACT = 'identical_code_artifact';
const OUTPUT = new Set([EXACT, 'different_code_artifact']);
const UNSUPPORTED = new Set(['unsupported_configuration', 'lean_unsupported']);

function hash(value) { return crypto.createHash('sha256').update(JSON.stringify(value)).digest('hex'); }
function stable(value) {
  if (Array.isArray(value)) return value.map(stable);
  if (value && typeof value === 'object') return Object.fromEntries(Object.keys(value).sort().map(k => [k, stable(value[k])]));
  return value;
}
function text(value) { return String(value).replace(/[\r\n]/g, ' ').replace(/[`<>|\[\]*]/g, '').slice(0, 500); }
function runUrl(repo, run) {
  return `https://github.com/${repo.owner}/${repo.repo}/actions/runs/${run.id}/attempts/${run.run_attempt}`;
}
function marker(body, prefix) {
  const start = body.indexOf(prefix);
  if (start < 0) return null;
  const end = body.indexOf(' -->', start);
  if (end < 0) throw new Error('Broken nightly marker');
  return JSON.parse(body.slice(start + prefix.length, end));
}
function checkedRun(run, workflow = WORKFLOW) {
  if (run.path?.split('@')[0] !== workflow || run.head_branch !== 'main' ||
      !/^[0-9a-f]{40}$/.test(run.head_sha) || !Number.isSafeInteger(run.id) ||
      !Number.isSafeInteger(run.run_attempt)) throw new Error('Unexpected source run');
  if (workflow === WORKFLOW && run.event !== 'push') throw new Error('Not a main push measurement');
  if (workflow === GATE && !['push', 'schedule', 'workflow_dispatch'].includes(run.event)) {
    throw new Error('Not a trusted main full-gate run');
  }
  return run;
}

function snapshot(report, run) {
  checkedRun(run);
  if (report.progress !== 'finished' || report.schema !== 1 || report.execution_performed ||
      report.binary_normalization || report.actual_ci_execution || report.configuration_overrides?.length) {
    throw new Error('Incomplete or changed measurement');
  }
  validateMeasurement({ measurement_complete: true, target: report.target, totals: report.totals,
    head_sha: run.head_sha, run_id: run.id, run_attempt: run.run_attempt,
    elapsed_seconds: 0, cpu_seconds: 0, peak_runner_memory_used_bytes: 0,
    full_artifact_equivalence_verified: report.full_artifact_equivalence_verified }, run);
  if (report.tests.length !== report.official_test_files || report.inventory.length !== report.official_test_files ||
      new Set(report.tests.map(t => t.test)).size !== report.official_test_files ||
      JSON.stringify(report.tests.map(t => t.test).sort()) !== JSON.stringify(report.inventory.map(t => t.test).sort())) {
    throw new Error('Incomplete test inventory');
  }
  const sources = report.source_hashes;
  const harnessFiles = ['FVTest/Backend/StockConfig.lean', 'tools/prejit-export/src/main.rs',
    'tools/prejit-export/Cargo.lock', 'scripts/patches/prejit-export.patch', 'scripts/stock-compiler-compare.py'];
  if (!/^[0-9a-f]{40}$/.test(report.upstream_commit) ||
      harnessFiles.some(file => !/^[0-9a-f]{64}$/.test(sources?.[file]))) throw new Error('Missing measurement provenance');
  const contract = hash(stable({ upstream: report.upstream_commit, target: report.target,
    dependencies: report.dependency_provenance, harness: Object.fromEntries(harnessFiles.map(f => [f, sources[f]])) }));
  const entries = [];
  const counts = {};
  const occurrences = new Map();
  for (const test of report.tests) {
    for (const variant of test.variants) {
      if (!/^[0-9a-f]{64}$/.test(test.source_sha256) || !['compile', 'run', 'unwind'].includes(variant.stage) ||
          !Number.isSafeInteger(variant.isa_index) || !Number.isSafeInteger(variant.command_index) ||
          !variant.flags || !variant.isa_flags || !variant.target ||
          typeof variant.reference_repeat_verified !== 'boolean') throw new Error('Missing test settings');
      const settings = hash(stable({ source: test.source_sha256, target: variant.target,
        flags: variant.flags, isa_flags: variant.isa_flags }));
      for (const fn of variant.functions_compared) {
        if (typeof fn.name !== 'string' || !Object.hasOwn(report.totals.function_statuses, fn.status)) {
          throw new Error('Invalid function result');
        }
        // Stock compile tests may repeat a function name within one file/stage.
        // Preserve each reported occurrence instead of deduplicating its result.
        const identity = [test.test, variant.stage, variant.isa_index, variant.command_index, fn.name];
        const stem = JSON.stringify(identity);
        const occurrence = occurrences.get(stem) ?? 0;
        occurrences.set(stem, occurrence + 1);
        const key = JSON.stringify([...identity, occurrence]);
        entries.push([key, settings, fn.status, variant.reference_repeat_verified]);
        counts[fn.status] = (counts[fn.status] ?? 0) + 1;
      }
    }
  }
  if (new Set(entries.map(e => e[0])).size !== entries.length ||
      JSON.stringify(stable(counts)) !== JSON.stringify(stable(report.totals.function_statuses))) {
    throw new Error('Duplicate function identity or inconsistent counts');
  }
  return { schema: 1, run: { id: run.id, run_attempt: run.run_attempt, head_sha: run.head_sha,
    head_branch: run.head_branch, event: run.event, path: run.path }, contract,
    entries: entries.sort((a, b) => a[0].localeCompare(b[0])), totals: report.totals };
}

function validateSnapshot(data) {
  if (data.schema !== 1 || !/^[0-9a-f]{64}$/.test(data.contract) || !Array.isArray(data.entries) ||
      data.entries.length > 100000) throw new Error('Invalid saved baseline');
  checkedRun(data.run);
  const counts = {};
  const keys = new Set();
  for (const entry of data.entries) {
    if (entry.length !== 4 || typeof entry[0] !== 'string' || entry[0].length > 4096 ||
        !/^[0-9a-f]{64}$/.test(entry[1]) || typeof entry[3] !== 'boolean' || keys.has(entry[0])) throw new Error('Invalid saved function');
    const key = JSON.parse(entry[0]);
    if (!Array.isArray(key) || key.length !== 6 || typeof key[0] !== 'string' || typeof key[4] !== 'string' ||
        !Number.isSafeInteger(key[5]) || key[5] < 0) {
      throw new Error('Invalid saved identity');
    }
    keys.add(entry[0]); counts[entry[2]] = (counts[entry[2]] ?? 0) + 1;
  }
  validateMeasurement({ measurement_complete: true, target: 'aarch64-unknown-linux-gnu', totals: data.totals,
    head_sha: data.run.head_sha, run_id: data.run.id, run_attempt: data.run.run_attempt,
    elapsed_seconds: 0, cpu_seconds: 0, peak_runner_memory_used_bytes: 0,
    full_artifact_equivalence_verified: false }, data.run);
  if (JSON.stringify(stable(counts)) !== JSON.stringify(stable(data.totals.function_statuses))) {
    throw new Error('Saved baseline counts disagree');
  }
  return data;
}

function difference(before, after) {
  const result = { comparable: before.contract === after.contract, gained: [], lost: [],
    supportGained: [], supportLost: [], added: [], removed: [], changedInput: [], unstableReference: [] };
  if (!result.comparable) return result;
  const old = new Map(before.entries.map(([key, settings, status, repeatable]) => [key, { settings, status, repeatable }]));
  for (const [key, settings, status, repeatable] of after.entries) {
    const previous = old.get(key);
    old.delete(key);
    if (!previous) { result.added.push(key); continue; }
    if (previous.settings !== settings) { result.changedInput.push(key); continue; }
    if (!previous.repeatable || !repeatable) { result.unstableReference.push(key); continue; }
    if (previous.status === EXACT && status !== EXACT) result.lost.push(key);
    if (previous.status !== EXACT && status === EXACT) result.gained.push(key);
    if (OUTPUT.has(previous.status) && UNSUPPORTED.has(status)) result.supportLost.push(key);
    if (UNSUPPORTED.has(previous.status) && OUTPUT.has(status)) result.supportGained.push(key);
  }
  result.removed = [...old.keys()];
  return result;
}

// `cargo fv` localises a function as `__fv_<cgu>_<name>`; the CGU hash is not a stable identity.
// Neither is a v0 crate disambiguator (`Cs<base62>_` before the crate name's length), which a
// toolchain or `Cargo.lock` change renews for every function of the crate.
function crateName(fn) { return fn.replace(/^__fv_[0-9a-f]+_/, '').replace(/Cs[0-9A-Za-z]*_(?=[1-9])/g, 'C'); }

// One full-gate run's `scripts/stock-crate-parity.py --json` rows per crate, kept as counts per
// function name, so that the CGU split and the order of repeated names do not decide a match.
function crateSnapshot(examples, run) {
  checkedRun(run, GATE);
  const totals = {}, entries = [];
  for (const example of CRATES) {
    const rows = examples[example];
    if (!Array.isArray(rows) || rows.length > 200000) throw new Error(`Invalid crate parity rows: ${example}`);
    const counts = new Map();
    const t = { functions: 0, identical: 0, missing: 0, stock_bytes: 0, lean_bytes: 0 };
    for (const row of rows) {
      if (!row || typeof row !== 'object' || typeof row.fn !== 'string' || !row.fn || row.fn.length > 4096) {
        throw new Error(`Invalid crate parity row: ${example}`);
      }
      if (Object.hasOwn(row, 'error')) { t.missing++; continue; }
      if (typeof row.equal !== 'boolean' || !Number.isSafeInteger(row.stock) || !Number.isSafeInteger(row.lean) ||
          row.stock < 0 || row.lean < 0) throw new Error(`Invalid crate parity row: ${example}`);
      const key = JSON.stringify([example, crateName(row.fn)]);
      const c = counts.get(key) ?? [0, 0];
      c[0] += row.equal ? 1 : 0; c[1]++; counts.set(key, c);
      t.functions++; t.identical += row.equal ? 1 : 0; t.stock_bytes += row.stock; t.lean_bytes += row.lean;
    }
    if (!t.functions) throw new Error(`Empty crate parity measurement: ${example}`);
    totals[example] = t;
    for (const [key, [identical, functions]] of counts) entries.push([key, identical, functions]);
  }
  return { schema: 1, run: { id: run.id, run_attempt: run.run_attempt, head_sha: run.head_sha,
    head_branch: run.head_branch, event: run.event, path: run.path },
    totals, entries: entries.sort((a, b) => a[0].localeCompare(b[0])) };
}

function validateCrate(data) {
  if (data?.schema !== 1 || !Array.isArray(data.entries) || data.entries.length > 400000 || !data.totals) {
    throw new Error('Invalid saved crate baseline');
  }
  checkedRun(data.run, GATE);
  const sums = Object.fromEntries(CRATES.map(example => [example, [0, 0]]));
  const keys = new Set();
  for (const entry of data.entries) {
    if (!Array.isArray(entry) || entry.length !== 3 || typeof entry[0] !== 'string' || entry[0].length > 4200 ||
        keys.has(entry[0]) || !Number.isSafeInteger(entry[1]) || !Number.isSafeInteger(entry[2]) ||
        entry[1] < 0 || entry[2] < 1 || entry[1] > entry[2]) throw new Error('Invalid saved crate function');
    const key = JSON.parse(entry[0]);
    if (!Array.isArray(key) || key.length !== 2 || !Object.hasOwn(sums, key[0]) || typeof key[1] !== 'string') {
      throw new Error('Invalid saved crate identity');
    }
    keys.add(entry[0]); sums[key[0]][0] += entry[1]; sums[key[0]][1] += entry[2];
  }
  for (const example of CRATES) {
    const t = data.totals[example];
    if (t?.identical !== sums[example][0] || t?.functions !== sums[example][1]) throw new Error('Saved crate counts disagree');
  }
  return data;
}

// Lost: a name with fewer identical copies than before, including one Lean no longer compiles.
// When most names of a crate changed (a toolchain or dependency update renames them), the two
// measurements are not compared name by name, as a changed reference is not on the filetest side.
function crateDifference(before, after) {
  const result = { comparable: true, gained: 0, lost: [], added: 0, removed: 0 };
  for (const example of CRATES) {
    const names = new Set(before.entries.filter(e => JSON.parse(e[0])[0] === example).map(e => e[0]));
    const kept = after.entries.filter(e => JSON.parse(e[0])[0] === example && names.has(e[0])).length;
    const counted = after.entries.filter(e => JSON.parse(e[0])[0] === example).length;
    if (2 * kept < Math.max(names.size, counted)) result.comparable = false;
  }
  if (!result.comparable) return result;
  const old = new Map(before.entries.map(([key, identical, functions]) => [key, { identical, functions }]));
  for (const [key, identical, functions] of after.entries) {
    const previous = old.get(key);
    old.delete(key);
    if (!previous) { result.added += functions; result.gained += identical; continue; }
    if (identical < previous.identical) result.lost.push([key, previous.identical - identical]);
    if (identical > previous.identical) result.gained += identical - previous.identical;
    if (functions > previous.functions) result.added += functions - previous.functions;
    if (functions < previous.functions) result.removed += previous.functions - functions;
  }
  for (const [key, previous] of old) {
    result.removed += previous.functions;
    if (previous.identical) result.lost.push([key, previous.identical]);
  }
  result.lost.sort((a, b) => a[0].localeCompare(b[0]));
  return result;
}

function crateSummary(repo, snapshot) {
  if (!snapshot) return null;
  return { sha: snapshot.run.head_sha, run_id: snapshot.run.id, run_attempt: snapshot.run.run_attempt,
    url: runUrl(repo, snapshot.run), totals: snapshot.totals };
}

// The newest full-gate run on main with a crate measurement for every crate, against the
// previous report's crate baseline. A run without the artifacts (the job was skipped or the
// measurement step failed) is passed over; it never resets the baseline.
async function crateReport({ github, repo, now, baseline, loadCrate }) {
  const runs = await github.paginate(github.rest.actions.listWorkflowRuns, { ...repo,
    workflow_id: GATE.split('/').at(-1), branch: 'main', per_page: 100,
    created: `>=${new Date(now.getTime() - 14 * DAY).toISOString()}` });
  const completed = runs.filter(r => r.status === 'completed' && Date.parse(r.updated_at) <= now.getTime())
    .sort((a, b) => Date.parse(b.created_at) - Date.parse(a.created_at) || b.id - a.id).slice(0, CRATE_RUNS);
  const problems = [];
  const passedOver = [];
  let latest = null;
  for (const run of completed) {
    checkedRun(run, GATE);
    // A crate artifact never stops the filetest digest: any error is named and the next older run read.
    try {
      const examples = {};
      for (const example of CRATES) {
        examples[example] = loadCrate ? await loadCrate(run, example) :
          await artifact(github, repo, run, `crate-parity-${example}-${run.run_attempt}`, 'crate');
      }
      latest = crateSnapshot(examples, run);
      break;
    } catch (error) {
      if (String(error?.message).startsWith('Missing or expired artifact:')) {
        passedOver.push({ sha: run.head_sha, url: runUrl(repo, run) });
      } else problems.push({ sha: run.head_sha, url: runUrl(repo, run), problem: String(error?.message ?? error) });
    }
  }
  const plan = { previous: crateSummary(repo, baseline), latest: crateSummary(repo, baseline), fresh: false,
    delta: null, range: null, problems, passedOver: passedOver.length ?
      { count: passedOver.length, newest: passedOver[0] } : null };
  if (!latest || baseline && latest.run.id === baseline.run.id && latest.run.run_attempt === baseline.run.run_attempt) {
    return { plan, saved: baseline };
  }
  if (baseline) {
    const range = await attribution(github, repo, baseline.run.head_sha, latest.run.head_sha);
    if (!['ahead', 'identical'].includes(range.status)) {
      problems.push({ sha: latest.run.head_sha, url: runUrl(repo, latest.run),
        problem: `history ${range.status}, not a forward comparison` });
      return { plan, saved: baseline };
    }
    plan.delta = crateDifference(baseline, latest);
    plan.range = range;
  }
  plan.latest = crateSummary(repo, latest);
  plan.fresh = true;
  return { plan, saved: latest };
}

async function artifact(github, repo, run, name, kind) {
  const artifacts = await github.paginate(github.rest.actions.listWorkflowRunArtifacts,
    { ...repo, run_id: run.id, per_page: 100 });
  const matches = artifacts.filter(a => a.name === name && !a.expired);
  if (matches.length !== 1) throw new Error(`Missing or expired artifact: ${name}`);
  if (matches[0].size_in_bytes > 64 * 1024 * 1024) throw new Error('Oversized source artifact');
  const response = await github.rest.actions.downloadArtifact({ ...repo, artifact_id: matches[0].id, archive_format: 'zip' });
  return JSON.parse(execFileSync('python3', [path.join(__dirname, 'stock-comparison-read-archive.py'), kind],
    { input: Buffer.from(response.data), maxBuffer: 64 * 1024 * 1024 }));
}

async function attribution(github, repo, before, after) {
  if (before === after) return { status: 'identical', authors: [], commits: [], url: null };
  const basehead = `${before}...${after}`;
  const commits = [];
  let status;
  for (let page = 1; ; page++) {
    const response = (await github.request('GET /repos/{owner}/{repo}/compare/{basehead}',
      { ...repo, basehead, per_page: 100, page })).data;
    status = response.status;
    commits.push(...response.commits);
    if (response.commits.length < 100) break;
    if (page >= 100) throw new Error('Commit range too large');
  }
  return { status, url: `https://github.com/${repo.owner}/${repo.repo}/compare/${basehead}`,
    authors: [...new Set(commits.map(c => c.author?.login ? `@${c.author.login}` :
      `${text(c.commit.author.name)} (GitHub account unavailable)`))],
    commits: commits.map(c => ({ sha: c.sha, title: text(c.commit.message.split('\n')[0]) })) };
}

function measured(snapshot) {
  if (!snapshot) return null;
  const t = snapshot.totals;
  return { exact: t.exact_code_artifacts, sha: snapshot.run.head_sha, totals: t,
    outputs: t.test_function_compilations - (t.function_statuses.expected_stock_rejection_no_binary ?? 0) };
}

async function collect({ github, context, issueNumber, now = new Date(), loadReport, loadState, loadCrate }) {
  const repo = context.repo;
  const issue = (await github.rest.issues.get({ ...repo, issue_number: issueNumber })).data;
  const previous = marker(issue.body ?? '', STATE);
  const since = previous?.through ?? new Date(now.getTime() - DAY).toISOString();
  if (!Number.isFinite(Date.parse(since)) || Date.parse(since) > now.getTime()) throw new Error('Invalid digest cursor');
  let baseline = null;
  let crateBaseline = null;
  if (previous) {
    const source = checkedRun((await github.rest.actions.getWorkflowRun({ ...repo, run_id: previous.snapshot_run_id })).data, NIGHTLY);
    const saved = loadState ? await loadState(source, previous.snapshot_attempt) : await artifact(github, repo, source,
      `stock-nightly-state-${previous.snapshot_attempt}`, 'state');
    if (saved.schema !== 1 || saved.through !== since) throw new Error('Baseline snapshot does not match issue cursor');
    baseline = saved.baseline ? validateSnapshot(saved.baseline) : null;
    // States from before crate parity have no `crate` member: the first crate report is an initial one.
    crateBaseline = saved.crate ? validateCrate(saved.crate) : null;
  }
  const crate = await crateReport({ github, repo, now, baseline: crateBaseline, loadCrate });
  const runs = await github.paginate(github.rest.actions.listWorkflowRuns, { ...repo, workflow_id: WORKFLOW.split('/').at(-1),
    branch: 'main', event: 'push', per_page: 100,
    created: `>=${new Date(Math.min(Date.parse(since), now.getTime() - 7 * DAY) - DAY).toISOString()}` });
  const completed = runs.filter(r => r.status === 'completed' && Date.parse(r.updated_at) <= now.getTime())
    .sort((a, b) => Date.parse(a.created_at) - Date.parse(b.created_at) || a.id - b.id);
  const load = async run => {
    checkedRun(run);
    const report = loadReport ? await loadReport(run) : await artifact(github, repo, run,
      `stock-comparison-artifacts-${run.run_attempt}`, 'measurement');
    return snapshot(report, run);
  };
  if (!baseline) {
    const older = completed.filter(r => r.conclusion === 'success' && Date.parse(r.updated_at) <= Date.parse(since)).reverse();
    for (const run of older) {
      try { baseline = await load(run); break; } catch (error) {
        // Initial setup may have no retained pre-window artifact. Record the gap below.
        if (!error.message.startsWith('Missing or expired artifact:')) throw error;
      }
    }
  }
  const initial = baseline;
  const rows = [];
  for (const run of completed.filter(r => Date.parse(r.updated_at) > Date.parse(since))) {
    checkedRun(run);
    const row = { run, url: runUrl(repo, run) };
    if (run.conclusion !== 'success') { row.problem = `measurement ${run.conclusion}`; rows.push(row); continue; }
    let next;
    try { next = await load(run); } catch (error) {
      if (!error.message.startsWith('Missing or expired artifact:')) throw error;
      row.problem = error.message; rows.push(row); continue;
    }
    row.exact = next.totals.exact_code_artifacts;
    row.outputs = next.totals.test_function_compilations - (next.totals.function_statuses.expected_stock_rejection_no_binary ?? 0);
    if (baseline) {
      row.range = await attribution(github, repo, baseline.run.head_sha, run.head_sha);
      if (!['ahead', 'identical'].includes(row.range.status)) {
        row.problem = `history ${row.range.status}, not a forward comparison`;
        rows.push(row); continue;
      }
      row.delta = difference(baseline, next);
    } else row.initial = true;
    baseline = next;
    rows.push(row);
  }
  const plan = { schema: 1, since, through: now.toISOString(), previous,
    snapshot_run_id: context.runId, snapshot_attempt: Number(process.env.GITHUB_RUN_ATTEMPT || 1),
    initial: measured(initial), latest: measured(baseline),
    compare: initial && baseline && initial.run.head_sha !== baseline.run.head_sha ?
      `https://github.com/${repo.owner}/${repo.repo}/compare/${initial.run.head_sha}...${baseline.run.head_sha}` : null,
    rows, crate: crate.plan };
  return { plan, saved: { schema: 1, through: plan.through, baseline, crate: crate.saved } };
}

function label(key) {
  const [file, stage, isa, command, fn, occurrence] = JSON.parse(key);
  return `${text(file)} ${text(fn)} (${stage}, ISA ${isa}, command ${command}, occurrence ${occurrence + 1})`;
}
function signed(value) {
  if (!value) return '0';
  return (value > 0 ? '+' : '−') + Math.abs(value).toLocaleString('en-US');
}
// The PR comment's table, with the change since the previous report in each row.
function table(before, after) {
  const old = before && totalsRows(before);
  return '| Check | Result | Change |\n| --- | --- | --- |\n' + totalsRows(after).map(row => {
    let change = '—';
    // By label: a report from before a row existed (the honest metric) has no change for it.
    const previous = old?.find(o => o.label === row.label);
    if (previous) {
      change = signed(row.value - previous.value);
      if (row.total !== previous.total) change += ` (of ${signed(row.total - previous.total)})`;
    }
    return `| ${row.label} | ${row.text} | ${change} |\n`;
  }).join('');
}
// The crate-parity part of the digest: one table, the change since the previous report in each
// row, and the functions that stopped matching.
function crateSection(crate) {
  const sha = value => `\`${value.slice(0, 12)}\``;
  let body = '\n#### Real crates: byte-identical functions (`cargo fv`, full gate)\n\n';
  let compact = '';
  if (!crate.latest) {
    body += 'No crate measurement yet.\n';
    compact = ' Crates: no measurement yet.';
  } else {
    const at = `[${sha(crate.latest.sha)}](${crate.latest.url})`;
    if (!crate.fresh) body += `No new full-gate measurement since the previous report. The latest is at ${at}.\n\n`;
    else if (!crate.previous) body += `Full gate at ${at}. No earlier crate measurement to compare with.\n\n`;
    else if (crate.range?.url) body += `Full gate ${sha(crate.previous.sha)} → ${at} ([commits](${crate.range.url})).\n\n`;
    else body += `Full gate at ${at}, the same commit as the previous report.\n\n`;
    body += '| Crate | Byte-identical | Change |\n| --- | --- | --- |\n';
    const parts = [];
    for (const example of CRATES) {
      const t = crate.latest.totals[example];
      const o = crate.fresh && crate.previous ? crate.previous.totals[example] : null;
      let change = '—';
      if (o) {
        change = signed(t.identical - o.identical);
        if (t.functions !== o.functions) change += ` (of ${signed(t.functions - o.functions)})`;
      }
      body += `| ${example} | ${fraction(t.identical, t.functions)} | ${change} |\n`;
      parts.push(`${example} ${t.identical}/${t.functions}` + (o ? ` (${signed(t.identical - o.identical)})` : ''));
    }
    // Quiet days add nothing to the compacted history.
    if (crate.fresh) compact = ` Crates: ${parts.join(', ')} at ${crate.latest.sha.slice(0, 12)}.`;
    if (crate.delta && !crate.delta.comparable) {
      body += '\nMost function names changed between the two measurements (a toolchain or dependency ' +
        'update?), so they are not compared function by function.\n';
      compact += ' Crate function names changed: not compared by function.';
    }
    const lost = crate.delta?.lost ?? [];
    if (lost.length) {
      const total = lost.reduce((sum, [, count]) => sum + count, 0);
      const name = ([key, count]) => {
        const [example, fn] = JSON.parse(key);
        return `${example} ${text(fn)}` + (count > 1 ? ` (${count} copies)` : '');
      };
      const authors = crate.range?.authors?.length ? `; commits by ${crate.range.authors.map(text).join(', ')}` : '';
      body += `\n**Lost crate matches** (${total.toLocaleString('en-US')}${authors}):\n` +
        `${lost.slice(0, 30).map(entry => `- ${name(entry)}`).join('\n')}\n` +
        (lost.length > 30 ? `- ... and ${(lost.length - 30).toLocaleString('en-US')} more (plan artifact)\n` : '');
      compact += ` Lost crate matches${crate.range?.url ? ` (${crate.range.url}${authors})` : ''}: ` +
        `${lost.slice(0, 30).map(name).join('; ')}${lost.length > 30 ? `; and ${lost.length - 30} more` : ''}.`;
    }
  }
  if (crate.passedOver) {
    body += `\n${crate.passedOver.count} newer full-gate run(s) had no crate artifacts ` +
      `(newest: [${sha(crate.passedOver.newest.sha)}](${crate.passedOver.newest.url})).\n`;
  }
  if (crate.problems?.length) {
    body += `\nCrate parity not read: ${crate.problems.map(p => `[${sha(p.sha)}](${p.url}) (${text(p.problem)})`).join(', ')}.\n`;
    compact += ` Crate parity not read: ${crate.problems.map(p => `${p.sha.slice(0, 12)} (${text(p.problem)})`).join(', ')}.`;
  }
  return { body, compact };
}

function render(plan) {
  const sha = value => `\`${value.slice(0, 12)}\``;
  const link = row => `[${sha(row.run.head_sha)}](${row.url})`;
  let body = `### Compiler agreement: ${plan.through.slice(0, 10)}\n\n`;
  let compact = `${plan.through.slice(0, 10)}: `;
  if (!plan.latest) {
    body += 'No valid measurement yet.\n';
    compact += 'no valid measurement.';
  } else {
    const change = plan.initial ? plan.latest.exact - plan.initial.exact : null;
    if (plan.compare) body += `Main ${sha(plan.initial.sha)} → ${sha(plan.latest.sha)} ([commits](${plan.compare})).\n\n`;
    else if (plan.initial) body += `Main at ${sha(plan.latest.sha)}, as in the previous report.\n\n`;
    else body += `Main at ${sha(plan.latest.sha)}. No earlier measurement to compare with.\n\n`;
    body += table(plan.initial?.totals, plan.latest.totals);
    const honest = plan.latest.totals.proved_exact_code_artifacts;
    const honestBefore = plan.initial?.totals.proved_exact_code_artifacts;
    compact += `${plan.latest.exact}/${plan.latest.outputs} exact` + (change === null ? '' : ` (${signed(change)})`) +
      (honest === undefined ? '' : `, ${honest} honest` +
        (honestBefore === undefined ? '' : ` (${signed(honest - honestBefore)})`)) +
      ` at ${plan.latest.sha.slice(0, 12)}.`;
  }
  const problems = plan.rows.filter(row => row.problem);
  if (problems.length) {
    body += `\nNot compared: ${problems.map(row => `${link(row)} (${text(row.problem)})`).join(', ')}.\n`;
    compact += ` Not compared: ${problems.map(row => `${row.run.head_sha.slice(0, 12)} (${text(row.problem)})`).join(', ')}.`;
  }
  const changed = plan.rows.filter(row => row.delta && !row.delta.comparable);
  if (changed.length) {
    body += `\nThe stock reference or the measuring code changed at ${changed.map(link).join(', ')}: ` +
      'part of the change may come from the measurement, not the compiler.\n';
    compact += ` Reference or harness changed at ${changed.map(row => row.run.head_sha.slice(0, 12)).join(', ')}.`;
  }
  // Lost matches are named, with the measured commit range where they were first seen.
  const losses = plan.rows.filter(row => row.delta?.comparable && row.delta.lost.length);
  const lost = losses.reduce((sum, row) => sum + row.delta.lost.length, 0);
  if (lost) {
    const lines = losses.flatMap(row => row.delta.lost.map(key => `- ${label(key)}, first seen at ${link(row)}` +
      (row.range.url ? ` ([commits](${row.range.url}))` : '')));
    body += `\n**Lost exact matches** (${lost.toLocaleString('en-US')}):\n${lines.slice(0, 30).join('\n')}\n` +
      (lines.length > 30 ? `- ... and ${(lines.length - 30).toLocaleString('en-US')} more (report artifact)\n` : '');
    compact += ' ' + losses.map(row => `Lost at ${row.run.head_sha.slice(0, 12)}` +
      (row.range.url ? ` (${row.range.url}; ${row.range.authors.map(text).join(', ') || 'authors unavailable'})` : '') +
      `: ${row.delta.lost.map(label).join('; ')}.`).join(' ');
  }
  // Plans from before crate parity have no `crate` member and render as before.
  if (plan.crate) {
    const crate = crateSection(plan.crate);
    body += crate.body; compact += crate.compact;
  }
  // The compact record keeps lost matches and their attribution after the comment is deleted.
  body = `${COMMENT}${JSON.stringify({ run: plan.snapshot_run_id, attempt: plan.snapshot_attempt })} -->\n` + body +
    `\n${COMPACT}${JSON.stringify(zlib.deflateSync(Buffer.from(compact)).toString('base64'))} -->`;
  if (body.length > LIMIT) throw new Error('Digest exceeds comment limit; do not advance the cursor');
  return { body, compact, lost };
}

function botComments(comments) {
  return comments.filter(c => c.user?.login === 'github-actions[bot]' && c.user?.type === 'Bot' && c.body?.startsWith(COMMENT))
    .sort((a, b) => a.id - b.id);
}
function section(body) {
  const start = body.indexOf(START), end = body.indexOf(END);
  if ((start < 0) !== (end < 0) || start >= 0 && end < start) throw new Error('Broken managed issue section');
  return start < 0 ? null : body.slice(start, end + END.length);
}

async function publish({ github, context, issueNumber, plan, core, keep = 30 }) {
  const repo = context.repo;
  const issue = (await github.rest.issues.get({ ...repo, issue_number: issueNumber })).data;
  const previous = marker(issue.body ?? '', STATE);
  if (JSON.stringify(previous) !== JSON.stringify(plan.previous)) throw new Error('Issue cursor changed; recollect before publishing');
  const currentRun = checkedRun((await github.rest.actions.getWorkflowRun({ ...repo, run_id: context.runId })).data, NIGHTLY);
  if (!['schedule', 'workflow_dispatch'].includes(currentRun.event) || currentRun.id !== plan.snapshot_run_id ||
      currentRun.run_attempt !== plan.snapshot_attempt) throw new Error('Publishing requires a trusted main nightly run');
  // The snapshot must exist BEFORE the issue cursor can point to it.
  const saved = await artifact(github, repo, currentRun, `stock-nightly-state-${plan.snapshot_attempt}`, 'state');
  if (saved.schema !== 1 || saved.through !== plan.through ||
      (saved.baseline?.run.head_sha ?? null) !== (plan.latest?.sha ?? null) ||
      (saved.crate?.run.id ?? null) !== (plan.crate?.latest?.run_id ?? null)) throw new Error('Uploaded baseline disagrees with digest');
  if (saved.baseline) validateSnapshot(saved.baseline);
  if (saved.crate) validateCrate(saved.crate);
  const comments = await github.paginate(github.rest.issues.listComments, { ...repo, issue_number: issueNumber, per_page: 100 });
  const rendered = render(plan);
  const own = botComments(comments);
  let current = own.find(c => {
    const identity = marker(c.body, COMMENT);
    return identity?.run === context.runId && identity.attempt === plan.snapshot_attempt;
  });
  if (!current) current = (await github.rest.issues.createComment({ ...repo, issue_number: issueNumber, body: rendered.body })).data;
  else if (current.body !== rendered.body) throw new Error('Existing digest differs; refusing to overwrite it');
  const candidates = botComments([...comments.filter(c => c.id !== current.id), current]).slice(0, -keep);
  const oldSection = section(issue.body ?? '') ?? '';
  const archiveStart = '<!-- clifv-nightly-archive:start -->', archiveEnd = '<!-- clifv-nightly-archive:end -->';
  let archive = oldSection.includes(archiveStart) ? oldSection.split(archiveStart)[1].split(archiveEnd)[0].trim() : '';
  if (archive === 'No comments compacted yet.') archive = '';
  let archivedThrough = previous?.archived_through ?? 0;
  const newArchive = candidates.filter(c => c.id > archivedThrough).map(c => {
    const summary = marker(c.body, COMPACT);
    if (typeof summary !== 'string') throw new Error('Old digest has no compact record; preserve its comment');
    return `- ${zlib.inflateSync(Buffer.from(summary, 'base64'), { maxOutputLength: LIMIT }).toString('utf8')}`;
  }).join('\n');
  let proposed = [archive, newArchive].filter(Boolean).join('\n');
  const makeSection = (history, cutoff) => `${START}\n## Latest measurement\n\n` +
    (plan.latest ? `${plan.latest.exact}/${plan.latest.outputs} exact outputs at \`${plan.latest.sha.slice(0, 12)}\`.\n` : 'No valid baseline yet.\n') +
    (plan.crate?.latest ? `Real crates (\`cargo fv\`): ${CRATES.map(example => {
      const t = plan.crate.latest.totals[example];
      return `${example} ${t.identical}/${t.functions}`;
    }).join(', ')} byte-identical at \`${plan.crate.latest.sha.slice(0, 12)}\`.\n` : '') +
    `\n[Latest daily report](${current.html_url}).\n\n## Compacted history\n\n${archiveStart}\n${history || 'No comments compacted yet.'}\n${archiveEnd}\n\n` +
    `${STATE}${JSON.stringify({ through: plan.through, snapshot_run_id: context.runId,
      snapshot_attempt: plan.snapshot_attempt, archived_through: cutoff })} -->\n${END}`;
  const replace = managed => oldSection ? issue.body.replace(oldSection, managed) : `${issue.body ?? ''}\n\n${managed}`;
  let deletions = candidates;
  let cutoff = candidates.length ? Math.max(archivedThrough, ...candidates.map(c => c.id)) : archivedThrough;
  if (replace(makeSection(proposed, cutoff)).length > LIMIT) {
    core.warning('Compacted history is full; preserve old comments rather than lose findings');
    proposed = archive; cutoff = archivedThrough; deletions = [];
  }
  const updated = replace(makeSection(proposed, cutoff));
  if (updated.length > LIMIT) throw new Error('Issue body too large; preserve comments and cursor');
  const fresh = (await github.rest.issues.get({ ...repo, issue_number: issueNumber })).data;
  if (fresh.body !== issue.body) throw new Error('Issue body changed; preserve human edits and comments');
  await github.rest.issues.update({ ...repo, issue_number: issueNumber, body: updated });
  const verified = (await github.rest.issues.get({ ...repo, issue_number: issueNumber })).data;
  if (section(verified.body) !== section(updated)) throw new Error('Archive update not confirmed; preserve comments');
  // Only bot-owned marked comments incorporated into the confirmed issue body can be deleted.
  for (const comment of deletions) await github.rest.issues.deleteComment({ ...repo, comment_id: comment.id });
  core.info(`Published ${current.html_url}; compacted ${deletions.length} bot comments`);
  return current;
}

async function prepareFiles(args) {
  const result = await collect(args);
  const rendered = render(result.plan);
  fs.mkdirSync('nightly', { recursive: true });
  fs.writeFileSync('nightly/state.json', JSON.stringify(result.saved));
  fs.writeFileSync('nightly/plan.json', JSON.stringify(result.plan));
  fs.writeFileSync('nightly/report.md', rendered.body);
  fs.appendFileSync(process.env.GITHUB_STEP_SUMMARY, rendered.body);
  return result;
}

module.exports = { snapshot, validateSnapshot, difference, crateSnapshot, validateCrate, crateDifference,
  collect, render, publish, prepareFiles, marker, botComments, START, END, STATE, COMMENT, COMPACT, WORKFLOW,
  NIGHTLY, GATE };
