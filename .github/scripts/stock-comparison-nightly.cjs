// Trusted main reports are data, never executable input. No compiler rebuilds here.
const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');
const zlib = require('node:zlib');
const { execFileSync } = require('node:child_process');
const { validateMeasurement } = require('./stock-comparison-comment.cjs');

const WORKFLOW = '.github/workflows/stock-compiler-comparison.yml';
const NIGHTLY = '.github/workflows/stock-comparison-nightly.yml';
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

async function collect({ github, context, issueNumber, now = new Date(), loadReport, loadState }) {
  const repo = context.repo;
  const issue = (await github.rest.issues.get({ ...repo, issue_number: issueNumber })).data;
  const previous = marker(issue.body ?? '', STATE);
  const since = previous?.through ?? new Date(now.getTime() - DAY).toISOString();
  if (!Number.isFinite(Date.parse(since)) || Date.parse(since) > now.getTime()) throw new Error('Invalid digest cursor');
  let baseline = null;
  if (previous) {
    const source = checkedRun((await github.rest.actions.getWorkflowRun({ ...repo, run_id: previous.snapshot_run_id })).data, NIGHTLY);
    const saved = loadState ? await loadState(source, previous.snapshot_attempt) : await artifact(github, repo, source,
      `stock-nightly-state-${previous.snapshot_attempt}`, 'state');
    if (saved.schema !== 1 || saved.through !== since) throw new Error('Baseline snapshot does not match issue cursor');
    baseline = saved.baseline ? validateSnapshot(saved.baseline) : null;
  }
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
    if (run.conclusion !== 'success') { row.problem = `Measurement ${run.conclusion}; no compiler-regression claim`; rows.push(row); continue; }
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
        row.problem = `History ${row.range.status}: not a forward comparison; baseline unchanged`;
        rows.push(row); continue;
      }
      row.delta = difference(baseline, next);
    } else row.initial = true;
    baseline = next;
    rows.push(row);
  }
  const plan = { schema: 1, since, through: now.toISOString(), previous,
    snapshot_run_id: context.runId, snapshot_attempt: Number(process.env.GITHUB_RUN_ATTEMPT || 1),
    initial: initial ? { exact: initial.totals.exact_code_artifacts, sha: initial.run.head_sha } : null,
    latest: baseline ? { exact: baseline.totals.exact_code_artifacts, sha: baseline.run.head_sha,
      outputs: baseline.totals.test_function_compilations - (baseline.totals.function_statuses.expected_stock_rejection_no_binary ?? 0) } : null,
    rows };
  return { plan, saved: { schema: 1, through: plan.through, baseline } };
}

function label(key) {
  const [file, stage, isa, command, fn, occurrence] = JSON.parse(key);
  return `${text(file)} ${text(fn)} (${stage}, ISA ${isa}, command ${command}, occurrence ${occurrence + 1})`;
}
function render(plan) {
  let body = `### Compiler agreement: ${plan.through.slice(0, 10)}\n\n`;
  body += `Window: ${plan.since} → ${plan.through}.\n`;
  body += plan.latest ? `Latest: **${plan.latest.exact} / ${plan.latest.outputs} exact outputs** at \`${plan.latest.sha.slice(0, 12)}\`.\n` : 'No valid baseline available.\n';
  let gained = 0, lost = 0;
  const archived = [];
  for (const row of plan.rows) {
    const reference = `[${row.run.head_sha.slice(0, 12)}](${row.url})`;
    body += `\n#### ${reference}\n\n`;
    if (row.problem) { body += `${text(row.problem)}.\n`; archived.push(`${reference}: ${text(row.problem)}.`); continue; }
    if (row.initial) { body += `Initial baseline: ${row.exact}/${row.outputs}; no earlier valid measurement.\n`; archived.push(`${reference}: initial baseline ${row.exact}/${row.outputs}.`); continue; }
    const attribution = row.range.url ? `[Measured commit range](${row.range.url}); authors: ${row.range.authors.map(text).join(', ') || 'unavailable'}.` : 'Same-commit rerun; changes are not attributed to an author.';
    body += `${attribution}\n`;
    for (const commit of row.range.commits.slice(0, 20)) body += `- \`${commit.sha.slice(0, 12)}\`: ${commit.title}\n`;
    if (row.range.commits.length > 20) body += `- ${row.range.commits.length - 20} more commits in the linked range.\n`;
    if (!row.delta.comparable) {
      body += `\nReference or harness changed: **not directly comparable**. New baseline: ${row.exact}/${row.outputs}.\n`;
      archived.push(`${reference}: reference/harness changed; baseline ${row.exact}/${row.outputs}. ${attribution}`); continue;
    }
    const d = row.delta;
    gained += d.gained.length; lost += d.lost.length;
    const counts = `Exact outputs +${d.gained.length} / -${d.lost.length}; supported outputs +${d.supportGained.length} / -${d.supportLost.length}; identities added ${d.added.length}, removed ${d.removed.length}, input/settings changed ${d.changedInput.length}, unstable-reference outputs excluded ${d.unstableReference.length}.`;
    body += `\n${counts}\n`;
    const regressions = [...new Set([...d.lost, ...d.supportLost])];
    if (regressions.length) body += '\nFirst-observed regressions (not proven causes):\n' + regressions.map(key => `- ${label(key)}`).join('\n') + '\n';
    if (d.removed.length) body += '\nRemoved output identities (coverage losses, not byte regressions):\n' + d.removed.map(key => `- ${label(key)}`).join('\n') + '\n';
    archived.push(`${reference}: ${counts} ${attribution}` +
      (regressions.length ? ` Regressions: ${regressions.map(label).join('; ')}.` : '') +
      (d.removed.length ? ` Removed: ${d.removed.map(label).join('; ')}.` : ''));
  }
  if (!plan.rows.length) body += '\nNo newly completed main measurements.\n';
  body += '\nRanges show where a change was first observed, not proof of a specific culprit. Failed/cancelled runs are measurement gaps. This measures artifact equality, not execution or formal proof coverage.\n';
  const compact = `${plan.through.slice(0, 10)}: ${plan.rows.length} measurements, exact gains ${gained}, losses ${lost}. ` +
    (plan.latest ? `Latest ${plan.latest.exact}/${plan.latest.outputs}. ` : '') + archived.join(' ');
  // The compact record retains every regression and attribution, not expiring artifact links alone.
  body = `${COMMENT}${JSON.stringify({ run: plan.snapshot_run_id, attempt: plan.snapshot_attempt })} -->\n` + body +
    `\n${COMPACT}${JSON.stringify(zlib.deflateSync(Buffer.from(compact)).toString('base64'))} -->`;
  if (body.length > LIMIT) throw new Error('Digest exceeds comment limit; do not advance the cursor');
  return { body, compact, gained, lost };
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
      (saved.baseline?.run.head_sha ?? null) !== (plan.latest?.sha ?? null)) throw new Error('Uploaded baseline disagrees with digest');
  if (saved.baseline) validateSnapshot(saved.baseline);
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

module.exports = { snapshot, validateSnapshot, difference, collect, render, publish, prepareFiles,
  marker, botComments, START, END, STATE, COMMENT, COMPACT, WORKFLOW, NIGHTLY };
