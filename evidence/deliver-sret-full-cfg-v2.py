from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import subprocess
import time

b = Path('/home/lee/clifv')
r = b / '.worktrees/stock-extending-production-20261031'
e = b / '.git/agent-evidence/stock-memory-20261029'
env = dict(os.environ)
env.update(json.loads((e / 'author-env-v1.json').read_text()))
env.update(FV_MEMCAP='6G', LEAN_NUM_THREADS='2', OMP_NUM_THREADS='2', OMP_THREAD_LIMIT='2')
branch = 'agent/stock-sret-copy-full-values-20261101'

def run(*args):
    return subprocess.check_output(args, cwd=r, env=env, text=True).strip()

parent = json.loads((e / 'return-pin-runtime-landed-v1.json').read_text())
assert parent['status'] == 'landed' and parent['tree_equal']
assert run('git', 'status', '--porcelain') == ''
assert run('git', 'rev-parse', 'HEAD') == parent['source']
published = json.loads((e / 'sret-full-cfg-publication-v1.json').read_text())
hashes = published['source_hashes']
assert run('git', 'rev-parse', branch) == published['source']
run('git', 'switch', branch)
for attempt in range(1, 7):
    run('git', 'fetch', 'origin', 'main')
    base = run('git', 'rev-parse', 'origin/main')
    run('git', 'merge-base', '--is-ancestor', parent['merged'], base)
    run('git', 'merge', '--no-edit', 'origin/main')
    head = run('git', 'rev-parse', 'HEAD')
    assert set(run('git', 'diff', '--name-only', base, head).splitlines()) == set(hashes)
    assert all(hashlib.sha256((r / name).read_bytes()).hexdigest() == digest for name, digest in hashes.items())
    # Start exact-head CI while the unchanged local gates run.
    run('git', 'push', 'origin', branch)
    assert run('git', 'ls-remote', 'origin', 'refs/heads/' + branch).split()[0] == head
    run('gh', 'pr', 'edit', '868', '--repo', 'eth-act/clifv', '--base', 'main')
    logs = e / ('sret-full-cfg-current-main-recovery-r' + str(attempt))
    logs.mkdir(exist_ok=True)
    modules = ['FV.Backend.Proof.StockReturnFullBody', 'FV.Backend.Proof.StockMemorySretCopyFullReturn', 'FV.Backend.Proof.StockReturnFullBodyWitness', 'FV.Backend.Proof.StockMemorySretCopyFullReturnWitness']
    with (logs / 'kernel.log').open('w') as log:
        subprocess.run(['nice', '-n', '10', str(r / 'scripts/memcap.sh'), 'python3', 'scripts/lake-serial-build.py',
                        '--budget', '6G', '--max-jobs', '1', '--max-cap', '6G', '--default-cap', '3G',
                        '--profile', 'scripts/lake-module-peaks.tsv', '--out', str(logs / 'modules'), *modules],
                       cwd=r, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
    with (logs / 'audit-summary.log').open('w') as log:
        subprocess.run(['nice', '-n', '10', str(r / 'scripts/memcap.sh'), 'python3', 'scripts/axiom-audit.py',
                        '--log-dir', str(logs / 'audit'), 'scripts/audit/stock-sret-full-values.lean'],
                       cwd=r, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
    def axioms(path):
        content = ' '.join(path.read_text().split())
        found = {name: sorted(a.strip() for a in values.split(',') if a.strip())
                 for name, values in re.findall(r"'(\S+)' depends on axioms: \[([^]]*)\]", content)}
        found.update({name: [] for name in re.findall(r"'(\S+)' does not depend on any axioms", content)})
        return found
    baseline = axioms(e / 'sret-full-cfg-packet-kernel-v2/audit/stock-sret-full-values.log')
    current = axioms(logs / 'audit/stock-sret-full-values.log')
    assert len(baseline) == 12 and current == baseline
    assert run('git', 'rev-parse', 'HEAD') == head and run('git', 'status', '--porcelain') == ''
    assert all(hashlib.sha256((r / name).read_bytes()).hexdigest() == digest for name, digest in hashes.items())
    previous = None
    for poll in range(180):
        pr = json.loads(run('gh', 'pr', 'view', '868', '--repo', 'eth-act/clifv',
                            '--json', 'headRefOid,baseRefName,statusCheckRollup,state'))
        assert pr['state'] == 'OPEN' and pr['baseRefName'] == 'main', pr
        if pr['headRefOid'] != head:
            assert poll < 6, pr
            time.sleep(10)
            continue
        checks = pr['statusCheckRollup']
        states = [(c.get('name', c.get('context')), c.get('status', c.get('state')), c.get('conclusion')) for c in checks]
        if states != previous:
            print('CI', json.dumps(states), flush=True)
            previous = states
        failed = [c for c in checks if c.get('conclusion') in ['FAILURE', 'CANCELLED', 'TIMED_OUT', 'ACTION_REQUIRED']
                  or c.get('state') in ['FAILURE', 'ERROR']]
        assert not failed, failed
        if len(checks) >= 4 and all(c.get('conclusion') == 'SUCCESS' or c.get('state') == 'SUCCESS' for c in checks):
            break
        time.sleep(20)
    else:
        raise RuntimeError('The exact-head CI did not finish within one hour. Inspect existing runs before retrying.')
    if run('gh', 'api', 'repos/eth-act/clifv/commits/main', '--jq', '.sha') != base:
        print('Main advanced; reconcile and repeat the existing gates with the warm cache.', flush=True)
        continue
    assert run('git', 'rev-parse', 'HEAD') == head and run('git', 'status', '--porcelain') == ''
    tree = run('git', 'rev-parse', head + '^{tree}')
    run('gh', 'pr', 'merge', '868', '--repo', 'eth-act/clifv', '--squash', '--match-head-commit', head)
    pr = json.loads(run('gh', 'pr', 'view', '868', '--repo', 'eth-act/clifv', '--json', 'state,mergeCommit'))
    assert pr['state'] == 'MERGED', pr
    merged = pr['mergeCommit']['oid']
    run('git', 'fetch', 'origin', 'main')
    assert run('git', 'rev-parse', merged + '^{tree}') == tree
    receipt = dict(status='landed', pr=868, source=head, base=base, merged=merged, tested_tree=tree,
                   tree_equal=True, source_hashes=hashes, checks=checks, generic_roots=10, fixed_roots=2,
                   full_goal_complete=False, utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
    (e / 'sret-full-cfg-landed-v1.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt), flush=True)
    
    break
else:
    raise RuntimeError('Main advanced six times. Inspect the exact changes before further delivery.')
