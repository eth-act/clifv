from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess
import time

b = Path('/home/lee/clifv')
r = b / '.worktrees/stock-extending-production-20261031'
e = b / '.git/agent-evidence/stock-memory-20261029'
env = dict(os.environ)
env.update(json.loads((e / 'author-env-v1.json').read_text()))
env.update(FV_MEMCAP='6G', LEAN_NUM_THREADS='2', OMP_NUM_THREADS='2', OMP_THREAD_LIMIT='2')
branch = 'agent/stock-shared-image-extension-20261101'

def run(*args):
    return subprocess.check_output(args, cwd=r, env=env, text=True).strip()

parent = json.loads((e / 'void-call-file-landed-v1.json').read_text())
assert parent['status'] == 'landed' and parent['tree_equal']
assert run('git', 'status', '--porcelain') == ''
assert run('git', 'rev-parse', 'HEAD') == parent['source']
published = json.loads((e / 'link-image-extension-publication-v1.json').read_text())
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
    gate_source = (e / 'verify-link-image-extension-current-main-v1.py').read_text()
    gate_source = gate_source.replace('link-image-extension-current-main-', 'link-image-extension-current-main-recovery-r' + str(attempt) + '-')
    gate = e / ('verify-link-image-extension-current-main-recovery-r' + str(attempt) + '.py')
    gate.write_text(gate_source)
    subprocess.run(['python3',str(gate)],cwd=r,env=env,check=True)
    assert run('git', 'rev-parse', 'HEAD') == head and run('git', 'status', '--porcelain') == ''
    assert all(hashlib.sha256((r / name).read_bytes()).hexdigest() == digest for name, digest in hashes.items())
    run('git', 'push', 'origin', branch)
    assert run('git', 'ls-remote', 'origin', 'refs/heads/' + branch).split()[0] == head
    run('gh', 'pr', 'edit', '866', '--repo', 'eth-act/clifv', '--base', 'main')
    previous = None
    for poll in range(180):
        pr = json.loads(run('gh', 'pr', 'view', '866', '--repo', 'eth-act/clifv',
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
    run('gh', 'pr', 'merge', '866', '--repo', 'eth-act/clifv', '--squash', '--match-head-commit', head)
    pr = json.loads(run('gh', 'pr', 'view', '866', '--repo', 'eth-act/clifv', '--json', 'state,mergeCommit'))
    assert pr['state'] == 'MERGED', pr
    merged = pr['mergeCommit']['oid']
    run('git', 'fetch', 'origin', 'main')
    assert run('git', 'rev-parse', merged + '^{tree}') == tree
    receipt = dict(status='landed', pr=866, source=head, base=base, merged=merged, tested_tree=tree,
                   tree_equal=True, source_hashes=hashes, checks=checks, original_statement_headers=34, original_axiom_sets=34,
                   full_goal_complete=False, utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
    (e / 'link-image-extension-landed-v1.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt), flush=True)
    
    break
else:
    raise RuntimeError('Main advanced six times. Inspect the exact changes before further delivery.')
