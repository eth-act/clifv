from pathlib import Path
import datetime
import json
import os
import subprocess
import time

b = Path('/home/lee/clifv')
e = b / '.git/agent-evidence/stock-memory-20261029'
env = dict(os.environ)
env.update(json.loads((e / 'author-env-v1.json').read_text()))

def run(*args):
    return subprocess.check_output(args, cwd=b, env=env, text=True).strip()

parent = json.loads((e / 'return-pin-call-consumer-landed-v1.json').read_text())
assert parent['status'] == 'landed' and parent['tree_equal']
backed = json.loads((e / 'return-pin-runtime-branch-v2.json').read_text())
# The dependency now has a new tested source after current-main reconciliation.
# Verify its landed ancestry and the exact adapter-only diff instead of an obsolete parent SHA.
run('git', 'fetch', 'origin', 'main')
base = run('git', 'rev-parse', 'origin/main')
run('git', 'merge-base', '--is-ancestor', parent['merged'], base)
branch = backed['branch']
assert run('git', 'rev-parse', branch) == backed['source']
tree = run('git', 'merge-tree', '--write-tree', backed['source'], base).splitlines()[0]
assert set(run('git', 'diff-tree', '--no-commit-id', '--name-only', '-r', base, tree).splitlines()) == set(backed['source_hashes'])
commit = run('git', 'commit-tree', tree, '-p', backed['source'], '-p', base, '-m',
             'Reconcile the complete-file linker adapter onto its landed dependency')
run('git', 'update-ref', 'refs/heads/' + branch, commit, backed['source'])
run('git', 'push', 'origin', branch)
assert run('git', 'ls-remote', 'origin', 'refs/heads/' + branch).split()[0] == commit
url = run('gh', 'pr', 'create', '--repo', 'eth-act/clifv', '--base', 'main', '--head', branch,
          '--title', 'Add the ABI-aware complete-file linker adapter',
          '--body-file', str(e / 'return-pin-runtime-pr-body-v2.md'))
receipt = dict(status='published', pr=url, branch=branch, source=commit, base=base,
               source_hashes=backed['source_hashes'], full_goal_complete=False,
               scope='A four-file PR follows the landed860 dependency on the actual current main. '
                     'The exact adapter-only diff is checked. Final current-main module gates and '
                     'exact-head CI remain required before merge. The tracked build view is unchanged.',
               utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(e / 'return-pin-runtime-publication-v3.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt), flush=True)
