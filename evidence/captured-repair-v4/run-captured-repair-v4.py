from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import subprocess

base = Path('/home/lee/clifv')
root = base / '.worktrees/stock-cfg-source-20261025'
evidence = base / '.git/agent-evidence/stock-memory-20261029'
state = evidence / 'captured-repair-state-v4.json'
records = []
env = dict(os.environ)
env.update(json.loads((evidence / 'author-env-v1.json').read_text()))
env.update(FV_ROOT=str(root), FV_MEMCAP='10G', OMP_NUM_THREADS='1',
           OMP_THREAD_LIMIT='1', LEAN_NUM_THREADS='1', CARGO_BUILD_JOBS='1')
targets = ['FV.Backend.Proof.IselShpTTabS5', 'FV.E2E.StockMemoryActivationWitness',
           'FVTest.Backend.Lowering.StockMemoryProductionLinked']


def save(status, **extra):
    state.write_text(json.dumps(dict(status=status, records=records,
        utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), **extra), indent=2) + '\n')


def run(label, args):
    save('running', phase=label)
    with (evidence / ('captured-repair-' + label + '-v4.log')).open('w') as log:
        done = subprocess.run([str(root / 'scripts/memcap.sh'), *args], cwd=root,
            env=env, stdout=log, stderr=subprocess.STDOUT)
    records.append(dict(label=label, returncode=done.returncode))
    assert done.returncode == 0, (label, done.returncode)


try:
    profile = evidence / 'captured-shape-s5-profile-v4.tsv'
    profile.write_text('# Eight GiB was an observed OOM lower bound. Cap this retry at ten GiB.\n'
        'FV.Backend.Proof.IselShpTTabS5\t8192\t28\n')
    run('targets', ['python3', '-I', 'scripts/lake-serial-build.py', '--budget', '10G',
        '--max-jobs', '1', '--max-cap', '10G', '--default-cap', '10G',
        '--profile', str(profile), '--out', str(evidence / 'captured-repair-modules-v4'), *targets])
    run('old-audit', ['lake', 'env', 'lean', 'scripts/audit/stock-memory-source.lean'])
    def axioms(path):
        return {name: set(value.strip() for value in values.split(',') if value.strip())
            for name, values in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", path.read_text(), re.S)}
    old = axioms(evidence / 'author-normal-gates-v1/all-axioms/stock-memory-source.log')
    current = axioms(evidence / 'captured-repair-old-audit-v4.log')
    assert len(old) == 105 and current == old
    paths = ['FV/E2E/StockMemoryActivationWitness.lean',
             'FVTest/Backend/Lowering/StockMemoryProductionLinked.lean']
    save('passed', axiom_roots=105, old_axiom_sets_exact=True,
        source_sha256={p: hashlib.sha256((root / p).read_bytes()).hexdigest() for p in paths},
        scope='Three failed targets and exact old audit repaired; complete consumer gate still required')
except BaseException as error:
    save('failed', error=repr(error))
    raise
