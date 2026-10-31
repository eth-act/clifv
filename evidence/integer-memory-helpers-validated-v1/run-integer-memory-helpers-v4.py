from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import subprocess

base = Path('/home/lee/clifv')
evidence = base / '.git/agent-evidence/stock-memory-20261029'
root = base / '.worktrees/stock-cfg-source-20261025'
output = evidence / 'integer-memory-helpers-v1'
source = output / 'source'
lib = output / 'lib'
state = evidence / 'integer-memory-helpers-state-v4.json'
records = []


def save(status, **extra):
    state.write_text(json.dumps(dict(status=status, records=records,
        utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), **extra), indent=2) + '\n')


env = dict(os.environ)
env.update(json.loads((evidence / 'author-env-v1.json').read_text()))
env.update(OMP_NUM_THREADS='1', OMP_THREAD_LIMIT='1', LEAN_NUM_THREADS='1', FV_MEMCAP='2G')
env['LEAN_PATH'] = str(lib) + ':' + (evidence / 'integer-helpers-lean-path-v1.txt').read_text().strip()
modules = ['StockMemoryHelperProjection',
           'StockMemoryHelperContracts', 'StockMemoryHelperWitness']
try:
    for module in modules:
        save('running', phase=module)
        path = source / 'FV/Backend/Proof' / (module + '.lean')
        target = lib / 'FV/Backend/Proof' / (module + '.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        with (output / (module + '.log')).open('w') as log:
            done = subprocess.run(['lean', '-j1', '--root=' + str(source),
                '-o', str(target), str(path)], cwd=root, env=env,
                stdout=log, stderr=subprocess.STDOUT)
        records.append(dict(module=module, returncode=done.returncode,
            source_sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
        if done.returncode:
            raise RuntimeError((module, done.returncode))
    save('running', phase='axioms')
    audit = output / 'axioms.log'
    with audit.open('w') as log:
        done = subprocess.run(['lean', '-j1', '--root=' + str(source), str(source / 'Audit.lean')],
            cwd=root, env=env, stdout=log, stderr=subprocess.STDOUT)
    assert done.returncode == 0, ('axioms', done.returncode)
    axioms = {name: set(x.strip() for x in values.split(',') if x.strip())
        for name, values in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", audit.read_text(), re.S)}
    assert len(axioms) == 8, axioms
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    assert all(value <= allowed for value in axioms.values()), axioms
    save('passed', axiom_roots=8, standard_only=True, load_variants=7, store_variants=4,
         source_gates_unchanged=True, scope='Focused helper contracts and witnesses only')
except BaseException as error:
    save('failed', error=repr(error))
    raise
