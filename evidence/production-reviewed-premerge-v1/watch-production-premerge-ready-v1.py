from pathlib import Path
import datetime
import json
import re
import time

import psutil

evidence = Path('/home/lee/clifv/.git/agent-evidence/stock-memory-20261029')
state_path = evidence / 'production-reverse-gates-state-v5.json'
receipt = evidence / 'production-premerge-ready-state-v1.json'
watcher = 2311744
required = {'reverse-closure', 'executables', 'memory-audit'}


def save(status, **extra):
    receipt.write_text(json.dumps(dict(status=status,
        utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        dependency=watcher, **extra), indent=2) + '\n')


def axioms(path):
    return {name: set(x.strip() for x in values.split(','))
            for name, values in re.findall(
                r"'([^']+)' depends on axioms: \[([^]]*)\]",
                path.read_text(), re.S)}


save('waiting')
try:
    while True:
        live = psutil.pid_exists(watcher)
        try:
            state = json.loads(state_path.read_text())
        except json.JSONDecodeError:
            if not live:
                raise RuntimeError('Gate exited without a readable final state')
            time.sleep(2)
            continue
        if state['status'] == 'failed':
            raise RuntimeError(('Production gate failed', state))
        passed = {r['id'] for r in state['records'] if r['returncode'] == 0}
        if (required <= passed and
                (state['status'] == 'passed' or
                 (live and state['status'] == 'running' and
                  state.get('phase') != 'memory-audit'))):
            old = axioms(evidence / 'author-normal-gates-v1/all-axioms/stock-memory-source.log')
            current = axioms(evidence / 'production-memory-audit-v5.log')
            assert len(old) == 105 and current == old
            save('passed', gate_state=state, audit_roots=105,
                 axiom_sets_exact=True,
                 approved_head='b6cdec54ace309896038fdecbb7c47a2d991e2fe',
                 scope='Pre-merge conditions only. Recheck current head, source, main, and runtime status before merging. Runtime failures require immediate revert.')
            break
        if not live:
            raise RuntimeError(('Gate stopped before reviewed conditions passed', state))
        time.sleep(2)
except BaseException as error:
    save('failed', error=repr(error))
    raise
