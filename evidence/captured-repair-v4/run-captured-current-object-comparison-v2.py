from pathlib import Path
import datetime
import hashlib
import json
import sys
import time

import psutil

base = Path('/home/lee/clifv')
root = base / '.worktrees/stock-cfg-source-20261025'
evidence = base / '.git/agent-evidence/stock-memory-20261029'
state = evidence / 'captured-current-object-comparison-state-v2.json'
rows = []


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(status, **extra):
    state.write_text(json.dumps(dict(
        status=status,
        utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        rows=rows,
        **extra,
    ), indent=2) + '\n')


save('waiting', dependency=2802342)
while psutil.pid_exists(2802342):
    time.sleep(2)

try:
    inputs_path = evidence / 'captured-real-inputs-state-v4.json'
    inputs = json.loads(inputs_path.read_text())
    assert inputs['status'] == 'passed', inputs
    assert inputs['sources'] == 4543 and inputs['checked'] == 4
    assert inputs['source_hashes_exact']
    reference_path = evidence / 'captured-object-reference-v1/receipt.json'
    reference = json.loads(reference_path.read_text())
    assert reference['status'] == 'passed'
    expected = {(r['function'], r['cleanup']): r for r in reference['rows']}
    actual = {(r['function'], r['cleanup']): r for r in inputs['records']}
    assert len(expected) == len(actual) == len(inputs['records']) == 8
    assert actual.keys() == expected.keys()
    sys.path.insert(0, str(root / 'scripts'))
    from byte_compare import ELF
    from stock_common import comparison

    save('running')
    for index, record in enumerate(inputs['records']):
        key = record['function'], record['cleanup']
        prior = expected[key]
        source = Path(record['path'])
        assert str(source) == prior['original_path']
        assert digest(source) == record['source_sha256'] == prior['original_sha256']
        assert record['actual_allocator_matches_provider']
        assert record['cleanup'] or record['plain_stock_binding_checked']
        label = str(index // 2) + ('-cleanup' if record['cleanup'] else '-plain')
        obj = evidence / 'captured-real-inputs-v4' / (label + '.o')
        assert digest(obj) == record['object_sha256']
        elf = ELF(obj)
        symbol, code = elf.function(record['function'])
        relocations = elf.function_relocations(symbol, {})
        result = comparison(bytes.fromhex(prior['stock_bytes']), code,
                            prior['stock_metadata']['relocations'], relocations)
        rows.append(dict(function=record['function'], cleanup=record['cleanup'],
                         original_sha256=digest(source), object_sha256=digest(obj),
                         object_path=str(obj), comparison=result,
                         actual_allocator_matches_provider=True))
        assert result['exact_code_and_relocations'], rows[-1]
    save('passed', cases=len(rows), code_and_relocations_exact=len(rows),
         inputs_receipt_sha256=digest(inputs_path),
         reference_receipt_sha256=digest(reference_path),
         settings_contract_verified=False,
         scope='Current-base default function bytes and relocations against preserved repeated Cranelift exports. No settings-contract, full-artifact, or official-suite gain claim.')
except BaseException as error:
    save('failed', error=repr(error))
    raise
