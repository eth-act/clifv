from pathlib import Path
import datetime
import hashlib
import importlib.util
import json
import os
import subprocess
import sys

base = Path('/home/lee/clifv')
root = base / '.worktrees/stock-cfg-source-20261025'
evidence = base / '.git/agent-evidence/stock-memory-20261029'
output = evidence / 'configured-original-captures-v1'
source = output / 'source'
state = evidence / 'configured-original-captures-state-v1.json'
records = []


def save(status, **extra):
    state.write_text(json.dumps(dict(status=status, records=records,
        utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), **extra), indent=2) + '\n')


env = dict(os.environ)
env.update(json.loads((evidence / 'author-env-v1.json').read_text()))
env.update(FV_MEMCAP='2G', OMP_NUM_THREADS='1', OMP_THREAD_LIMIT='1', LEAN_NUM_THREADS='1')
env['LEAN_PATH'] = str(output / 'lib') + ':' + (evidence / 'integer-helpers-lean-path-v1.txt').read_text().strip()
sys.path.insert(0, str(root / 'scripts'))
spec = importlib.util.spec_from_file_location('official_compare', root / 'scripts/stock-compiler-compare.py')
compare = importlib.util.module_from_spec(spec)
spec.loader.exec_module(compare)
try:
    save('running', phase='compile-configuration-adapter')
    with (output / 'StockConfig.log').open('w') as log:
        done = subprocess.run(['lean', '-j1', '--root=' + str(source), '-o',
            str(output / 'lib/FVTest/Backend/StockConfig.olean'),
            str(source / 'FVTest/Backend/StockConfig.lean')], cwd=root, env=env,
            stdout=log, stderr=subprocess.STDOUT)
    assert done.returncode == 0
    reference = json.loads((evidence / 'captured-object-reference-v1/receipt.json').read_text())
    assert len(reference['rows']) == 8
    variants = {}
    for manifest in (evidence / 'captured-object-reference-v1').glob('*/first/manifest.json'):
        data = json.loads(manifest.read_text())
        for variant in data['variants']:
            for name in variant['functions']:
                variants[name.removeprefix('%')] = variant
    expected = {row['original_path']: row['original_sha256'] for row in reference['rows']}
    assert len(expected) == 4
    for index, row in enumerate(reference['rows']):
        path = Path(row['original_path'])
        assert compare.digest(path) == row['original_sha256']
        request = compare.request_for(variants[row['function']], path)
        assert {'name': 'tls_model', 'value': 'elf_gd'} in request['flags']
        request_path = output / f'{index}.request.json'
        request_path.write_text(json.dumps(request, indent=2) + '\n')
        results = []
        for mode in ['native-baseline', 'interpreted-adapter']:
            save('running', phase=f'{index}-{mode}')
            obj = output / f'{index}-{mode}.o'
            receipt_path = output / f'{index}-{mode}.receipt.json'
            allocation = output / f'{index}-{mode}.allocator.json'
            compiler = [str(root / '.lake/build/bin/lean-backend')] if mode == 'native-baseline' else [
                'lean', '-j1', '--root=' + str(source), '--run', str(source / 'FVTest/Backend/Main.lean')]
            args = [*compiler, str(path), str(obj), '--regalloc', 'regalloc2',
                '--stock-config', str(request_path), '--config-receipt', str(receipt_path),
                *([] if row['cleanup'] else ['--no-dead-cleanup'])]
            done = subprocess.run(args, cwd=root,
                env=dict(env, LEAN_REGALLOC_KEEP=str(allocation)), capture_output=True, text=True)
            (output / f'{index}-{mode}.log').write_text(done.stdout + done.stderr)
            receipt = json.loads(receipt_path.read_text())
            assert done.returncode == 3 and not obj.exists() and not allocation.exists()
            assert receipt['request'] == request and not receipt['configuration_accepted']
            assert 'tls_model=elf_gd' in receipt['error'], receipt
            results.append(dict(mode=mode, returncode=done.returncode, receipt=receipt,
                object_emitted=False, allocator_called=False))
        assert results[0]['receipt'] == results[1]['receipt']
        records.append(dict(function=row['function'], cleanup=row['cleanup'],
            original_path=str(path), source_sha256=row['original_sha256'], results=results))
    assert all(compare.digest(Path(path)) == digest for path, digest in expected.items())
    save('passed', sources=4, cases=8, accepted=0, rejected=8,
        source_hashes_exact=True, settings_unchanged=True,
        scope='Exact original requests retain the existing settings rejection. This is acceptance parity, not binary agreement or an official-suite measurement.')
except BaseException as error:
    save('failed', error=repr(error))
    raise
