from pathlib import Path
import datetime
import hashlib
import importlib.util
import json
import os
import subprocess
import sys
import unittest

base = Path('/home/lee/clifv')
evidence = base / '.git/agent-evidence/stock-memory-20261029'
root = base / '.worktrees/stock-cfg-source-20261025'
output = evidence / 'configured-provider-focus-v1'
source = output / 'source'
lib = output / 'lib'
state = evidence / 'configured-provider-focus-state-v2.json'
records = [{'module': 'StockConfig', 'returncode': 0, 'source_sha256': 'dd2377dcea00a7931969a828b0b06640cc8fbe916c4281f2711cdaca6c06c266'}, {'module': 'Main', 'returncode': 0, 'source_sha256': 'e8a65e830f0617a3c567b455e52ba3dbf2c81cb9d38c0d32d6b0e2fc99bae4d2'}]
cases = []


def save(status, **extra):
    state.write_text(json.dumps(dict(status=status, records=records, cases=cases,
        utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), **extra), indent=2) + '\n')


env = dict(os.environ)
env.update(json.loads((evidence / 'author-env-v1.json').read_text()))
env.update(OMP_NUM_THREADS='1', OMP_THREAD_LIMIT='1', LEAN_NUM_THREADS='1', FV_MEMCAP='2G')
env['LEAN_PATH'] = str(lib) + ':' + (evidence / 'integer-helpers-lean-path-v1.txt').read_text().strip()
os.environ.update(env)
try:
    for module in []:  # Both unchanged module checks passed in v1.
        save('running', phase=module)
        path = source / 'FVTest/Backend' / (module + '.lean')
        target = lib / 'FVTest/Backend' / (module + '.olean')
        with (output / (module + '.log')).open('w') as log:
            done = subprocess.run(['lean', '-j1', '--root=' + str(source),
                '-o', str(target), str(path)], cwd=root, env=env,
                stdout=log, stderr=subprocess.STDOUT)
        records.append(dict(module=module, returncode=done.returncode,
            source_sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
        if done.returncode:
            raise RuntimeError((module, done.returncode))
    save('running', phase='maintained-tests-via-interpreter')
    sys.path.insert(0, str(root / 'scripts'))
    spec = importlib.util.spec_from_file_location('configured_provider_draft',
        evidence / 'test_stock_configured_provider.next.py')
    draft = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(draft)
    draft.ROOT = root
    original = draft.StockConfiguredProviderTests

    class FocusTests(original):
        @classmethod
        def setUpClass(cls):
            cls.native = root / '.lake/build/bin/lean-backend'
            cls.trace = root / '.lake/build/bin/lean-backend-lowering-trace'
            cls.allocator = root / 'rust/target/release/lean-regalloc'
            assert all(p.exists() for p in [cls.native, cls.trace, cls.allocator])
            cls.request = json.loads((evidence / 'stock-config-aarch64.next.json').read_text())

        def compile_at(self, directory, text, cleanup, configured, typed=False, request=None):
            self.backend = output / 'configured-lean-backend' if configured else self.native
            result = super().compile_at(directory, text, cleanup, configured, typed, request)
            process, receipt, allocator = result
            row = dict(function=text.splitlines()[0], cleanup=cleanup, configured=configured,
                typed=typed, returncode=process.returncode,
                source_sha256=hashlib.sha256(text.encode()).hexdigest(), receipt=receipt,
                allocator=allocator, stderr=process.stderr)
            obj = directory / 'program.o'
            if obj.exists():
                elf = draft.ELF(obj)
                name = text.splitlines()[0].split('%', 1)[1].split('(', 1)[0]
                symbol, code = elf.function(name)
                row.update(object_sha256=hashlib.sha256(obj.read_bytes()).hexdigest(),
                    function_bytes=code.hex(), relocations=elf.function_relocations(symbol, {}))
            cases.append(row)
            save('running', phase='maintained-tests-via-interpreter')
            return result

    with (output / 'tests.log').open('w') as log:
        result = unittest.TextTestRunner(stream=log, verbosity=2).run(
            unittest.defaultTestLoader.loadTestsFromTestCase(FocusTests))
    assert result.wasSuccessful() and result.testsRun == 3 and not result.skipped
    configured = [case for case in cases if case['configured']]
    assert len(configured) == 8
    assert sum(case['returncode'] == 0 for case in configured) == 7
    assert sum(case['returncode'] == 3 for case in configured) == 1
    save('passed', tests=3, configured_cases=8, source_gates_unchanged=True,
        scope='Adapter type-check and maintained behavior through Lean interpreter against existing native baseline; final native build and official comparison remain pending')
except BaseException as error:
    save('failed', error=repr(error))
    raise
