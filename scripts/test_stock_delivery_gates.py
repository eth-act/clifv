"""Exercise failure, source provenance and recovery with real subprocesses."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location('delivery', Path(__file__).with_name('stock-delivery-gates.py'))
G = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(G)


class DeliveryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.root = self.base / 'repo'
        self.root.mkdir()
        scripts = self.root / 'scripts'
        scripts.mkdir()
        memcap = scripts / 'memcap.sh'
        memcap.write_text('#!/bin/sh\nexec "$@"\n')
        memcap.chmod(0o755)
        (self.root / 'source').write_text('original')
        for args in [('init', '-q'), ('add', '.'), ('-c', 'user.name=test', '-c', 'user.email=test@example.org', 'commit', '-qm', 'fixture')]:
            subprocess.run(['git', *args], cwd=self.root, check=True)
        self.out = self.base / 'out'
        self.manifest = {'packet': 'fixture', 'base': G.git(self.root, 'rev-parse', 'HEAD'),
                         'candidate': G.git(self.root, 'rev-parse', 'HEAD'), 'gates': [self.gate()]}

    def gate(self, code=None, **extra):
        if code is None:
            code = "from pathlib import Path; p=Path('{out}/count'); p.write_text(p.read_text()+'x' if p.exists() else 'x'); print('verified')"
        return {'id': 'check', 'argv': [sys.executable, '-c', code],
                'complete_inputs': True, 'requires': ['^verified$'], **extra}

    def run_gates(self, resume=False):
        self.out.mkdir(exist_ok=True)
        return G.execute(self.manifest, self.root, self.out, resume)

    def count(self):
        return (self.out / 'count').read_text()

    def test_success_resume_and_original_provenance(self):
        result = self.run_gates()
        head = result['gates'][0]['source_head']
        # An empty commit changes HEAD but not any actual input bytes.
        subprocess.run(['git', '-c', 'user.name=test', '-c', 'user.email=test@example.org',
                        'commit', '--allow-empty', '-qm', 'metadata'], cwd=self.root, check=True)
        result = self.run_gates(True)
        self.assertEqual(self.count(), 'x')
        self.assertEqual(result['gates'][0]['source_head'], head)
        self.assertNotEqual(result['head'], head)

    def test_command_failure_stops_following_gate(self):
        self.manifest['gates'] = [self.gate("import sys; print('verified'); sys.exit(7)"),
                                  dict(self.gate(), id='never')]
        with self.assertRaisesRegex(ValueError, 'exited 7'):
            self.run_gates()
        record = json.loads((self.out / 'check.json').read_text())
        self.assertEqual(record['returncode'], 7)
        self.assertEqual(record['state'], 'failed')
        self.assertFalse((self.out / 'never.json').exists())

    def test_success_exit_with_runtime_panic_fails(self):
        self.manifest['gates'] = [self.gate("print('verified'); print('Error: index out of bounds')")]
        with self.assertRaisesRegex(ValueError, 'forbidden output'):
            self.run_gates()

    def test_missing_assertion_fails(self):
        self.manifest['gates'] = [self.gate("print('nothing verified')")]
        with self.assertRaisesRegex(ValueError, 'missing required output'):
            self.run_gates()

    def test_changed_tracked_input_reruns(self):
        self.run_gates()
        (self.root / 'source').write_text('changed')
        self.assertEqual(G.summary(self.manifest, self.root, self.out)['state'], 'incomplete')
        self.run_gates(True)
        self.assertEqual(self.count(), 'xx')

    def test_tool_call_identity_does_not_force_reexecution(self):
        self.run_gates()
        with patch.dict(os.environ, CODEX_TOOL_CALL_ID='next-call'):
            self.run_gates(True)
        self.assertEqual(self.count(), 'x')

    def test_new_untracked_source_invalidates(self):
        self.run_gates()
        (self.root / 'new-source.lean').write_text('def x := 1')
        self.run_gates(True)
        self.assertEqual(self.count(), 'xx')

    def test_external_input_and_environment_invalidation(self):
        data = self.base / 'external'
        data.write_text('one')
        self.manifest['inputs'] = [str(data)]
        self.run_gates()
        data.write_text('two')
        self.run_gates(True)
        with patch.dict(os.environ, STOCK_TEST_OPTION='different'):
            self.run_gates(True)
        self.assertEqual(self.count(), 'xxx')

    def test_corrupted_log_reruns_and_keeps_attempts(self):
        self.run_gates()
        record = json.loads((self.out / 'check.json').read_text())
        Path(record['log']).write_text('corrupt')
        self.run_gates(True)
        self.assertEqual(self.count(), 'xx')
        self.assertEqual(len(list(self.out.glob('check-*.json'))), 2)

    def test_corrupted_output_reruns(self):
        self.manifest['gates'][0]['outputs'] = ['{out}/count']
        self.run_gates()
        (self.out / 'count').write_text('tampered')
        self.run_gates(True)
        self.assertEqual(self.count(), 'tamperedx')

    def test_unknown_dependencies_never_reuse(self):
        self.manifest['gates'][0].pop('complete_inputs')
        self.run_gates()
        self.run_gates(True)
        self.assertEqual(self.count(), 'xx')

    def test_reporting_failure_preserves_pass_and_resume_does_not_reexecute(self):
        write = G.atomic_json
        def fail_receipt(path, value):
            if Path(path).name == 'receipt.json':
                raise OSError('injected reporting failure')
            write(path, value)
        with patch.object(G, 'atomic_json', side_effect=fail_receipt):
            with self.assertRaisesRegex(OSError, 'reporting failure'):
                self.run_gates()
        record = json.loads((self.out / 'check.json').read_text())
        self.assertEqual(record['state'], 'passed')
        self.assertEqual(G.summary(self.manifest, self.root, self.out)['state'], 'passed')
        self.run_gates(True)
        self.assertEqual(self.count(), 'x')

    def test_historical_receipt_is_separate_and_not_a_gate_pass(self):
        history = self.base / 'historic.json'
        history.write_text('{"state":"passed","head":"old"}')
        self.manifest['historical_evidence'] = [str(history)]
        result = G.summary(self.manifest, self.root, self.out)
        self.assertEqual(result['state'], 'incomplete')
        self.assertEqual(result['historical_evidence'][str(history)], G.digest(history))
        self.assertFalse(result['gates'][0]['current_pass'])

    def test_inputs_changing_during_command_fail(self):
        code = "from pathlib import Path; Path('source').write_text('changed'); print('verified')"
        self.manifest['gates'] = [self.gate(code)]
        with self.assertRaisesRegex(ValueError, 'inputs changed during gate'):
            self.run_gates()

    def test_missing_declared_input_fails_before_execution(self):
        self.manifest['inputs'] = [str(self.base / 'missing')]
        with self.assertRaisesRegex(ValueError, 'matched no files'):
            self.run_gates()
        self.assertFalse((self.out / 'count').exists())

    def test_scheduler_resource_limits_are_enforced(self):
        self.manifest['gates'][0]['argv'] = [sys.executable, 'scripts/lake-serial-build.py', 'FV', '--max-cap', '32G']
        _, env, argv = G.fingerprint(self.manifest, self.manifest['gates'][0], self.root, self.out)
        self.assertEqual(argv[-6:], ['--budget', '16G', '--max-jobs', '2', '--max-cap', '16G'])
        self.assertEqual(env['FV_MEMCAP'], '16G')


if __name__ == '__main__':
    unittest.main()
