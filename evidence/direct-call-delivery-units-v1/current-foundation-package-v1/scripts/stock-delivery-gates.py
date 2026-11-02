#!/usr/bin/env python3
"""Run explicit Stock delivery checks with durable, source-bound receipts.

Use plan/run/resume/report MANIFEST --root CHECKOUT --out EXTERNAL_DIRECTORY.
The manifest is a JSON object with packet, base, candidate, gates, and optional
inputs (glob patterns), tools (executable names), env, and baselines. Each gate
has id, argv, optional inputs/env/outputs/requires/forbids, and complete_inputs.
Only complete_inputs=true checks may be reused. The entire tracked working tree,
runner, manifest, effective environment and tool bytes are fingerprinted as well
as declared inputs; declare external tools/data/import outputs explicitly. Use
normal Lake builds for dependency keys. Commands are sequential and memcapped.

report validates evidence and never runs a compiler. Historical receipts listed
under historical_evidence are hashed and reported separately, never gate passes.
"""
import argparse
import datetime
import fcntl
import hashlib
import glob
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def identity(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def stamp():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def atomic_json(path, value):
    path = Path(path)
    fd, name = tempfile.mkstemp(prefix=path.name + '.', dir=path.parent)
    try:
        with os.fdopen(fd, 'w') as stream:
            json.dump(value, stream, indent=2, sort_keys=True)
            stream.write('\n')
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(name, path)
    finally:
        Path(name).unlink(missing_ok=True)


def git(root, *args):
    return subprocess.check_output(['git', *args], cwd=root).decode().strip()


def load_manifest(path):
    manifest = json.loads(Path(path).read_text())
    for name in ('packet', 'base', 'candidate', 'gates'):
        if name not in manifest:
            raise ValueError('missing manifest field: ' + name)
    ids = set()
    for gate in manifest['gates']:
        name = gate['id']
        if not re.fullmatch(r'[A-Za-z0-9_-]+', name) or name in ids:
            raise ValueError('invalid or duplicate gate id: ' + name)
        ids.add(name)
        argv = gate['argv']
        if not argv or not all(isinstance(a, str) for a in argv):
            raise ValueError('gate argv must be a nonempty string array')
        for field in ('requires', 'forbids'):
            for pattern in gate.get(field, []):
                re.compile(pattern)
    if not ids:
        raise ValueError('manifest has no gates')
    return manifest


def file_hashes(patterns, root, out):
    result = {}
    for pattern in patterns:
        pattern = pattern.replace('{out}', str(out)).replace('{root}', str(root))
        path = Path(pattern)
        matches = sorted(Path(p) for p in glob.glob(str(path if path.is_absolute() else root / path), recursive=True))
        files = [p for p in matches if p.is_file()]
        if not files:
            raise ValueError('input/output pattern matched no files: ' + pattern)
        for path in files:
            result[str(path.absolute())] = digest(path)
    return result


def environment(manifest, gate, out, root):
    env = dict(os.environ)
    env.update({k: str(v) for k, v in manifest.get('env', {}).items()})
    env.update({k: str(v) for k, v in gate.get('env', {}).items()})
    env.update(OMP_NUM_THREADS='2', OMP_THREAD_LIMIT='2', LEAN_NUM_THREADS='2', CARGO_BUILD_JOBS='2')
    env.setdefault('FV_MEMCAP', '8G')
    if env['FV_MEMCAP'] not in ('1G', '2G', '3G', '4G', '6G', '8G', '12G', '16G'):
        raise ValueError('FV_MEMCAP must be a supported cap no greater than16G')
    return {k: v.replace('{out}', str(out)).replace('{root}', str(root)) for k, v in env.items()}


def fingerprint(manifest, gate, root, out, details=None):
    if "_manifest_path" in manifest and digest(manifest["_manifest_path"]) != manifest["_manifest_sha256"]:
        raise ValueError("manifest changed during gate run")
    env = environment(manifest, gate, out, root)
    names = subprocess.check_output(['git', 'ls-files', '--cached', '--others', '--exclude-standard', '-z'], cwd=root).decode().split('\0')
    tracked = {}
    for name in names:
        if name:
            path = root / name
            tracked[name] = digest(path) if path.is_file() else None
    tools = {}
    argv = [a.replace('{out}', str(out)).replace('{root}', str(root)) for a in gate['argv']]
    if Path(argv[0]).name == 'lake-serial-build.py' or any(Path(a).name == 'lake-serial-build.py' for a in argv[1:2]):
        argv += ['--budget', '16G', '--max-jobs', '2', '--max-cap', '16G']
        env['FV_MEMCAP'] = '16G'
    for name in [argv[0], *manifest.get('tools', []), *gate.get('tools', [])]:
        path = shutil.which(name, path=env.get('PATH'))
        if path is None and (root / name).is_file():
            path = str(root / name)
        if not path:
            raise ValueError('tool is missing: ' + name)
        resolved = Path(path).resolve()
        tools[name] = {'path': str(resolved), 'sha256': digest(resolved)}
    body = {'tracked': tracked, 'declared': file_hashes(manifest.get('inputs', []) + gate.get('inputs', []), root, out),
            'tools': tools, 'environment': {k: identity(v) for k, v in env.items()
                if k not in ('_', 'SHLVL', 'CODEX_TOOL_CALL_ID')}, 'manifest': manifest,
            'runner_sha256': digest(__file__), 'root': str(root), 'gate': gate}
    if details is not None:
        details.update(body)
    return identity(body), env, argv


def valid_record(record, key, root, out):
    if record.get('state') != 'passed' or record.get('returncode') != 0 or record.get('input_key') != key:
        return False
    try:
        if digest(record['log']) != record['log_sha256']:
            return False
        outputs = file_hashes(record.get('output_patterns', []), root, out)
        return outputs == record.get('outputs', {})
    except (OSError, ValueError):
        return False


def historical(manifest, root, out):
    return file_hashes(manifest.get('historical_evidence', []), root, out)


def inspect(manifest, root, out):
    rows = []
    for gate in manifest['gates']:
        key, _, _ = fingerprint(manifest, gate, root, out)
        path = out / (gate['id'] + '.json')
        try:
            record = json.loads(path.read_text())
        except (OSError, ValueError):
            record = {}
        intact = valid_record(record, key, root, out)
        rows.append({'id': gate['id'], 'current_pass': intact,
                     'reusable': bool(gate.get('complete_inputs', False)) and intact,
                     'source_head': record.get('source_head'), 'input_key': key})
    return rows


def summary(manifest, root, out):
    rows = inspect(manifest, root, out)
    result = {'packet': manifest['packet'], 'utc': stamp(), 'head': git(root, 'rev-parse', 'HEAD'),
              'state': 'passed' if all(r['current_pass'] for r in rows) else 'incomplete',
              'gates': rows, 'historical_evidence': historical(manifest, root, out),
              'baselines': manifest.get('baselines', {})}
    return result


def execute(manifest, root, out, resume):
    historical(manifest, root, out)  # Validate references before starting work.
    for gate in manifest['gates']:
        details = {}
        key, env, argv = fingerprint(manifest, gate, root, out, details)
        atomic_json(out / (key + '.inputs.json'), details)
        path = out / (gate['id'] + '.json')
        if resume and gate.get('complete_inputs', False) and path.exists():
            try:
                old = json.loads(path.read_text())
                if valid_record(old, key, root, out):
                    print('reuse ' + gate['id'], flush=True)
                    continue
            except ValueError:
                pass
        # Unique attempt logs preserve earlier successful and failed evidence.
        attempt = time.time_ns()
        log = out / f"{gate['id']}-{attempt}.log"
        record = {'id': gate['id'], 'state': 'running', 'started': stamp(), 'argv': argv,
                  'source_head': git(root, 'rev-parse', 'HEAD'), 'input_key': key,
                  'log': str(log), 'output_patterns': gate.get('outputs', [])}
        atomic_json(path, record)
        atomic_json(out / f"{gate['id']}-{attempt}.json", record)
        started = time.monotonic()
        print('run ' + gate['id'], flush=True)
        try:
            with log.open('w') as stream:
                proc = subprocess.run([str(root / 'scripts/memcap.sh'), *argv], cwd=root,
                                      env=env, stdout=stream, stderr=subprocess.STDOUT)
            record['returncode'] = proc.returncode
            record['log_sha256'] = digest(log)
            text = log.read_text(errors='replace')
            if proc.returncode:
                raise ValueError('command exited ' + str(proc.returncode))
            for pattern in gate.get('requires', []):
                if not re.search(pattern, text, re.M):
                    raise ValueError('missing required output: ' + pattern)
            for pattern in [r'Error: index out of bounds', *gate.get('forbids', [])]:
                if re.search(pattern, text, re.M):
                    raise ValueError('forbidden output: ' + pattern)
            if fingerprint(manifest, gate, root, out)[0] != key:
                raise ValueError('inputs changed during gate')
            record['outputs'] = file_hashes(gate.get('outputs', []), root, out)
            record['state'] = 'passed'
        except Exception as error:
            record.update(state='failed', error=str(error))
        finally:
            record.update(finished=stamp(), seconds=time.monotonic()-started)
            atomic_json(out / f"{gate['id']}-{attempt}.json", record)
            atomic_json(path, record)
        if record['state'] != 'passed':
            raise ValueError(gate['id'] + ': ' + record['error'])
    # A reporting failure leaves each completed, independently resumable record.
    result = summary(manifest, root, out)
    atomic_json(out / 'receipt.json', result)
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['plan', 'run', 'resume', 'report'])
    parser.add_argument('manifest', type=Path)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args(argv)
    root, out = args.root.resolve(), args.out.resolve()
    if out == root or root in out.parents:
        parser.error('--out must be outside the checkout')
    try:
        manifest = load_manifest(args.manifest)
        manifest.update(_manifest_path=str(args.manifest.resolve()), _manifest_sha256=digest(args.manifest))
        if args.action in ['run', 'resume']:
            if args.action == 'run' and out.exists():
                raise ValueError('run requires a new output directory; use resume')
            out.mkdir(parents=True, exist_ok=True)
            with (out / '.lock').open('w') as lock:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                result = execute(manifest, root, out, args.action == 'resume')
        else:
            result = summary(manifest, root, out)
        print(json.dumps(result, indent=2))
        return 0 if args.action == 'plan' or result['state'] == 'passed' else 1
    except (OSError, ValueError, KeyError) as error:
        print(str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
