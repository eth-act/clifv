from pathlib import Path
import datetime
import json
import os
import shutil
import subprocess

base = Path('/home/lee/clifv')
root = base / '.worktrees/stock-memory-delivery-20261030'
evidence = base / '.git/agent-evidence/stock-memory-20261029'
stage = evidence / 'main5018-ci-wave2-stages-v1'
state = evidence / 'main5018-ci-wave2-state-v1.json'
expected_sha = '5018b9509dc124154dbe08a5bd85862595d8eab7'
artifacts = [(13014151380, 'stage-w2-0'), (13016702646, 'stage-w2-1'),
             (13017369838, 'stage-w2-2'), (13018826212, 'stage-w2-3'),
             (13013245463, 'stage-w2-4'), (13016018299, 'stage-w2-5'),
             (13018352855, 'stage-w2-6'), (13017660322, 'stage-w2-9')]
records = []


def save(status, **extra):
    state.write_text(json.dumps(dict(status=status,
        utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        records=records, **extra), indent=2) + '\n')


env = dict(os.environ)
env.update(json.loads((evidence / 'author-env-v1.json').read_text()))
env.update(FV_ROOT=str(root), FV_MEMCAP='1G', OMP_NUM_THREADS='1',
           OMP_THREAD_LIMIT='1', LEAN_NUM_THREADS='1')
save('running', phase='metadata')
try:
    assert shutil.disk_usage(base).free > 100 * 1024**3
    stage.mkdir(exist_ok=False)
    for artifact, name in artifacts:
        metadata = json.loads(subprocess.check_output([
            'gh', 'api', f'repos/eth-act/clifv/actions/artifacts/{artifact}']))
        assert metadata['id'] == artifact and metadata['name'] == name
        assert not metadata['expired']
        assert metadata['workflow_run']['head_sha'] == expected_sha
        records.append(metadata)
        save('running', phase='download', artifact=artifact)
        subprocess.run(['gh', 'run', 'download', str(metadata['workflow_run']['id']),
                        '--name', name, '--dir', str(stage / name)],
                       cwd=root, env=env, check=True)
        assert list((stage / name).rglob('outputs.jsonl'))
    save('running', phase='additive-import')
    with (evidence / 'main5018-ci-wave2-import-v1.log').open('w') as log:
        subprocess.run(['python3', 'scripts/lake-unstage.py', str(stage)],
                       cwd=root, env=env, stdout=log,
                       stderr=subprocess.STDOUT, check=True)
    shutil.rmtree(stage)
    save('passed', additive_only=True, stage_removed=True,
         source_changed=False, artifact_count=len(records),
         memory_cap='1G', temporary_loan_requires_return=True)
except BaseException as error:
    save('failed', error=repr(error), staging_preserved=stage.exists())
    raise
