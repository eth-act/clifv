from pathlib import Path
import datetime
import fcntl
import hashlib
import json
import os
import shutil
import subprocess
import time

b = Path('/home/lee/clifv')
r = b / '.worktrees/stock-extending-production-20261031'
e = b / '.git/agent-evidence/stock-memory-20261029'
sha = '893eee2f6e85bd40e92be35420f3714fee0e74a9'
run_id = 41329973860
state = e / 'main870-ci-wave2-state-v2.json'
records = []
manifests = []
imported = set()
env = dict(os.environ)
env.update(json.loads((e / 'author-env-v1.json').read_text()))
env.update(FV_ROOT=str(r), FV_MEMCAP='1G', LEAN_NUM_THREADS='1',
           OMP_NUM_THREADS='1', OMP_THREAD_LIMIT='1')
env.update(LAKE_CACHE_DIR=env['FV_LAKE_CACHE'], LAKE_ARTIFACT_CACHE='true', LAKE_RESTORE_ARTIFACTS='true')

def api(path):
    return json.loads(subprocess.check_output(['gh', 'api', path], cwd=r, env=env, text=True))

def save(status, **extra):
    data = dict(status=status, source_sha=sha, run=run_id, records=records,
                manifests=manifests, imported_shards=sorted(imported), cache=env['FV_LAKE_CACHE'],
                utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                full_goal_complete=False, source_changed=False, **extra)
    temp = state.with_suffix('.tmp')
    temp.write_text(json.dumps(data, indent=2) + '\n')
    temp.replace(state)

# This job imports each successful shard without waiting for the slowest shard.
# It never imports an artifact from an unfinished or failed producer.
try:
    deadline = time.monotonic() + 12 * 3600
    while len(imported) < 10:
        metadata = api(f'repos/eth-act/clifv/actions/runs/{run_id}')
        assert metadata['head_sha'] == sha and metadata['event'] == 'push' and metadata['name'] == 'Full gate'
        jobs = api(f'repos/eth-act/clifv/actions/runs/{run_id}/jobs?per_page=100')['jobs']
        selected = [j for j in jobs if j['name'].startswith('Build wave 2 (')]
        assert len(selected) == 10
        failed = [j for j in selected if j['status'] == 'completed' and j['conclusion'] != 'success']
        assert not failed, 'A wave2 producer failed; retain already imported successful shards'
        available = api(f'repos/eth-act/clifv/actions/runs/{run_id}/artifacts?per_page=100')['artifacts']
        by_name = {item['name']: item for item in available}
        ready = []
        for shard in range(10):
            producer = [j for j in selected if j['name'] == f'Build wave 2 ({shard}) / shard {shard}']
            assert len(producer) == 1
            name = f'stage-w2-{shard}'
            if shard not in imported and producer[0]['status'] == 'completed' and producer[0]['conclusion'] == 'success' and name in by_name:
                ready.append((shard, name, by_name[name]['id'], producer[0]))
        if ready:
            assert shutil.disk_usage(b).free > 100 * 1024**3
            stage = e / ('main870-ci-wave2-batch-' + '-'.join(str(x[0]) for x in ready) + '-v2')
            with (e / 'main870-cache-import.lock').open('a+') as lock:
                fcntl.flock(lock, fcntl.LOCK_EX)
                stage.mkdir(exist_ok=False)
                save('running', phase='download', batch=[x[0] for x in ready])
                for shard, name, artifact_id, producer in ready:
                    item = api(f'repos/eth-act/clifv/actions/artifacts/{artifact_id}')
                    assert item['id'] == artifact_id and item['name'] == name and not item['expired']
                    assert item['workflow_run']['head_sha'] == sha and item['workflow_run']['id'] == run_id
                    assert item['workflow_run']['repository_id'] == 1391033036
                    assert item['size_in_bytes'] < 512 * 1024**2
                    records.append(dict(artifact=item, producer=producer))
                    subprocess.run(['gh', 'run', 'download', str(run_id), '--name', name,
                                    '--dir', str(stage / name)], cwd=r, env=env, check=True)
                    outputs = list((stage / name).rglob('outputs.jsonl'))
                    assert outputs
                    for index, path in enumerate(outputs):
                        data = path.read_bytes()
                        copy = e / f'main870-ci-wave2-{name}-outputs-{index}-v2.jsonl'
                        copy.write_bytes(data)
                        manifests.append(dict(artifact=artifact_id, path=str(copy),
                                              sha256=hashlib.sha256(data).hexdigest(),
                                              entries=max(0, len(data.splitlines()) - 1)))
                save('running', phase='additive-import', batch=[x[0] for x in ready])
                log = e / ('main870-ci-wave2-import-' + '-'.join(str(x[0]) for x in ready) + '-v2.log')
                with log.open('w') as output:
                    subprocess.run(['nice', '-n', '10', str(r / 'scripts/memcap.sh'), 'python3',
                                    'scripts/lake-unstage.py', str(stage)], cwd=r, env=env,
                                   stdout=output, stderr=subprocess.STDOUT, check=True)
                shutil.rmtree(stage)
                imported.update(x[0] for x in ready)
                save('waiting' if len(imported) < 10 else 'passed', phase='producer-jobs',
                     additive_only=True, stage_removed=True, memory_cap='1G')
                print('Imported successful wave2 shards:', sorted(imported), flush=True)
        if len(imported) == 10:
            break
        assert metadata['status'] != 'completed', 'Producer run ended before every required successful cache artifact arrived'
        assert time.monotonic() < deadline, 'Bounded observation deadline; do not infer producer failure'
        save('waiting', phase='producer-jobs', producer_status=[dict(id=j['id'], status=j['status'], conclusion=j['conclusion']) for j in selected])
        time.sleep(45)
except BaseException as error:
    save('failed', error=repr(error), successful_imports_preserved=True)
    raise
