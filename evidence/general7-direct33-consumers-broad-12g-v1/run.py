from pathlib import Path
import datetime, fcntl, hashlib, json, os, psutil, select, signal, subprocess, sys, time
D = Path(__file__).resolve().parent
from restore_config import restore_config
E = D.parent
B = Path('/home/lee/clifv')
W = E / 'direct-call-store-live-packet-v1/fault-world-w-prep-v1'
K = W / 'linked-source-current-main-v1'
N = E / 'stock-current-main-full-gate-v6'
P = E / '892-joint-current-context-v2/package'
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def live(p):
    try:
        return p.is_running() and p.status() != psutil.STATUS_ZOMBIE
    except psutil.NoSuchProcess:
        return False
def arguments(p):
    try:
        return p.cmdline()
    except (psutil.NoSuchProcess, psutil.ZombieProcess):
        return []
def wait(p):
    try:
        fd = os.pidfd_open(p.pid)
    except ProcessLookupError:
        return
    try:
        select.select([fd], [], [])
    finally:
        os.close(fd)
lock = (D / 'owner.lock').open('a+')
fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
assert not (D / 'state.json').exists()
for other in psutil.process_iter(['pid', 'cmdline','uids']):
    if other.info['uids'] is None or other.info['uids'].real != os.getuid(): continue
    args = other.info['cmdline'] or []
    assert not any(str(E / 'backup-reviewed-handoff-') in a for a in args), ('A backup is active', other.pid)
Q = E / 'general7-main-candidate-v1/direct33-remaining-kernel-cone-v1'
assert sha(Q / 'manifest.json') == '8e06b3066f562546b31736b7e57f529d26ee2f8b0ff34ee118d08af3c2dde411'
assert sha(D / 'gate.py') == 'fc527bc2beeecdad87bbc72e94a2a495605be47f835cad27e5ed42a8c907e0f8'
ns = json.loads((N / 'execution-state.json').read_text())
assert ns['status'] == 'running_normal'
pid = ns['active_scheduler']
proc = psutil.Process(pid)
birth = proc.create_time()
assert str(E / 'broad-two-job-scheduling-proposal-v1/lake-serial-build-drain.py') in proc.cmdline()
scope = Path(f'/sys/fs/cgroup/user.slice/user-{os.getuid()}.slice/user@{os.getuid()}.service/clifv.slice')
assert scope.is_dir()
state = {'status': 'arming_guard', 'owner': os.getpid(), 'owner_birth': psutil.Process().create_time(), 'scheduler': pid, 'scheduler_birth': birth, 'scope_parent': str(scope), 'same_controller_resumed': False, 'signals_to_compilers': [], 'source_share_release': 'source2GiB and acquire1GiB remain active;priority replaces broad12GiB', 'allocation': 'exclusive12GiB priority providers;broad controller paused;source2GiB/acquire1GiB;no backup', 'full_goal_complete': False, 'config_plan_sha256':sha(D/'config-restoration.json')}
def save():
    state['utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    q = D / 'state.tmp'
    q.write_text(json.dumps(state, indent=2) + '\n')
    os.replace(q, D / 'state.json')
def busy():
    for f in scope.glob('worker-o-General7-consumer33-*.scope/cgroup.procs'):
        try:
            if f.read_text().strip():
                return True
        except FileNotFoundError:
            pass
    return False
save()
subprocess.run(['ai-coord', 'watch', '--label', 'General7-consumer33-broad-resume-v1', '--', 'python3', str(D / 'guard.py')], cwd=B, check=True)
for _ in range(100):
    if (D / 'guard-armed.json').exists():
        break
    time.sleep(.1)
else:
    raise RuntimeError('Independent guard did not arm')
paused = False
consumer = None
signal.signal(signal.SIGTERM, lambda *_: sys.exit(143))
try:
    initial = [p for p in proc.children() if live(p)]
    state['boundary_jobs'] = [{'pid': p.pid, 'args': arguments(p)} for p in initial]
    state['status'] = 'waiting_natural_boundary'
    save()
    for child in initial:
        wait(child)
    assert proc.is_running() and proc.create_time() == birth
    os.kill(pid, signal.SIGSTOP)
    paused = True
    state['controller_paused'] = True
    save()
    while True:
        direct = [p for p in proc.children() if live(p)]
        queries = []
        for p in direct:
            try:
                if '--no-build' in p.cmdline() or 'query' in p.cmdline():
                    queries.append(p)
            except psutil.NoSuchProcess:
                pass
        if queries:
            os.kill(pid, signal.SIGCONT)
            paused = False
            for p in queries:
                wait(p)
            os.kill(pid, signal.SIGSTOP)
            paused = True
            continue
        children = [p for p in proc.children(recursive=True) if live(p)]
        if not children:
            break
        for p in children:
            wait(p)
    assert proc.status() == psutil.STATUS_STOPPED
    for f in scope.glob(f'fvb-{pid}-*.scope/cgroup.procs'):
        try:
            assert not f.read_text().strip(), str(f)
        except FileNotFoundError:
            pass
    sys.path.insert(0, str(N))
    from preflight import check
    check(P, N / 'release.json')
    release = {'approved': True, 'allocation': '12G', 'broad_controller_pid': pid, 'manifest_sha256': sha(Q / 'manifest.json'), 'script_sha256': sha(D / 'gate.py'), 'scheduler_birth': birth, 'source_share_release': state['source_share_release']}
    assert not (D / 'command-release-v1.json').exists()
    (D / 'command-release-v1.json').write_text(json.dumps(release, indent=2) + '\n')
    consumer = subprocess.Popen([sys.executable, str(D / 'launch.py')], cwd=B, stdout=(D / 'consumer-command.log').open('w'), stderr=subprocess.STDOUT)
    for _ in range(100):
        if (D / 'consumer-identity.json').exists():
            break
        time.sleep(.1)
    else:
        raise RuntimeError('Consumer identity did not arm')
    identity = json.loads((D / 'consumer-identity.json').read_text())
    assert identity['pid'] == consumer.pid
    state.update(status='running_sequential_consumers', consumer=identity)
    save()
    (D / 'permit.json').write_text(json.dumps({'approved': True, 'manifest_sha256': release['manifest_sha256']}))
    rc = consumer.wait()
    state['consumer_exit'] = rc
    save()
    assert rc == 0, ('Inspect exact consumer diagnostic; no unchanged retry', rc)
    check(P, N / 'release.json')
    state['status'] = 'passed'
    save()
except BaseException as exc:
    state.update(status='failed_inspect_exact_diagnostic', error=repr(exc))
    save()
    raise
finally:
    if consumer is not None and consumer.poll() is None:
        if not (D / 'permit.json').exists():
            (D / 'cancel.json').write_text('{"cancelled_before_compiler_launch":true}\n')
        consumer.wait()
    if paused:
        while busy():
            time.sleep(.5)
        assert psutil.Process(pid).create_time() == birth
        state['configuration_restoration']=restore_config(D)
        save()
        os.kill(pid, signal.SIGCONT)
        state.update(same_controller_resumed=True, restored_allocation='broad12GiB/source2GiB/acquire1GiB/orchestration1GiB')
        save()
        print('Resumed the same broad scheduler', pid, flush=True)
