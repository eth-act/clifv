from pathlib import Path
import datetime, fcntl, hashlib, json, os, psutil, select, signal, subprocess, sys, time
D = Path(__file__).resolve().parent
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
for other in psutil.process_iter(['pid', 'cmdline']):
    args = other.info['cmdline'] or []
    assert not any(str(E / 'backup-reviewed-handoff-') in a for a in args), ('A backup is active', other.pid)
assert sha(K / 'consumer-input-manifest-v1.json') == '494cbdb09a64b98c08ec8a233c6d0bd216b643034b694b8aa0322fb0d62a8d56'
assert sha(W / 'verify-linked-source-consumers-3g-v1.py') == '71f5bdc6f22883698c485602ef67b8645b0857a985fa8f17987bec6b955fa3f4'
assert sha(K / 'consumer-preflight-v1/receipt.json') == '0a60bab397072e4e908839949a7294e5c4de3d5dda44cfd561f217d2b2207ffb'
m = json.loads((K / 'consumer-input-manifest-v1.json').read_text())
peak = m['baseline_peak']
assert sha(Path(peak['path'])) == peak['sha256'] and peak['exit'] == 0 and peak['LinkArm_KiB'] == 2453292
ns = json.loads((N / 'execution-state.json').read_text())
assert ns['status'] == 'running_normal'
pid = ns['active_scheduler']
proc = psutil.Process(pid)
birth = proc.create_time()
assert str(E / 'broad-two-job-scheduling-proposal-v1/lake-serial-build-drain.py') in proc.cmdline()
scope = Path(f'/sys/fs/cgroup/user.slice/user-{os.getuid()}.slice/user@{os.getuid()}.service/clifv.slice')
assert scope.is_dir()
state = {'status': 'arming_guard', 'owner': os.getpid(), 'owner_birth': psutil.Process().create_time(), 'scheduler': pid, 'scheduler_birth': birth, 'scope_parent': str(scope), 'same_controller_resumed': False, 'signals_to_compilers': [], 'source_share_release': 'source_guarantees explicitly released 2GiB; no compiler or verifier', 'allocation': '3GiB source consumers; broad compilation paused; acquire1GiB; no backup', 'full_goal_complete': False}
def save():
    state['utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    q = D / 'state.tmp'
    q.write_text(json.dumps(state, indent=2) + '\n')
    os.replace(q, D / 'state.json')
def busy():
    for f in scope.glob('worker-o-source-consumer-*.scope/cgroup.procs'):
        try:
            if f.read_text().strip():
                return True
        except FileNotFoundError:
            pass
    return False
save()
subprocess.run(['ai-coord', 'watch', '--label', 'linked-source-consumer-resume-guard-v1', '--', 'python3', str(D / 'guard.py')], cwd=B, check=True)
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
    release = {'approved': True, 'allocation': '3G', 'broad_controller_pid': pid, 'manifest_sha256': sha(K / 'consumer-input-manifest-v1.json'), 'script_sha256': sha(W / 'verify-linked-source-consumers-3g-v1.py'), 'scheduler_birth': birth, 'source_share_release': state['source_share_release']}
    assert not (K / 'consumer-release-v1.json').exists()
    (K / 'consumer-release-v1.json').write_text(json.dumps(release, indent=2) + '\n')
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
        os.kill(pid, signal.SIGCONT)
        state.update(same_controller_resumed=True, restored_allocation='broad12GiB/source2GiB/acquire1GiB/orchestration1GiB')
        save()
        print('Resumed the same broad scheduler', pid, flush=True)
