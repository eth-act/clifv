from pathlib import Path
import datetime, json, os, psutil, signal, time
D = Path(__file__).resolve().parent
def read():
    return json.loads((D / 'state.json').read_text())
def alive(pid, birth):
    try:
        p = psutil.Process(pid)
        return p.create_time() == birth and p.status() != psutil.STATUS_ZOMBIE
    except psutil.NoSuchProcess:
        return False
s = read()
(D / 'guard-armed.json').write_text(json.dumps({'guard': os.getpid(), 'owner': s['owner'], 'scheduler': s['scheduler']}))
emergency = False
while True:
    s = read()
    if s.get('same_controller_resumed'):
        break
    if not alive(s['owner'], s['owner_birth']):
        identity = D / 'consumer-identity.json'
        if identity.exists():
            c = json.loads(identity.read_text())
            if alive(c['pid'], c['birth']):
                time.sleep(.5)
                continue
        busy = False
        for pattern in ['worker-o-validated-W23-*.scope/cgroup.procs', f"fvb-{s['scheduler']}-*.scope/cgroup.procs"]:
            for f in Path(s['scope_parent']).glob(pattern):
                try:
                    busy |= bool(f.read_text().strip())
                except FileNotFoundError:
                    pass
        if not busy:
            if alive(s['scheduler'], s['scheduler_birth']):
                p = psutil.Process(s['scheduler'])
                if p.status() == psutil.STATUS_STOPPED:
                    os.kill(p.pid, signal.SIGCONT)
                    emergency = True
            break
    time.sleep(.5)
(D / 'guard-receipt.json').write_text(json.dumps({'status': 'completed', 'emergency_resume': emergency, 'scheduler': s['scheduler'], 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}))
