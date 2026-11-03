from pathlib import Path
import json, os, psutil, sys, time
D = Path(__file__).resolve().parent
p = psutil.Process()
(D / 'consumer-identity.json').write_text(json.dumps({'pid': p.pid, 'birth': p.create_time()}))
while not (D / 'permit.json').exists():
    if (D / 'cancel.json').exists():
        sys.exit(143)
    s = json.loads((D / 'state.json').read_text())
    try:
        owner = psutil.Process(s['owner'])
        assert owner.create_time() == s['owner_birth'] and owner.status() != psutil.STATUS_ZOMBIE
    except (psutil.NoSuchProcess, AssertionError):
        sys.exit(143)
    time.sleep(.1)
os.execv(sys.executable, [sys.executable, str(D / 'gate.py')])
