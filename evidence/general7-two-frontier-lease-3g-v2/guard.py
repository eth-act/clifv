from common import D,restore
import json,os,psutil,time
s=json.loads((D/'state.json').read_text())
def live(pid,birth):
    try:
        p=psutil.Process(pid);return p.create_time()==birth and p.status()!=psutil.STATUS_ZOMBIE
    except psutil.NoSuchProcess:return False
(D/'guard-armed.json').write_text(json.dumps({'guard':os.getpid(),'owner':s['owner']}))
emergency=False
while not (D/'shares-restored.json').exists():
    if not live(s['owner'],s['owner_birth']):
        p=D/'consumer-identity.json'
        c=json.loads(p.read_text()) if p.exists() else None
        busy=c is not None and live(c['pid'],c['birth'])
        for f in Path(s['scope_parent']).glob('worker-o-general7-two3v2-*.scope/cgroup.procs'):
            try:busy=busy or bool(f.read_text().strip())
            except FileNotFoundError:pass
        if not busy:
            restore('independent guard after owner exit');emergency=True;break
    time.sleep(.2)
(D/'guard-receipt.json').write_text(json.dumps({'status':'released','emergency':emergency,'source_GiB':2,'acquire_GiB':1}))
