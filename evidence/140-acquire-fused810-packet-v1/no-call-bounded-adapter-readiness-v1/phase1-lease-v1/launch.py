from common import *
import sys
p=psutil.Process();save(D/'consumer-identity.json',{'pid':p.pid,'birth':p.create_time()})
while not (D/'permit.json').exists():
 if (D/'cancel.json').exists():sys.exit(143)
 s=json.loads((D/'state.json').read_text())
 if not live(s['owner'],s['owner_birth']):sys.exit(143)
 time.sleep(.1)
os.execv(sys.executable,[sys.executable,str(D/'gate.py')])
