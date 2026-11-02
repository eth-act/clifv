from pathlib import Path
import json,os,psutil,subprocess,time
D=Path(__file__).resolve().parent;E=D.parent;state=D/'provider-large-slot-v1/state.json';backup=E/'production-current-context-backup-v10.json';owner=json.loads((D/'priority-handoff-owner-v1.json').read_text())
while True:
 s=json.loads(state.read_text())
 if s.get('same_controller_resumed'):
  assert s['status']=='passed',('Priority provider failed; preserve all outputs and inspect',s);break
 try:p=psutil.Process(owner['pid']);assert p.create_time()==owner['birth'] and p.status()!='zombie'
 except (psutil.NoSuchProcess,AssertionError):raise RuntimeError('Priority handoff ended without a passing receipt; inspect the resume guard')
 time.sleep(2)
assert backup.is_file() and json.loads(backup.read_text())['remote_verified'],'The temporary1GiB backup share must finish before reuse'
print('Same scheduler resumed; backup exited; final isolated1GiB gate starts',flush=True)
env=dict(os.environ,WORKER_O_PROOF_SLOT_GRANTED='foundation-1G')
subprocess.run(['python3',str(D/'run-current-foundation-v4.py')],env=env,check=True)
subprocess.run(['python3',str(D/'publish-foundation-v1.py')],check=True)
