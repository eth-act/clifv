from pathlib import Path
import os,sys,subprocess,json,hashlib,datetime,signal,time
D=Path(__file__).resolve().parent
root=D/'fake-process-test';assert not root.exists();root.mkdir();(root/'FV').mkdir();(root/'scripts').mkdir();(root/'bin').mkdir()
(root/'lakefile.toml').write_text('name = "mock_process_test"\n[[lean_lib]]\nname = "FV"\n')
for name in ['A','B','C']:(root/'FV'/f'{name}.lean').write_text('-- Process-control fixture. No Lean compiler runs.\n')
(root/'profile.tsv').write_text('FV.A\t1024\t1000\nFV.B\t1024\t900\nFV.C\t1024\t1\n')
(root/'scripts/memcap.sh').write_text('#!/bin/sh\nexec "$@"\n');(root/'scripts/memcap.sh').chmod(0o755)
(root/'bin/lake').write_text('''#!/usr/bin/env python3
from pathlib import Path
import os,sys,time,signal
r=Path.cwd();n=sys.argv[-1]
def event(s):
 with (r/'events.jsonl').open('a') as f:f.write(s+'\\n')
def stop(s,f):event('SIGNAL '+n+' '+str(s));sys.exit(99)
signal.signal(signal.SIGTERM,stop)
event('START '+n+' '+os.environ.get('FV_MEMCAP',''))
if n=='FV.A':
 time.sleep(0.2);event('FAIL '+n);sys.exit(1)
time.sleep(2.2);event('SUCCESS '+n);print('Built '+n)
''');(root/'bin/lake').chmod(0o755)
env=dict(os.environ,PATH=str(root/'bin')+':'+os.environ['PATH']);env.pop('FV_LAKE_CACHE',None);env.pop('LAKE_CACHE_DIR',None)
argv=[sys.executable,str(D/'lake-serial-build-drain.py'),'--root',str(root),'--out',str(root/'logs'),'--budget','12G','--max-jobs','2','--min-cap','4G','--default-cap','12G','--max-cap','12G','--margin','2','--heavy','16G','--profile',str(root/'profile.tsv'),'--no-dedup','--no-batch-check','--no-slice-gate','--drift-time-scale','0','FV']
with (D/'test-drain.log').open('w') as f:r=subprocess.run(argv,env=env,stdout=f,stderr=subprocess.STDOUT)
events=(root/'events.jsonl').read_text().splitlines();assert r.returncode!=0
assert any(x.startswith('FAIL FV.A') for x in events),events
assert any(x.startswith('SUCCESS FV.B') for x in events),events
assert not any(x.startswith('SIGNAL') for x in events),events
assert not any('FV.C' in x for x in events),events
assert len(list((root/'logs/failed-attempts').glob('*/attempt.json')))==1
receipt={'status':'passed_process_control_simulation','no_Lean_or_Lake_compiler_ran':True,'no_real_cache_created':True,'first_failure_preserved':True,'healthy_peer_completed_without_signal':True,'third_job_not_launched_after_failure':True,'events':events,'returncode':r.returncode,'helper_sha256':hashlib.sha256((D/'lake-serial-build-drain.py').read_bytes()).hexdigest(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(D/'test-drain-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
