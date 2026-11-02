from pathlib import Path
import subprocess,sys
F=Path(__file__).resolve().parent
def run(script,*args):return subprocess.run([sys.executable,str(F/script),*args]).returncode
for label,version in [('arminstfoot',11),('step',12)]:
 assert run('query-'+label+'-key-v1.py')==0
 assert run('recover-'+label+'-native-v1.py')==0
 rc=run('verify-access-v'+str(version)+'.py','--attempt','armfault-provider-normal-v'+str(version),'--preflight')
 if rc==0:break
 assert version==11,'Stop on missing or stale final context'
 log=(F/'runs/armfault-provider-normal-v11/normal-import-check.log').read_text()
 errors=[line for line in log.splitlines() if '✖' in line]
 assert len(errors)==1 and 'FV.ArmFault.Step' in errors[0],errors
