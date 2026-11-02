from pathlib import Path
import datetime,hashlib,json,os,subprocess,sys
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';T=Path(__file__).resolve().parent;Q=T.parent;R=Q/'validation-package-v1';J=E/'892-joint-current-context-v2/package';L=T/'link-source-transport-audit-v1';L.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
A=J/'scripts/axiom-audit.py';published=subprocess.check_output(['git','show','37fc00cb91cf37557777f0664878a164c59587cf:scripts/axiom-audit.py'],cwd=B);assert A.read_bytes()==published
old=T/'shared-source-transport-proposal-v1/link-source-transport-contracts.lean';new=T/'shared-induction-proposal-v1/link-trap-ind-kernel-contracts.lean'
env=dict(os.environ)
for k in ['FV_LAKE_CACHE','FV_MEMCAP_OFF','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','LAKE_CACHE_DIR']:env.pop(k,None)
env.update(PATH=str(T/'tool-bin')+':/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+env['PATH'],WORKER_O_AUDIT_COMMAND_LOG=str(L/'actual-lean-commands.jsonl'),FV_ROOT=str(R),FV_MEMCAP='2G',FV_MEMCAP_STATS=str(L/'audit.mem'),FV_MEMCAP_UNIT='worker-o-real-repository-audits',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false')
argv=['python3',str(A),'--cwd',str(R),'--log-dir',str(L/'audit'),str(old),str(new)]
with (L/'summary.log').open('w') as stream:rc=subprocess.call([str(J/'scripts/memcap.sh'),*argv],cwd=R,env=env,stdout=stream,stderr=subprocess.STDOUT)
state=dict(status='passed' if rc==0 else 'failed',real_exit=rc,actual_unchanged_repository_auditor=str(A),auditor_sha256=sha(A),argv=argv,resource_wrapper_sha256=sha(T/'tool-bin/lake'),wrapper_only_adds_j1=True,actual_lean_commands=[json.loads(x) for x in (L/'actual-lean-commands.jsonl').read_text().splitlines()],audits={str(p):sha(p) for p in [old,new]},stats=(L/'audit.mem').read_text() if (L/'audit.mem').exists() else None,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(L/'receipt.json').write_text(json.dumps(state,indent=2)+'\n');print('real repository auditor exit',rc,flush=True);print((L/'summary.log').read_text(),flush=True)
if rc:raise SystemExit(rc)
import sys
sys.path.insert(0,str(Q));from axiom_records import parse_records
import re
old_sets={}
for path,expectedPath,count in [(old,T/'link-trap-old-audit-v1/exact-set-comparison.json',52),(new,T/'link-trap-ind-old-audit-v1/exact-set-comparison.json',29)]:
 actual=dict(parse_records((L/'audit'/(path.stem+'.log')).read_text()));assert len(actual)==count,(path,len(actual))
 expected=json.loads(expectedPath.read_text())['axiom_sets']
 for n,v in expected.items():assert actual[n]==v,(n,actual[n],v)
 for n,v in actual.items():assert set(v)<={'propext','Classical.choice','Quot.sound'},n
 old_sets.update(actual)
# Stop before :=, an equation clause, or a structure proof's where keyword.
def headers(source):
 out={}
 for m in re.finditer(r'^theorem ([\w\'.]+)',source,re.M):
  end=re.search(r' :=|\n  \|| where(?:\n|$)',source[m.start():]);assert end,m.group(1)
  out[m.group(1)]=source[m.start():m.start()+end.start()].rstrip()
 return out
counts={}
for name in ['LinkTrapCall','LinkTrapCallInd']:
 published=subprocess.check_output(['git','show','770e543c:FV/E2E/'+name+'.lean'],cwd=B,text=True);required=headers(published);actual=headers((R/('FV/E2E/'+name+'.lean')).read_text())
 for n,h in required.items():assert actual[n]==h,(name,n)
 counts[name]=len(required)
(L/'exact-set-comparison.json').write_text(json.dumps(dict(status='passed',axiom_sets=old_sets,roots=81,old60_exact=True,old_header_counts=counts,header_parser='Raw declaration header ends before :=, equation clause, or where; all roots retained.'),indent=2)+'\n')
