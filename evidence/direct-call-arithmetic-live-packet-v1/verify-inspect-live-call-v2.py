from pathlib import Path
import hashlib,json,os,re,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';Q=E/'direct-call-arithmetic-live-packet-v1';V=B/'.worktrees/stock-extending-production-20261031';R=Q/'validation-package-v1';logs=Q/'inspect-live-call-v2';logs.mkdir();lib=R/'.lake/build/lib/lean';assert lib.is_dir()
base=json.loads((Q/'predecessor-source-context-v1.json').read_text());assert base['carrier_head']==subprocess.check_output(['git','rev-parse','HEAD'],cwd=V,text=True).strip()
ref=base['immutable_production'];sources={};dag={};todo=['FV/Backend/Lowering/StockArithmetic.lean','FV/Backend/LinearScan.lean','FV/Clif/Parse.lean']
while todo:
 n=todo.pop()
 if n in sources:continue
 data=subprocess.check_output(['git','show',ref+':'+n],cwd=B);assert (V/n).read_bytes()==data,('carrier dependency source changed',n)
 sources[n]=hashlib.sha256(data).hexdigest();deps=[m.replace('.','/')+'.lean' for m in re.findall(r'^import\s+([\w.]+)',data.decode(),re.M) if m.startswith(('FV.','FVTest.'))];dag[n]=deps;todo.extend(set(deps)-sources.keys())
 for suffix in ['.olean','.olean.private','.olean.server','.ilean']:
  src=V/'.lake/build/lib/lean'/Path(n).with_suffix(suffix);dst=lib/Path(n).with_suffix(suffix)
  if src.exists():dst.parent.mkdir(parents=True,exist_ok=True);
   if not dst.exists():os.link(src,dst)
for n,h in base['configs'].items():
 data=(V/n).read_bytes();assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==h;(R/n).write_bytes(data)
keys={}
def key(n):
 if n not in keys:keys[n]=hashlib.sha256(json.dumps([base['configs'],sources[n],[(d,key(d)) for d in sorted(dag[n])]],sort_keys=True).encode()).hexdigest()
 return keys[n]
for n in sources:key(n)
(logs/'declared-context.json').write_text(json.dumps(dict(source_hashes=sources,dependency_keys=keys,configs=base['configs'],runtime_only=True,current_main_validation=False,probe_sha256=hashlib.sha256((Q/'InspectLiveCallV2.lean').read_bytes()).hexdigest()),indent=2)+'\n')
env=dict(os.environ);env.update(json.loads((E/'author-env-v1.json').read_text()));env.pop('FV_LAKE_CACHE',None);env.update(FV_ROOT=str(V),FV_MEMCAP='2G',FV_MEMCAP_STATS=str(logs/'probe.mem'),FV_MEMCAP_UNIT='worker-o-live-call-probe-v1',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false');env['LEAN_PATH']=str(lib)+':'+subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=V,env=env,text=True).strip()
with (logs/'probe.log').open('w') as out:r=subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh'),'lake','env','lean','-j1','-DElab.async=false','--run',str(Q/'InspectLiveCallV2.lean')],cwd=R,env=env,stdout=out,stderr=subprocess.STDOUT)
(logs/'result.json').write_text(json.dumps(dict(status='passed' if r.returncode==0 else 'failed',exit_code=r.returncode,stats=(logs/'probe.mem').read_text()),indent=2)+'\n');print('Probe exit',r.returncode);raise SystemExit(r.returncode)
