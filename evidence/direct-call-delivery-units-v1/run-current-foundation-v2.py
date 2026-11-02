from pathlib import Path
import datetime,hashlib,json,os,psutil,re,subprocess,fcntl
D=Path(__file__).resolve().parent;E=D.parent;S=json.loads((D/'current-foundation-snapshot-v1.json').read_text());C=json.loads((D/'class-foundation-prepared-v1.json').read_text());P=Path(S['package']);L=D/'current-gate-v2';L.mkdir();lock=(D/'current-gate.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
assert os.environ.get('WORKER_O_PROOF_SLOT_GRANTED')=='foundation-1G'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
for n,h in S['sources'].items():assert sha(P/n)==h,n
config=P/'lakefile.toml';assert '"-j1"' in config.read_text()
env=dict(os.environ)
for k in ['FV_LAKE_CACHE','FV_MEMCAP_OFF','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT']:env.pop(k,None)
env.update(PATH='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+env['PATH'],FV_ROOT=str(P),FV_MEMCAP='1G',LAKE_CACHE_DIR=str(E/'892-current-main-context-v1/package/.lake/ci-cache'),LAKE_ARTIFACT_CACHE='true',LAKE_RESTORE_ARTIFACTS='true',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1')
records=[]
def run(label,argv):
 conflicts=[]
 for proc in psutil.process_iter(['pid','name','cmdline','status']):
  try:
   a=proc.info['cmdline'] or []
   if proc.info['name']=='lean' and proc.info['status']!='zombie':
    for target in argv:
     if target.startswith('FV.') and any(target.replace('.','/')+'.lean' in x for x in a):conflicts.append({'pid':proc.pid,'module':target})
  except (psutil.NoSuchProcess,psutil.AccessDenied):pass
 assert not conflicts,('Existing module owner',conflicts)
 env['FV_MEMCAP_UNIT']='worker-o-foundation-current-'+label;env['FV_MEMCAP_STATS']=str(L/(label+'.mem'))
 with (L/(label+'.log')).open('w') as stream:rc=subprocess.call(['/home/lee/clifv/.worktrees/stock-extending-production-20261031/scripts/memcap.sh',*argv],cwd=P,env=env,stdout=stream,stderr=subprocess.STDOUT)
 records.append({'label':label,'argv':argv,'exit':rc,'memstats':(L/(label+'.mem')).read_text() if (L/(label+'.mem')).exists() else None});(L/'progress.json').write_text(json.dumps({'status':'running' if rc==0 else 'failed','records':records},indent=2)+'\n');print(label,'exit',rc,flush=True);assert rc==0,('Inspect actual current diagnostic',label)
# Real normal-key providers write only isolated artifact paths. The cache uses the existing native protocol.
chain=['FV.Backend.Lowering.StockMemoryStoreCfgNI','FV.Backend.Lowering.StockMemoryLoadStoreNI','FV.Backend.Lowering.StockMemoryCapturedCopyNI','FV.Backend.Lowering.StockMemorySretCopyNI','FV.Backend.Lowering.StockVoidCallNI']
for i,mod in enumerate(chain):run('normal-chain-'+str(i),['lake','build',mod])
for i,rel in enumerate(S['outside_providers']):run('outside-'+str(i),['lake','build',rel[:-5].replace('/','.')] )
providers=[n[:-5].replace('/','.') for n in S['sources'] if n not in C['source_hashes']]
run('complete-normal-import-check',['lake','build','--no-build',*providers])
# Compile the new modules with normal Lake keys. All provider keys passed above.
newmods=[n[:-5].replace('/','.') for n in C['source_hashes'] if n.startswith('FV/')]
pending=set(newmods);ordered=[]
while pending:
 ready=sorted(m for m in pending if not ({x for x in re.findall(r'^import\s+([\w.]+)',(P/(m.replace('.','/')+'.lean')).read_text(),re.M)}&pending));assert ready;ordered+=ready;pending.difference_update(ready)
for i,mod in enumerate(ordered):run('candidate-'+str(i),['lake','build',mod])
run('candidate-normal-check',['lake','build','--no-build',*newmods])
# The policy checks exact marked fixed witnesses and rejects all other nonstandard axioms.
env['LEAN_PATH']=str(P/'.lake/build/lib/lean')+':/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/lib/lean'
helper=D/'axiom-audit-j1.py'
run('audit',['python3',str(helper),'--cwd',str(P),'--log-dir',str(L/'audit'),*[str(P/n) for n in C['source_hashes'] if n.startswith('scripts/audit/')]])
axes={}
for p in (L/'audit').glob('*.log'):
 text=' '.join(p.read_text().split())
 for name,value in re.findall(r"'(.+?)' depends on axioms: \[([^]]*)\]",text):axes[name]=[x.strip() for x in value.split(',') if x.strip()]
 for name in re.findall(r"'(.+?)' does not depend on any axioms",text):axes[name]=[]
std={'propext','Classical.choice','Quot.sound'};fixed=sum(any(x not in std for x in v) for v in axes.values());assert len(axes)==43 and fixed==5,(len(axes),fixed)
for n,h in S['sources'].items():assert sha(P/n)==h,n
outputs={}
for n in S['sources']:
 if n.startswith('scripts/'):continue
 stem=P/'.lake/build/lib/lean'/Path(n).with_suffix('');assert Path(str(stem)+'.olean').exists(),n
 outputs[n]={suffix:sha(str(stem)+suffix) for suffix in ['.olean','.olean.private','.olean.server','.trace'] if Path(str(stem)+suffix).exists()}
state={'status':'passed','base':C['base'],'tree':C['tree'],'sources':S['sources'],'new_sources':C['source_hashes'],'records':records,'proper_current_normal_provider_check':True,'axiom_sets':axes,'standard_roots':38,'fixed_roots':5,'outputs':outputs,'no_live_package_writes':True,'full_goal_complete':False,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};(D/'class-foundation-current-state-v1.json').write_text(json.dumps(state,indent=2)+'\n');print('CURRENT MAIN FOUNDATION PASSED43 ROOTS',flush=True)
