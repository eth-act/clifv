"""Validate the frozen five-file packet after its real current-normal providers pass."""
from pathlib import Path
import argparse,json,hashlib,subprocess,os,re,fcntl,shutil,datetime
from preflight import OUT,PLAN,check
p=argparse.ArgumentParser();p.add_argument('--root',required=True);p.add_argument('--release',required=True);p.add_argument('--providers',type=Path,required=True);p.add_argument('--attempt',required=True);a=p.parse_args();context=check(a.root,a.release);release=json.loads(Path(a.release).read_text());assert release['allow_binding_packet_prefix'] is True;assert os.environ.get('WORKER_O_FULL_GATE_GRANTED')=='513-production-shared';
group=Path('/proc/self/cgroup').read_text().strip().split('0::')[-1];cg=Path('/sys/fs/cgroup')/group.lstrip('/');assert int((cg/'memory.max').read_text())<=12*1024**3,'Run the entire binding gate in the approved aggregate scope'
providers=json.loads(a.providers.read_text());assert providers['status']=='passed' and providers['phase']=='binding-providers';assert providers['context']['tree']==PLAN['combined_tree'];root=Path(a.root);assert a.attempt.replace('-','').isalnum();prefix=OUT/('binding-prefix-'+a.attempt);assert not prefix.exists();lock=(OUT/'exclusive-shared-gate.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);E=OUT.parent;manifest=json.loads((E/'direct-call-result-packet-v1.json').read_text());packet=E/'direct-call-result-packet-v1';logs=OUT/'binding-runs'/a.attempt;logs.mkdir(parents=True)
env=dict(os.environ);env.pop('FV_LAKE_CACHE',None);env.pop('FV_MEMCAP_OFF',None);env.update(LAKE_CACHE_DIR=PLAN['existing_cache'],LAKE_ARTIFACT_CACHE='true',LAKE_RESTORE_ARTIFACTS='true',PATH='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+env['PATH'],LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',PYTHONDONTWRITEBYTECODE='1')
roots=['FV.Backend.Proof.StockSourceCallWitness','FV.Backend.Proof.StockSourceResults','FV.Backend.Proof.StockResults','FV.Backend.Proof.IselCtlCallRules','FV.E2E.ExtSemGuard']
with (logs/'proper-current-normal-keys.log').open('w') as stream:rc=subprocess.call(['lake','build','--no-build',*roots],cwd=root,env=env,stdout=stream,stderr=subprocess.STDOUT)
assert rc==0,'No prefix source or kernel is created before complete proper-current provider keys pass'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
# Preserve all current imports as immutable content hashes. The exclusive queue lock prevents writers.
imports={}
for line in subprocess.check_output(['git','grep','-n','-E',r'^(public |private |meta )*import ',PLAN['combined_tree'],'--','*.lean'],cwd='/home/lee/clifv',text=True).splitlines():
 _,path,_,text=line.split(':',3);imports.setdefault(path,set()).update(w.replace('.','/')+'.lean' for w in re.sub(r'^(?:(?:public|private|meta)\s+)*import\s+','',text).split('--')[0].split())
closure={x.replace('.','/')+'.lean' for x in roots};todo=list(closure)
while todo:
 for d in imports.get(todo.pop(),set())-closure:
  if d not in PLAN['all_source_blobs']:continue
  closure.add(d);todo.append(d)
pinned={}
for rel in closure:
 stem=root/'.lake/build/lib/lean'/Path(rel).with_suffix('');pinned[rel]={}
 for suffix in ['.olean','.olean.private','.olean.server','.ir','.ir.sig']:
  f=Path(str(stem)+suffix)
  if f.exists():pinned[rel][suffix]=sha(f)
 assert '.olean' in pinned[rel],rel
prefix.mkdir()
for rel,h in manifest['files'].items():
 source=packet/rel;assert sha(source)==h;dest=prefix/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(source.read_bytes())
lib=prefix/'.lake/build/lib/lean';lib.mkdir(parents=True);env['LEAN_PATH']=str(lib)+':'+str(root/'.lake/build/lib/lean')+':/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/lib/lean';records=[]
for i,rel in enumerate(['FV/Backend/Proof/StockDirectCallResult.lean','FV/Backend/Proof/StockDirectCallResultFixture.lean','FV/Backend/Proof/StockDirectCallResultWitness.lean']):
 stem=lib/Path(rel).with_suffix('');stem.parent.mkdir(parents=True,exist_ok=True)
 with (logs/(str(i)+'-kernel.log')).open('w') as stream:rc=subprocess.call(['/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean','-j2','--root='+str(prefix),str(prefix/rel),'-o',str(stem)+'.olean','-i',str(stem)+'.ilean','-c',str(stem)+'.c'],cwd=prefix,env=env,stdout=stream,stderr=subprocess.STDOUT)
 records.append({'source':rel,'exit':rc});assert rc==0,('Inspect exact current prefix diagnostic',rel)
with (logs/'audit-policy.log').open('w') as stream:rc=subprocess.call(['python3',str(OUT/'helpers/axiom-audit-j2.py'),'--cwd',str(root),'--log-dir',str(logs/'audit'),*[str(prefix/rel) for rel in manifest['files'] if rel.startswith('scripts/audit/')]],cwd=root,env=env,stdout=stream,stderr=subprocess.STDOUT)
assert rc==0;axes={}
for f in (logs/'audit').glob('*.log'):
 text=' '.join(f.read_text().split())
 for name,value in re.findall(r"'(.+?)' depends on axioms: \[([^]]*)\]",text):axes[name]=[x.strip() for x in value.split(',') if x.strip()]
 for name in re.findall(r"'(.+?)' does not depend on any axioms",text):axes[name]=[]
standard={'propext','Classical.choice','Quot.sound'};fixed=sum(any(x not in standard for x in values) for values in axes.values());assert len(axes)==13 and fixed==2
for rel,parts in pinned.items():
 for suffix,h in parts.items():assert sha(str(root/'.lake/build/lib/lean'/Path(rel).with_suffix(''))+suffix)==h,('Imported artifact changed during gate',rel)
receipt={'status':'passed','context':context,'source_hashes':manifest['files'],'proper_current_normal_provider_check':True,'immutable_import_hashes':pinned,'kernel_records':records,'axiom_sets':axes,'standard_roots':11,'fixed_roots':2,'production_activation':False,'full_goal_complete':False,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};(logs/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');shutil.rmtree(prefix/'.lake');print('CURRENT BINDING PACKET PASSED13ROOTS; expendable outputs removed')
