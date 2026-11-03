from pathlib import Path
import json,hashlib,subprocess,os,psutil,re,shutil,importlib.util
D=Path(__file__).resolve().parent;Q=D.parent;E=Q.parent;R=Q/'validation-package-v1';P=E/'892-joint-current-context-v2/package';L=D/'current8f-three-donor-reuse-v1';L.mkdir();I=json.loads((D/'current8f-kernel-manifest.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert sha(D/'current8f-kernel-manifest.json')=='48c9e596dedc944d7df34034f5588f2216b478b38300fc9917f3c379d8d0da42';main='8f073980e9630c8d3cd9d6f6f77ab462474c7bcb';ordered=['FV.E2E.StockResultCallNIW'];baseline=sorted(set(I['import_graph'])-set(ordered));assert len(baseline)==775;staged={'FV/E2E/WorldReturnTraceCore.lean','FV/E2E/StockMemoryMachineReturnValueW.lean'};origin={}
for rel,h in I['source_hashes'].items():
 n=rel[:-5].replace('/','.');p=D/'source'/rel if n in ordered else R/rel;assert sha(p)==h,rel
 if n in ordered:origin[rel]={'kind':'new owned export','sha256':h};continue
 if rel in staged:origin[rel]={'kind':'explicit approved staged W helper','sha256':h};continue
 data=subprocess.check_output(['git','show',main+':'+rel]);assert hashlib.sha256(data).hexdigest()==h,('Current main source differs',rel);origin[rel]={'kind':'exact current8f Git blob','sha256':h}
(L/'current-source-context.json').write_text(json.dumps({'main':main,'sources':origin,'graph':I['import_graph'],'source_closure':len(origin),'old_files_changed':[]},indent=2)+'\n')
for p in psutil.process_iter(['uids','name','status','cmdline']):
 try:
  if p.info['uids'].real!=os.getuid() or p.info['name'] not in ['lean','lake'] or p.info['status']=='zombie':continue
  assert not p.cwd().startswith(str(R)) and not any(str(R) in a for a in (p.info['cmdline'] or [])),('R writer',p.pid)
 except(psutil.NoSuchProcess,psutil.AccessDenied):pass
cfg={c:sha(R/c) for c in ['lakefile.toml','lean-toolchain','lake-manifest.json']};env=dict(os.environ)
for k in ['FV_MEMCAP_OFF','FV_LAKE_CACHE','LEAN_PATH','LEAN_SYSROOT','LEAN_SRC_PATH','LAKE_CACHE_DIR']:env.pop(k,None)
env.update(PATH='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+env['PATH'],FV_ROOT=str(R),FV_MEMCAP='2G',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1');records=[];outputs={}
def run(label,args,allowed=(0,)):
 e=dict(env,FV_MEMCAP_STATS=str(L/(label+'.mem')),FV_MEMCAP_UNIT='worker-o-result-call-W-'+label)
 with (L/(label+'.log')).open('w') as f:rc=subprocess.call([str(P/'scripts/memcap.sh'),*args],cwd=R,env=e,stdout=f,stderr=subprocess.STDOUT)
 records.append({'label':label,'argv':args,'exit':rc,'log_sha256':sha(L/(label+'.log')),'memory':(L/(label+'.mem')).read_text()});(L/'progress.json').write_text(json.dumps(records,indent=2)+'\n');print(label,rc,flush=True);assert rc in allowed,(label,rc);return rc

# Verify the complete donor context before touching any owned output.
import tomllib
context=json.loads((D/'current8f-source-context.json').read_text()); affected={'FV.E2E.StockResultCallSource','FV.E2E.StockResultCallPair','FV.E2E.StockResultCallLayout'}
closure=set();todo=['FV.E2E.StockResultCallPair','FV.E2E.StockResultCallLayout']
while todo:
 n=todo.pop()
 if n in closure:continue
 closure.add(n);todo.extend(I['import_graph'][n])
assert not 'FV.E2E.ABIReadOnlyMachine' in closure
for n in closure:assert sha(P/Path(n.replace('.','/')+'.lean'))==context['sources'][n]['sha256'],n
def strip_weak(x):
 if isinstance(x,dict):return {k:strip_weak(v) for k,v in x.items() if k!='weakLeanArgs'}
 if isinstance(x,list):return [strip_weak(v) for v in x]
 return x
assert strip_weak(tomllib.loads((P/'lakefile.toml').read_text()))==strip_weak(tomllib.loads((R/'lakefile.toml').read_text()))
for c in ['lean-toolchain','lake-manifest.json']:assert sha(P/c)==sha(R/c),c
for proc in psutil.process_iter(['uids','name','status','cmdline']):
 try:
  if proc.info['uids'].real!=os.getuid() or proc.info['name'] not in ['lean','lake'] or proc.info['status']=='zombie':continue
  args=proc.info['cmdline'] or []
  for n in affected:assert not any(n.replace('.','/')+'.lean' in arg or n.replace('.','/')+'.c' in arg for arg in args),('Active exact donor writer',proc.pid,n)
 except(psutil.NoSuchProcess,psutil.AccessDenied):pass
# The unchanged command helper records commands, memory, and exit codes for both roots.
def donor_run(label,args):
 e=dict(env,FV_ROOT=str(P),FV_MEMCAP_STATS=str(L/(label+'.mem')),FV_MEMCAP_UNIT='worker-o-result-donor-'+label)
 with (L/(label+'.log')).open('w') as out:rc=subprocess.call([str(P/'scripts/memcap.sh'),*args],cwd=P,env=e,stdout=out,stderr=subprocess.STDOUT)
 records.append({'label':label,'cwd':str(P),'argv':args,'exit':rc,'log_sha256':sha(L/(label+'.log')),'memory':(L/(label+'.mem')).read_text()});(L/'progress.json').write_text(json.dumps(records,indent=2)+'\n');print(label,rc,flush=True);assert rc==0,(label,rc)
donor_run('P-proper-three-closure',['lake','build','--no-build',*sorted(closure)])
order=[];done=set()
def topo(n):
 if n in done:return
 for dep in I['import_graph'][n]:
  if dep in affected:topo(dep)
 done.add(n);order.append(n)
for n in sorted(affected):topo(n)
copied={}
for i,n in enumerate(order):
 run('copy-deps'+str(i),['lake','build','--no-build',*I['import_graph'][n]])
 run('copy-key'+str(i),['lake','query','--no-build','+'+n+':depHash']);keys=re.findall(r'^[0-9a-f]{16}$',(L/('copy-key'+str(i)+'.log')).read_text(),re.M);assert len(keys)==1
 tr=P/'.lake/build/lib/lean'/Path(n.replace('.','/')+'.trace');md=json.loads(tr.read_text());assert md.get('inputs') and not md.get('synthetic') and md['depHash']==keys[0],(n,'Donor mismatch')
 if n=='FV.E2E.StockResultCallSource':assert keys[0]=='717a34a67ea22f5c'
 before=sha(tr);arts={}
 for area in ['lib/lean','ir']:
  stem=P/'.lake/build'/area/n.replace('.','/')
  for f in stem.parent.glob(stem.name+'.*'):
   if not f.is_file() or f.name.endswith(('.c.o','.o','.bc')):continue
   h=sha(f);dest=R/f.relative_to(P);assert str(dest.parent.resolve()).startswith(str(R.resolve())) and not dest.is_symlink(),str(dest)
   if dest.exists():
    assert dest.stat().st_uid==os.getuid() and dest.stat().st_nlink==1
    saved=L/'preserved-rejected-outputs'/dest.relative_to(R);saved.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(dest,saved);assert sha(saved)==sha(dest);dest.unlink()
   dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,dest);assert sha(f)==h and sha(dest)==h;arts[str(dest.relative_to(R))]=h
 assert sha(tr)==before;copied[n]={'native_key':keys[0],'trace_sha256':before,'artifacts':arts,'origin':'proper full-input P donor'}
 run('copy-normal'+str(i),['lake','build','--no-build',n])
(L/'verified-P-copy.json').write_text(json.dumps(copied,indent=2)+'\n')


remaining={}
for i,n in enumerate(['FV.E2E.StockResultCallRun','FV.E2E.StockResultCallDomain']):
 run('remaining-key'+str(i),['lake','query','--no-build','+'+n+':depHash']);keys=re.findall(r'^[0-9a-f]{16}$',(L/('remaining-key'+str(i)+'.log')).read_text(),re.M);assert len(keys)==1
 ready=run('remaining-ready'+str(i),['lake','build','--no-build',n],allowed=(0,3));remaining[n]={'expected_key':keys[0],'ready_exit':ready,'donors':{}}
 for donor in [P,Path('/home/lee/clifv/.worktrees/loop-20261102')]:
  tr=donor/'.lake/build/lib/lean'/Path(n.replace('.','/')+'.trace');md=json.loads(tr.read_text());remaining[n]['donors'][str(donor)]={'trace_sha256':sha(tr),'native_key':md['depHash'],'synthetic':md.get('synthetic'),'inputs':bool(md.get('inputs')),'matches':md['depHash']==keys[0]}
(L/'receipt.json').write_text(json.dumps({'status':'THREE_COHERENT_P_DONORS_COPIED;REMAINING_TWO_READINESS_RECORDED','copied':copied,'records':records,'remaining':remaining},indent=2)+'\n')
