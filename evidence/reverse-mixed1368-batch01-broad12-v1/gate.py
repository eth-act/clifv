from pathlib import Path
import json,hashlib,os,psutil,re,shutil,subprocess,time,tomllib,tempfile
from restore_config import restore_config
L=Path(__file__).resolve().parent;E=L.parent;B=Path('/home/lee/clifv');D=E/'general7-main-candidate-v1/current8f-full-reverse-inventory-v1';G=B/'.worktrees/loop-20261102';P=E/'892-joint-current-context-v2/package';R=E/'direct-call-store-live-packet-v1/validation-package-v1';roots={'P':P,'R':R};tool='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake';lean='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean';helper=E/'140-acquire-fused810-packet-v1/outside-avoids-extraction-proposal-v1/HashNative.lean'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
proposal=D/'complete-mixed1368-repair-proposal-v1.json';assert sha(proposal)=='22a24f8a74333cf7d11a11704015f2cf2a6b136742a4e5c6d8517665627af833';I=json.loads(proposal.read_text());C=json.loads((D/'complete-mixed-repair-classification-v1.json').read_text());bindings=json.loads((D/'unaffected2013-current-bindings-v1.json').read_text());baseKeys={r['target']:r['key'] for r in bindings['rows']};base= json.loads((D/'baseline2013-output-bindings-v1/receipt.json').read_text());origins=json.loads((D/'complete3381-reviewed-origin-donor-disposition-v3.json').read_text());approved={x['target']:x for x in origins['rows'] if x['existing_approved_archive_matches']};release=json.loads((L/'command-release-v1.json').read_text());assert release['approved'] and release['allocation']=='12G' and release['manifest_sha256']==sha(proposal) and release['script_sha256']==sha(Path(__file__));original=(L/'original-G-lakefile.toml').read_bytes();projected=original.replace(b'weakLeanArgs = [',b'weakLeanArgs = ["-j1",',1);assert original!=projected;records=[];nodes=[];fresh=0;started=time.monotonic();cache={};saved=L/'preserved-old-targets';saved.mkdir();currentKeys=dict(baseKeys);seq=0
sources=C['source_hashes3381'];order=C['ordered3381'];index={n:i for i,n in enumerate(order)}
def closure(n):
 if n not in cache:
  out={n}
  for d in C['imports'].get(n,[]):out|=closure(d)
  cache[n]=out
 return cache[n]
def full_source_check(names):
 for n in names:assert sha(G/Path(n.replace('.','/')+'.lean'))==sources[n],('source drift',n)
def guards():
 p=psutil.Process(release['broad_controller_pid']);assert p.uids().real==os.getuid() and p.create_time()==release['scheduler_birth'] and p.status()==psutil.STATUS_STOPPED;assert not any(x.is_running() and x.status()!=psutil.STATUS_ZOMBIE for x in p.children(recursive=True))
 assert (G/'lakefile.toml').read_bytes() in [original,projected]
 for f,h in I['canonical_G_configuration'].items():
  if f!='lakefile.toml':assert sha(G/f)==h
 for z in psutil.process_iter(['pid']):
  try:
   if z.uids().real!=os.getuid():continue
   args=z.cmdline()
   if args and Path(args[0]).name in ['lean','lake','lake.orig','leanc'] and z.cwd().startswith(str(G)):raise AssertionError(('other G compiler',z.pid))
  except(psutil.NoSuchProcess,psutil.AccessDenied):continue
env=dict(os.environ)
for k in ['FV_MEMCAP_OFF','FV_LAKE_CACHE','LEAN_PATH','LEAN_SYSROOT','LEAN_SRC_PATH','LAKE_CACHE_DIR']:env.pop(k,None)
env.update(PATH='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+env['PATH'],FV_ROOT=str(G),FV_MEMCAP='12G',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2')
def run(label,argv,root=G,allowed=(0,)):
 global seq
 guards();seq+=1;label=str(seq).zfill(4)+'-'+label;out=L/(label+'.stdout');err=L/(label+'.stderr');mem=L/(label+'.mem');e=dict(env,FV_MEMCAP_STATS=str(mem),FV_MEMCAP_UNIT='worker-o-mixed1368-b01-'+str(seq))
 with out.open('w') as o,err.open('w') as x:p=subprocess.run([str(P/'scripts/memcap.sh'),*argv],cwd=root,env=e,stdout=o,stderr=x)
 r={'label':label,'argv':argv,'cwd':str(root),'exit':p.returncode,'stdout_sha256':sha(out),'stderr_sha256':sha(err),'memory':mem.read_text() if mem.exists() else 'MISSING'};records.append(r);(L/'commands.json').write_text(json.dumps(records,indent=2)+'\n');assert p.returncode in allowed,(label,p.returncode,str(err));return p.returncode,out.read_text(),err.read_text()
def normal(label,names,root=G,allowed=(0,)):return run(label,[tool,'build','--no-build',*names],root,allowed)
def keys(label,names):
 _,text,_=run(label,[tool,'--json','query','--no-build',*['+'+n+':depHash' for n in names]]);got=[json.loads(x) for x in text.splitlines() if x.strip()];assert len(got)==len(names);return dict(zip(names,got))
def payloads(root,n):
 rel=Path(n.replace('.','/'));out={}
 for area,ext in [('.lake/build/lib/lean','.trace'),('.lake/build/lib/lean','.olean'),('.lake/build/lib/lean','.ilean'),('.lake/build/lib/lean','.olean.hash'),('.lake/build/lib/lean','.ilean.hash'),('.lake/build/ir','.c'),('.lake/build/ir','.c.hash')]:
  p=Path(area)/rel.with_suffix(ext);out[str(p)]=sha(root/p)
 return out
def cold(label,root,n):
 rel=Path(n.replace('.','/'));t=json.loads((root/'.lake/build/lib/lean'/rel.with_suffix('.trace')).read_text());assert not t['outputs'].get('m'),('unexpected module output mode',n)
 fs=[root/'.lake/build/lib/lean'/rel.with_suffix('.olean'),root/'.lake/build/lib/lean'/rel.with_suffix('.ilean'),root/'.lake/build/ir'/rel.with_suffix('.c')];expected=[t['outputs']['o'][0].split('.')[0],t['outputs']['i'].split('.')[0],t['outputs']['c'].split('.')[0]]
 _,out,_=run(label,[lean,'-j1','--run',str(helper),*[str(f) for f in fs]],E);lines=out.splitlines();assert len(lines)==3
 for line,path,h in zip(lines,fs,expected):
  name,binary,text=line.split('\t');assert name==str(path) and binary==h,(n,name,binary,h)
 return payloads(root,n)
def creator_ok(n,key):
 p=G/'.lake/build/lib/lean'/Path(n.replace('.','/')+'.trace')
 if not p.exists():return False
 t=json.loads(p.read_text())
 if t.get('depHash')!=key:return False
 if not t.get('synthetic') and t.get('inputs') and any('/bin/lean ' in z.get('message','') for z in t.get('log',[])):return True
 a=approved.get(n);return bool(a and a['G_trace_sha256']==sha(p) and any(x['native_key']==key for x in a['existing_approved_archive_matches']))
def preserve(n):
 rel=Path(n.replace('.','/'));old={}
 for area in ['lib/lean','ir']:
  stem=G/'.lake/build'/area/rel
  for f in stem.parent.glob(stem.name+'.*'):
   if f.is_file():
    h=sha(f);dest=saved/h
    if not dest.exists():shutil.copyfile(f,dest)
    old[str(f.relative_to(G))]=h
 return old
def donor(n,key,deps):
 for owner,root in roots.items():
  rel=Path(n.replace('.','/'));tr=root/'.lake/build/lib/lean'/rel.with_suffix('.trace')
  if not tr.exists():continue
  t=json.loads(tr.read_text())
  if t.get('synthetic') or not t.get('inputs') or t.get('depHash')!=key:continue
  command='\n'.join(x.get('message','') for x in t.get('log',[]))
  if '/bin/lean ' not in command or str(root/rel.with_suffix('.lean')) not in command:continue
  if any(not (root/Path(x.replace('.','/')+'.lean')).exists() or sha(root/Path(x.replace('.','/')+'.lean'))!=sources[x] for x in closure(n)):continue
  a=tomllib.loads((G/'lakefile.toml').read_text());b=tomllib.loads((root/'lakefile.toml').read_text())
  for x in [a,b]:x['weakLeanArgs']=[v for v in x.get('weakLeanArgs',[]) if v not in ['-j1','-j2']]
  if a!=b or any((G/f).read_bytes()!=(root/f).read_bytes() for f in ['lean-toolchain','lake-manifest.json']):continue
  good=True
  for d in deps:
   dt=root/'.lake/build/lib/lean'/Path(d.replace('.','/')+'.trace')
   if not dt.exists() or json.loads(dt.read_text()).get('depHash')!=currentKeys[d]:good=False;break
   dp=payloads(root,d);gp=payloads(G,d)
   if any(dp[f]!=gp[f] for f in dp if not f.endswith('.trace')):good=False;break
  if not good:continue
  before=sha(tr);rc,_,_=normal('donor-normal',[n],root,(0,3))
  if rc!=0:continue
  assert sha(tr)==before;expected=cold('donor-cold',root,n);return owner,root,expected
 return None
status='RUNNING';error=None
try:
 guards();assert (G/'lakefile.toml').read_bytes()==original;full_source_check(order);normal('unaffected2013',C['unaffected2013']);assert keys('baseline2013-keys',C['unaffected2013'])==baseKeys
 for f,h in base['payload_sha256'].items():assert sha(G/f)==h,('baseline output drift',f)
 for row in bindings['rows']:assert creator_ok(row['target'],row['key']),('baseline creator drift',row['target'])
 for f,h in I['protected118_prior_nodes'].items():assert sha(G/f)==h,('protected118 drift',f)
 tmp=G/'lakefile.toml.mixed1368-project';tmp.write_bytes(projected);os.replace(tmp,G/'lakefile.toml')
 for i,row in enumerate(I['nodes_topological']):
  if fresh>=64 or time.monotonic()-started>=1800:status='BATCH_LIMIT_PASSED_INCOMPLETE';break
  n=row['target'];guards();deps=sorted(closure(n)-{n},key=index.get);full_source_check(closure(n));assert all(x in currentKeys for x in deps),('unvalidated predecessor',n);normal('deps-'+str(i),deps);key=keys('key-'+str(i),[n])[n]
  if row['initial_current_key'] is not None:assert key==row['initial_current_key'],('initial key drift',n,key)
  rc,_,_=normal('ready-'+str(i),[n],allowed=(0,3));old={};kind='existing proper current output'
  if not (rc==0 and creator_ok(n,key)):
   choice=donor(n,key,deps);old=preserve(n)
   if choice:
    owner,root,expected=choice;kind='verified donor '+owner
    for f,h in expected.items():
     src=root/f;dest=G/f;assert sha(src)==h;assert dest.parent.resolve().is_relative_to(G.resolve()) and dest.parent.stat().st_uid==os.getuid();fd,tmp=tempfile.mkstemp(dir=dest.parent,prefix='.owned-mixed1368-');os.close(fd);shutil.copyfile(src,tmp);os.replace(tmp,dest);assert sha(dest)==h
   else:
    kind='fresh single leaf';rel=Path(n.replace('.','/'))
    for area in ['lib/lean','ir']:
     stem=G/'.lake/build'/area/rel
     for f in stem.parent.glob(stem.name+'.*'):
      if f.is_file() and not f.name.endswith('.trace.nobuild') and (f.is_symlink() or f.stat().st_nlink!=1 or not f.stat().st_mode&0o200):
       fd,tmp=tempfile.mkstemp(dir=f.parent,prefix='.owned-leaf-');os.close(fd);shutil.copyfile(f,tmp);os.replace(tmp,f)
    primary=G/'.lake/build/lib/lean'/rel.with_suffix('.trace')
    if primary.exists():primary.unlink()
    _,ko,ke=run('kernel-'+str(i),[tool,'-v','build','+'+n+':leanArts']);assert '/bin/lean ' in ko+ke and '-j1' in ko+ke and str(G/rel.with_suffix('.lean')) in ko+ke,('missing fresh compiler command',n);fresh+=1
   normal('normal-'+str(i),[n]);assert creator_ok(n,key),('creator/key postcheck',n)
  outputs=cold('current-cold-'+str(i),G,n);currentKeys[n]=key;nodes.append({'target':n,'key':key,'kind':kind,'source_sha256':row['source_sha256'],'outputs':outputs,'preserved_old':old});(L/'passed-nodes.json').write_text(json.dumps(nodes,indent=2)+'\n');print('completed',i+1,n,kind,'fresh',fresh,flush=True)
 else:status='ALL1368_TARGETS_PASSED_PENDING_FINAL_GATES'
except BaseException as exc:
 status='FAILED_AT_FIRST_DIAGNOSTIC';error=repr(exc)
 raise
finally:
 restoration=restore_config(L);(L/'gate-config-restoration.json').write_text(json.dumps(restoration,indent=2)+'\n')
 if status!='FAILED_AT_FIRST_DIAGNOSTIC':
  normal('batch-original-normals',[x['target'] for x in nodes]);normal('baseline2013-final',C['unaffected2013']);full_source_check(order)
  for f,h in base['payload_sha256'].items():assert sha(G/f)==h,('baseline mutated',f)
  for f,h in I['protected118_prior_nodes'].items():assert sha(G/f)==h,('protected118 mutated',f)
  if status=='ALL1368_TARGETS_PASSED_PENDING_FINAL_GATES':
   normal('complete3381',order);requested=json.loads((D/'remaining-cone-proposal-v1.json').read_text())['requested'];normal('reverse326',requested);status='PASSED_COMPLETE3381_NORMAL_AND326;FINAL_PROVENANCE_AUDIT_REQUIRED'
 (L/'receipt.json').write_text(json.dumps({'status':status,'proposal_sha256':sha(proposal),'nodes':nodes,'commands':records,'fresh_kernels':fresh,'error':error,'elapsed_seconds':time.monotonic()-started,'baseline2013_outputs_unchanged':True,'protected118_unchanged':True,'canonical_config_restored':True,'full_original_goal':'OPEN'},indent=2)+'\n');(L/'lease-ended.json').write_text('{"canonical_config_restored":true}\n')
