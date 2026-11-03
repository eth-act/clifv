from common import *
import hashlib,subprocess,sys,shutil,tomllib,re
B=Path('/home/lee/clifv');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
proposal=O/'bounded-phase1-proposal-v1.json';assert sha(proposal)=='4fd49bbe71d6dce3015658dcc4b1f9a26c245b3d04590eb59bd0e16abf868b08'
release=json.loads((D/'start-approved.json').read_text());assert release['parent_resource_approved'] and release['source2_released'] and release['acquire1_released']
S=json.loads((E/'140-fence-packet-v1/import-snapshot-v25.json').read_text());I=json.loads((O/'inventory.json').read_text());G=I['no_call_definitions']['modules'];Q=json.loads((O/'normal-readiness-v4.json').read_text());expected={r['module']:r['expected_key']for r in Q['queries']if r.get('expected_key')}
targets=['FV.E2E.RegLevelCorrectX','FV.E2E.DeadCleanupWorldX','FV.E2E.LinkWorldXW','FV.E2E.DeadCleanupWorldXW']
for p,h in S['config_hashes'].items():assert sha(F/p)==h,(p,'config changed')
assert '-j1' in (F/'lakefile.toml').read_text() and '-j2' not in (F/'lakefile.toml').read_text()
for m,v in G.items():assert sha(F/Path(m.replace('.','/')+'.lean'))==v['source_sha256'],m
records=[];outputs={};save(D/'progress.json',{'status':'preflight','records':records})
env=dict(os.environ)
for k in ['FV_LAKE_CACHE','FV_MEMCAP_OFF','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','LAKE_CACHE_DIR']:env.pop(k,None)
tool=Path(S['lean_executable']).parent;env.update(PATH=str(tool)+':'+env['PATH'],FV_ROOT=str(F),FV_MEMCAP='3G',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LAKE_CACHE_DIR=str(E/'140-fence-packet-v1/disabled-cache'))
def clean_overlap():
 for p in psutil.process_iter(['name','cmdline','status']):
  try:
   if p.info['status']=='zombie' or p.info['name'] not in ['python3','python','lake','lean','rclone','git']:continue
   args=' '.join(p.info['cmdline']or[]).lower()
   assert not (str(E).lower() in args and any(x in args for x in ['backup-reviewed','run-backup','reverse326','reverse-326'])),('Forbidden overlapping owner',p.pid)
   if p.info['name'] in ['lake','lean']:
    assert not (p.cwd()==str(F) or any(str(F) in a for a in p.info['cmdline']or[])),('Duplicate F writer',p.pid)
  except(psutil.NoSuchProcess,psutil.AccessDenied):pass

def cap(label,args,stdin=None,leaf=None):
 guard=json.loads((D/'guard-armed.json').read_text());assert live(guard['pid'],guard['birth']) and not (D/'shares-restored.json').exists()
 clean_overlap();env['FV_MEMCAP_UNIT']='worker-o-acquire-phase1-v1-'+label;env['FV_MEMCAP_STATS']=str(D/(label+'.mem'))
 command=[str(B/'.worktrees/stock-extending-production-20261031/scripts/memcap.sh'),*args]
 observations=[];bad=[]
 with (D/(label+'.stdout')).open('w') as out,(D/(label+'.stderr')).open('w') as err:
  child=subprocess.Popen(command,cwd=F,env=env,stdin=subprocess.PIPE if stdin is not None else None,stdout=out,stderr=err,text=True)
  save(D/'active-child.json',{'pid':child.pid,'birth':psutil.Process(child.pid).create_time(),'label':label})
  if stdin is not None:child.stdin.write(stdin);child.stdin.close()
  while child.poll() is None:
   if leaf:
    for p in psutil.process_iter(['name','cmdline','status','create_time']):
     try:
      args0=p.info['cmdline']or[]
      if p.info['name']=='lean' and p.info['status']!='zombie' and any(str(F) in a for a in args0):
       key=(p.pid,p.info['create_time'])
       if not any((v['pid'],v['birth'])==key for v in observations):observations.append({'pid':p.pid,'birth':p.info['create_time'],'argv':args0})
       if '-j1' not in args0 or str(F/Path(leaf.replace('.','/')+'.lean')) not in args0:bad.append({'pid':p.pid,'argv':args0})
     except(psutil.NoSuchProcess,psutil.AccessDenied):pass
   time.sleep(.1)
  rc=child.wait()
 rec={'label':label,'argv':args,'exit':rc,'stats':(D/(label+'.mem')).read_text() if (D/(label+'.mem')).exists() else None,'effective_Lean_observations':observations,'unexpected_compilers':bad}
 records.append(rec);save(D/'progress.json',{'status':'running' if rc==0 else 'failed','records':records,'outputs':outputs})
 assert rc==0,('First failure; preserve diagnostics',label,rc)
 assert not bad,('Unexpected compiler argv; no new node',bad)
 return (D/(label+'.stdout')).read_text().strip()

def closure(m):
 seen=set()
 def visit(n):
  if n in seen:return
  seen.add(n)
  for d in G[n]['imports']:
   if d in G:visit(d)
 visit(m);return sorted(seen)

def current_input(m):
 for n in closure(m):assert sha(F/Path(n.replace('.','/')+'.lean'))==G[n]['source_sha256'],n
 deps=[n for n in closure(m)if n!=m]
 cap(m.split('.')[-1]+'-deps',[str(tool/'lake'),'build','--no-build',*deps])
 key=cap(m.split('.')[-1]+'-key',[str(tool/'lake'),'query','--no-build','+'+m+':depHash'])
 assert key==expected[m],(m,'expected key changed',key,expected[m])

def output_record(m,origin):
 rel=Path(m.replace('.','/')+'.lean');stem=F/'.lake/build/lib/lean'/rel.with_suffix('');tr=Path(str(stem)+'.trace');data=json.loads(tr.read_text());assert data['depHash']==expected[m]
 arts={}
 for directory in ['lib/lean','ir']:
  p=F/'.lake/build'/directory/rel.with_suffix('')
  for a in p.parent.glob(p.name+'.*'):
   if a.is_file():arts[str(a.relative_to(F))]=sha(a)
 assert str(stem.relative_to(F))+'.olean' in arts
 outputs[m]={'source_sha256':sha(F/rel),'normal_input_key':data['depHash'],'outputs':data['outputs'],'artifacts':arts,'origin':origin}
 save(D/'completed-outputs.json',outputs)

def copy_owned(src,dest):
 assert src.is_file() and not src.is_symlink();assert not dest.exists(),dest
 dest.parent.mkdir(parents=True,exist_ok=True)
 with src.open('rb')as r,dest.open('xb')as w:shutil.copyfileobj(r,w)
 assert sha(src)==sha(dest)

# The approved native archive is extracted only into owned scratch.
origin=O/'linkclif-native-origin-v1/receipt.json';assert sha(origin)=='77285b5964a67c1f176285f3f2712944a2dd586e8069b0b94cde02b99b4562ab';od=json.loads(origin.read_text());entry=od['records']['FV/E2E/LinkClif.lean']['matched'];archive=E/'892-current-main-context-v1/package/.lake/ci-cache/artifacts'/entry['archive'];assert sha(archive)==entry['archive_sha256']
current_input('FV.E2E.LinkClif')
scratch=D/'linkclif-scratch';scratch.mkdir();lib=scratch/'lib';ir=scratch/'ir';lib.mkdir();ir.mkdir()
payload=json.dumps([{'file':str(archive),'base':[str(lib),str(ir)],'hash':expected['FV.E2E.LinkClif']}])
cap('LinkClif-native-extract',[str(tool/'leantar'),'--jobs','1','-x','-j','-'],payload)
for ext,root in [('olean',lib),('ilean',lib),('c',ir)]:
 files=list(root.rglob('*.'+ext));assert len(files)==1;assert sha(files[0])==entry['payloads'][ext]['extracted_sha256']
for root,directory in [(lib,'lib/lean'),(ir,'ir')]:
 for p in root.rglob('*'):
  if not p.is_file():continue
  assert p.resolve().is_relative_to(scratch.resolve()) and not p.is_symlink()
  copy_owned(p,F/'.lake/build'/directory/p.relative_to(root))
cap('LinkClif-normal',[str(tool/'lake'),'build','--no-build','FV.E2E.LinkClif']);output_record('FV.E2E.LinkClif',{'approved_native_origin_sha256':sha(origin)})
shutil.rmtree(scratch)
for i,m in enumerate(targets):
 current_input(m)
 if m in ['FV.E2E.LinkWorldXW','FV.E2E.DeadCleanupWorldXW']:
  save(D/'awaiting-retained-review.json',{'module':m,'receipt_sha256':'e9eaffc06fb8b62047cb11c5007f56ab3f93080ca0f26ce0c55af48a4adf7824'})
  while not (D/'retained-W-reuse-approved.json').exists():
   if (D/'cancel.json').exists():raise RuntimeError('Stopped before retained reuse')
   time.sleep(.2)
  approved=json.loads((D/'retained-W-reuse-approved.json').read_text());assert approved['receipt_sha256']=='e9eaffc06fb8b62047cb11c5007f56ab3f93080ca0f26ce0c55af48a4adf7824'
  evidence=json.loads((O/'retained-two-W-provider-coherence-v1.json').read_text())['records'][m];root=E/'direct-call-store-live-packet-v1/fault-world-w-prep-v1/historical-R-preserved-before-c4f-v1/owned-outputs';rel=Path(m.replace('.','/')+'.lean')
  for directory in ['lib/lean','ir']:
   stem=root/'.lake/build'/directory/rel.with_suffix('')
   for p in stem.parent.glob(stem.name+'.*'):
    if p.is_file():copy_owned(p,F/p.relative_to(root))
  origin_record={'approved_retained_W_receipt_sha256':approved['receipt_sha256']}
 else:
  cap('leaf-'+str(i),[str(tool/'lake'),'-v','build','+'+m+':leanArts'],leaf=m)
  origin_record={'actual_leaf_record':records[-1]}
 cap(m.split('.')[-1]+'-normal',[str(tool/'lake'),'build','--no-build',m]);output_record(m,origin_record)
cap('normal379',[str(tool/'lake'),'build','--no-build',*sorted(set(Q['existing374'])|set(targets)|{'FV.E2E.LinkClif'})])
save(D/'receipt.json',{'status':'passed_approved_phase1_exact_379_normal_context','records':records,'outputs':outputs,'all_sources_verified':{m:v['source_sha256']for m,v in G.items()},'configs':S['config_hashes'],'no_dependency_Lean_builds':True,'approved_target_order':targets,'source2_acquire1_restore_on_owner_exit':True,'full_goal_complete':False})
print('Phase1 passed. Both shares restore after all commands exit.',flush=True)
