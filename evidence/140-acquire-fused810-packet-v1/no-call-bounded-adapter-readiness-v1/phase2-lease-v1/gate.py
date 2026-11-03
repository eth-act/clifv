from common import *
import hashlib,subprocess,sys,shutil,tomllib,re
B=Path('/home/lee/clifv');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
proposal=O/'bounded-phase2-proposal-v1.json';assert sha(proposal)=='cfc443bffecf9ffb908f97b7989ccc0ade1005ce52fa10d0fa99771092fd7df1'
release=json.loads((D/'start-approved.json').read_text());assert release['parent_resource_approved'] and release['source2_released'] and release['acquire1_released']
S=json.loads((D/'temporary-import-snapshot-v26.json').read_text());I=json.loads((O/'inventory.json').read_text());G=I['no_call_definitions']['modules'];Q=json.loads((O/'normal-readiness-v4.json').read_text());expected={r['module']:r['expected_key']for r in Q['queries']if r.get('expected_key')}
phase1=O/'phase1-lease-v3/receipt.json'
assert sha(phase1)=='c7e56d5dd6602b03bc922c81959d65737bcde81e9949ff65db5ec4bef279fbce'
previous=json.loads(phase1.read_text())
for row in previous['outputs'].values():
 for path,h in row['artifacts'].items():assert sha(F/path)==h,('Phase1 output changed',path)
covered=set(Q['existing374'])|set(previous['outputs']);assert len(covered)==379
queries=json.loads((O/'downstream-eleven-query-v1/receipt.json').read_text())
newExpected={r['module']:r['expected_key']for r in queries['records']if r['expected_key']}
assert newExpected=={'FV.E2E.LinkWorldX':'b35c5e3883905110','FV.E2E.LinkClifN':'449ed896fdcb130e','FV.E2E.Link':'cc2f9f2e01683268'}
expected.update(newExpected)
targets=['FV.E2E.LinkWorldX','FV.E2E.Link']
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
    for owned in [E/'direct-call-store-live-packet-v1/validation-package-v1',E/'general7-main-candidate-v1']:
     assert not (p.cwd()==str(owned) or any(str(owned) in a for a in p.info['cmdline']or[])),('Source lease writer overlap',p.pid)
  except(psutil.NoSuchProcess,psutil.AccessDenied):pass

def cap(label,args,stdin=None,leaf=None):
 guard=json.loads((D/'guard-armed.json').read_text());assert live(guard['pid'],guard['birth']) and not (D/'shares-restored.json').exists()
 clean_overlap();env['FV_MEMCAP_UNIT']='worker-o-acquire-phase2-v1-'+label;env['FV_MEMCAP_STATS']=str(D/(label+'.mem'))
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

cap('projection-normal379',[str(tool/'lake'),'build','--no-build',*sorted(covered)])
projectionKeys={}
for name,key in expected.items():
 actual=cap('projection-key-'+name.split('.')[-1],[str(tool/'lake'),'query','--no-build','+'+name+':depHash'])
 assert actual==key,(name,'Weak projection changed native key',actual,key)
 projectionKeys[name]=actual
save(D/'projection-normal-key-receipt-v1.json',{'status':'passed_actual379_normal_and_all_eight_keys_unchanged','keys':projectionKeys,'config_hashes':S['config_hashes'],'canonical_sha256':sha(D/'canonical-lakefile.toml'),'projected_sha256':sha(D/'projected-lakefile.toml')})
# Recover only the newly approved LinkClifN native archive into its namespace.
origin=O/'linkclifn-native-origin-v1/receipt.json'
assert sha(origin)=='80b88531222f938492a1cc16140b561195c99bd084bb14b165d3ce5f8ba30bb8'
entry=json.loads(origin.read_text())['records']['FV/E2E/LinkClifN.lean']['matched']
archive=E/'892-current-main-context-v1/package/.lake/ci-cache/artifacts'/entry['archive']
assert sha(archive)==entry['archive_sha256']
current_input('FV.E2E.LinkClifN')
scratch=D/'linkclifn-scratch';scratch.mkdir();lib=scratch/'lib';ir=scratch/'ir';lib.mkdir();ir.mkdir()
payload=json.dumps([{'file':str(archive),'base':[str(lib),str(ir)],'hash':expected['FV.E2E.LinkClifN']}])
cap('LinkClifN-native-extract',[str(tool/'leantar'),'--jobs','1','-x','-j','-'],payload)
for ext,root,directory in [('olean',lib,'lib/lean'),('ilean',lib,'lib/lean'),('c',ir,'ir')]:
 files=list(root.rglob('*.'+ext));assert len(files)==1
 assert sha(files[0])==entry['payloads'][ext]['extracted_sha256']
 copy_owned(files[0],F/'.lake/build'/directory/('FV/E2E/LinkClifN.'+ext))
traces=list(lib.rglob('*.trace'));assert len(traces)==1
assert json.loads(traces[0].read_text())['depHash']==expected['FV.E2E.LinkClifN']
copy_owned(traces[0],F/'.lake/build/lib/lean/FV/E2E/LinkClifN.trace')
cap('LinkClifN-normal',[str(tool/'lake'),'build','--no-build','FV.E2E.LinkClifN'])
output_record('FV.E2E.LinkClifN',{'approved_native_origin_sha256':sha(origin),'archive_sha256':sha(archive),'namespace_paths_checked':True})
shutil.rmtree(scratch)
for i,m in enumerate(targets):
 current_input(m)
 cap('leaf-'+str(i),[str(tool/'lake'),'-v','build','+'+m+':leanArts'],leaf=m)
 origin_record={'actual_leaf_record':records[-1]}
 cap(m.split('.')[-1]+'-normal',[str(tool/'lake'),'build','--no-build',m])
 output_record(m,origin_record)
for row in previous['outputs'].values():
 for path,h in row['artifacts'].items():assert sha(F/path)==h,('Phase1 output changed',path)
cap('normal382',[str(tool/'lake'),'build','--no-build',*sorted(covered|set(targets)|{'FV.E2E.LinkClifN'})])
save(D/'receipt.json',{'status':'passed_approved_phase2_exact_382_normal_context','records':records,'outputs':outputs,'phase1_receipt_sha256':sha(phase1),'phase1_outputs_unchanged':True,'all_sources_verified':{m:v['source_sha256']for m,v in G.items()},'configs':S['config_hashes'],'no_dependency_Lean_builds':True,'approved_target_order':targets,'recovered_only':'FV.E2E.LinkClifN','source2_acquire1_restore_on_owner_exit':True,'remaining_eight_kernels_authorized':False,'full_goal_complete':False})
print('Phase2 passed. Both shares restore after all commands exit.',flush=True)
