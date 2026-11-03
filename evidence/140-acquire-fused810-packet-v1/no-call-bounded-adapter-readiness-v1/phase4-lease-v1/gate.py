from common import *
import hashlib,subprocess,sys,shutil,tomllib,re
B=Path('/home/lee/clifv');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
proposal=O/'bounded-phase4-proposal-v1.json';assert sha(proposal)=='3b38b40190229785daaf06be488e068130b97055651b5a901664a884c75bf40c'
release=json.loads((D/'start-approved.json').read_text());assert release['parent_resource_approved'] and release['source2_released'] and release['acquire1_released']
S=json.loads((D/'temporary-import-snapshot-v26.json').read_text());I=json.loads((O/'inventory.json').read_text());G=I['no_call_definitions']['modules'];Q=json.loads((O/'normal-readiness-v4.json').read_text());expected={r['module']:r['expected_key']for r in Q['queries']if r.get('expected_key')}
phase1=O/'phase1-lease-v3/receipt.json'
assert sha(phase1)=='c7e56d5dd6602b03bc922c81959d65737bcde81e9949ff65db5ec4bef279fbce'
previous=json.loads(phase1.read_text())
for row in previous['outputs'].values():
 for path,h in row['artifacts'].items():assert sha(F/path)==h,('Phase1 output changed',path)
phase2=O/'phase2-lease-v1/receipt.json'
assert sha(phase2)=='46815667197d62b9a273a2ec344c8bd81ebb82d9555e9faace42dc29fda0455d'
previous2=json.loads(phase2.read_text())
for row in previous2['outputs'].values():
 for path,h in row['artifacts'].items():assert sha(F/path)==h,('Phase2 output changed',path)
phase3=O/'phase3-lease-v1/receipt.json'
assert sha(phase3)=='036a165c1c4c3a35c5c6e2e93993baaf4ca66971e746e198ac498ec7e2e503e6'
previous3=json.loads(phase3.read_text())
for row in previous3['outputs'].values():
 for path,h in row['artifacts'].items():assert sha(F/path)==h,('Phase3 output changed',path)
covered=set(Q['existing374'])|set(previous['outputs'])|set(previous2['outputs'])|set(previous3['outputs']);assert len(covered)==384
queries=json.loads((O/'downstream-eleven-query-v1/receipt.json').read_text())
newExpected={r['module']:r['expected_key']for r in queries['records']if r['expected_key']}
assert newExpected=={'FV.E2E.LinkWorldX':'b35c5e3883905110','FV.E2E.LinkClifN':'449ed896fdcb130e','FV.E2E.Link':'cc2f9f2e01683268'}
expected.update(newExpected)
queries2=json.loads((O/'downstream-eight-query-v1/receipt.json').read_text())
nextExpected={r['module']:r['expected_key']for r in queries2['records']if r['expected_key']}
assert nextExpected=={'FV.E2E.CompiledEither':'cfa5ab1ba93a25fe','FV.E2E.LinkPlace':'5c9ee145acafbded'}
expected.update(nextExpected)
queries3=json.loads((O/'downstream-six-query-v1/receipt.json').read_text())
newestExpected={r['module']:r['expected_key']for r in queries3['records']if r['expected_key']}
assert newestExpected=={'FV.E2E.LinkArm':'5b69d2172986191e','FV.E2E.CompiledEitherW':'d5e7fd26cd02855c'}
expected.update(newestExpected)
targets=['FV.E2E.LinkArm']
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
 clean_overlap();env['FV_MEMCAP_UNIT']='worker-o-acquire-phase4-v1-'+label;env['FV_MEMCAP_STATS']=str(D/(label+'.mem'))
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

cap('projection-normal384',[str(tool/'lake'),'build','--no-build',*sorted(covered)])
projectionKeys={}
for name,key in expected.items():
 actual=cap('projection-key-'+name.split('.')[-1],[str(tool/'lake'),'query','--no-build','+'+name+':depHash'])
 assert actual==key,(name,'Weak projection changed native key',actual,key)
 projectionKeys[name]=actual
save(D/'projection-normal-key-receipt-v1.json',{'status':'passed_actual384_normal_and_all_twelve_keys_unchanged','keys':projectionKeys,'config_hashes':S['config_hashes'],'canonical_sha256':sha(D/'canonical-lakefile.toml'),'projected_sha256':sha(D/'projected-lakefile.toml')})
# Recover only the exact creator-bound retained CompiledEitherW variant.
coherence=O/'retained-CompiledEitherW-provider-coherence-v1.json'
binding=O/'retained-CompiledEitherW-C-content-binding-v1.json'
assert sha(coherence)=='27565fc1e92021100ea924e549c609741ff6959508bc0125c91c23fd82dd1600'
assert sha(binding)=='6ea54535f2b5fb06df9d2b3e0a97e06d7eca7d44567b7fe555d70fb979ac5d88'
evidence=json.loads(coherence.read_text());Cbinding=json.loads(binding.read_text())
creator=E/'direct-call-store-live-packet-v1/fault-world-w-prep-v1/linked-w-four-providers-v1/receipt.json'
assert sha(creator)==evidence['creator_receipt_sha256']
assert sha(E/'direct-call-store-live-packet-v1/fault-world-w-prep-v1/verify-four-w-providers-v1.py')==evidence['creator_script_sha256']
assert sha(E/'direct-call-store-live-packet-v1/fault-world-w-prep-v1/linked-w-dependencies384-v1.json')==evidence['creator_dependencies_sha256']
assert sha(E/'direct-call-store-live-packet-v1/fault-world-w-prep-v1/historical-R-preserved-before-c4f-v1/receipt.json')==evidence['preservation_receipt_sha256']
current_input('FV.E2E.CompiledEitherW')
for module,row in evidence['source_dependency_closure'].items():
 rel=Path(module.replace('.','/')+'.lean')
 assert sha(F/rel)==row['source_sha256']==row['creator_source_sha256']==row['preserved_source_sha256']
 if module!='FV.E2E.CompiledEitherW':
  td=json.loads((F/'.lake/build/lib/lean'/rel.with_suffix('.trace')).read_text())
  assert td['depHash']==row['F_native_key']==row['creator_native_key'] and td['outputs']==row['F_outputs']==row['creator_outputs']
root=E/'direct-call-store-live-packet-v1/fault-world-w-prep-v1/historical-R-preserved-before-c4f-v1/owned-outputs'
assert sha(Path(Cbinding['actual_C_path']))==Cbinding['actual_content_sha256']
assert Cbinding['native_content_hash']+'.c'==evidence['creator_record']['outputs']['c']
assert json.loads(Path(evidence['retained_trace_path']).read_text())['depHash']==expected['FV.E2E.CompiledEitherW']
for artifact,row in evidence['payloads'].items():
 assert sha(root/artifact)==row['sha256']==row['preservation_sha256']
 if row['creator_record_sha256']:assert row['sha256']==row['creator_record_sha256']
for artifact in evidence['payloads']:
 assert artifact.startswith('.lake/build/lib/lean/FV/E2E/CompiledEitherW.') or artifact.startswith('.lake/build/ir/FV/E2E/CompiledEitherW.')
 copy_owned(root/artifact,F/artifact)
cap('CompiledEitherW-normal',[str(tool/'lake'),'build','--no-build','FV.E2E.CompiledEitherW'])
output_record('FV.E2E.CompiledEitherW',{'approved_retained_coherence_sha256':sha(coherence),'approved_C_native_content_binding_sha256':sha(binding),'creator_receipt_sha256':sha(creator)})
for i,m in enumerate(targets):
 current_input(m)
 cap('leaf-'+str(i),[str(tool/'lake'),'-v','build','+'+m+':leanArts'],leaf=m)
 origin_record={'actual_leaf_record':records[-1]}
 cap(m.split('.')[-1]+'-normal',[str(tool/'lake'),'build','--no-build',m])
 output_record(m,origin_record)
for row in previous['outputs'].values():
 for path,h in row['artifacts'].items():assert sha(F/path)==h,('Phase1 output changed',path)
for row in previous2['outputs'].values():
 for path,h in row['artifacts'].items():assert sha(F/path)==h,('Phase2 output changed',path)
for row in previous3['outputs'].values():
 for path,h in row['artifacts'].items():assert sha(F/path)==h,('Phase3 output changed',path)
cap('normal386',[str(tool/'lake'),'build','--no-build',*sorted(covered|set(targets)|{'FV.E2E.CompiledEitherW'})])
save(D/'receipt.json',{'status':'passed_approved_phase4_exact_386_normal_context','records':records,'outputs':outputs,'phase1_receipt_sha256':sha(phase1),'phase2_receipt_sha256':sha(phase2),'phase2_outputs_unchanged':True,'phase3_receipt_sha256':sha(phase3),'phase3_outputs_unchanged':True,'phase1_outputs_unchanged':True,'all_sources_verified':{m:v['source_sha256']for m,v in G.items()},'configs':S['config_hashes'],'no_dependency_Lean_builds':True,'approved_target_order':targets,'recovered_only':'FV.E2E.CompiledEitherW','source2_acquire1_restore_on_owner_exit':True,'remaining_four_kernels_authorized':False,'full_goal_complete':False})
print('Phase4 passed. Both shares restore after all commands exit.',flush=True)
