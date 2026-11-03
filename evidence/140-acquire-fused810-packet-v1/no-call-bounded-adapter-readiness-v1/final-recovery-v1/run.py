from pathlib import Path
import os,json,hashlib,subprocess,psutil,time,shutil,datetime
D=Path(__file__).resolve().parent;O=D.parent;E=O.parent.parent;F=E/'140-fence-packet-v1/package';B=Path('/home/lee/clifv')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def save(v):(D/'receipt.json').write_text(json.dumps(v,indent=2)+'\n')
proposal=O/'bounded-final-recovery-proposal-v1.json';assert sha(proposal)=='3b681bbc849ce029a499c008cf20686c8cef6540e10bf54a50c14e1425b5d5fa'
P=json.loads(proposal.read_text());cp=O/'retained-LinkGoodBoundedW-F-coherence-v1.json';assert sha(cp)==P['current_F_coherence_sha256'];C=json.loads(cp.read_text())
bp=O/'retained-LinkGoodBoundedW-native-payload-binding-v1.json';assert sha(bp)==P['cold_payload_binding_sha256'];binding=json.loads(bp.read_text())
creator=E/'direct-call-store-live-packet-v1/fault-world-w-prep-v1/retained-LinkGoodBoundedW-ea71-creator-binding-v1.json';assert sha(creator)==P['historical_creator_binding_sha256'];origin=json.loads(creator.read_text())
S=json.loads((E/'140-fence-packet-v1/import-snapshot-v25.json').read_text());G=json.loads((O/'inventory.json').read_text())['no_call_definitions']['modules'];Q=json.loads((O/'normal-readiness-v4.json').read_text());covered=set(Q['existing374']);prior={}
for phase in ['phase1-lease-v3','phase2-lease-v1','phase3-lease-v1','phase4-lease-v1','phase5-lease-v1','phase6-ordinary-v1']:
 v=json.loads((O/phase/'receipt.json').read_text());covered.update(v['outputs'])
 for m,row in v['outputs'].items():prior[m]=row
assert len(G)==390 and len(covered)==389 and set(G)-covered=={'FV.E2E.LinkGoodBoundedW'}
for path,h in S['config_hashes'].items():assert sha(F/path)==h
for m,row in C['source_dependency_closure'].items():
 rel=Path(m.replace('.','/')+'.lean');assert sha(F/rel)==row['source_sha256']==row['creator_source_sha256']
 if m!='FV.E2E.LinkGoodBoundedW':
  td=json.loads((F/'.lake/build/lib/lean'/rel.with_suffix('.trace')).read_text());assert td['depHash']==row['F_native_key']and td['outputs']==row['F_outputs']
for field in ['creator_context','preserved_mapping']:assert sha(Path(origin[field+'_path']))==origin[field+'_sha256']
for kind in ['progress','kernel_log','memory']:assert sha(Path(origin['creator'][kind+'_path']))==origin['creator'][kind+'_sha256']
assert sha(E/'direct-call-store-live-packet-v1/fault-world-w-prep-v1/verify-bounded-W-extraction-kernels-v1.py')==C['creator_script_sha256']
for row in binding['records'].values():assert sha(Path(row['path']))==row['sha256']
for rel,row in P['approved_recovery_paths_requested'].items():
 assert sha(Path(row['retained_path']))==row['sha256']
 assert not(F/rel).exists(),('Never overwrite',rel)
assert len(P['approved_recovery_paths_requested'])==7
state={'status':'preflight','authority':'Parent approved only exact final recovery3b681bbc; no kernel/config/share change','proposal_sha256':sha(proposal),'coherence_sha256':sha(cp),'creator_binding_sha256':sha(creator),'native_payload_binding_sha256':sha(bp),'records':[],'copied':{},'provider_builds':False,'config_changed':False,'source_or_broad_share_borrowed':False,'full_goal_complete':False};save(state)
env=dict(os.environ)
for k in ['FV_LAKE_CACHE','FV_MEMCAP_OFF','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','LAKE_CACHE_DIR']:env.pop(k,None)
tool=Path(S['lean_executable']).parent;env.update(PATH=str(tool)+':'+env['PATH'],FV_ROOT=str(F),FV_MEMCAP='1G',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LAKE_CACHE_DIR=str(E/'140-fence-packet-v1/disabled-cache'))
def unchanged():
 for rel,h in S['config_hashes'].items():assert sha(F/rel)==h
 for row in prior.values():
  for rel,h in row['artifacts'].items():assert sha(F/rel)==h,('Prior output changed',rel)
def cap(label,args):
 assert args[:2]in [['build','--no-build'],['query','--no-build']]
 unchanged()
 env['FV_MEMCAP_UNIT']='worker-o-final-recovery-'+label;env['FV_MEMCAP_STATS']=str(D/(label+'.mem'))
 for p in psutil.process_iter(['name','cmdline','status']):
  try:
   if p.info['status']!='zombie'and p.info['name']in['lean','lake','leantar']:assert not(p.cwd()==str(F)or any(str(F)in a for a in p.info['cmdline']or[])),('Other F consumer',p.pid)
  except(psutil.NoSuchProcess,psutil.AccessDenied):pass
 command=[str(B/'.worktrees/stock-extending-production-20261031/scripts/memcap.sh'),str(tool/'lake'),*args]
 with(D/(label+'.stdout')).open('w')as out,(D/(label+'.stderr')).open('w')as err:rc=subprocess.call(command,cwd=F,env=env,stdout=out,stderr=err)
 rec={'label':label,'argv':command,'exit':rc,'stats':(D/(label+'.mem')).read_text()if(D/(label+'.mem')).exists()else None};state['records'].append(rec);state['status']='running'if rc==0 else 'failed';save(state);assert rc==0,('Stop first failure',label,rc)
 return(D/(label+'.stdout')).read_text().strip()
cap('normal389',['build','--no-build',*sorted(covered)])
key=cap('final-key',['query','--no-build','+FV.E2E.LinkGoodBoundedW:depHash']);assert key==P['expected_key']=='ea71a143faf1eb2c'
for rel,row in P['approved_recovery_paths_requested'].items():
 src=Path(row['retained_path']);dest=F/rel;dest.parent.mkdir(parents=True,exist_ok=True)
 with src.open('rb')as read,dest.open('xb')as write:shutil.copyfileobj(read,write)
 assert sha(dest)==row['sha256'];state['copied'][rel]=sha(dest);save(state)
cap('final-leaf-normal',['build','--no-build','FV.E2E.LinkGoodBoundedW'])
cap('normal390',['build','--no-build',*sorted(G)])
unchanged();rel=Path('FV/E2E/LinkGoodBoundedW.lean');tr=F/'.lake/build/lib/lean'/rel.with_suffix('.trace');td=json.loads(tr.read_text());assert td['depHash']==key and td['outputs']==C['outputs']
artifacts={}
for directory in ['lib/lean','ir']:
 stem=F/'.lake/build'/directory/rel.with_suffix('')
 for p in stem.parent.glob(stem.name+'.*'):
  if p.is_file():artifacts[str(p.relative_to(F))]=sha(p)
state.update(status='passed_complete_proper_normal390_after_exact_creator_recovery',sources={m:sha(F/Path(m.replace('.','/')+'.lean'))for m in G},configs=S['config_hashes'],final_native_key=key,final_outputs=td['outputs'],final_artifacts=artifacts,prior_outputs_unchanged=True,canonical_config_unchanged=True,historical_setup_not_copied=True,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());save(state);print('Final exact recovery and complete390 normal passed. No compiler or config/share change.',flush=True)
