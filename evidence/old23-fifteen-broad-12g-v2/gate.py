from pathlib import Path
import json,hashlib,os,subprocess,psutil,re,shutil,tempfile,importlib.util,tomllib
D=Path(__file__).resolve().parent;E=D.parent;Q=E/'direct-call-store-live-packet-v1';R=Q/'validation-package-v1';P=E/'892-joint-current-context-v2/package';C=Q/'production-current8f-dispatcher-integration-v1';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();proposal=C/'old23-fifteen-repair-proposal-v1.json';assert sha(proposal)=='5e1544450469f3f7efc89db54914d98ef5b36c002a68b1ee0b538a7f92a3d8e5';I=json.loads(proposal.read_text());release=json.loads((D/'command-release-v1.json').read_text());assert release['approved'] and release['allocation']=='12G' and release['script_sha256']==sha(Path(__file__)) and release['manifest_sha256']==sha(proposal);g=I['complete_graph'];sources=I['complete_source_hashes'];names=[x['target'] for x in I['topological_nodes']];assert len(names)==15;prepared=json.loads((D/'prepared-inputs.json').read_text());assert sha(D/'named-approved-origins.json')==prepared['named_origins_sha256'];assert sha(P/'scripts/memcap.sh')==prepared['canonical_memcap_sha256'];known=json.loads((D/'named-approved-origins.json').read_text());protected={};normal_receipt=C/'ordinary1715-creator-binding-v1/receipt.json';N=json.loads(normal_receipt.read_text())
for n,e in N['records'].items():
 rel=n.replace('.','/');protected['.lake/build/lib/lean/'+rel+'.trace']=e['trace_sha256']
 for ext,h in e['payload_sha256'].items():protected['.lake/build/'+('ir' if ext=='c' else 'lib/lean')+'/'+rel+'.'+ext]=h
protected.update(json.loads((C/'ten-source-projection-run-v1/receipt.json').read_text())['protected_prior_W_outputs'])
for file in ['ABI-W716-focused-v1/receipt.json','independent-void-NI-and-W-v1/receipt.json','ordinary-dispatcher-kernels-v1/receipt.json']:
 data=json.loads((C/file).read_text())['outputs']
 if file.startswith('ABI-'):protected.update(data)
 else:
  for e in data.values():protected.update(e['artifacts'])
assert not any(any(rel.startswith('.lake/build/'+area+'/'+n.replace('.','/')+'.') for area in ['lib/lean','ir']) for rel in protected for n in names),'Target overlaps protected passed outputs'
assert '-j1' in json.dumps(tomllib.loads((R/'lakefile.toml').read_text()))
env=dict(os.environ)
for k in ['FV_MEMCAP_OFF','FV_LAKE_CACHE','LEAN_PATH','LEAN_SYSROOT','LEAN_SRC_PATH','LAKE_CACHE_DIR']:env.pop(k,None)
env.update(PATH='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+env['PATH'],FV_ROOT=str(R),FV_MEMCAP='12G',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2');commands=[];passed={}
def guards(check_outputs=False):
 controller=psutil.Process(release['broad_controller_pid']);assert controller.create_time()==release['scheduler_birth'] and controller.status()==psutil.STATUS_STOPPED
 assert not any(p.is_running() and p.status()!=psutil.STATUS_ZOMBIE for p in controller.children(recursive=True))
 for p in psutil.process_iter(['uids','name','status']):
  try:
   if p.info['uids'].real==os.getuid() and p.info['name'] in ['lean','lake'] and p.info['status']!='zombie':assert not p.cwd().startswith(str(R)),p.pid
  except(psutil.NoSuchProcess,psutil.AccessDenied):pass
 for f,h in I['configs'].items():assert sha(R/f)==h,f
 for n,h in sources.items():assert sha(R/Path(n.replace('.','/')+'.lean'))==h,n
 if check_outputs:
  for rel,h in protected.items():assert sha(R/rel)==h,rel

def run(label,args,allowed=(0,)):
 guards();e=dict(env,FV_MEMCAP_STATS=str(D/(label+'.mem')),FV_MEMCAP_UNIT='worker-o-old23-fifteen-'+label)
 with (D/(label+'.log')).open('w') as out:rc=subprocess.call([str(P/'scripts/memcap.sh'),*args],cwd=R,env=e,stdout=out,stderr=subprocess.STDOUT)
 mem=(D/(label+'.mem')).read_text();commands.append({'label':label,'argv':args,'exit':rc,'memory':mem,'log_sha256':sha(D/(label+'.log'))});(D/'progress.json').write_text(json.dumps(commands,indent=2)+'\n');print(label,rc,flush=True);assert rc in allowed and 'oom 0\n' in mem and 'oom_kill 0\n' in mem,(label,rc);return rc

def closure(n):
 seen=set();todo=g[n][:]
 while todo:
  a=todo.pop()
  if a in seen:continue
  seen.add(a);todo+=g[a]
 return seen

def origin(n):
 rel=Path(n.replace('.','/'));tr=R/'.lake/build/lib/lean'/rel.with_suffix('.trace');md=json.loads(tr.read_text());assert not md.get('synthetic'),n
 payload={ext:sha(R/('.lake/build/ir' if ext=='c' else '.lake/build/lib/lean')/rel.with_suffix('.'+ext)) for ext in ['olean','ilean','c']}
 if md.get('inputs'):kind='full-input native creator'
 else:
  a=known.get(n);assert a and a['native_key']==md['depHash'] and a['trace_sha256']==sha(tr) and a['payload_sha256']==payload,(n,'unsupported compact creator')
  for ref in a['approved_origins']:
   f=Path(ref['receipt']);assert sha(f)==ref.get('receipt_sha256',ref.get('sha256'))
  kind='specifically approved archive-derived creator'
 return {'native_key':md['depHash'],'trace_sha256':sha(tr),'payload_sha256':payload,'creator':kind}

def artifacts(n):
 out={}
 for area in ['lib/lean','ir']:
  stem=R/'.lake/build'/area/n.replace('.','/')
  for p in stem.parent.glob(stem.name+'.*'):
   if p.is_file():out[str(p.relative_to(R))]=sha(p)
 return out

def preserve_and_detach(n):
 for rel,h in artifacts(n).items():
  target=R/rel;parent=target.parent.resolve(strict=True);assert parent.is_relative_to(R.resolve());a=parent
  while True:
   assert a.stat().st_uid==os.getuid()
   if a==R.resolve():break
   a=a.parent
  saved=D/'old-target-outputs'/rel;saved.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(target,saved);assert sha(saved)==h
  if target.is_symlink() or target.stat().st_nlink!=1 or not target.stat().st_mode&0o200:
   fd,tmp=tempfile.mkstemp(prefix='.old23-detach-',dir=parent);os.close(fd);shutil.copyfile(target,tmp);assert sha(Path(tmp))==h;os.replace(tmp,target)

guards(True);unaffected=sorted(set(g)-set(names));assert len(unaffected)==1730
assert sha(D/'continuation-input.json')==prepared['continuation_sha256'];continuation=json.loads((D/'continuation-input.json').read_text());prior=Path(continuation['complete_creator_classification']);assert sha(prior)==continuation['complete_creator_classification_sha256'];old_classification=json.loads(prior.read_text());origins={n:origin(n) for n in unaffected}
for n,e in origins.items():
 previous=old_classification['unaffected1730_records'][n]
 assert e['native_key']==previous['native_key'] and e['trace_sha256']==previous['trace_sha256'] and e['payload_sha256']==previous['payload_sha256'],n
(D/'reused-unaffected1730-normal.json').write_text(json.dumps({'original_normal_exit':0,'original_normal_log_sha256':old_classification['passed_stage_commands'][0]['log_sha256'],'all_current_source_config_trace_key_payload_bindings_match':True,'complete_creator_classification_sha256':sha(prior)}))
(D/'unaffected-creators.json').write_text(json.dumps(origins,indent=2)+'\n')
for index,entry in enumerate(I['topological_nodes']):
 n=entry['target'];deps=closure(n);assert deps
 run('deps'+str(index),['lake','build','--no-build',*sorted(deps)]);run('key'+str(index),['lake','query','--no-build','+'+n+':depHash']);keys=re.findall(r'^[0-9a-f]{16}$',(D/('key'+str(index)+'.log')).read_text(),re.M);assert len(keys)==1
 if entry.get('actual_current_key'):assert keys==[entry['actual_current_key']],(n,'root key drift')
 (D/('bound-key'+str(index)+'.json')).write_text(json.dumps({'target':n,'key':keys[0],'dependencies_normal':True,'source_sha256':sources[n]}))
 ready=run('ready'+str(index),['lake','build','--no-build',n],allowed=(0,3))==0
 if not ready:
  # BodySplit's exact current P artifact remains held. Fresh R compilation is explicitly approved.
  candidates=[]
  tr=P/'.lake/build/lib/lean'/Path(n.replace('.','/')+'.trace')
  if tr.exists() and json.loads(tr.read_text()).get('depHash')==keys[0] and n!='FV.Backend.Proof.StockMemorySretCopyBodySplit':candidates.append({'owner':'P','trace':str(tr),'sha256':sha(tr)})
  for label,cache in [('A',Path('/home/lee/clifv/.worktrees/driver-proof-resume/.lake/artifact-cache')),('C',E/'892-current-main-context-v1/package/.lake/ci-cache')]:
   f=cache/'outputs/fv'/(keys[0]+'.json')
   if f.exists():
    item={'owner':label,'descriptor':str(f),'sha256':sha(f)}
    exact_held=(n=='FV.Backend.Proof.StockMemorySretCopyBodySplit' and label=='C' and str(f)==str(E/'892-current-main-context-v1/package/.lake/ci-cache/outputs/fv/63903f5e5fce0ef6.json') and item['sha256']=='9728c487f8408c97286861a791fb7813fa9c1fcb4f83b34dc0c161df274500aa')
    if exact_held:
     item.update(action='matched held descriptor;no artifact consumed;fresh R compilation approved',setup_differences_held=21)
     (D/('held-BodySplit-descriptor'+str(index)+'.json')).write_text(json.dumps(item,indent=2)+'\n')
     preserved=D/('held-BodySplit-descriptor'+str(index)+'.raw.json');shutil.copyfile(f,preserved);assert sha(preserved)==item['sha256'] and sha(f)==item['sha256']
    else:candidates.append(item)
  (D/('matching-candidates'+str(index)+'.json')).write_text(json.dumps(candidates,indent=2)+'\n');assert not candidates,(n,'matching donor/cache needs exact review before a duplicate build')
  preserve_and_detach(n);run('kernel'+str(index),['lake','-v','build','+'+n+':leanArts'])
 run('normal'+str(index),['lake','build','--no-build',n]);e=origin(n);assert e['native_key']==keys[0];e['artifacts']=artifacts(n);e['existing_normal_reused']=ready;passed[n]=e;(D/'passed-targets.json').write_text(json.dumps(passed,indent=2)+'\n')
run('complete1745',['lake','build','--no-build',*sorted(g)]);origins={n:origin(n) for n in g};(D/'consumed-creators1745.json').write_text(json.dumps(origins,indent=2)+'\n');old_inventory=Q/'production-call-store-constructor-proposal-v1/old-contract-inventory-v2.json';old=json.loads(old_inventory.read_text())
for n,e in old['roots'].items():assert e['header'] in (R/e['source']).read_text(),n
roots=sorted(old['roots']);audit=D/'old23.lean';modules=sorted({e['source'][:-5].replace('/','.') for e in old['roots'].values()});audit.write_text(''.join('import '+n+'\n' for n in modules)+''.join('#print axioms '+n+'\n' for n in roots));run('real-old23-audit',['python3',str(P/'scripts/axiom-audit.py'),'--cwd',str(R),'--log-dir',str(D/'audit'),str(audit)])
spec=importlib.util.spec_from_file_location('records',E/'general7-main-candidate-v1/old-axiom-preservation-v1/axiom_records.py');collector=importlib.util.module_from_spec(spec);spec.loader.exec_module(collector);axes={}
for p in (D/'audit').glob('*.log'):
 for n,a in collector.parse_records(p.read_text()):assert n not in axes;axes[n]=sorted(a)
assert set(axes)==set(roots)
for n,e in old['roots'].items():assert axes[n]==sorted(e['prior_exact_AX']),(n,axes[n],e['prior_exact_AX'])
assert axes['E2E.ReturnPinMode.pins_of_valid']==[];guards(True);f=D/'receipt.json';f.write_text(json.dumps({'status':'PASSED_CURRENT8F_OLD23_REPAIR_NORMAL1745_EXACT_AX','proposal_sha256':sha(proposal),'release_sha256':sha(D/'command-release-v1.json'),'configs':I['configs'],'targets':passed,'commands':commands,'consumed_creators1745_sha256':sha(D/'consumed-creators1745.json'),'old23_axiom_sets':axes,'all23_old_headers_exact':True,'protected_outputs_unchanged':True,'no_G_access':True,'new_setup_exceptions':[],'BodySplit_donor':'held;fresh R only if required','full_dispatcher_activation':'OPEN'},indent=2)+'\n');print('receipt',sha(f))
