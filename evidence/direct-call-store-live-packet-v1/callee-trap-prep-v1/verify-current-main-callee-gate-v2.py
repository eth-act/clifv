from pathlib import Path
import datetime,hashlib,json,os,re,shutil,subprocess,psutil
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';T=Path(__file__).resolve().parent;Q=T.parent;R=Q/'validation-package-v1';J=E/'892-joint-current-context-v2/package';L=T/'current-main-callee-gate-v2';L.mkdir();base='770e543c350bf158dc782b7f80afb9748817e0af';sources={};dag={};C=T/'standalone-callee-canonical-v2';M=json.loads((C/'manifest.json').read_text());new={n for n in M['source_hashes'] if n.startswith('FV/')};todo=sorted(new)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
S=Q/'standalone-class-canonical-v1';prior=json.loads((S/'manifest.json').read_text());retained=set(prior['source_hashes'])
for n,h in prior['source_hashes'].items():assert sha(S/n)==h,n
while todo:
 n=todo.pop()
 if n in sources:continue
 data=(C/n).read_bytes() if n in new else subprocess.check_output(['git','show',base+':'+n],cwd=B)
 if n not in new and n not in retained:
  if (J/n).exists() and (J/n).read_bytes()==data:pass
  else:assert (R/n).exists() and (R/n).read_bytes()==data,('No exact current source provider',n)
 sources[n]=data;dag[n]=[x.replace('.','/')+'.lean' for x in re.findall(r'^import\s+([\w.]+)',data.decode(),re.M) if x.startswith(('FV.','FVTest.'))];todo.extend(dag[n])
active=[]
for p in psutil.process_iter(['pid','name','cmdline','status']):
 try:
  if p.info['name']!='lean' or p.info['status']=='zombie':continue
  for arg in p.info['cmdline'] or []:
   if arg.startswith(str(J)+'/') and arg.endswith('.lean') and str(Path(arg).relative_to(J)) in sources:active.append(dict(pid=p.pid,path=arg))
 except(psutil.NoSuchProcess,psutil.AccessDenied):pass
assert not active,('Active baseline provider',active)
for n,data in sources.items():
 p=R/n;p.parent.mkdir(parents=True,exist_ok=True)
 if n not in new and p.exists():assert p.read_bytes()==data,n
 p.write_bytes(data)
 if n in new:continue
 if not (J/n).exists() or (J/n).read_bytes()!=data:continue
 stem=Path(n).with_suffix('')
 for area in ['lib/lean','ir']:
  p=J/'.lake/build'/area/stem
  for src in p.parent.glob(p.name+'.*'):
   if not src.is_file():continue
   dest=R/src.relative_to(J)
   if dest.exists():continue
   dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dest)
configs={n:sha(R/n) for n in ['lean-toolchain','lakefile.toml','lake-manifest.json']}
for n in configs:
 published=subprocess.check_output(['git','show',base+':'+n],cwd=B)
 expected=published.replace(b'weakLeanArgs = [',b'weakLeanArgs = ["-j1",',1) if n=='lakefile.toml' else published
 assert (R/n).read_bytes()==expected,n
keys={}
def key(n):
 if n not in keys:keys[n]=hashlib.sha256(json.dumps([configs,hashlib.sha256(sources[n]).hexdigest(),[(d,key(d)) for d in sorted(dag[n])]],sort_keys=True).encode()).hexdigest()
 return keys[n]
for n in sources:key(n)
context=dict(status='running',base=base,source_hashes={n:hashlib.sha256(data).hexdigest() for n,data in sources.items()},imports=dag,dependency_keys=keys,configs=configs,no_duplicate_active_provider=True,no_shared_writes=True,budget='2G-j1');(L/'context.json').write_text(json.dumps(context,indent=2)+'\n')
for n in new:
 if n in sources:
  p=L/'source-snapshot'/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(sources[n])
env=dict(os.environ)
for k in ['FV_LAKE_CACHE','FV_MEMCAP_OFF','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT']:env.pop(k,None)
env.update(PATH='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+env['PATH'],FV_ROOT=str(R),FV_MEMCAP='2G',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1');records=[]
for label,argv in [('providers-and-14-normal-keys',['lake','build','--no-build',*[n[:-5].replace('/','.') for n in sources]]),('14-current-kernel-targets',['lake','build',*[n[:-5].replace('/','.') for n in sorted(new)]])]:
 env['FV_MEMCAP_UNIT']='worker-o-call-store-'+label;env['FV_MEMCAP_STATS']=str(L/(label+'.mem'))
 with (L/(label+'.log')).open('w') as stream:rc=subprocess.call([str(J/'scripts/memcap.sh'),*argv],cwd=R,env=env,stdout=stream,stderr=subprocess.STDOUT)
 records.append(dict(label=label,argv=argv,exit=rc,stats=(L/(label+'.mem')).read_text() if (L/(label+'.mem')).exists() else None));(L/'progress.json').write_text(json.dumps(dict(status='running' if rc==0 else 'failed',records=records),indent=2)+'\n');print(label,'exit',rc,flush=True)
 if rc:raise SystemExit(rc)
# Bind the real auditor to its exact landed bytes. Preserve the previous old46/new68 AX sets.
A=J/'scripts/axiom-audit.py';assert A.read_bytes()==subprocess.check_output(['git','show',base+':scripts/axiom-audit.py'],cwd=B)
env['PATH']=str(T/'tool-bin')+':'+env['PATH'];env['WORKER_O_AUDIT_COMMAND_LOG']=str(L/'actual-lean-commands.jsonl');env['FV_MEMCAP_STATS']=str(L/'audit.mem')
old=Q/'standalone-class-canonical-v1/scripts/audit/stock-call-store-class-final.lean';audit=C/'scripts/audit/stock-call-store-callee-complete.lean'
argv=['python3',str(A),'--cwd',str(R),'--log-dir',str(L/'audit'),str(old),str(audit)]
with (L/'audit-summary.log').open('w') as stream:rc=subprocess.call([str(J/'scripts/memcap.sh'),*argv],cwd=R,env=env,stdout=stream,stderr=subprocess.STDOUT)
print('actual-repository-auditor exit',rc,flush=True)
if rc:raise SystemExit(rc)
import sys
sys.path.insert(0,str(Q));from axiom_records import parse_records
expected=json.loads((T/'real-repository-audits-v2/exact-set-comparison.json').read_text())['axiom_sets']
actual=dict(parse_records((L/'audit'/(audit.stem+'.log')).read_text()));assert actual==expected
old_actual=dict(parse_records((L/'audit'/(old.stem+'.log')).read_text()));assert old_actual==json.loads((Q/'audit-class-v2/receipt.json').read_text())['axiom_sets']
outputs={}
for n in sources:
 stem=Path(n).with_suffix('');trace=R/'.lake/build/lib/lean'/stem.with_suffix('.trace');olean=R/'.lake/build/lib/lean'/stem.with_suffix('.olean');assert trace.exists() and olean.exists(),n
 outputs[n]=dict(trace=json.loads(trace.read_text()),trace_sha256=sha(trace),olean_sha256=sha(olean))
context.update(status='passed-current-main-candidate',records=records,base_tree=subprocess.check_output(['git','rev-parse',base+'^{tree}'],cwd=B,text=True).strip(),canonical_manifest_sha256=sha(C/'manifest.json'),audit_roots=68,axiom_sets=actual,old46_exact=True,old56_exact=True,real_repository_auditor_exit=rc,real_repository_auditor_sha256=sha(A),normal_outputs=outputs,original_input_hashes={n:sha(Q/n) for n in ['original-caller.clif','original-callee.clif']},config_delta='Only explicit -j1 in weakLeanArgs; exact pinned Lake trace policy',utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(L/'receipt.json').write_text(json.dumps(context,indent=2)+'\n')
print('current-main gate passed:',len(sources),'sources,14 kernels,68 roots',flush=True)
