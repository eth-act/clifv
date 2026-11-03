from pathlib import Path
import json,hashlib,subprocess,os,shutil,tempfile,psutil,tomllib,traceback
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';D=E/'general7-main-candidate-v1/current8f-full-reverse-inventory-v1';G=B/'.worktrees/loop-20261102';roots={'P':E/'892-joint-current-context-v2/package','R':E/'direct-call-store-live-packet-v1/validation-package-v1'};tool='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake';env=dict(os.environ,LAKE_RESTORE_ARTIFACTS='false')
L=D/'conditional-donor318-run-v2';L.mkdir();logs=L/'logs';logs.mkdir();preserved=L/'preserved';preserved.mkdir();prior=json.loads((D/'conditional-donor318-run-v1/receipt.json').read_text());assert len(prior['records'])==8;records=list(prior['records']);commands=[];done={x['target'] for x in records}
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()
proposal=D/'conditional-donor318-recovery-proposal-v1.json';assert sha(proposal)=='2f5102328475ca1f4d1df834c738b172a67ab4cbbc4b333a9e4fd34fc405ca7f';m=json.loads(proposal.read_text());base=json.loads((D/'remaining-cone-proposal-v1.json').read_text());disposition=json.loads((D/'complete3381-reviewed-origin-donor-disposition-v3.json').read_text());approved={x['target']:x['G_trace_sha256'] for x in disposition['rows'] if x['existing_approved_archive_matches']};config0={label:{f:sha(root/f) for f in ['lakefile.toml','lean-toolchain','lake-manifest.json']} for label,root in [('G',G),*roots.items()]};cache={}
def closure(n):
 if n not in cache:
  x={n}
  for a in base['imports'].get(n,[]):x|=closure(a)
  cache[n]=x
 return cache[n]
def check_configs():
 a=tomllib.loads((G/'lakefile.toml').read_text());a['weakLeanArgs']=[x for x in a.get('weakLeanArgs',[]) if x not in ['-j1','-j2']]
 for label,root in [('G',G),*roots.items()]:
  for f,h in config0[label].items():assert sha(root/f)==h,('config drift',label,f)
  b=tomllib.loads((root/'lakefile.toml').read_text());b['weakLeanArgs']=[x for x in b.get('weakLeanArgs',[]) if x not in ['-j1','-j2']];assert a==b
  for f in ['lean-toolchain','lake-manifest.json']:assert (root/f).read_bytes()==(G/f).read_bytes()
def writer_check(target):
 for z in psutil.process_iter(['pid']):
  try:
   if z.uids().real!=os.getuid():continue
   cmd=z.cmdline()
   if not cmd or Path(cmd[0]).name not in ['lean','lake','lake.orig','leanc']:continue
   cwd=z.cwd()
   if cwd.startswith(str(G)):raise AssertionError(('active G compiler',z.pid))
   for root in roots.values():
    if str(root/Path(target.replace('.','/')+'.lean')) in cmd:raise AssertionError(('active donor writer',target,z.pid))
  except (psutil.NoSuchProcess,psutil.AccessDenied):continue
counter=0
def run(root,args,label,allowed=(0,)):
 global counter
 counter+=1;f=logs/(str(counter).zfill(4)+'-'+label+'.log');p=subprocess.run([tool,*args],cwd=root,env=env,capture_output=True,text=True);f.write_text(p.stdout+'\nSTDERR\n'+p.stderr);commands.append({'root':str(root),'args':args,'exit':p.returncode,'log':str(f.relative_to(L)),'sha256':sha(f)});assert p.returncode in allowed,(label,p.returncode,str(f));return p
def payloads(root,target):
 rel=Path(target.replace('.','/'));out={}
 for area,ext in [('.lake/build/lib/lean','.trace'),('.lake/build/lib/lean','.olean'),('.lake/build/lib/lean','.ilean'),('.lake/build/lib/lean','.olean.hash'),('.lake/build/lib/lean','.ilean.hash'),('.lake/build/ir','.c'),('.lake/build/ir','.c.hash')]:
  f=Path(area)/rel.with_suffix(ext);out[str(f)]=sha(root/f)
 return out
def checkpoint(status,error=None):
 (L/'receipt.json').write_text(json.dumps({'status':status,'proposal_sha256':sha(proposal),'config0':config0,'records':records,'commands':commands,'error':error,'setup_and_nobuild_unchanged':True,'full326_and3381':'OPEN'},indent=2)+'\n')
try:
 check_configs()
 for i,row in enumerate(m['rows_topological']):
  n=row['target']
  if n in done:continue
  rel=Path(n.replace('.','/'));check_configs();writer_check(n);assert sha(G/rel.with_suffix('.lean'))==row['source_sha256'];deps=[x for x in base['complete_source_order'] if x in closure(n) and x!=n]
  run(G,['build','--no-build',*deps],str(i)+'-G-deps')
  for dep in deps:
   tr=G/'.lake/build/lib/lean'/Path(dep.replace('.','/')+'.trace');t=json.loads(tr.read_text());assert (not t.get('synthetic') and t.get('inputs')) or approved.get(dep)==sha(tr),('unsupported G dependency creator',n,dep)
  q=run(G,['--json','query','--no-build','+'+n+':depHash'],str(i)+'-G-key');key=json.loads(q.stdout.strip());gtr=G/'.lake/build/lib/lean'/rel.with_suffix('.trace');gt=json.loads(gtr.read_text()) if gtr.exists() else {};ready=run(G,['build','--no-build',n],str(i)+'-G-ready',(0,3))
  if ready.returncode==0 and not gt.get('synthetic') and gt.get('inputs') and gt.get('depHash')==key:
   records.append({'target':n,'key':key,'status':'already proper current normal; skipped'});checkpoint('RUNNING');continue
  donors=[]
  for candidate in row['provisional_donors']:
   label=candidate['owner'];root=roots[label];tr=root/'.lake/build/lib/lean'/rel.with_suffix('.trace')
   if not tr.exists():continue
   t=json.loads(tr.read_text())
   if t.get('synthetic') or not t.get('inputs') or t.get('depHash')!=key:continue
   if any(not (root/Path(x.replace('.','/')+'.lean')).exists() or (root/Path(x.replace('.','/')+'.lean')).read_bytes()!=(G/Path(x.replace('.','/')+'.lean')).read_bytes() for x in closure(n)):continue
   text='\n'.join(x.get('message','') for x in t.get('log',[]))
   if '/bin/lean ' not in text or str(root/rel.with_suffix('.lean')) not in text:continue
   donors.append((label,root,sha(tr)))
  assert donors,('no exact current proper donor',n,key)
  label,root,creator=donors[0];run(root,['build','--no-build',n],str(i)+'-'+label+'-full-normal');expected=payloads(root,n);assert expected[str(Path('.lake/build/lib/lean')/rel.with_suffix('.trace'))]==creator;writer_check(n);check_configs();old={}
  for f,h in expected.items():
   src=root/f;dest=G/f;assert sha(src)==h;assert dest.parent.resolve().is_relative_to(G.resolve()) and dest.parent.stat().st_uid==os.getuid()
   if dest.exists():
    previous=sha(dest);save=preserved/previous
    if not save.exists():shutil.copyfile(dest,save)
    old[f]=previous
   fd,tmp=tempfile.mkstemp(dir=dest.parent,prefix='.owned-donor318-');os.close(fd);shutil.copyfile(src,tmp);os.replace(tmp,dest);assert sha(dest)==h
  run(G,['build','--no-build',n],str(i)+'-G-final-normal');records.append({'target':n,'key':key,'donor':label,'creator_trace_sha256':creator,'payloads':expected,'preserved_old':old,'status':'recovered actual current normal'});checkpoint('RUNNING');print('completed',i+1,n,flush=True)
 checkpoint('PASSED_EXACT318_DONOR_SCOPE;FULL326_AND3381_OPEN');print('FINAL',len(records),flush=True)
except BaseException as e:
 checkpoint('STOPPED_AT_FIRST_UNSUPPORTED_CONDITION',repr(e));traceback.print_exc();raise
