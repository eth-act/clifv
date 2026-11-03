from pathlib import Path
import os,sys,json,subprocess,hashlib,datetime
X=Path(__file__).resolve().parent;D=X/'light-leaf-v1';P=X/'light-current8f-query-v1/package';E=X.parent.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
T=Path('/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin');C=P/'lakefile.toml'
if len(sys.argv)==1:
 D.mkdir();canonical=C.read_bytes();assert sha(C)=='3ce79410e1ea993cdc54cd09f694bd53696ab3cab647b10cc493de0890d4e801'
 (D/'canonical-lakefile.toml').write_bytes(canonical)
 rd,wr=os.pipe()
 guard='''import os,sys,json,hashlib\nfrom pathlib import Path\nr=int(sys.argv[1]);d=Path(sys.argv[2]);c=Path(sys.argv[3]);os.write(1,b"armed\\n")\nwhile os.read(r,4096):pass\nc.write_bytes((d/"canonical-lakefile.toml").read_bytes())\n(d/"guard-restored.json").write_text(json.dumps({"canonical_config_restored":True,"sha256":hashlib.sha256(c.read_bytes()).hexdigest()})+"\\n")\n'''
 g=subprocess.Popen([sys.executable,'-c',guard,str(rd),str(D),str(C)],pass_fds=(rd,),stdout=subprocess.PIPE);os.close(rd);assert g.stdout.readline()==b'armed\n'
 (D/'guard-armed.json').write_text(json.dumps({'guard_pid':g.pid,'canonical_sha256':sha(C),'resource_share':'ordinary acquire1GiB only','source_or_broad_handoff':False})+'\n')
 try:
  projection=canonical.replace(b'weakLeanArgs = [',b'weakLeanArgs = ["-j1", ',1);assert projection!=canonical;C.write_bytes(projection);(D/'weak-j1-lakefile.toml').write_bytes(projection)
  env=dict(os.environ);env.update(FV_MEMCAP='1G',FV_MEMCAP_UNIT='worker-o-outside-avoids-light-leaf-v1',FV_MEMCAP_STATS=str(D/'memstats'))
  rc=subprocess.call(['/home/lee/clifv/.worktrees/stock-extending-production-20261031/scripts/memcap.sh',sys.executable,str(Path(__file__).resolve()),'worker'],env=env)
 finally:
  os.close(wr);g.wait();assert C.read_bytes()==canonical
 (D/'exit.json').write_text(json.dumps({'exit':rc,'guard_restored_sha256':sha(D/'guard-restored.json')})+'\n');sys.exit(rc)
env=dict(os.environ);env.pop('FV_LAKE_CACHE',None);env.pop('FV_MEMCAP_OFF',None);env.update(LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LAKE_CACHE_DIR=str(D/'disabled-cache'),OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1',LEAN_NUM_THREADS='1',PATH=str(T)+':'+env['PATH'])
cl=X/'creator-classification155-v1/receipt.json';assert sha(cl)=='a827234361fcaba7eebe84e9e61ea28dee6e7719097ea3e977ff97d351135f7a';rows=json.loads(cl.read_text())['records'];assert len(rows)==155
for m,row in rows.items():
 rel=m.replace('.','/');assert sha(P/(rel+'.lean'))==row['current_source_sha256']
 for ext,folder in [('olean','.lake/build/lib/lean'),('ilean','.lake/build/lib/lean'),('c','.lake/build/ir')]:assert sha(P/folder/(rel+'.'+ext))==row['payloads'][ext]['sha256']
records=[]
def run(label,args,wrap=False):
 e=dict(env)
 if wrap:e['PATH']=str(E/'fence-acquire-audit-correction-v1/tools/bin')+':'+e['PATH']
 with (D/(label+'.log')).open('w') as out:r=subprocess.run(args,cwd=P,env=e,stdout=out,stderr=subprocess.STDOUT)
 records.append({'label':label,'argv':args,'exit':r.returncode,'log_sha256':sha(D/(label+'.log'))});print(label,r.returncode,flush=True);assert r.returncode==0,(label,(D/(label+'.log')).read_text()[-3000:]);return (D/(label+'.log')).read_text().strip()
run('normal155-before',[str(T/'lake'),'build','--no-build',*rows])
keys=run('keys155',[str(T/'lake'),'query','--no-build',*['+'+m+':depHash' for m in rows]]).splitlines();assert keys==[r['current_key'] for r in rows.values()]
key=run('new-key',[str(T/'lake'),'query','--no-build','+FV.E2E.OutsideAvoids:depHash']);assert key=='b6c00cc0e27eed0d'
leaf=P/'FV/E2E/OutsideAvoids.lean';assert leaf.read_bytes()==(X/'new-source/FV/E2E/OutsideAvoids.lean').read_bytes()
run('fresh-leaf',[str(T/'lake'),'build','FV.E2E.OutsideAvoids'])
run('normal156-after',[str(T/'lake'),'build','--no-build',*rows,'FV.E2E.OutsideAvoids'])
assert run('new-key-after',[str(T/'lake'),'query','--no-build','+FV.E2E.OutsideAvoids:depHash'])==key
names=['OutsideAvoids','OutsideAvoids.mk','OutsideAvoids.stack','OutsideAvoids.args','OutsideAvoids.valid']
audit=D/'outside-avoids-light.lean';audit.write_text('import FV.E2E.OutsideAvoids\n'+''.join('#check E2E.DeadCleanupExecBytes.'+n+'\n#print axioms E2E.DeadCleanupExecBytes.'+n+'\n' for n in names))
auditor=E/'fence-acquire-audit-correction-v1/tools/scripts/axiom-audit.py';run('real-auditor',[sys.executable,str(auditor),'--cwd',str(P),'--log-dir',str(D/'audit-logs'),str(audit)],True)
for m,row in rows.items():
 rel=m.replace('.','/')
 for ext,folder in [('olean','.lake/build/lib/lean'),('ilean','.lake/build/lib/lean'),('c','.lake/build/ir')]:assert sha(P/folder/(rel+'.'+ext))==row['payloads'][ext]['sha256']
files={str(p.relative_to(P)):sha(p) for folder in ['.lake/build/lib/lean','.lake/build/ir'] for p in (P/folder/'FV/E2E').glob('OutsideAvoids.*') if p.is_file()}
(D/'receipt.json').write_text(json.dumps({'status':'passed_fresh_current8f_light_leaf_and_real_auditor','origin_ref':'8f073980e9630c8d3cd9d6f6f77ab462474c7bcb','source_sha256':sha(leaf),'source_key':key,'prerequisite_classification_sha256':sha(cl),'prerequisites':155,'all_prerequisite_payloads_unchanged':True,'canonical_config_sha256':sha(D/'canonical-lakefile.toml'),'weak_j1_config_sha256':sha(C),'records':records,'artifact_hashes':files,'audit_source_sha256':sha(audit),'real_auditor_sha256':sha(auditor),'old23_header_AX_gate':'held394_importer_LinkClifN_source_mismatch','shared_P_or_F_mutated':False,'broader_build_authorized':False,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()},indent=2)+'\n')
print('receipt',sha(D/'receipt.json'),flush=True)
