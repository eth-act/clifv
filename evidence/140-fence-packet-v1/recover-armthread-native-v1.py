from pathlib import Path
import json,os,hashlib,subprocess,shutil,time
F=Path(__file__).resolve().parent;E=F.parent;P=F/'package';C=E/'892-current-main-context-v1/package/.lake/ci-cache';O=F/'runs/armthread-native-recovery-v1';O.mkdir(exist_ok=False);stage=O/'stage';(stage/'lib').mkdir(parents=True);(stage/'ir').mkdir()
S=json.loads((F/'import-snapshot-v9.json').read_text());key=json.loads((F/'runs/armthread-key-query-v1/stdout.log').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();mapping=C/'outputs/fv'/(key+'.json');M=json.loads(mapping.read_text());assert M['service'] is None;artifact=C/'artifacts'/M['data'];originalArchive=sha(artifact);originalMapping=sha(mapping)
env=dict(os.environ);env.update(FV_ROOT=str(P),FV_MEMCAP='1G',FV_MEMCAP_UNIT='worker-o-fence-armthread-native-recovery-v1',FV_MEMCAP_STATS=str(O/'stats.mem'),OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1');cmd=['/usr/bin/bwrap','--ro-bind','/','/','--bind',str(stage),str(stage),'--proc','/proc','--dev','/dev','--','/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin/leantar','--jobs','1','-C',str(stage/'lib'),'-C',str(stage/'ir'),'-x','-j','-'];start=time.time()
with (O/'extract.log').open('w') as log:r=subprocess.run(['/home/lee/clifv/.worktrees/stock-extending-production-20261031/scripts/memcap.sh',*cmd],input=json.dumps([{'file':str(artifact),'hash':key}]),text=True,cwd=stage,env=env,stdout=log,stderr=subprocess.STDOUT)
assert r.returncode==0,r.returncode
allowed={'ArmThread'+s for s in ['.trace','.olean','.olean.hash','.olean.server','.olean.server.hash','.olean.private','.olean.private.hash','.ilean','.ilean.hash','.c','.c.hash','.ir','.ir.hash','.ir.sig','.ir.sig.hash']};files=[p for p in stage.rglob('*') if p.is_file() or p.is_symlink()]
assert files and all(not p.is_symlink() and p.parent in {stage/'lib',stage/'ir'} and p.name in allowed for p in files)
trace=json.loads((stage/'lib/ArmThread.trace').read_text());assert trace['depHash']==key
for ext in ['.olean','.ilean']:assert (stage/'lib'/('ArmThread'+ext)).exists()
assert (stage/'ir/ArmThread.c').exists();changed=[]
for src in files:
 root=P/'.lake/build'/('lib/lean' if src.parent.name=='lib' else 'ir')/'FV/Concurrency';dest=root/src.name;old=sha(dest) if dest.exists() else None
 if dest.exists():dest.unlink()
 shutil.copy2(src,dest);assert sha(dest)==sha(src);rel=str(dest.relative_to(P));S['artifacts'][rel]=sha(dest);changed.append({'path':rel,'old_sha256':old,'new_sha256':sha(dest)})
assert sha(artifact)==originalArchive and sha(mapping)==originalMapping
receipt={'status':'native_archive_restored_normal_check_pending','module':'FV.Concurrency.ArmThread','native_input_key':key,'key_query':'runs/armthread-key-query-v1','mapping':str(mapping),'mapping_sha256':originalMapping,'archive':str(artifact),'archive_sha256':originalArchive,'native_tool_sha256':sha(Path(cmd[14])) if False else sha(Path('/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin/leantar')),'argv':cmd,'seconds':time.time()-start,'stats':(O/'stats.mem').read_text(),'outputs':changed,'sandbox':'read-only filesystem except owned staging directory','cache_modified':False,'live_package_modified':False,'kernel_ran':False}
(O/'state.json').write_text(json.dumps(receipt,indent=2)+'\n');S['status']='requires_full_normal_check';S['native_armthread_recovery']=receipt;(F/'import-snapshot-v10.json').write_text(json.dumps(S,indent=2)+'\n');v=(F/'verify-access-v9.py').read_text().replace('import-snapshot-v9.json','import-snapshot-v10.json').replace('import-normal-check-v9.json','import-normal-check-v10.json');(F/'verify-access-v10.py').write_text(v);print('Native artifact restored; full normal no-build check remains')
