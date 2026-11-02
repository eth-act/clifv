from pathlib import Path
import os,subprocess,json,time,hashlib,datetime
F=Path(__file__).resolve().parent;E=F.parent;P=E/'892-joint-current-context-v2/package';C=E/'892-current-main-context-v1/package/.lake/ci-cache';O=F/'runs/w-native-key-query-v1';O.mkdir(exist_ok=False);env=dict(os.environ)
for k in ['FV_LAKE_CACHE','FV_MEMCAP_OFF','LEAN_PATH','LEAN_SRC_PATH']:env.pop(k,None)
env.update(FV_ROOT=str(P),FV_MEMCAP='1G',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1',PYTHONDONTWRITEBYTECODE='1')
lake='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake';records=[];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for mod in ['FV.E2E.DeadCleanupRealizesW','FV.E2E.DeadCleanupRegLevelW']:
 name=mod.rsplit('.',1)[-1];env['FV_MEMCAP_UNIT']='worker-o-fence-w-key-'+name.lower();env['FV_MEMCAP_STATS']=str((O/(name+'.mem')).resolve());cmd=['/usr/bin/bwrap','--ro-bind','/','/','--proc','/proc','--dev','/dev','--chdir',str(P.resolve()),'--',lake,'query','--json','--no-build','+'+mod+':depHash'];start=time.time()
 with (O/(name+'.stdout')).open('w') as out,(O/(name+'.stderr')).open('w') as err:r=subprocess.run(['/home/lee/clifv/.worktrees/stock-extending-production-20261031/scripts/memcap.sh',*cmd],env=env,stdout=out,stderr=err)
 row={'module':mod,'argv':cmd,'exit':r.returncode,'seconds':time.time()-start,'memstats':(O/(name+'.mem')).read_text(),'filesystem_read_only':True,'no_build':True}
 if r.returncode==0:
  key=json.loads((O/(name+'.stdout')).read_text());row['normal_input_key']=key;mapping=C/'outputs/fv'/(key+'.json');row['mapping_available']=mapping.exists()
  if mapping.exists():
   M=json.loads(mapping.read_text());archive=C/'artifacts'/M['data'];row.update(mapping=str(mapping),mapping_sha256=sha(mapping),mapping_data=M,archive_available=archive.is_file())
   if archive.is_file():row.update(archive=str(archive),archive_sha256=sha(archive))
 records.append(row);(O/'state.json').write_text(json.dumps({'status':'read_only_query_complete' if len(records)==2 else 'running','records':records,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()},indent=2)+'\n');print(json.dumps(row),flush=True)
