from pathlib import Path
import subprocess,json,hashlib,shutil,os,datetime
O=Path(__file__).resolve().parent;A=O.parent;E=A.parent;P=E/'892-joint-current-context-v2/package';D=O/'light-current8f-query-v1';F=D/'package';D.mkdir();F.mkdir();proposal=json.loads((O/'manifest.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();ref=proposal['origin_ref'];configs={}
for n in ['lakefile.toml','lake-manifest.json','lean-toolchain']:
 data=subprocess.check_output(['git','show',ref+':'+n],cwd='/home/lee/clifv');(F/n).write_bytes(data);configs[n]=sha(F/n)
providers={}
for m,h in proposal['new_module_dependency_hashes'].items():
 rel=Path(m.replace('.','/')+'.lean');src=P/rel;assert sha(src)==h,m;dst=F/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
 files={}
 for folder in ['.lake/build/lib/lean','.lake/build/ir']:
  stem=P/folder/rel.with_suffix('')
  for src in stem.parent.glob(stem.name+'.*'):
   if src.name.endswith('.setup.json') or not src.is_file():continue
   relfile=src.relative_to(P);dest=F/relfile;dest.parent.mkdir(parents=True,exist_ok=True)
   if src.suffix in ['.olean','.ilean','.c']:
    dest.symlink_to(src)
   else:shutil.copy2(src,dest)
   files[str(relfile)]={'sha256':sha(src),'view':'read_only_payload_symlink' if dest.is_symlink() else 'owned_metadata_copy'}
 trace=P/'.lake/build/lib/lean'/rel.with_suffix('.trace');td=json.loads(trace.read_text());providers[m]={'source_sha256':h,'donor_native_key':td['depHash'],'donor_outputs':td['outputs'],'files':files}
(F/'FV/E2E/OutsideAvoids.lean').write_bytes((O/'new-source/FV/E2E/OutsideAvoids.lean').read_bytes())
(D/'source-only-purpose.json').write_text(json.dumps({'owner':'acquire worker','purpose':'temporary current8f source/key metadata query; no proof-artifact reuse or compiler authorization inferred','proposal_sha256':sha(O/'manifest.json'),'donor':str(P),'config_hashes':configs,'providers':providers,'cache_restores_permitted':False,'creator_provenance_review_required_before_kernel':True},indent=2)+'\n')
env=dict(os.environ);env.pop('FV_LAKE_CACHE',None);env.pop('FV_MEMCAP_OFF',None);env.update(LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LAKE_CACHE_DIR=str(D/'disabled-cache'),OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1',LEAN_NUM_THREADS='1')
tool=Path('/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin');env['PATH']=str(tool)+':'+env['PATH'];records=[]
def run(label,args):
 with (D/(label+'.stdout')).open('w') as out,(D/(label+'.stderr')).open('w') as err:r=subprocess.run([str(tool/'lake'),*args],cwd=F,env=env,stdout=out,stderr=err)
 text=(D/(label+'.stdout')).read_text().strip();records.append({'label':label,'argv':[str(tool/'lake'),*args],'exit':r.returncode,'stdout':text,'stderr_sha256':sha(D/(label+'.stderr'))});return r.returncode,text
rc,text=run('normal155',['build','--no-build',*proposal['new_module_dependency_hashes']])
keys={}
if rc==0:
 for m in ['FV.Backend.Proof.IselContract','FV.E2E.RegLevelSim']:
  q,key=run('key-'+m.split('.')[-1],['query','--no-build','+'+m+':depHash']);assert q==0,(m,q);keys[m]=key;assert key==providers[m]['donor_native_key'],(m,key,providers[m]['donor_native_key'])
 q,key=run('OutsideAvoids-new-key',['query','--no-build','+FV.E2E.OutsideAvoids:depHash']);keys['FV.E2E.OutsideAvoids']=key;assert q==0,q
for m,row in providers.items():
 for rel,record in row['files'].items():assert sha(P/rel)==record['sha256'],('donor changed',m,rel)
receipt={'status':'passed_current8f_normal155_and_exact_keys_query_only' if rc==0 else 'failed_current8f_normal155_query','config_hashes':configs,'canonical_current8f_config_sha256':configs['lakefile.toml'],'donor_weak_configuration':'weak -j2','donor_config_sha256':sha(P/'lakefile.toml'),'canonical_has_no_thread_flag':True,'records':records,'queried_keys':keys,'provider_bindings_sha256':sha(D/'source-only-purpose.json'),'donor_bytes_unchanged':True,'Lean_compilers_started':0,'proof_artifact_reuse_approved':False,'old394_importer_gate_held':True,'creator_provenance_review_required':True,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};(D/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(receipt['status'],keys);print('receipt',sha(D/'receipt.json'));assert rc==0,'Preserve failed query, no provider build'
