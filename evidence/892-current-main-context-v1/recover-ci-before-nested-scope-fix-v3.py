"""Recover exact-main producer artifacts into disposable package-local staging only."""
from pathlib import Path
import argparse, datetime, hashlib, json, os, re, shutil, subprocess, time, zipfile

OUT=Path(__file__).resolve().parent
E=OUT.parent
PKG=OUT/'package'
BASE='3a6719b44b0e6b38e24cd0de82655f93b78272a9'
RUN=41408842551
STAGES=PKG/'.lake/ci-stages'
ARCHIVES=PKG/'.lake/ci-downloads'
OWN_CACHE=PKG/'.lake/ci-cache'
V=Path('/home/lee/clifv/.worktrees/stock-extending-production-20261031')
args=argparse.ArgumentParser();args.add_argument('--watch',action='store_true');a=args.parse_args()
deadline=time.monotonic()+4*3600
statefile=OUT/'ci-recovery-state.json'
state=json.loads(statefile.read_text()) if statefile.exists() else {'artifacts':{},'attempts':[]}

def api(path):return json.loads(subprocess.check_output(['gh','api',path],text=True))
def sha(path):
    result=hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda:stream.read(1024*1024),b''):result.update(chunk)
    return result.hexdigest()
def save(status,**extra):
    state.update(status=status,run=RUN,head=BASE,cache_scope='disposable package-local staging; no global cache mutation',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),**extra)
    statefile.write_text(json.dumps(state,indent=2)+'\n')

context=json.loads((OUT/'context.json').read_text())
assert context['base']==BASE
changed={item['filename'] for item in json.loads(subprocess.check_output(['gh','api','repos/eth-act/clifv/pulls/892/files?per_page=100'],text=True))}
# The manifest, not a pending PR update, defines the exact candidate files.
manifest=json.loads((E/'return-pin-production-delivery-packet-v1.json').read_text())
assert changed==set(manifest['files'])
basepaths=set(subprocess.check_output(['git','ls-tree','-r','--name-only',BASE],cwd=V,text=True).splitlines())
baseline_targets=sorted(p[:-5].replace('/','.') for p in context['source_hashes'] if p.startswith(('FV/','FVTest/')) and p in basepaths and p not in manifest['files'])
(OUT/'baseline-normal-targets.txt').write_text('\n'.join(baseline_targets)+'\n')
env=dict(os.environ)
env.update(json.loads((E/'author-env-v1.json').read_text()))
env.pop('FV_LAKE_CACHE',None)
env.update(LAKE_CACHE_DIR=str(OWN_CACHE),LAKE_ARTIFACT_CACHE='true',LAKE_RESTORE_ARTIFACTS='true',FV_ROOT=str(PKG),FV_MEMCAP='1G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',CARGO_BUILD_JOBS='2')
assert Path(env['LAKE_CACHE_DIR']).is_relative_to(PKG)
for name in ['lakefile.toml','lake-manifest.json','lean-toolchain']:
    data=subprocess.check_output(['git','show',BASE+':'+name],cwd=V)
    dest=PKG/name
    if dest.exists() and dest.read_bytes()!=data:
        (OUT/('before-ci-'+name)).write_bytes(dest.read_bytes())
        dest.unlink()
    dest.write_bytes(data)
packages=PKG/'.lake/packages'
if not packages.exists():packages.symlink_to(V/'.lake/packages',target_is_directory=True)

while True:
    run=api(f'repos/eth-act/clifv/actions/runs/{RUN}')
    assert run['head_sha']==BASE and run['event']=='push' and run['name']=='Full gate'
    jobs=api(f'repos/eth-act/clifv/actions/runs/{RUN}/jobs?per_page=100')['jobs']
    artifacts=api(f'repos/eth-act/clifv/actions/runs/{RUN}/artifacts?per_page=100')['artifacts']
    found=False
    for item in artifacts:
        match=re.fullmatch(r'stage-w([123])-(\d+)',item['name'])
        full=item['name']=='lake-full'
        if (not match and not full) or str(item['id']) in state['artifacts']:continue
        wave,shard=map(int,match.groups()) if match else (0,0)
        producer_name='Assemble build and executables' if full else f'Build wave {wave} ({shard}) / shard {shard}'
        producers=[j for j in jobs if j['name']==producer_name]
        if len(producers)!=1 or producers[0]['status']!='completed' or producers[0]['conclusion']!='success':continue
        assert item['workflow_run']['id']==RUN and item['workflow_run']['head_sha']==BASE and not item['expired']
        bound=(8 if full else 2)*1024**3
        assert item['size_in_bytes']<=bound, 'Artifact exceeds the explicit bounded download size'
        assert shutil.disk_usage(PKG).free>100*1024**3
        assert sum(v['compressed_bytes'] for v in state['artifacts'].values())+item['size_in_bytes']<=40*1024**3
        ARCHIVES.mkdir(parents=True,exist_ok=True);STAGES.mkdir(parents=True,exist_ok=True)
        archive=ARCHIVES/(str(item['id'])+'.zip')
        with archive.open('wb') as stream:
            subprocess.run(['gh','api',f'repos/eth-act/clifv/actions/artifacts/{item["id"]}/zip'],stdout=stream,check=True)
        assert archive.stat().st_size<=bound
        if item.get('digest','').startswith('sha256:'):assert sha(archive)==item['digest'].split(':',1)[1]
        stage=STAGES/item['name'];assert not stage.exists();stage.mkdir()
        with zipfile.ZipFile(archive) as bundle:
            members=bundle.infolist()
            assert sum(x.file_size for x in members)<=(10 if full else 4)*1024**3
            for member in members:
                target=stage/member.filename
                assert target.resolve().is_relative_to(stage.resolve())
                assert not ((member.external_attr>>16)&0o170000)==0o120000
                if member.is_dir():target.mkdir(parents=True,exist_ok=True);continue
                target.parent.mkdir(parents=True,exist_ok=True)
                with bundle.open(member) as src,target.open('wb') as dest:shutil.copyfileobj(src,dest,1024*1024)
        mappings=list(stage.rglob('outputs.jsonl'));assert mappings
        maps=[]
        for i,path in enumerate(mappings):
            receipt=OUT/(item['name']+'-outputs-'+str(i)+'.jsonl');receipt.write_bytes(path.read_bytes())
            maps.append({'path':str(receipt),'sha256':sha(receipt),'entries':max(0,len(receipt.read_text().splitlines())-1)})
        state['artifacts'][str(item['id'])]={'name':item['name'],'producer':producers[0],'metadata':item,'compressed_bytes':archive.stat().st_size,'zip_sha256':sha(archive),'mappings':maps}
        save('recovering',new_artifact=item['name'])
        archive.unlink();found=True
        print('RECOVERED',item['name'],'from successful exact-head producer',flush=True)
    if found:
        attempt=OUT/('ci-normal-context-attempt-'+str(len(state['attempts'])+1));attempt.mkdir()
        # Never let a cache restore write through old hardlinked output inodes.
        if (PKG/'.lake/build').exists():shutil.rmtree(PKG/'.lake/build')
        # Reset only this disposable staging cache when trying a coherent selection.
        if OWN_CACHE.exists():shutil.rmtree(OWN_CACHE)
        with (attempt/'unstage.log').open('w') as log:
            if (STAGES/'lake-full').exists():
                command=['lake','cache','unstage',str(STAGES/'lake-full')]
            else:
                command=['python3',str(V/'scripts/lake-unstage.py'),'--root',str(PKG),str(STAGES)]
            result=subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh'),*command],cwd=PKG,env=env,stdout=log,stderr=subprocess.STDOUT)
        assert result.returncode==0,'Inspect the preserved package-local unstage diagnostic'
        with (attempt/'normal-keys.log').open('w') as log:
            result=subprocess.run(['nice','-n','10',str(V/'scripts/memcap.sh'),'lake','build','--no-build',*baseline_targets],cwd=PKG,env=env,stdout=log,stderr=subprocess.STDOUT)
        row={'path':str(attempt),'normal_key_exit':result.returncode,'normal_key_log_sha256':sha(attempt/'normal-keys.log'),'baseline_targets':len(baseline_targets),'scope':'No compiler allowed; proper normal-key check/restore only'}
        state['attempts'].append(row)
        if result.returncode==0:
            output_hashes={}
            for module in baseline_targets:
                stem=PKG/'.lake/build/lib/lean'/module.replace('.','/')
                assert Path(str(stem)+'.olean').is_file(), ('Verified target has no required olean',module)
                output_hashes[module]={}
                for suffix in ['.olean','.ilean','.olean.private','.olean.server','.ir','.trace','.c']:
                    path=Path(str(stem)+suffix)
                    if path.is_file():output_hashes[module][suffix]={'path':str(path.relative_to(PKG)),'sha256':sha(path),'bytes':path.stat().st_size}
            manifest=OUT/'coherent-baseline-output-hashes.json'
            manifest.write_text(json.dumps({'head':BASE,'producer_run':RUN,'normal_key_attempt':row,'modules':output_hashes},indent=2)+'\n')
            save('coherent_current_context_ready',context_attempt=row,normal_baseline_targets=len(baseline_targets),no_builds_run=True)
            print('COHERENT CURRENT CONTEXT READY',len(baseline_targets),'baseline targets',flush=True)
            break
        print('CONTEXT INCOMPLETE: source-key verification needs additional producer artifacts',flush=True)
    save('waiting_for_successful_exact_head_artifacts',producer_jobs=[{'id':j['id'],'name':j['name'],'status':j['status'],'conclusion':j['conclusion']} for j in jobs])
    if run['status']=='completed':raise RuntimeError('The exact-head producer ended before a coherent required context was obtained; preserve all successful artifacts')
    if not a.watch or time.monotonic()>=deadline:break
    time.sleep(45)
