from pathlib import Path
import datetime,hashlib,json,os,psutil,subprocess,tomllib,stat
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';D=Path(__file__).resolve().parent;J=E/'892-joint-current-context-v2/package';base=json.loads((D/'main-actual.json').read_text())['sha'];api=json.loads((D/'892-actual.json').read_text());tree=json.loads((D/'main-actual.json').read_text())['commit']['tree']['sha'];assert api['merged'] and api['merge_commit_sha']==base;assert subprocess.check_output(['git','rev-parse',api['head']['sha']+'^{tree}'],cwd=B,text=True).strip()==tree
old=json.loads((E/'513-shared-gate-queue-v4/snapshot-plan.json').read_text());normalpath=E/'892-joint-current-context-v2/normal-providers-state-v1.json';normal=json.loads(normalpath.read_text());assert normal['status']=='passed' and normal['normal_project_targets']==2895 and normal['authoritative_final_no_build_exit']==0
entries={};modes={}
for row in subprocess.check_output(['git','ls-tree','-rz',tree],cwd=B).split(b'\0'):
 if not row:continue
 header,name=row.split(b'\t',1);mode,kind,value=header.decode().split()
 if kind=='blob':entries[name.decode()]=value;modes[name.decode()]=mode
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def blob(p):
 p=Path(p);data=os.readlink(p).encode() if p.is_symlink() else p.read_bytes();return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
projection={};auxiliary={}
for n,h in normal['source_hashes'].items():
 assert sha(J/n)==h,('Validated source changed',n)
 if n not in entries:
  assert n in ['matrix/PrepareTypedBundles.lean','matrix/BackendEntrySmoke.lean','matrix/PrepareActualBundles.lean','matrix/ReflowTypedBundle.lean','matrix/ReflowActualBundle.lean'];auxiliary[n]=h;continue
 assert blob(J/n)==entries[n],('Current tree changes validated source',n);projection[n]=h
configs={}
for n in ['lean-toolchain','lake-manifest.json','lakefile.toml']:
 data=subprocess.check_output(['git','cat-file','blob',entries[n]],cwd=B)
 if n=='lakefile.toml':assert (J/n).read_bytes()==data.replace(b'weakLeanArgs = [',b'weakLeanArgs = ["-j2",',1)
 else:assert (J/n).read_bytes()==data
 configs[n]=dict(canonical_blob=entries[n],operational_sha256=sha(J/n))
released=[]
for owner in old['required_release_owners']:
 try:
  p=psutil.Process(owner['pid']);same=p.create_time()==owner['create_time'];assert not same or p.status()==psutil.STATUS_ZOMBIE,owner;observed=dict(pid=owner['pid'],same_process=same,status=p.status())
 except psutil.NoSuchProcess:observed=dict(pid=owner['pid'],exists=False)
 released.append(dict(owner=owner,observation=observed))
# Preserve every source/blob that produced the existing successful normal outputs.
bridge=dict(status='passed',base=base,current_tree=tree,actual_892_merged_commit=api['merge_commit_sha'],actual_892_head=api['head']['sha'],validated85_head='85b0aa1f2cf1cf0ff4d442d65d688ffa306eea87',validated85_tree='5b924d76f99cd81bede204d7906e16dd72889b32',normal_source_context_tree=normal['joint_tree'],normal_provider_receipt=str(normalpath),normal_provider_receipt_sha256=sha(normalpath),validated_source_hashes=projection,validated_sources=len(projection),preserved_auxiliary_sources=auxiliary,all_normal_source_hashes_checked=len(projection)+len(auxiliary),all_validated_sources_equal_actual_tree=True,configs=configs,reviewed_10690_bridge=str(E/'892-joint-current-context-v2/reviewed-publication-state-v6.json'),reviewed_10690_bridge_sha256=sha(E/'892-joint-current-context-v2/reviewed-publication-state-v6.json'),released_owners=released,normal_outputs_preserved=normal['outputs'],old_executions_relabelled=False)
(D/'source-projection-bridge.json').write_text(json.dumps(bridge,indent=2)+'\n')
missing=[];different=[];mode_only=[]
for n,wanted in entries.items():
 p=J/n
 if not(p.exists() or p.is_symlink()):missing.append(n)
 elif n!='lakefile.toml' and blob(p)!=wanted:different.append(n)
 if p.exists() and not p.is_symlink() and bool(p.stat().st_mode&stat.S_IXUSR)!=(modes[n]=='100755'):mode_only.append(n)
unknown=[str(p.relative_to(J)) for prefix in ['FV','FVTest','corpus/dsl','crate-proofs'] for p in (J/prefix).rglob('*.lean') if '.lake' not in p.parts and str(p.relative_to(J)) not in entries];assert not unknown,unknown
assert set(different)<={'LEARNINGS.md','scripts/lake-serial-build.py'},('Unreviewed changed canonical source',different)
patch=D/'harness-patches/scripts/check-stock-mixed-integration.py';operational={'lakefile.toml':dict(canonical_blob=entries['lakefile.toml'],sha256=sha(J/'lakefile.toml')),'scripts/check-stock-mixed-integration.py':dict(canonical_blob=entries['scripts/check-stock-mixed-integration.py'],sha256=sha(patch))}
manifest=dict(view=str(J.resolve()),source_repository=str(B),revision=base,tree=tree,source_blobs=entries,operational_sources=operational,code_source_exceptions=[],scope='Full tracked source bytes, exact current repository tree, and two reviewed operational exceptions')
(D/'source-snapshot-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
lake=tomllib.loads(subprocess.check_output(['git','cat-file','blob',entries['lakefile.toml']],cwd=B).decode());mods=sorted(n for n in entries if n.endswith('.lean') and n.startswith(('FV/','FVTest/','corpus/dsl/')));audits=sorted(n for n in entries if n.startswith('scripts/audit/') and n.endswith('.lean'));crates=sorted(n for n in entries if n.startswith('crate-proofs/') and n.endswith('.lean'));executables=[x['name'] for x in lake.get('lean_exe',[])];assert set(old['all_modules'])<=set(mods);assert set(old['all_audits'])<=set(audits);assert set(old['all_crate_sources'])<=set(crates);assert set(old['executables'])<=set(executables)
plan=dict(old,status='prepared_requires_coordinator_review',base=base,head892=api['head']['sha'],actual_892_merged_commit=base,combined_tree=tree,source_context_tree=normal['joint_tree'],validated_head892=bridge['validated85_head'],validated_tree892=bridge['validated85_tree'],existing_snapshot=str(J.resolve()),existing_cache=str((E/'892-current-main-context-v1/package/.lake/ci-cache').resolve()),all_source_blobs=entries,source_modes=modes,all_modules=mods,all_audits=audits,all_crate_sources=crates,executables=executables,old_execution_provenance=bridge,source_snapshot_manifest=str((D/'source-snapshot-manifest.json').resolve()),operational_source_overrides=operational,future_additions='Future main drift requires a new reviewed bridge. Never restart a healthy compiler.',utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(D/'snapshot-plan.json').write_text(json.dumps(plan,indent=2)+'\n');delta=dict(status='prepared_not_materialized',missing_files=missing,reviewed_existing_preimages=different,mode_only=mode_only,harness_patch='harness-patches/check-stock-mixed-integration.patch',old_normal_outputs_preserved=True,old_normal_targets=2895,new_cache=False,new_worktree=False);(D/'materialization-delta.json').write_text(json.dumps(delta,indent=2)+'\n')
fresh=json.loads((D/'fresh-full-gates.json').read_text());fresh.update(all_modules=len(mods),all_audit_files=audits,crate_sources=crates,executables=executables);(D/'fresh-full-gates.json').write_text(json.dumps(fresh,indent=2)+'\n');print('Queue inventories',len(entries),'sources,',len(mods),'modules,',len(audits),'audits,',len(crates),'crate sources,',len(executables),'executables; missing',len(missing),'changed',different,'mode-only',mode_only)
