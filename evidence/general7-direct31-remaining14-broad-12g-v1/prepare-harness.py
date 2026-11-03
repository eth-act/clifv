from pathlib import Path
import json,hashlib,shutil
E=Path('/home/lee/clifv/.git/agent-evidence/stock-memory-20261029');old=E/'general7-remaining29-conditional-broad-12g-v1';D=E/'general7-direct31-remaining14-broad-12g-v1';D.mkdir();Q=E/'general7-main-candidate-v1/direct31-remaining14-cone-proposal-v1';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert sha(Q/'manifest.json')=='63fb8ab4bb6eee09a306171f246b9578a96c19dc13c416c258db04651c697115'
s=(old/'gate.py').read_text().replace('remaining29-conditional-cone-proposal-v1','direct31-remaining14-cone-proposal-v1').replace('64840f96902c88957a8e07c26b8d5808db57e10dfa37dc081bf2b75ee9e1fa27','63fb8ab4bb6eee09a306171f246b9578a96c19dc13c416c258db04651c697115').replace('conditional_topological_order\'','conditional_topological_order65\'').replace('protected_ready_frontier16','protected_ready_donors15').replace('unaffected1304','unaffected1688').replace('== 1304','== 1688').replace('== 337','== 65').replace('worker-o-general7-cone29-','worker-o-general7-direct31-cone14-').replace('complete1657','complete1768')
s=s.replace("I['source_hashes'] = {n.replace", "for record in I['records'].values():\n    if record['expected_key'] == 'BIND_ONLY_AFTER_PREDECESSOR_NORMAL_SUCCESS': record['expected_key'] = None\nI['source_hashes'] = {n.replace")
a=s.index('approved = {}');b=s.index('def without_weak',a)
s=s[:a]+'''assert sha(Q/'approved-per-entry-origins.json')==I['approved_origins_sha256']
approved=json.loads((Q/'approved-per-entry-origins.json').read_text())
def origin_ok(root,name):
    path=root/'.lake/build/lib/lean'/Path(name.replace('.', '/')+'.trace')
    data=json.loads(path.read_text())
    if data.get('synthetic'):return False
    if data.get('inputs'):return True
    r=approved.get(name.replace('.', '/')+'.lean',{})
    return r.get('trace_sha256')==sha(path) and r.get('native_key')==data['depHash'] and r.get('outputs')==data['outputs']
'''+s[b:]
# Protect every passed General7 candidate target, including normal reuses.
a=s.index('    for record in ni[\'records\']:');b=s.index('    return out',a)
s=s[:a]+'''    full=json.loads((E/'general7-main-candidate-v1/direct31-current-inventory-v1/manifest.json').read_text())
    for name in full['completed_affected30']:
        for directory,extensions in [('lib/lean',['.trace','.olean','.ilean']),('ir',['.c'])]:
            stem=G/'.lake/build'/directory/name.replace('.','/')
            for ext in extensions:
                file=stem.with_suffix(ext)
                assert file.is_file(),file
                out[str(file)]=sha(file)
    protected=json.loads((Q/'protected-donor-artifacts.json').read_text())
    assert sha(Q/'protected-donor-artifacts.json')==I['protected_artifacts_sha256']
    for rel,h in protected.items():
        assert sha(P/rel)==h,rel
        out[str(P/rel)]=h
'''+s[b:]
(D/'gate.py').write_text(s)
for name in ['run.py','guard.py','launch.py']:
 s=(old/name).read_text().replace('remaining29-conditional-cone-proposal-v1','direct31-remaining14-cone-proposal-v1').replace('64840f96902c88957a8e07c26b8d5808db57e10dfa37dc081bf2b75ee9e1fa27','63fb8ab4bb6eee09a306171f246b9578a96c19dc13c416c258db04651c697115').replace('worker-o-general7-cone29-','worker-o-general7-direct31-cone14-').replace('general7-cone29-broad-resume-v1','general7-direct31-cone14-broad-resume-v1').replace('a74f059187cc2d865aac9720b41fdb3bcedde6eaa878993dd744919ced612eb6',sha(D/'gate.py'))
 if name=='run.py':
  s=s.replace("for other in psutil.process_iter(['pid', 'cmdline']):\n    args", "for other in psutil.process_iter(['pid', 'cmdline','uids']):\n    if other.info['uids'] is None or other.info['uids'].real != os.getuid(): continue\n    args")
 (D/name).write_text(s)
shutil.copyfile(Q/'writer-release-v1.json',D/'R-writer-release.json')
roots={'P':E/'892-joint-current-context-v2/package','G':Path('/home/lee/clifv/.worktrees/loop-20261102')};(D/'donor-config-allowlist.json').write_text(json.dumps({label:{c:sha(p/c) for c in ['lakefile.toml','lake-manifest.json','lean-toolchain']} for label,p in roots.items()},indent=2)+'\n')
(D/'harness-manifest.json').write_text(json.dumps({'proposal_sha256':sha(Q/'manifest.json'),'scripts':{n:sha(D/n) for n in ['run.py','guard.py','gate.py','launch.py']},'writer_release_sha256':sha(D/'R-writer-release.json'),'no_compiler_started':True,'guard_protocol':'same tested natural-boundary controller pause, independent pid/birth guard, cgroup drain before resume'},indent=2)+'\n');print(D,sha(D/'harness-manifest.json'))
