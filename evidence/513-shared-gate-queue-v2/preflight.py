"""Check an already-materialized shared snapshot. Never change source or owners."""
from pathlib import Path
import argparse, hashlib, json, os, subprocess

OUT=Path(__file__).resolve().parent
PLAN=json.loads((OUT/'snapshot-plan.json').read_text())
PROTECTED={3477137,3478090,3478318,1849857}

def check(root,release_path,stage):
    if stage=='combined':
        assert PLAN.get('required_extension',{}).get('status')=='bound', 'Final compiler-mode manifest remains pending; do not select draft CLI hashes'
    root=Path(root).resolve()
    assert root.parent==Path('/home/lee/clifv/.worktrees'), 'Use an owned existing worktree, never the dirty primary checkout'
    release=json.loads(Path(release_path).read_text())
    assert release['owner']=='worker-O execution coordinator'
    assert release['view']==str(root)
    assert release['allow_shared_full_gate'] is True
    assert set(release['released_old_owner_pids']) >= PROTECTED
    assert release['resource_budget']=='12G/max1; O aggregate16G'
    overlap=OUT/'source-overlap-decision.json'
    assert release['reviewed_overlap_sha256']==hashlib.sha256(overlap.read_bytes()).hexdigest()
    backup=Path(release['backup_receipt'])
    assert backup.is_file() and release['backup_receipt_sha256']==hashlib.sha256(backup.read_bytes()).hexdigest()
    assert release['remote_backup_verified'] is True
    for pid in PROTECTED:
        status=Path('/proc')/str(pid)/'stat'
        if status.exists():
            state=status.read_text().rsplit(')',1)[1].split()[0]
            assert state=='Z', ('Protected owner still active; do not mutate its view',pid)
    for item in [*PLAN['activation_sources'].values(),*PLAN['typed_sources'].values(),*PLAN.get('extension_sources',{}).values()]:
        assert hashlib.sha256(Path(item['path']).read_bytes()).hexdigest()==item['sha256'], ('Packet changed; regenerate and review queue',item['path'])
    expected=PLAN['base'] if stage=='baseline' else PLAN['combined_tree']
    got=subprocess.check_output(['git','rev-parse','HEAD^{tree}'],cwd=root,text=True).strip()
    if stage=='baseline':
        expected=subprocess.check_output(['git','rev-parse',PLAN['base']+'^{tree}'],cwd=root,text=True).strip()
    assert got==expected, ('Snapshot tree differs',got,expected)
    assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=normal'],cwd=root,text=True).strip(), 'The shared snapshot must stay clean'
    free=os.statvfs(root).f_bavail*os.statvfs(root).f_frsize
    assert free>=100*1024**3, 'Keep at least100GiB free before full validation'
    return {'root':str(root),'stage':stage,'tree':got,'release_sha256':hashlib.sha256(Path(release_path).read_bytes()).hexdigest(),'plan_sha256':hashlib.sha256((OUT/'snapshot-plan.json').read_bytes()).hexdigest()}

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--root',required=True)
    p.add_argument('--release',required=True)
    p.add_argument('--stage',choices=['baseline','combined'],required=True)
    a=p.parse_args()
    print(json.dumps(check(a.root,a.release,a.stage)))
