"""Run only after the parent grants the existing 3GiB proof slot."""
from pathlib import Path
import argparse, datetime, fcntl, hashlib, json, os, shutil, subprocess

args = argparse.ArgumentParser()
args.add_argument('--attempt',required=True)
attempt = args.parse_args().attempt
assert attempt.replace('-','').replace('_','').isalnum()
assert os.environ.get('WORKER_O_PROOF_SLOT_GRANTED') == '513', 'Parent must grant the existing proof slot; do not reserve or launch another build'
OUT = Path(__file__).resolve().parent
PKG = OUT/'focused-package-v1'
FROZEN = Path('/home/lee/clifv/.worktrees/stock-extending-production-20261031')
context = json.loads((OUT/'focused-context-v1.json').read_text())
ownership = json.loads((OUT/'focused-ownership-v1.json').read_text())
logs = OUT/'attempts'/attempt
assert not logs.exists(), 'Keep previous diagnostics; choose a new attempt label'
logs.mkdir(parents=True)
lock = (OUT/'focused-execution.lock').open('a+')
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
env = dict(os.environ)
env.update(json.loads((OUT.parent/'author-env-v1.json').read_text()))
env.pop('FV_LAKE_CACHE',None)
env.update(FV_ROOT=str(PKG),FV_MEMCAP='3G',LEAN_NUM_THREADS='2',OMP_NUM_THREADS='2',OMP_THREAD_LIMIT='2',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false')
lake_path = subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=FROZEN,env=env,text=True).strip()
tool_path = subprocess.check_output(['lake','env','printenv','PATH'],cwd=FROZEN,env=env,text=True).strip()
lean = shutil.which('lean',path=tool_path)
assert lean
env['PATH'] = tool_path

def hashfile(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def imported_outputs_unchanged():
    for item in ownership['hardlinked_imports']:
        p = PKG/item['path']
        assert hashfile(p) == item['sha256'], ('Imported snapshot changed',item['path'])

assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=FROZEN,text=True).strip() == context['frozen_source']
imported_outputs_unchanged()
for p, detail in context['focused_targets'].items():
    for name, item in detail['sources'].items():
        data = (PKG/name).read_bytes()
        blob = subprocess.check_output(['git','hash-object','--stdin'],input=data,cwd=FROZEN,text=False).decode().strip()
        assert blob == item['candidate_blob'], name

memcap = str(FROZEN/'scripts/memcap.sh')
def run(source, library, logfile, outputs=False):
    child = dict(env,LEAN_PATH=str(library)+':'+lake_path)
    command = ['nice','-n','10',memcap,lean,'--root='+str(PKG),str(PKG/source)]
    if outputs:
        stem = library/Path(source).with_suffix('')
        stem.parent.mkdir(parents=True,exist_ok=True)
        # This path is exclusively owned. Unlink every destination before Lean can write it.
        for suffix in ['.olean','.ilean','.olean.private','.olean.server','.c']:
            Path(str(stem)+suffix).unlink(missing_ok=True)
        command += ['-o',str(stem)+'.olean','-i',str(stem)+'.ilean','-c',str(stem)+'.c']
    with logfile.open('w') as log:
        subprocess.run(command,cwd=PKG,env=child,stdout=log,stderr=subprocess.STDOUT,check=True)

run('BaselineTypes.lean',PKG/'.lake/baseline-lib',logs/'baseline-types-axioms.log')
local = PKG/'.lake/build/lib/lean'
passed = []
for source in context['queue']:
    log = logs/(Path(source).stem+'.log')
    run(source,local,log,True)
    passed.append(source)
    (logs/'kernel-progress.json').write_text(json.dumps({'passed':passed},indent=2)+'\n')
    print('KERNEL',source,'passed',flush=True)
run('CandidateTypes.lean',local,logs/'candidate-types-axioms.log')
old = (logs/'baseline-types-axioms.log').read_bytes()
new = (logs/'candidate-types-axioms.log').read_bytes()
assert old == new, 'Current-main elaborated types or exact axiom output changed'
imported_outputs_unchanged()
receipt = {'status':'passed','base':context['base'],'candidate_tree':context['candidate_tree'],'modules':passed,'exact_type_axiom_roots':context['comparison_roots'],'baseline_context_sources_equal_frozen':context['baseline_closure_count'],'candidate_context_sources':context['candidate_closure_count'],'output_hashes':{p:hashfile(local/Path(p).with_suffix('.olean')) for p in passed},'all_import_snapshots_unchanged':True,'full_affected_gates':'PENDING','full_goal_complete':False,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(logs/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'status':'passed','modules':len(passed),'exact_types_axiom_sets':len(context['comparison_roots'])}),flush=True)
