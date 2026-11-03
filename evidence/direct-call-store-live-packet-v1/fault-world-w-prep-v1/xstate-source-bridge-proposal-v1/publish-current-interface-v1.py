from pathlib import Path
import json,hashlib,os,subprocess
D=Path(__file__).resolve().parent;C=D/'canonical-source-interface-v2';M=json.loads((C/'manifest.json').read_text());B=Path('/home/lee/clifv');L=D/'publication-v1';L.mkdir();branch='agent/unwind-source-fault-interface-20261103';base=M['base'];env=dict(os.environ,GIT_INDEX_FILE=str(L/'index'))
def run(args,**kw):return subprocess.check_output(args,cwd=B,**kw).decode().strip()
assert run(['gh','api','repos/eth-act/clifv/commits/main','--jq','.sha'])==base,'Reconcile actual main before publication'
for n,h in M['sources'].items():assert hashlib.sha256((C/'source'/n).read_bytes()).hexdigest()==h,n
assert subprocess.call(['git','show-ref','--verify','--quiet','refs/heads/'+branch],cwd=B)!=0,'Preserve existing branch'
subprocess.run(['git','read-tree',base],cwd=B,env=env,check=True)
for n in M['sources']:
 data=(C/'source'/n).read_bytes();blob=run(['git','hash-object','-w','--stdin'],input=data);subprocess.run(['git','update-index','--add','--cacheinfo','100644,'+blob+','+n],cwd=B,env=env,check=True)
tree=run(['git','write-tree'],env=env);title='Add unwind source memory-fault continuation contracts';msg=L/'commit.txt';msg.write_text(title+'\n');head=run(['git','commit-tree',tree,'-p',base,'-F',str(msg)]);subprocess.run(['git','update-ref','refs/heads/'+branch,head],cwd=B,check=True);subprocess.run(['git','push','origin',head+':refs/heads/'+branch],cwd=B,check=True)
body=L/'body.md';body.write_text('''Unwind handlers can reach memory faults outside ordinary source reachability. Add internal contracts over actual unwind states and preserve handler tables, post-unwind memory, and all five existing trap clauses. The old admission embeds unchanged. Actual `MemTrapAt` events cover ordinary and atomic accesses.

Validation: 177 proper normal modules, focused kernels, eight standard-axiom roots through the repository auditor, and complete default-flag load/store witnesses. All 175 imported source files match current main. The old `UnwindStatement` remains byte-exact.

Production must still derive these internal instances. Actual caught-handler fault execution and executable first-fault transfer remain open under #140.
''');url=run(['gh','pr','create','--repo','eth-act/clifv','--base','main','--head',branch,'--title',title,'--body-file',str(body)]);receipt=dict(status='published-awaiting-review-and-four-CI-checks',url=url,head=head,base=base,tree=tree,branch=branch,source_hashes=M['sources'],canonical_manifest_sha256=hashlib.sha256((C/'manifest.json').read_bytes()).hexdigest());(L/'published.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
