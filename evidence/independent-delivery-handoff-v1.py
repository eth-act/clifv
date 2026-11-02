from pathlib import Path
import hashlib,json,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';V=B/'.worktrees/stock-extending-production-20261031'
def recognize_landed(pr,receipt_name,env=None,activate_view=False):
 path=E/receipt_name
 if not path.exists():return None
 receipt=json.loads(path.read_text())
 if not receipt.get('independent_delivery'):return None
 assert receipt['status']=='landed' and receipt['tree_equal']
 def run(*args):return subprocess.check_output(args,cwd=B,env=env,text=True).strip()
 actual=json.loads(run('gh','pr','view',str(pr),'--repo','eth-act/clifv','--json','state,mergeCommit,headRefOid'))
 published=receipt.get('published_source',receipt['source'])
 assert actual['state']=='MERGED' and actual['mergeCommit']['oid']==receipt['merged'] and actual['headRefOid']==published
 assert run('git','rev-parse',receipt['merged']+'^{tree}')==receipt['tested_tree']
 assert run('git','rev-parse',published+'^{tree}')==receipt['tested_tree']
 for name,digest in receipt.get('source_hashes',{}).items():
  data=subprocess.check_output(['git','show',published+':'+name],cwd=B,env=env);assert hashlib.sha256(data).hexdigest()==digest
 if activate_view:
  owner=Path('/proc/3477137/cmdline');assert not owner.exists() or b'return-pin-call-consumer-recovery-v3' not in owner.read_bytes(),'Keep the healthy frozen build view'
  assert run('git','-C',str(V),'status','--porcelain')==''
  branch=receipt['branch'];run('git','fetch','origin',branch)
  run('git','-C',str(V),'switch',branch)
  run('git','-C',str(V),'merge','--ff-only','origin/'+branch)
  assert run('git','-C',str(V),'rev-parse','HEAD')==receipt['source']
  assert run('git','-C',str(V),'status','--porcelain')==''
 print('Recognized independently landed PR',pr,'at',receipt['merged'],'; saved source and required gates remain intact.',flush=True)
 return receipt

def wait_for_independent_delivery(pr,prepared_name,receipt_name):
 import time
 prepared_path=E/prepared_name
 if not prepared_path.exists():return
 prepared=json.loads(prepared_path.read_text())
 assert prepared['pr']==pr
 receipt_path=E/receipt_name
 while not receipt_path.exists():
  owner_path=E/f'{pr}-independent-delivery-owner-v1.json'
  assert owner_path.exists(),'Inspect the independent delivery owner before changing the shared view'
  owner=json.loads(owner_path.read_text());assert owner['head']==prepared['published_source']
  process=Path('/proc')/str(owner['pid'])/'cmdline'
  assert process.exists() and b'merge-independent-packet-delivery-v1.py' in process.read_bytes(),'The independent delivery stopped. Inspect its evidence before any source switch.'
  time.sleep(10)
