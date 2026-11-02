from pathlib import Path
import datetime,hashlib,json,re,subprocess,sys
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';V=B/'.worktrees/stock-extending-production-20261031';config=json.loads(Path(sys.argv[1]).read_text())
def git(*args,data=None):return subprocess.check_output(['git',*args],cwd=B,input=data).decode().strip()
source=git('-C',str(V),'rev-parse','HEAD');assert source=='a4c0726d46c5908b4ac06cf797ee939af8644703' and not git('-C',str(V),'status','--porcelain')
validation=json.loads((E/config['validation']).read_text());assert validation['status']=='passed';manifest=json.loads((E/(config['packet']+'.json')).read_text());hashes=manifest['files'];packet=E/config['packet']
assert validation['source_hashes']==hashes
parent=json.loads((E/config['parent']).read_text());assert parent['status']=='landed' and parent['tree_equal']
subprocess.run(['git','fetch','origin','main'],cwd=B,check=True);base=git('rev-parse','origin/main');git('merge-base','--is-ancestor',parent['merged'],base)
old=git('ls-remote','origin','refs/heads/'+config['branch']).split()[0];git('cat-file','-e',old+'^{commit}')
tree=git('merge-tree','--write-tree',old,base).splitlines()[0];assert len(tree)==40
assert set(git('diff-tree','--no-commit-id','--name-only','-r',base,tree).splitlines())==set(hashes)
head=git('commit-tree',tree,'-p',old,'-p',base,'-m',config['commit_message'])
entries={line.split('\t',1)[1]:line.split()[2] for line in git('ls-tree','-r',head).splitlines()}
pending=[n for n in hashes if n.endswith('.lean')];closure={}
while pending:
 n=pending.pop()
 if n in closure:continue
 assert n in entries,n
 p=packet/n if n in hashes else V/n
 assert p.exists(),('Source requires a new verification context',n)
 data=p.read_bytes();assert git('hash-object','--stdin',data=data)==entries[n],('Source changed after kernel verification',n)
 if n in hashes:assert hashlib.sha256(data).hexdigest()==hashes[n]
 closure[n]=entries[n]
 for m in re.findall(r'^import\s+([\w.]+)',data.decode(),re.M):
  d=m.replace('.','/')+'.lean'
  if d in entries:pending.append(d)
configfiles=['lean-toolchain','lakefile.toml','lake-manifest.json','scripts/axiom-audit.py','scripts/memcap.sh']
for n in configfiles:assert git('rev-parse',source+':'+n)==entries[n],n
receipt=dict(status='prepared',pr=config['pr'],branch=config['branch'],previous_source=old,published_source=head,validated_source=source,base=base,tree=tree,source_hashes=hashes,import_source_closure=closure,import_source_closure_equal=True,validation=config['validation'],parent=config['parent'],requires_peer_review=True,full_goal_complete=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(E/config['prepared']).write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:receipt[k] for k in ['status','pr','published_source','base','tree','import_source_closure_equal']}),flush=True)
