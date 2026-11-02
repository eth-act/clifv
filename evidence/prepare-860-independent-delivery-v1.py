from pathlib import Path
import datetime,hashlib,json,os,re,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';V=B/'.worktrees/stock-extending-production-20261031';source='a4c0726d46c5908b4ac06cf797ee939af8644703';branch='agent/stock-void-call-consumers-20261101'
def git(*args,data=None):return subprocess.check_output(['git',*args],cwd=B,input=data).decode().strip()
assert git('-C',str(V),'rev-parse','HEAD')==source and not git('-C',str(V),'status','--porcelain')
subprocess.run(['git','fetch','origin','main'],cwd=B,check=True);base=git('rev-parse','origin/main');assert base==git('ls-remote','origin','refs/heads/main').split()[0]
assert git('ls-remote','origin','refs/heads/'+branch).split()[0]==source
mergebase=git('merge-base',source,base)
old_tree=git('ls-tree','-r',source);main_tree=git('ls-tree','-r',base)
def entries(text):return {line.split('\t',1)[1]:line.split()[2] for line in text.splitlines()}
old=entries(old_tree);main=entries(main_tree)
roots=git('diff','--name-only',mergebase,source).splitlines()
changed_main=git('diff','--name-status',mergebase,base).splitlines();assert all(line.startswith('A\t') for line in changed_main),changed_main
merged_tree=git('merge-tree','--write-tree',source,base).splitlines()[0]
assert len(merged_tree)==40
candidate=git('commit-tree',merged_tree,'-p',source,'-p',base,'-m','Merge current main for ABI return-pin consumer delivery')
new=entries(git('ls-tree','-r',candidate));pending=[n for n in roots if n.endswith('.lean')];closure=set()
while pending:
 name=pending.pop()
 if name in closure:continue
 assert name in old and name in new and old[name]==new[name],name
 data=(V/name).read_bytes();assert git('hash-object','--stdin',data=data)==old[name],name
 closure.add(name)
 for m in re.findall(r'^import\s+([\w.]+)',data.decode(),re.M):
  dep=m.replace('.','/')+'.lean'
  if dep in old:pending.append(dep)
config=['lean-toolchain','lakefile.toml','lake-manifest.json','scripts/axiom-audit.py','scripts/memcap.sh']
for n in config:assert old.get(n)==new.get(n),n
headers=json.loads((E/'return-pin-call-consumer-current-main-state-recovery12-r1.json').read_text());assert headers['status']=='passed'
receipt=dict(status='prepared',source=source,publication_source=candidate,base=base,tree=merged_tree,branch=branch,main_additions=len(changed_main),main_existing_changes=0,source_roots=roots,import_source_closure={n:old[n] for n in sorted(closure)},configuration_hashes={n:old.get(n) for n in config},import_source_closure_equal=True,view_unchanged=True,per_pr_gate='Existing user authorization: ONE QUICK, DIRTY, CHEAP direct peer review, exact current-main import equality, exact-head CI, and tested/merged tree equality. The broader full140 local gate remains live on its frozen snapshot.',requires_peer_review=True,full_goal_complete=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(E/'860-independent-delivery-prepared-v1.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:receipt[k] for k in ['status','source','publication_source','base','tree','main_additions','main_existing_changes','import_source_closure_equal']}));print('Import sources:',len(closure))
