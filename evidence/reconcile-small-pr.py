from pathlib import Path
import subprocess,os,json,sys
b=Path('/home/lee/clifv');e=b/'.git/agent-evidence/stock-memory-20261029';packet=json.loads(Path(sys.argv[1]).read_text());number=sys.argv[2];branch=packet['branch'];files=packet['files']
if 'scripts/audit/stock-memory-source.lean' not in files and 'activation' not in branch:files=files+['scripts/audit/stock-memory-source.lean']
def git(*args,data=None,env=None):return subprocess.check_output(['git',*args],cwd=b,input=data,env=env).decode().strip()
def content(ref,path):
 r=subprocess.run(['git','show',ref+':'+path],cwd=b,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
 return None if r.returncode else r.stdout
subprocess.run(['git','fetch','origin','main'],cwd=b,check=True);main=git('rev-parse','origin/main');head=git('rev-parse',branch);oldbase=packet['base'];selected={}
for path in files:
 desired=content(head,path);previous=content(oldbase,path);current=content(main,path)
 assert desired is not None,path
 assert current in (previous,desired),(path,'Concurrent source conflict; preserve both versions and resolve explicitly')
 selected[path]=desired
idx=e/('reconcile-pr'+number+'.index');idx.unlink(missing_ok=True);env=dict(os.environ,GIT_INDEX_FILE=str(idx));git('read-tree',main,env=env)
for path,data in selected.items():
 blob=git('hash-object','-w','--stdin',data=data);git('update-index','--add','--cacheinfo','100644',blob,path,env=env)
tree=git('write-tree',env=env);subprocess.run(['git','diff','--check',main,tree],cwd=b,check=True)
# Both parents preserve the published branch and the complete current-main tree.
commit=git('commit-tree',tree,'-p',head,'-p',main,'-m','Reconcile memory delivery packet onto current main')
git('update-ref','refs/heads/'+branch,commit,head);subprocess.run(['git','push','origin',branch],cwd=b,check=True);subprocess.run(['gh','pr','edit',number,'--base','main'],cwd=b,check=True);idx.unlink()
receipt=dict(pr=int(number),branch=branch,old_head=head,main=main,commit=commit,changed_files=git('diff','--name-only',main,commit).splitlines(),unpublished_work_untouched=True)
(e/('pr'+number+'-reconcile.json')).write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
