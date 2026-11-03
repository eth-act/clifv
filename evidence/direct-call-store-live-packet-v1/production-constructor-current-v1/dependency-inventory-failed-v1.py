from pathlib import Path
import subprocess,hashlib,json,re,os
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';Q=E/'direct-call-store-live-packet-v1';D=Q/'production-constructor-current-v1';R=Q/'validation-package-v1';P=E/'892-joint-current-context-v2/package';M='9a3f25fb20cd26d3744476319253d712417f057e'
raw=subprocess.check_output(['git','ls-tree','-rz','--full-tree',M],cwd=B);blobs={}
for x in raw.split(b'\0'):
 if not x:continue
 info,n=x.split(b'\t');mode,typ,obj=info.split();blobs[n.decode()]=obj.decode()
def gitsha(raw):return hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
records={};changed={};unpublished={};missing=[];synthetic=[]
def collect(n):
 path=n.replace('.','/')+'.lean'
 if path in records:return
 f=D/'source'/path
 if f.exists():kind='candidate'
 else:f=R/path;kind='baseline'
 if not f.exists():raise RuntimeError(str(f))
 src=f.read_bytes();expected=blobs.get(path)
 if kind=='baseline' and gitsha(src)!=expected:
  unpublished[path]=dict(source_sha256=sha(f),observed_git_blob=gitsha(src),current_blob=expected)
 rec=dict(kind=kind,source_sha256=sha(f),current_blob=expected)
 records[path]=rec
 if kind=='baseline':
  for owner,root in [('R',R),('P',P)]:
   stem=root/'.lake/build/lib/lean'/path[:-5];tr=stem.with_suffix('.trace')
   if tr.exists():
    td=json.loads(tr.read_text());rec[owner]=dict(native_key=td.get('depHash'),synthetic=td.get('synthetic',False),trace_sha256=sha(tr),olean_present=stem.with_suffix('.olean').exists())
  if not any(rec.get(o,{}).get('olean_present') and not rec[o]['synthetic'] for o in ['R','P']):
   (synthetic if any(rec.get(o,{}).get('synthetic') for o in ['R','P']) else missing).append(path)
 for m in re.findall(r'^import\s+([\w.]+)',src.decode(),re.M):
  imp=m.replace('.','/')+'.lean'
  if imp in blobs or (R/imp).exists() or (D/'source'/imp).exists():collect(m)
for path in json.loads((D/'inventory.json').read_text())['records']:collect(path[:-5].replace('/','.'))
assert not unpublished,unpublished
configs={n:dict(R_sha256=sha(R/n),P_sha256=sha(P/n),current_blob=blobs[n],R_matches_current=gitsha((R/n).read_bytes())==blobs[n]) for n in ['lakefile.toml','lake-manifest.json','lean-toolchain']}
state=dict(status='source-coherent;artifact-record-inventory-only;real-normal-keys-required',main=M,records=records,source_projection_matches_current=True,configs=configs,missing_proper_artifacts=missing,synthetic_only_artifacts=synthetic,unpublished_baseline_sources=unpublished,source_config_reconciliation='R/P weak-j1/j2 versus current weak flags must be normalized in candidate package; pinned Lake excludes weakLeanArgs from native key.',missing_artifacts_are_not_build_authorization=True)
(D/'dependency-inventory.json').write_text(json.dumps(state,indent=2)+'\n');print('sources',len(records),'missing',len(missing),'synthetic',len(synthetic));print('\n'.join(missing+synthetic));print(sha(D/'dependency-inventory.json'))
