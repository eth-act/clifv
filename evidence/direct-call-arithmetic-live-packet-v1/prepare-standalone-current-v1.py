from pathlib import Path
import datetime,hashlib,json,os,shutil,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';Q=E/'direct-call-arithmetic-live-packet-v1';S=Q/'standalone-class-source-v1';M=json.loads((S/'manifest.json').read_text());R=Q/'validation-package-v1';J=E/'892-joint-current-context-v2/package';D=E/'direct-call-delivery-units-v1';old=json.loads((D/'class-foundation-current-state-v1.json').read_text());L=Q/'standalone-current-prepare-v1';L.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
# The active normal scheduler owns J. This script reads J only.
for n,h in M['source_hashes'].items():
 if n not in M['owned_sources']:assert old['sources'][n]==h,('external provider differs from accepted foundation',n)
assert json.loads((Q/'live-class-audit-v1/receipt.json').read_text())['status']=='passed'
# Preserve source and output identities before retiring obsolete preserved-context outputs.
outputs={str(p.relative_to(R)):sha(p) for p in (R/'.lake/build').rglob('*') if p.is_file()}
(L/'retired-preserved-artifacts.json').write_text(json.dumps(outputs,indent=2)+'\n')
shutil.rmtree(R/'.lake/build')
for n,h in M['source_hashes'].items():
 data=(S/n).read_bytes() if n in M['owned_sources'] else subprocess.check_output(['git','show',M['base']+':'+n],cwd=B)
 assert hashlib.sha256(data).hexdigest()==h,n
 p=R/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
for n in M['owned_sources']:
 if not n.startswith('scripts/'):continue
 p=R/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((S/n).read_bytes())
original={};effective={}
for n,h in M['configs'].items():
 data=subprocess.check_output(['git','show',M['base']+':'+n],cwd=B);assert hashlib.sha256(data).hexdigest()==h
 original[n]=h
 # Match the accepted foundation's build-only worker limit. Weak args do not enter normal module traces.
 if n=='lakefile.toml':
  assert b'weakLeanArgs = [' in data
  data=data.replace(b'weakLeanArgs = [',b'weakLeanArgs = ["-j1",',1)
 assert data==(Path(json.loads((D/'current-foundation-snapshot-v1.json').read_text())['package'])/n).read_bytes(),('effective config differs from accepted normal build',n)
 (R/n).write_bytes(data);effective[n]=hashlib.sha256(data).hexdigest()
# Native Lake needs current repository scripts, with exact current-main contents.
for n in subprocess.check_output(['git','ls-tree','-r','--name-only',M['base'],'scripts'],cwd=B,text=True).splitlines():
 if n in M['owned_sources']:continue
 p=R/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(subprocess.check_output(['git','show',M['base']+':'+n],cwd=B))
 mode=subprocess.check_output(['git','ls-tree',M['base'],n],cwd=B,text=True).split()[0]
 if mode=='100755':p.chmod(0o755)
# Borrow immutable products only when the complete source/config dependency closure matches J.
Jctx=json.loads((E/'892-joint-current-context-v2/context.json').read_text());matches={}
def equal(n):
 if n not in matches:matches[n]=(Jctx['source_hashes'].get(n)==M['source_hashes'][n] and all(equal(d) for d in M['imports'][n]))
 return matches[n]
borrowed={};missing=[]
for n in M['source_hashes']:
 if n in M['owned_sources']:continue
 if not equal(n):missing.append(n);continue
 stem=Path(n).with_suffix('')
 if not (J/'.lake/build/lib/lean'/Path(str(stem)+'.olean')).exists():missing.append(n);continue
 for area in ['lib/lean','ir']:
  p=J/'.lake/build'/area/stem
  for src in p.parent.glob(p.name+'.*'):
   if not src.is_file():continue
   target=R/src.relative_to(J);target.parent.mkdir(parents=True,exist_ok=True)
   if src.suffix in ['.trace','.hash','.json']:shutil.copyfile(src,target)
   else:os.link(src,target)
   borrowed[str(target.relative_to(R))]=sha(target)
state=dict(status='prepared_not_validated',base=M['base'],source_hashes=M['source_hashes'],original_configs=original,effective_configs=effective,borrowed_artifacts=borrowed,requires_native_restore=missing,all_external_sources_equal_accepted_foundation=True,source_closure=808,no_live_package_writes=True,normal_native_cache=str(E/'892-current-main-context-v1/package/.lake/ci-cache'),utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(L/'receipt.json').write_text(json.dumps(state,indent=2)+'\n');print('prepared',len(borrowed),'products;',len(missing),'providers need native restoration',flush=True)
