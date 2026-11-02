from pathlib import Path
import json,hashlib,os,re,shutil,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';Q=Path(__file__).resolve().parent;J=E/'892-joint-current-context-v2/package';R=Q/'validation-package-v1';R.mkdir();L=Q/'probe-context-v1';L.mkdir();base='45a70ee6e405d0a5e590603c320ec28799595f45'
configs={}
for n in ['lean-toolchain','lakefile.toml','lake-manifest.json']:
 data=(J/n).read_bytes()
 if n=='lakefile.toml':data=data.replace(b'"-j2",',b'"-j1",')
 (R/n).write_bytes(data);configs[n]=hashlib.sha256(data).hexdigest()
(R/'.lake').mkdir();(R/'.lake/packages').symlink_to((J/'.lake/packages').resolve(),target_is_directory=True)
sources={};dag={};todo=['FV/Backend/Lowering/StockArithmetic.lean','FV/Backend/LinearScan.lean','FV/Clif/Parse.lean']
while todo:
 n=todo.pop()
 if n in sources:continue
 data=subprocess.check_output(['git','show',base+':'+n],cwd=B);assert (J/n).read_bytes()==data,('Frozen broad source differs',n);sources[n]=data;dag[n]=[x.replace('.','/')+'.lean' for x in re.findall(r'^import\s+([\w.]+)',data.decode(),re.M) if x.startswith(('FV.','FVTest.'))];todo.extend(dag[n])
borrowed={}
for n,data in sources.items():
 p=R/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data);stem=Path(n).with_suffix('');assert (J/'.lake/build/lib/lean'/Path(str(stem)+'.olean')).exists(),('Missing baseline provider',n)
 for area in ['lib/lean','ir']:
  p=J/'.lake/build'/area/stem
  for src in p.parent.glob(p.name+'.*'):
   if not src.is_file():continue
   d=R/src.relative_to(J);d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,d);borrowed[str(d.relative_to(R))]=hashlib.sha256(d.read_bytes()).hexdigest()
keys={}
def key(n):
 if n not in keys:keys[n]=hashlib.sha256(json.dumps([configs,hashlib.sha256(sources[n]).hexdigest(),[(d,key(d)) for d in sorted(dag[n])]],sort_keys=True).encode()).hexdigest()
 return keys[n]
for n in sources:key(n)
context=dict(status='prepared_not_verified',base=base,source_context='Published main45a frozen source; inner loop only, not later current-main publication',source_hashes={n:hashlib.sha256(d).hexdigest() for n,d in sources.items()},imports=dag,dependency_keys=keys,effective_configs=configs,borrowed_artifacts=borrowed,native_cache=str(E/'892-current-main-context-v1/package/.lake/ci-cache'),budget='2G-j1',broad_owner_untouched=True,no_new_warmcache=True);(L/'context.json').write_text(json.dumps(context,indent=2)+'\n')
caller=(Q/'original-caller.clif').read_text();callee=(Q/'original-callee.clif').read_text();original=(E/'direct-call-arithmetic-live-packet-v1/InspectLiveCallV2.lean').read_text();a=original.index('def callerText');b=original.index('def main',a);s=original[:a]+'def callerText : String := '+json.dumps(caller)+'\ndef calleeText : String := '+json.dumps(callee)+'\n\n'+original[b:];s=s.replace('[7,31,79,101,121]','[7,11,31,101,109,121]');(Q/'InspectCallStoreV1.lean').write_text(s);print('Prepared',len(sources),'provider sources and original call/store probe')
