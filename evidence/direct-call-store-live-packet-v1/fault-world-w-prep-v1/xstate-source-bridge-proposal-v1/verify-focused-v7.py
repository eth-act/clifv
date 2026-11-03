from pathlib import Path
import json,hashlib,subprocess,os,psutil,shutil
D=Path(__file__).resolve().parent;W=D.parent;Q=W.parent;T=Q/'callee-trap-prep-v1';E=Q.parent;R=Q/'validation-package-v1';P=E/'892-joint-current-context-v2/package';L=D/'focused-kernels-v7';L.mkdir()
# This independent focused check runs only after both current linked controllers exit.
for pid in [2763404,2795422]:
 try:
  p=psutil.Process(pid);assert p.status()==psutil.STATUS_ZOMBIE,(pid,p.cmdline())
 except psutil.NoSuchProcess:pass
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
scope=json.loads((D/'scope.json').read_text());sources={n:scope['source_hashes'][n] for n in scope['focused_core_sources']};dag={};hashes={}
for n,h in sources.items():assert sha(D/'source'/n)==h
import re
def visit(n):
 if n in hashes:return
 src=D/'source'/n if n in sources else R/n;hashes[n]=sha(src);dag[n]=[x.replace('.','/')+'.lean' for x in re.findall(r'^import\s+([\w.]+)',src.read_text(),re.M) if x.startswith('FV.')]
 for dep in dag[n]:visit(dep)
for n in sources:visit(n)
for p in psutil.process_iter(['name','cmdline','status']):
 try:
  if p.info['name']=='lean' and p.info['status']!='zombie':assert not any(str(R/n) in (p.info['cmdline'] or []) for n in hashes),(p.pid,'active provider')
 except(psutil.NoSuchProcess,psutil.AccessDenied):pass
env=dict(os.environ)
for k in ['FV_LAKE_CACHE','FV_MEMCAP_OFF','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','LAKE_CACHE_DIR']:env.pop(k,None)
env.update(PATH='/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin:'+env['PATH'],FV_ROOT=str(R),FV_MEMCAP='2G',LAKE_ARTIFACT_CACHE='false',LAKE_RESTORE_ARTIFACTS='false',LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1');records=[]
def run(label,args):
 e=dict(env,FV_MEMCAP_STATS=str(L/(label+'.mem')),FV_MEMCAP_UNIT='worker-o-unwind-prototype-'+label)
 with (L/(label+'.log')).open('w') as f:rc=subprocess.call([str(P/'scripts/memcap.sh'),*args],cwd=R,env=e,stdout=f,stderr=subprocess.STDOUT)
 records.append(dict(label=label,argv=args,exit=rc,stats=(L/(label+'.mem')).read_text() if (L/(label+'.mem')).exists() else None));(L/'progress.json').write_text(json.dumps(records,indent=2)+'\n');print(label,rc,flush=True)
 if rc:raise SystemExit(rc)
run('proper-dependencies',['lake','build','--no-build',*[n[:-5].replace('/','.') for n in sorted(set(hashes)-set(sources))]])
for n in ['FV/E2E/UnwindReachSource.lean','FV/E2E/UnwindMemoryFaultSource.lean']:
 dst=R/n;assert not dst.exists() or sha(dst) in [sources[n],'4edcd9513fe197cae7d9931d408437d41c3f547b336287a3fb400bd1e90bcc66','081c0a924fedb2e3a35e6d30fa4e390ba544808a7ba91729a2cbf8181013efb2','459491999d74a88d094e083d88626f48592654377ffcdd34313641d7cd43a2db','4b7eb8359888f784d3613210d759c41fe2a04403eadf90726e876f0e611194fa','6a669917eed337adae24e0800accb1d944dc07a09577c54ee8d42ac42d695608'],n;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(D/'source'/n,dst)
 run(('reuse-' if dst.stem=='UnwindReachSource' else 'kernel-')+dst.stem,['lake','build','--no-build',n[:-5].replace('/','.')] if dst.stem=='UnwindReachSource' else ['lake','-v','build','+'+n[:-5].replace('/','.')+':leanArts'])
run('complete-normal',['lake','build','--no-build','FV.E2E.UnwindReachSource','FV.E2E.UnwindMemoryFaultSource'])
roots=['E2E.ReachX.trans','E2E.TrapsExplicitX.at_reached','E2E.MapFaultsFromX.at_reached','E2E.MapFaultsX.at_reachedX','E2E.MapFaultsX.at_reached','E2E.TrapsExplicitX.toMX','E2E.UnwindMemoryWitness.default_load_admitted','E2E.UnwindMemoryWitness.default_store_admitted'];audit=L/'unwind-memory-source.lean';audit.write_text('import FV.E2E.UnwindMemoryFaultSource\n\n'+'\n'.join('#print axioms '+n for n in roots)+'\n');env['PATH']=str(T/'tool-bin')+':'+env['PATH'];env['WORKER_O_AUDIT_COMMAND_LOG']=str(L/'actual-lean-commands.jsonl');run('real-audit',['python3',str(P/'scripts/axiom-audit.py'),'--cwd',str(R),'--log-dir',str(L/'audit'),str(audit)])
(L/'receipt.json').write_text(json.dumps(dict(status='passed-focused-source-interface-only',source_hashes=sources,full_source_hashes=hashes,configs={n:sha(R/n) for n in ['lean-toolchain','lakefile.toml','lake-manifest.json']},records=records,real_auditor_sha256=sha(P/'scripts/axiom-audit.py'),standard_roots=roots,open=scope['open'],no_new_production_admission=True),indent=2)+'\n')
