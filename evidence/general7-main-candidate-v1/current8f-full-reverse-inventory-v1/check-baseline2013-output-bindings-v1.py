from pathlib import Path
import json,hashlib,subprocess,os
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';D=E/'general7-main-candidate-v1/current8f-full-reverse-inventory-v1';G=B/'.worktrees/loop-20261102';L=D/'baseline2013-output-bindings-v1';L.mkdir();helper=E/'140-acquire-fused810-packet-v1/outside-avoids-extraction-proposal-v1/HashNative.lean';assert hashlib.sha256(helper.read_bytes()).hexdigest()=='b9ccda01cacbfad79e205b60c9bddcae02f3944aa2c248d3df891d6b67b413dc';m=json.loads((D/'unaffected2013-current-bindings-v1.json').read_text());assert not m['problems'];entries=[];snapshot={}
def sha(f):
 h=hashlib.sha256()
 with f.open('rb') as inp:
  for part in iter(lambda:inp.read(1048576),b''):h.update(part)
 return h.hexdigest()
for row in m['rows']:
 rel=Path(row['target'].replace('.','/'));tr=G/'.lake/build/lib/lean'/rel.with_suffix('.trace');assert sha(tr)==row['trace_sha256'];t=json.loads(tr.read_text());assert t['depHash']==row['key'];assert not t['outputs'].get('m'),row['target']
 for ext,expected in [('olean',t['outputs']['o'][0].split('.')[0]),('ilean',t['outputs']['i'].split('.')[0]),('c',t['outputs']['c'].split('.')[0])]:
  area='ir' if ext=='c' else 'lib/lean';f=G/'.lake/build'/area/rel.with_suffix('.'+ext);entries.append((f,expected));snapshot[str(f.relative_to(G))]=sha(f)
 for area,ext in [('lib/lean','.trace'),('lib/lean','.olean.hash'),('lib/lean','.ilean.hash'),('ir','.c.hash')]:
  f=G/'.lake/build'/area/rel.with_suffix(ext);snapshot[str(f.relative_to(G))]=sha(f)
records=[];env=dict(os.environ);env.pop('LEAN_PATH',None);env.update(LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OMP_THREAD_LIMIT='1');native={}
for start in range(0,len(entries),256):
 chunk=entries[start:start+256];p=subprocess.run(['/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean','-j1','--run',str(helper),*[str(f) for f,_ in chunk]],cwd=E,env=env,capture_output=True,text=True);out=L/('native'+str(start)+'.stdout');err=L/('native'+str(start)+'.stderr');out.write_text(p.stdout);err.write_text(p.stderr);assert p.returncode==0,(start,p.returncode,p.stderr[-1000:]);lines=p.stdout.splitlines();assert len(lines)==len(chunk),(start,len(lines),len(chunk))
 for line,(f,expected) in zip(lines,chunk):
  name,binary,text=line.split('\t');assert name==str(f) and binary==expected,(name,binary,expected);native[str(f.relative_to(G))]=binary
 records.append({'start':start,'count':len(chunk),'exit':p.returncode,'stdout_sha256':sha(out),'stderr_sha256':sha(err)});print('checked cold payloads',min(start+256,len(entries)),flush=True)
for f,s in snapshot.items():assert sha(G/f)==s,('payload changed during check',f)
result={'status':'PASSED_CURRENT_BASELINE2013_NATIVE_AND_CRYPTOGRAPHIC_OUTPUT_BINDINGS','baseline_bindings_sha256':sha(D/'unaffected2013-current-bindings-v1.json'),'configs':{f:sha(G/f) for f in ['lakefile.toml','lean-toolchain','lake-manifest.json']},'helper_sha256':sha(helper),'payload_sha256':snapshot,'cold_native_hashes':native,'commands':records,'target_count':2013,'payload_native_count':len(entries),'new_project_compilers':0,'full3381_and326':'OPEN'};(L/'receipt.json').write_text(json.dumps(result,indent=2)+'\n');print('FINAL',len(snapshot),len(native),flush=True)
