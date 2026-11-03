from pathlib import Path
import subprocess,re,json,hashlib,ast,os,datetime
O=Path(__file__).resolve().parent;proposal=json.loads((O/'manifest.json').read_text());E=O.parents[1];P=E/'892-joint-current-context-v2/package';base=Path('/home/lee/clifv');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();ref=proposal['origin_ref']
tree=ast.parse((O/'inventory.py').read_text());exec(compile(ast.Module(body=[node for node in tree.body if isinstance(node,ast.FunctionDef) and node.name in ['clean','imports']],type_ignores=[]),'import-parser','exec'))
root='FV.E2E.DeadCleanupExecGot';todo=[root];modules={};missingOrigin=[]
while todo:
 m=todo.pop()
 if m in modules or m in missingOrigin:continue
 rel=m.replace('.','/')+'.lean';expected=proposal['all_current8f_lean_sources'].get(rel)
 if expected is None:missingOrigin.append(m);continue
 p=P/rel;actual=sha(p) if p.exists() else None
 data=p.read_bytes() if actual==expected else subprocess.check_output(['git','show',ref+':'+rel],cwd=base)
 assert hashlib.sha256(data).hexdigest()==expected
 deps=imports(data);trace=P/'.lake/build/lib/lean'/Path(rel).with_suffix('.trace');olean=trace.with_suffix('.olean');native=json.loads(trace.read_text()) if trace.exists() else None
 modules[m]={'source_sha256':expected,'donor_source_sha256':actual,'imports':deps,'donor_trace_sha256':sha(trace) if trace.exists() else None,'donor_native_key':native.get('depHash') if native else None,'donor_outputs':native.get('outputs') if native else None,'donor_olean_present':olean.exists(),'expected_key_query_run':False}
 todo.extend(n for n in deps if n.startswith('FV.'))
writers=[]
for proc in Path('/proc').iterdir():
 if not proc.name.isdigit():continue
 try:
  if proc.stat().st_uid!=os.getuid():continue
  argv=(proc/'cmdline').read_bytes().split(b'\0');args=[x.decode(errors='replace') for x in argv if x]
  if not args or Path(args[0]).name!='lean':continue
  for arg in args:
   if arg.startswith(str(P)+'/FV/') and arg.endswith('.lean'):
    m=arg[len(str(P))+1:-5].replace('/','.')
    if m in modules:writers.append({'pid':int(proc.name),'module':m,'argv':args})
 except (OSError,PermissionError):continue
configs={n:sha(P/n) for n in ['lakefile.toml','lake-manifest.json','lean-toolchain']}
sourceConfigs={n:hashlib.sha256(subprocess.check_output(['git','show',ref+':'+n],cwd=base)).hexdigest() for n in configs}
profiles={}
for n in [root,'FV.E2E.RegLevelSim']:
 hits=[]
 for folder in [E/'captured-consumer-modules-v2',E/'captured-consumer-modules-v1']:
  p=folder/(n+'.mem')
  if p.exists():hits.append({'path':str(p),'sha256':sha(p),'text':p.read_text(),'source_config_key_binding_established':False})
 profiles[n]=hits
receipt={'status':'read_only_static_donor_inventory_not_normal_readiness','proposal_manifest_sha256':sha(O/'manifest.json'),'origin_ref':ref,'donor':str(P),'root':root,'modules':modules,'module_count':len(modules),'missing_origin_sources':missingOrigin,'source_mismatches':[m for m,v in modules.items() if v['source_sha256']!=v['donor_source_sha256']],'missing_native_records':[m for m,v in modules.items() if v['donor_native_key'] is None],'missing_oleans':[m for m,v in modules.items() if not v['donor_olean_present']],'active_overlapping_lean_writers':writers,'donor_config_hashes':configs,'git8f_config_hashes':sourceConfigs,'config_differences':[n for n in configs if configs[n]!=sourceConfigs[n]],'profiles':profiles,'shared_mutations':0,'artifact_promotions':0,'Lean_compilers_started':0,'proper_normal_checks_run':False,'creator_provenance_review_required_before_reuse':True,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
D=O/'donor-inventory-v1';D.mkdir();(D/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print('closure',len(modules),'source mismatches',len(receipt['source_mismatches']),'missing native',len(receipt['missing_native_records']),'missing olean',len(receipt['missing_oleans']),'writers',len(writers),'config diffs',receipt['config_differences']);print('receipt',sha(D/'receipt.json'))
