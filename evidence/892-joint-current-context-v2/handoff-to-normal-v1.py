from pathlib import Path
import json,psutil,os,signal,time,hashlib,subprocess,datetime
O=Path(__file__).resolve().parent;S=json.loads((O/'normal-handoff-boundary-v1.json').read_text());C=json.loads((O/'context.json').read_text());P=Path(C['package']);shell=S['active_scope_shell'];controller=S['controller'];maxthreads=0
assert os.environ.get('WORKER_O_PROOF_SLOT_GRANTED')=='892-joint-12G'
def sha(f):return hashlib.sha256(Path(f).read_bytes()).hexdigest()
while True:
 st=Path(f'/proc/{shell}/stat').read_text().rsplit(')',1)[1].split()
 if st[0]=='Z':
  raw_exit=int(st[49]);break
 try:maxthreads=max(maxthreads,psutil.Process(S['active_lean']).num_threads())
 except psutil.NoSuchProcess:pass
 time.sleep(1)
assert raw_exit==0,('Active compiler failed before handoff',raw_exit)
cmd=S['active_lean_command'];source=str(Path(cmd[3]).relative_to(P));assert source in C['kernel_queue'];idx=C['kernel_queue'].index(source)
progress=O/'provider-kernels-v1/progress.json';r=json.loads(progress.read_text())['records'];assert len(r)==idx,(len(r),idx)
stem=P/'.lake/build/lib/lean'/Path(source).with_suffix('');outputs={}
for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir','.c']:
 f=Path(str(stem)+suffix)
 if f.exists():outputs[suffix]={'sha256':sha(f),'bytes':f.stat().st_size}
assert '.olean' in outputs
log=O/'provider-kernels-v1'/(str(idx)+'-'+Path(source).stem+'.log');stats=Path(S['scope_env']['FV_MEMCAP_STATS'])
rec={'index':idx,'source':source,'source_sha256':sha(P/source),'direct_import_output_sha256':{d:sha(P/'.lake/build/lib/lean'/Path(d).with_suffix('.olean')) for d in C['imports'][source] if d.startswith(('FV/','FVTest/'))},'command':cmd,'exit':0,'raw_proc_exit_code':raw_exit,'elapsed_seconds':time.time()-S['lean_create_time'],'max_os_threads':maxthreads,'memstats':stats.read_text(),'log_sha256':sha(log),'outputs':outputs,'collected_at_approved_controller_handoff':True};r.append(rec);progress.write_text(json.dumps({'records':r},indent=2)+'\n')
# Only the stopped Python controller receives these signals. The compiler already exited normally.
assert psutil.Process(controller).status()=='stopped';os.kill(controller,signal.SIGTERM);os.kill(controller,signal.SIGCONT)
for _ in range(100):
 if not psutil.pid_exists(controller) or psutil.Process(controller).status()==psutil.STATUS_ZOMBIE:break
 time.sleep(.1)
else:raise RuntimeError('Controller did not release')
S.update(status='active_module_preserved_controller_released',last_raw_module=source,last_raw_index=idx,completed_raw_kernels=len(r),compiler_exit=0,controller_exit='Planned SIGTERM+SIGCONT after compiler exit; not a compiler failure',utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(O/'normal-handoff-boundary-v1.json').write_text(json.dumps(S,indent=2)+'\n')
(O/'providers-state-raw-handoff-v1.json').write_text(json.dumps({'status':'approved_handoff_to_normal_keys','completed_raw_kernels':len(r),'last_module':source,'no_compiler_killed':True,'full_goal_complete':False},indent=2)+'\n')
print('APPROVED HANDOFF',source,'rawpassed',len(r),'compilerexit0; controlleronlySIGTERM',flush=True)
raise SystemExit(subprocess.call(['python3',str(O/'run-normal-providers-v1.py')],env=dict(os.environ)))
