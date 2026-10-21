from pathlib import Path
import argparse,datetime,json,os,re,subprocess
p=argparse.ArgumentParser();p.add_argument('--update-status',action='store_true');a=p.parse_args()
root=Path('/tmp/stock-arithmetic-arm-model-author-gates');view=Path('/home/lee/clifv/.worktrees/stock-driver-incremental')
checkout_head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=view,text=True).strip()
extra_state=json.loads((root/'committed-route-extra-gate.json').read_text())['state']
state=json.loads((root/'progress.json').read_text());now=datetime.datetime.now(datetime.timezone.utc).isoformat()
def live(pid,needle):
 try:
  raw=(Path('/proc')/str(pid)/'cmdline').read_bytes()
  stat=(Path('/proc')/str(pid)/'stat').read_text().rsplit(')',1)[1].split()
  return needle.encode() in raw and stat[0]!='Z'
 except (FileNotFoundError,ProcessLookupError,PermissionError):return False
controller=state['pid'];scheduler=1235140
uptime=float(Path('/proc/uptime').read_text().split()[0]);hz=os.sysconf('SC_CLK_TCK');page=os.sysconf('SC_PAGE_SIZE');jobs=[]
for proc in Path('/proc').iterdir():
 if not proc.name.isdigit():continue
 try:
  args=(proc/'cmdline').read_bytes().decode().split('\0');cwd=(proc/'cwd').resolve()
  if not args or Path(args[0]).name!='lean' or cwd!=view or not any(x.endswith('.lean') for x in args):continue
  st=(proc/'stat').read_text().rsplit(')',1)[1].split()
  if st[0]=='Z':continue
  jobs.append({'pid':int(proc.name),'source':next(x for x in args[1:] if x.endswith('.lean')),'cpu_seconds':round((int(st[11])+int(st[12]))/hz,1),'elapsed_seconds':round(uptime-int(st[19])/hz,1),'rss_MiB':round(int((proc/'statm').read_text().split()[1])*page/2**20,1)})
 except (FileNotFoundError,ProcessLookupError,PermissionError,UnicodeDecodeError):continue
log=(root/'all-modules/sched.log').read_text();done=re.findall(r'done (\S+) rc=(\d+)',log);bad=[{'module':m,'rc':int(c)} for m,c in done if c!='0']
r={'utc':now,'head':state['head'],'checkout_head':checkout_head,'supplemental_route_runtime_state':extra_state,'state':state['state'],'phase':state.get('phase'),'controller_pid':controller,'controller_live':live(controller,'/tmp/stock-arithmetic-arm-model-author-gates.py'),'scheduler_pid':scheduler,'scheduler_live':live(scheduler,'/tmp/stock-execute-scheduler.py'),'completed_module_records':len(done),'nonzero_records':bad,'actual_lean_jobs':sorted(jobs,key=lambda x:x['pid']),'latest_module_events':log.splitlines()[-3:]}
(root/'last-live-observation.json').write_text(json.dumps(r,indent=2)+'\n')
if a.update_status:
 # Do not turn stale metadata into a verified-wait claim.
 assert r['controller_live'] or jobs or state['state']!='running','live author handle missing: investigate before reporting a wait'
 text=subprocess.check_output(['gh','issue','view','44','--repo','eth-act/clifv','--json','body'],text=True);body=json.loads(text)['body']
 body=re.sub(r'Updated UTC: [^\n]+','Updated UTC: '+now+'. **Active. Full original #140 is unfinished.** Owner: @codygunton and this agent.',body,count=1)
 body=re.sub(r'\nLatest live arithmetic observation:.*\n','\n',body)
 summary='; '.join(str(j['pid'])+' '+Path(j['source']).name+' '+str(j['elapsed_seconds'])+'s elapsed/'+str(j['cpu_seconds'])+'sCPU' for j in jobs) or 'no Lean kernel observed; see recorded controller phase'
 body+='\nLatest live arithmetic observation: '+now+': controller'+str(controller)+' live='+str(r['controller_live'])+', scheduler'+str(scheduler)+' live='+str(r['scheduler_live'])+', phase='+str(r['phase'])+', state='+r['state']+'. Actual kernels: '+summary+'. '+str(len(done))+' completed current module records; '+str(len(bad))+' nonzero records. Validation head672c4dc4; checkout '+checkout_head[:8]+'. Original full140 remains active. Supplemental route-runtime state='+extra_state+'; logical function validation has its separate boundary above. Observation `/tmp/stock-arithmetic-arm-model-author-gates/last-live-observation.json`.\n'
 Path('/tmp/stock-ni-current-status44.md').write_text(body)
 subprocess.run(['gh','issue','edit','44','--repo','eth-act/clifv','--body-file','/tmp/stock-ni-current-status44.md'],check=True,stdout=subprocess.DEVNULL)
 resume=Path('/tmp/stock-current-resume.json');x=json.loads(resume.read_text());x['utc']=now;x['latest_authoritative_observation']=r;x['arithmetic']['latest_completed_modules_observed']=len(done);x['arithmetic']['latest_nonzero']=bad;x['arithmetic']['actual_compiler_pids_last_observed']=[j['pid'] for j in jobs];x['arithmetic']['observer']='/tmp/stock-observe-arithmetic-gate.py';x['previous_goal_turn']='verified wait: observer checked actual process command lines/states and current gate records; see latest_authoritative_observation';resume.write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(r))
