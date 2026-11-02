from pathlib import Path
import datetime,hashlib,json,os,subprocess,time
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029'
p=json.loads((E/'513-delivery-prepared-v1/prepared-state.json').read_text());old=p['prepared_head'];tree=p['prepared_tree'];branch=p['branch']
(E/'513-reconciliation-owner-v1.json').write_text(json.dumps(dict(pid=os.getpid(),head=old,branch=branch,exclusive=True),indent=2)+'\n')
def run(*args):return subprocess.check_output(args,cwd=B,text=True).strip()
for _ in range(720):
 if (E/'return-pin-production-landed-v1.json').exists():break
 time.sleep(10)
else:raise RuntimeError('Production parent still lacks an actual landed receipt; inspect its live controller.')
parent=json.loads((E/'return-pin-production-landed-v1.json').read_text());assert parent['status']=='landed' and parent['tree_equal'] and parent['source']==p['prospective_production_parent']
actual=json.loads(run('gh','pr','view','892','--repo','eth-act/clifv','--json','state,mergeCommit,headRefOid'));assert actual['state']=='MERGED' and actual['mergeCommit']['oid']==parent['merged'] and actual['headRefOid']==parent['source']
run('git','fetch','origin','main');base=run('gh','api','repos/eth-act/clifv/commits/main','--jq','.sha');assert run('git','rev-parse',base+'^{tree}')==parent['tested_tree'],'Inspect main drift before the normal reconciliation.'
assert run('git','ls-remote','origin','refs/heads/'+branch).split()[0]==old
assert run('git','merge-tree','--write-tree',old,base).splitlines()[0]==tree
assert set(run('git','diff','--name-only',base,tree).splitlines())==set(p['source_sha256'])
for n,h in p['source_sha256'].items():assert hashlib.sha256(subprocess.check_output(['git','show',tree+':'+n],cwd=B)).hexdigest()==h
context=json.loads((E/'513-delivery-prepared-v1/focused-context-equality.json').read_text())['source_paths']
for n,v in context.items():assert run('git','rev-parse',tree+':'+n)==v['candidate_blob']
head=run('git','commit-tree',tree,'-p',base,'-p',old,'-m','Reconcile stable outcome interfaces onto landed production activation')
run('git','merge-base','--is-ancestor',old,head);run('git','push','origin',head+':refs/heads/'+branch)
run('gh','pr','edit','513','--repo','eth-act/clifv','--base','main')
r=dict(status='prepared',pr=513,branch=branch,published_source=head,previous_source=old,base=base,tree=tree,source_hashes=p['source_sha256'],validated_source='77088aba2b9c528264aead43ab563d7ee17a102e',parent='return-pin-production-landed-v1.json',expected_main_tree=parent['tested_tree'],import_source_closure={n:v['candidate_blob'] for n,v in context.items()},import_source_closure_equal=True,import_source_scope='Focused seven-kernel current context only; full affected importers remain pending. All207 packet sources and203 consumer bodies retain exact parity.',focused_kernel_modules=7,exact_type_axiom_roots=8,old_headers_exact=372,consumer_bodies_exact=203,moved_declarations_exact=8,validation='513-recovery-packet-v1/focused-current-main-state-v1.json',reviewed_packet_source=old,reviewed_packet_tree=tree,source_tree_unchanged=True,full_goal_complete=False,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
(E/'513-independent-delivery-prepared-v2.json').write_text(json.dumps(r,indent=2)+'\n')
config=dict(pr=513,prepared='513-independent-delivery-prepared-v2.json',parent=r['parent'],review='513-independent-peer-review-v2.json',landed='513-recovered-landed-v1.json')
(E/'513-independent-delivery-config-v2.json').write_text(json.dumps(config,indent=2)+'\n');print(json.dumps(dict(status='reconciled_waiting_direct_review',pr=513,head=head,tree=tree,source_tree_unchanged=True,focused_context_sources=len(context),full_affected_validation_passed=False)),flush=True)
