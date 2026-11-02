from pathlib import Path
import datetime,fcntl,hashlib,json,os,psutil,re,subprocess
B=Path('/home/lee/clifv');E=B/'.git/agent-evidence/stock-memory-20261029';O=E/'892-joint-current-context-v2';P=O/'package';lock=(E/'892-final-publication-owner.lock').open('a+');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
for pid in [326832,456502]:
 assert not psutil.pid_exists(pid),('Previous healthy owner still exists',pid)
for p in psutil.process_iter(['cmdline']):
 args=p.info['cmdline'] or []
 assert not(any('merge-independent-packet-delivery-v3.py' in a for a in args) and any('production-independent-delivery-config-v5.json' in a for a in args)),('Existing892merger',p.pid)
def sha(p):
 with Path(p).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def git(*args,data=None):return subprocess.check_output(['git',*args],cwd=B,input=data).decode().strip()
def entries(tree):return {s.split('\t',1)[1]:s.split()[2] for s in git('ls-tree','-r',tree).splitlines()}
C=json.loads((O/'context.json').read_text());N=json.loads((O/'normal-providers-state-v1.json').read_text());Gpath=O/'runs/current-head-normal-v1/receipt.json';G=json.loads(Gpath.read_text());Qpath=E/'production-independent-delivery-prepared-v5.json';old=json.loads(Qpath.read_text());review=json.loads((E/'production-independent-peer-review-v5.json').read_text());assert N['status']==G['status']=='passed';assert N['normal_project_targets']==2895 and len(N['outputs'])==2895;assert N['authoritative_final_no_build_exit']==0;assert N['joint_tree']==C['joint_tree'];assert G['head892']==old['published_source'] and G['tree892']==old['tree'];assert all(r['exit']==0 for r in G['records']);assert (G['actual_backend_object_comparisons'],G['actual_complete_bundles'],G['actual_additional_typed_compiler_modes'],G['actual_generated_roots'])==(6,6,2,68)
assert G['provider_receipt_sha256']==sha(O/'providers-state-v1.json');provider=json.loads((O/'providers-state-v1.json').read_text());assert provider['normal_provider_receipt_sha256']==sha(O/'normal-providers-state-v1.json')
for n,h in C['source_hashes'].items():assert sha(P/n)==h,('Validated source changed',n)
for n,h in old['source_hashes'].items():assert sha(P/n)==h,('Canonical implementation changed',n)
for n,h in G['owned_output_sha256'].items():assert sha(P/'.lake/build/lib/lean'/Path(n).with_suffix('.olean'))==h,n
parity=json.loads((Gpath.parent/'exact-old-typed-axiom-parity.json').read_text());assert parity['status']=='passed' and len(parity['pairs'])==6
assert review['verdict']=='no blocking defect' and review['published_source']==old['published_source'] and review['implementation_files_unchanged']
# Only the runtime entrypoints modify existing files; all old theorem source files remain intact.
existing=[n for n in old['source_hashes'] if subprocess.run(['git','cat-file','-e',old['expected_main_tree']+':'+n],cwd=B,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode==0];assert set(existing)=={'FVTest/Backend/Main.lean','FVTest/Link/LeanLinkMain.lean','FVTest/E2E/LinkCheckMain.lean'}
for n in existing:
 for tree in [old['expected_main_tree'],old['tree']]:
  text=subprocess.check_output(['git','show',tree+':'+n],cwd=B,text=True)
  assert not re.search(r'^\s*(?:private\s+|protected\s+)?theorem\s',text,re.M),('Existing CLI theorem needs comparison',n)
normal_wrapper={'status':'passed','candidate_source':old['published_source'],'candidate_tree':old['tree'],'baseline_tree':old['expected_main_tree'],'source_hashes':old['source_hashes'],'old_headers_exact':True,'old_axiom_sets_exact':True,'exact_context':True,'kernel_gate_passed':True,'normal_gate_passed':True,'normal_provider_receipt_sha256':sha(O/'normal-providers-state-v1.json'),'actual_consumer_receipt_sha256':sha(Gpath),'actual_consumer_receipt':str(Gpath.relative_to(E)),'actual_counts':{k:G[k] for k in ['actual_backend_object_comparisons','actual_complete_bundles','actual_additional_typed_compiler_modes','actual_generated_roots']},'old_typed_parity_sha256':sha(Gpath.parent/'exact-old-typed-axiom-parity.json'),'existing_modified_files_have_no_theorems':existing,'full_goal_complete':False,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
assert not (O/'reviewed-publication-state-v5.json').exists();(O/'reviewed-publication-state-v5.json').write_text(json.dumps(normal_wrapper,indent=2)+'\n')
git('fetch','origin','main');base=git('rev-parse','origin/main');assert base==subprocess.check_output(['gh','api','repos/eth-act/clifv/commits/main','--jq','.sha'],cwd=B,text=True).strip();remote=git('ls-remote','origin','refs/heads/'+old['branch']).split()[0];assert remote==old['published_source']
tree=git('merge-tree','--write-tree',remote,base).splitlines()[0];assert len(tree)==40;candidate=entries(tree);validated=entries(C['joint_tree']);projected={}
for n,h in C['source_hashes'].items():
 if n not in validated:continue
 assert candidate.get(n)==validated[n],('Current-main source changed inside validated closure',n)
 projected[n]=candidate[n]
for n in ['lean-toolchain','lakefile.toml','lake-manifest.json','scripts/memcap.sh','scripts/axiom-audit.py']:
 assert candidate[n]==validated[n],('Current build configuration changed',n)
assert set(git('diff-tree','--no-commit-id','--name-only','-r',base,tree).splitlines())==set(old['source_hashes']);git('diff-tree','--check',base,tree)
head=git('commit-tree',tree,'-p',remote,'-p',base,'-m','Reconcile validated ABI production activation onto current main')
pre=dict(old,status='reconciled_current_context_passed',previous_source=remote,published_source=head,validated_source=base,base=base,tree=tree,expected_main_tree=git('rev-parse',base+'^{tree}'),validation='892-joint-current-context-v2/reviewed-publication-state-v6.json',actual_source_projection=projected,actual_source_projection_equal=True,historical_validation='892-joint-current-context-v2/reviewed-publication-state-v5.json',implementation_files_unchanged=True,utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(E/'production-independent-delivery-prepared-v6.json').write_text(json.dumps(pre,indent=2)+'\n')
validation=dict(normal_wrapper,candidate_source=head,candidate_tree=tree,baseline_tree=pre['expected_main_tree'],reconciled_from_validated_head=remote,entire_validated_source_projection_equal=True,validated_project_source_count=len(projected),full_goal_complete=False);(O/'reviewed-publication-state-v6.json').write_text(json.dumps(validation,indent=2)+'\n')
review6=dict(review,published_source=head,reviewed_source=review.get('reviewed_source',remote),carry_policy='All18reviewedimplementationfilesandtheirpatchremainexact;thecompletevalidatedsourceprojectionmatchescurrentmain.',actual_source_context_pending=False,reviewed_source_projection_equal=True);(E/'production-independent-peer-review-v6.json').write_text(json.dumps(review6,indent=2)+'\n')
config=json.loads((E/'production-independent-delivery-config-v5.json').read_text());config.update(prepared='production-independent-delivery-prepared-v6.json',review='production-independent-peer-review-v6.json',validation='892-joint-current-context-v2/reviewed-publication-state-v6.json',new_branch=False);(E/'production-independent-delivery-config-v6.json').write_text(json.dumps(config,indent=2)+'\n')
oldlocal=git('rev-parse','refs/heads/'+old['branch']);assert oldlocal==remote;git('update-ref','refs/heads/'+old['branch'],head,remote);git('push','origin','refs/heads/'+old['branch']+':refs/heads/'+old['branch']);assert git('ls-remote','origin','refs/heads/'+old['branch']).split()[0]==head
release={'status':'released_after_actual_normal_and_consumer_success','scheduler':326832,'observer':456502,'normal_receipt_sha256':sha(O/'normal-providers-state-v1.json'),'consumer_receipt_sha256':sha(Gpath),'reconciled_head':head,'full_goal_complete':False,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};(O/'reviewed-owner-release-v1.json').write_text(json.dumps(release,indent=2)+'\n');print(json.dumps({'status':'published_current_context_passed','head':head,'base':base,'tree':tree,'validated_source_count':len(projected),'large_slot_released':True}),flush=True)
