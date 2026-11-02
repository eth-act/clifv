from pathlib import Path
import json,hashlib,subprocess,os,datetime
O=Path(__file__).resolve().parent; E=O.parent; R=Path('/home/lee/clifv'); C=E/'892-current-main-context-v1'; S=json.loads((O/'context.json').read_text()); CI=C/'package'; OUT=O/'ci-context-v4';OUT.mkdir()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
main='7c979e18457fd49d96b6f88f5f364ef62490f94c';head='475273fce510620604804d4ffeb76c2b4ffe48d6'
for stage,ref in [('baseline',main),('candidate',head)]:
 d=S['stages'][stage];pkg=OUT/stage;pkg.mkdir();d['package']=str(pkg)
 for rel,h in d['source_hashes'].items():
  data=subprocess.check_output(['git','show',ref+':'+rel],cwd=R);assert hashlib.sha256(data).hexdigest()==h,(stage,rel)
  dest=pkg/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
 (pkg/'Types.lean').write_bytes((O/stage/'Types.lean').read_bytes())
S['actual_main']=main;S['actual_pr_head']=head;S['scope']='Exact-current focused context; coherent CI outputs plus missing baseline kernels';S['resource_cap']='12GiB explicit-j2, one kernel job'
base=Path(S['stages']['baseline']['package']);srcs=S['stages']['baseline']['source_hashes'];restored={};missing=[]
for rel,h in srcs.items():
 assert sha(CI/rel)==h
 stem=CI/'.lake/build/lib/lean'/Path(rel).with_suffix('')
 if not Path(str(stem)+'.olean').exists():missing.append(rel);continue
 restored[rel]={}
 for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir','.trace','.c']:
  src=Path(str(stem)+suffix)
  if src.exists():
   dest=base/src.relative_to(CI);dest.parent.mkdir(parents=True,exist_ok=True);os.link(src,dest)
   restored[rel][suffix]={'sha256':sha(src),'bytes':src.stat().st_size}
assert len(restored)==212 and len(missing)==12,(len(restored),len(missing))
state=json.loads((C/'ci-recovery-state.json').read_text());receipt=Path(state['last_513_core_check']['path']);assert json.loads(receipt.read_text())['checks']['iseldata']['exit']==0
S['ci_provenance']={'run':41408842551,'head':'3a6719b44b0e6b38e24cd0de82655f93b78272a9','core_receipt':str(receipt),'core_receipt_sha256':sha(receipt),'restored':restored,'missing':missing,'io_quiesced':True,'original119untouched':True}
(O/'context-ci-v4.json').write_text(json.dumps(S,indent=2)+'\n')
print(json.dumps({'baseline':main,'candidate':head,'restored':len(restored),'missing':missing,'source_guards':'all224baseline+226candidate exact currentGit'}))
