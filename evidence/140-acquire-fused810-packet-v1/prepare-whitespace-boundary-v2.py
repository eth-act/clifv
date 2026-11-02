from pathlib import Path
import json,hashlib
A=Path(__file__).resolve().parent;F=A.parent/'140-fence-packet-v1';P=F/'package';oldDir=A/'delivery-boundary-v1';O=A/'delivery-boundary-v2';h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();m=json.loads((oldDir/'manifest-v2.json').read_text());changes={};lineCount=0
for rel,oldHash in m['source_sha256'].items():
 oldSource=oldDir/'source'/rel;p=O/'source'/rel;assert h(oldSource)==oldHash;s=oldSource.read_text();new='\n'.join(x.rstrip(' \t') for x in s.splitlines())+'\n';assert p.read_text()==new
 if new!=s:
  changes[rel]={'old_sha256':oldHash,'new_sha256':h(p)};m['source_sha256'][rel]=h(p)
  lineCount+=sum(left!=right for left,right in zip(s.splitlines(),new.splitlines()))
assert len(changes)==3 and lineCount==4
changed={x[:-5].replace('/','.') for x in changes};allmods=m['candidate_topological_order'];affected=set(changed)
for mod in allmods:
 p=O/'source'/(mod.replace('.','/')+'.lean');deps=[n for l in p.read_text().splitlines() if l.startswith('import ') for n in l[7:].split()]
 if any(x in affected for x in deps):affected.add(mod)
queue=[x for x in allmods if x in affected];m['whitespace_only_changes']=changes;m['focused_rebuild_queue']=queue;m['previous_manifest_sha256']=h(oldDir/'manifest-v2.json');m['previous_current_gate_sha256']=h(oldDir/'current-gate-v2.json');m['reused_normal_keys_unchanged']=True
(O/'manifest.json').write_text(json.dumps(m,indent=2)+'\n')
for rel in changes:
 p=P/rel;assert h(p)==changes[rel]['old_sha256'];p.write_bytes((O/'source'/rel).read_bytes())
print(json.dumps({'changed_files':len(changes),'affected_kernels':len(queue),'queue':queue}))
