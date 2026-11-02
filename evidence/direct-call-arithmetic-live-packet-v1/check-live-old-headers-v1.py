from pathlib import Path
import json,re,hashlib
Q=Path(__file__).resolve().parent;P=Q.parent/'direct-call-production-class-packet-v1';R=Q/'validation-package-v1';M=json.loads((P/'reviewed-production-complete-v1/manifest.json').read_text());records={};bad={}
def headers(text):
 result={}
 for m in re.finditer(r'(?m)^(?:(?:private|protected|noncomputable)\s+)?(theorem|def|abbrev|structure|inductive)\s+([^\s{:(]+)',text):
  end=re.search(r':=|\bwhere\b',text[m.end():]);assert end,('header delimiter',m.group(2));header=text[m.start():m.end()+end.start()].rstrip();key=m.group(1)+' '+m.group(2);result.setdefault(key,[]).append(header)
 return result
for n,h in M.items():
 if not n.startswith(('FV/','FVTest/')) or not (R/n).exists():continue
 old=(P/'reviewed-production-complete-v1'/n).read_bytes();assert hashlib.sha256(old).hexdigest()==h,n
 before=headers(old.decode());after=headers((R/n).read_text())
 for k,values in before.items():
  for i,header in enumerate(values):
   target=after.get(k,[]);entry=n+':'+k+':'+str(i)
   if i>=len(target) or target[i]!=header:bad[entry]=dict(before=header,after=target[i] if i<len(target) else None)
   else:records[entry]=hashlib.sha256(header.encode()).hexdigest()
# Preserve the complete old semantic checker body, including every prior rejection theorem.
old=(P/'FV/Backend/SemanticABICheck.lean').read_text();body=old[old.index('namespace Backend.SemanticABI'):old.index('end Backend.SemanticABI')].strip();now=(R/'FV/Backend/SemanticABICheck.lean').read_text();old_checker_body_exact=body in now
state=dict(status='passed' if not bad and old_checker_body_exact else 'failed',compared=len(records),different=bad,headers=records,old_semantic_checker_body_exact=old_checker_body_exact,baseline='immutable complete49-source packet',context='staged live integration, not publication validation');(Q/'live-old-header-comparison-v1.json').write_text(json.dumps(state,indent=2)+'\n');print('headers',len(records),'different',len(bad),'old checker body exact',old_checker_body_exact);assert state['status']=='passed'
