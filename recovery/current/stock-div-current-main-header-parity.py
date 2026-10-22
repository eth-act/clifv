from pathlib import Path
import re,subprocess,json
root=Path.cwd();base='5c1351a088eee97b38925a5266f5a6f4cbd19797'
def declarations(s):
 frames=[];out={}
 original=s
 chars=list(s);i=0;depth=0;quoted=False
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;chars[i:i+2]=[' ',' '];i+=2;continue
   if s.startswith('-/',i):depth-=1;chars[i:i+2]=[' ',' '];i+=2;continue
   if s[i]!='\n':chars[i]=' '
   i+=1;continue
  if quoted:
   if s[i]=='\\':
    chars[i]=' ';i+=1
    if i<len(s):chars[i]=' ';i+=1
    continue
   if s[i]=='"':quoted=False
   if s[i]!='\n':chars[i]=' '
   i+=1;continue
  if s.startswith('/-',i):depth=1;chars[i:i+2]=[' ',' '];i+=2;continue
  if s.startswith('--',i):
   while i<len(s) and s[i]!='\n':chars[i]=' ';i+=1
   continue
  if s[i]=='"':quoted=True;chars[i]=' '
  i+=1
 s=''.join(chars)
 for m in re.finditer(r'(?m)^(namespace|section|end|theorem)\b([^\n]*)',s):
  kind,rest=m.group(1),m.group(2).strip()
  if kind in ('namespace','section'):frames.append((kind,rest.split()[0] if rest else ''))
  elif kind=='end':
   if frames:frames.pop()
  else:
   name=re.match(r'([^\s({:]+)',rest).group(1);end=s.find(':=',m.start());header=original[m.start():end].strip();scope='.'.join(x for k,x in frames if k=='namespace');out[(scope+'.'+name).strip('.')]=header
 return out
current={}
for folder in ['FV','FVTest']:
 for p in (root/folder).rglob('*.lean'):current.update(declarations(p.read_text()))
paths=subprocess.check_output(['git','diff','--diff-filter=M','--name-only',base],text=True).splitlines();prior={}
for name in paths:
 if name.endswith('.lean'):
  prior.update(declarations(subprocess.check_output(['git','show',base+':'+name],text=True)))
missing=sorted(set(prior)-set(current));changed=sorted(k for k,v in prior.items() if k in current and current[k]!=v)
result={'base':base,'old_public_headers':len(prior),'missing':missing,'changed':changed,'unchanged':not missing and not changed,'proofs':sorted(prior)}
Path('/tmp/stock-div-current-main-header-parity.json').write_text(json.dumps(result,indent=2));print({k:v for k,v in result.items() if k!='proofs'});assert result['unchanged']
