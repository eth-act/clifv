"""Read only comparison identity fields through jq's bounded streaming parser."""
import json,subprocess
FILTER='''select(length==2) | select(
 (.[0][0]!="tests" and (.[0][0]=="progress" or .[0][0]=="configuration_overrides" or .[0][0]=="binary_normalization")) or
 (.[0][0]=="tests" and (
  ((.[0]|length)==3 and (.[0][-1]=="test" or .[0][-1]=="source_sha256")) or
  ((.[0]|length)==5 and .[0][2]=="variants" and (.[0][-1]=="index" or .[0][-1]=="stage")) or
  ((.[0]|length)==7 and .[0][2]=="variants" and .[0][4]=="functions_compared" and (.[0][-1]=="index" or .[0][-1]=="name" or .[0][-1]=="status" or .[0][-1]=="exact_code_artifact"))
 )))'''
def read_comparison(path):
    tests={};variants={};functions={};meta={}
    proc=subprocess.Popen(['jq','--stream','-c',FILTER,str(path)],stdout=subprocess.PIPE,text=True)
    for line in proc.stdout:
        key,value=json.loads(line)
        if key[0]!='tests':
            if key[0]=='configuration_overrides' and len(key)>1:meta['configuration_overrides']=['nonempty']
            else:meta[key[0]]=value
        elif len(key)==3:tests.setdefault(key[1],{})[key[-1]]=value
        elif len(key)==5:variants.setdefault((key[1],key[3]),{})[key[-1]]=value
        else:functions.setdefault((key[1],key[3],key[5]),{})[key[-1]]=value
    assert proc.wait()==0,'Streaming comparison parser failed'
    inputs={r['test']:r['source_sha256'] for r in tests.values()};assert len(inputs)==len(tests)
    rows={}
    for (test,variant,_),row in functions.items():
        v=variants[test,variant];identity=(tests[test]['test'],v['index'],v['stage'],row['index'],row['name']);assert identity not in rows;rows[identity]=row
    return inputs,rows,meta
