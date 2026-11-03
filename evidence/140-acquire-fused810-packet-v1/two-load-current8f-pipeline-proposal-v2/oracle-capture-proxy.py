#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,subprocess,sys
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert len(sys.argv)==2
config=Path(os.environ['FV_TWO_LOAD_ORACLE_BINDING']);c=json.loads(config.read_text())
assert c['status']=='approved_exact_current_export'
real=Path(c['real_oracle']).resolve();assert sha(real)==c['real_oracle_sha256']
source=Path(sys.argv[1]);assert sha(source)==c['exact_oracle_input_sha256']
out=Path(c['raw_answer_directory']);out.mkdir(parents=True,exist_ok=False)
(out/'input.json').write_bytes(source.read_bytes())
answer=subprocess.run([str(real),sys.argv[1]],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
(out/'stdout.bin').write_bytes(answer.stdout);(out/'stderr.bin').write_bytes(answer.stderr)
(out/'state.json').write_text(json.dumps(dict(exit=answer.returncode,real_oracle_sha256=sha(real),input_sha256=sha(source),stdout_sha256=hashlib.sha256(answer.stdout).hexdigest(),stderr_sha256=hashlib.sha256(answer.stderr).hexdigest(),binding_sha256=sha(config),answer_unmodified=True),indent=2)+'\n')
sys.stdout.buffer.write(answer.stdout);sys.stdout.buffer.flush();sys.stderr.buffer.write(answer.stderr);sys.stderr.buffer.flush();sys.exit(answer.returncode)
