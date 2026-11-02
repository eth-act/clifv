from pathlib import Path
import subprocess
T=Path('/home/lee/clifv/.git/agent-evidence/stock-memory-20261029/return-pin-typed-proof-packet-v1')
for name in ['verify-v4.py','verify-actual-bundles-v1.py']:
 subprocess.run(['python3',str(T/name)],check=True)
