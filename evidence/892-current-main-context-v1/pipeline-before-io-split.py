"""One owned3GiB job: recover coherent CI inputs, then run only focused gates."""
from pathlib import Path
import os, subprocess

OUT=Path(__file__).resolve().parent
assert os.environ.get('WORKER_O_PROOF_SLOT_GRANTED')=='892-current-main'
subprocess.run(['python3',str(OUT/'recover-ci.py'),'--watch'],check=True)
subprocess.run(['python3',str(OUT/'run-focused.py'),'--attempt','current-kernel-matrix-v1'],check=True)
