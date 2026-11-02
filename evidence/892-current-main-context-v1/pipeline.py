"""Recover current CI inputs only; the parent must separately grant kernel capacity."""
from pathlib import Path
import os, subprocess

OUT=Path(__file__).resolve().parent
subprocess.run(['python3',str(OUT/'recover-ci.py'),'--watch'],check=True)
