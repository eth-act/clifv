"""Helpers shared by the stock comparison scripts (pinned stock revision, exact comparison)."""
import json
from pathlib import Path
import subprocess
import time

from byte_compare import byte_diff

ROOT = Path(__file__).resolve().parent.parent
PIN = "46c23a87dac1465986a8ad53ba6a7ae49372857b"
TARGET = "aarch64-unknown-linux-gnu"


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n")


def comparison(reference, lean, reference_relocs, lean_relocs):
    code = byte_diff(reference, lean)
    # Identity canonicalization only: %foo and foo designate the same symbol.
    def canonical(rows):
        return sorted((r["offset"], r["kind"], r["target"].removeprefix("%"), r["addend"]) for r in rows)
    relocs_equal = canonical(reference_relocs) == canonical(lean_relocs)
    return {"bytes": code, "relocations_equal": relocs_equal,
            "reference_relocations": reference_relocs, "lean_relocations": lean_relocs,
            "exact_code_and_relocations": code["equal"] and relocs_equal}


def command(argv, directory, name, env):
    directory.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    try:
        p = subprocess.run([str(a) for a in argv], capture_output=True, timeout=120, env=env, cwd=ROOT)
        status, stdout, stderr = p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired as e:
        status, stdout, stderr = "timeout", e.stdout or b"", e.stderr or b""
    (directory / (name + ".stdout")).write_bytes(stdout)
    (directory / (name + ".stderr")).write_bytes(stderr)
    result = {"argv": [str(a) for a in argv], "exit": status, "seconds": time.monotonic()-start}
    write(directory / (name + ".command.json"), result)
    return result
