#!/usr/bin/env python3
"""Portable timing fallback for lake-serial-build when GNU /usr/bin/time is absent."""
import pathlib
import resource
import subprocess
import sys
import time


def main(argv):
    output, *command = argv
    started = time.monotonic()
    child = subprocess.run(command)
    peak = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    # Linux reports KiB; macOS reports bytes.
    if sys.platform == 'darwin':
        peak //= 1024
    code = child.returncode if child.returncode >= 0 else 128-child.returncode
    pathlib.Path(output).write_text(
        f'Maximum resident set size (kbytes): {peak}\n'
        f'Elapsed seconds: {time.monotonic()-started}\nExit status: {code}\n')
    return code


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
