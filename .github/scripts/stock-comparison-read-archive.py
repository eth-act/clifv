#!/usr/bin/env python3
"""Read one bounded JSON member from an Actions artifact; never extract files."""
import io
import json
import sys
import tarfile
import zipfile

LIMIT = 64 * 1024 * 1024


def read_archive(source, kind):
    if len(source) > LIMIT:
        raise ValueError("oversized artifact")
    with zipfile.ZipFile(io.BytesIO(source)) as archive:
        members = archive.infolist()
        expected = "stock-comparison-artifacts.tar.gz" if kind == "measurement" else "state.json"
        if len(members) != 1 or members[0].filename != expected or members[0].file_size > LIMIT:
            raise ValueError("unexpected artifact contents")
        payload = archive.read(members[0])
    if kind == "measurement":
        with tarfile.open(fileobj=io.BytesIO(payload), mode="r|gz") as archive:
            for member in archive:
                if member.name == "target/ci-comparison/results.json":
                    if not member.isfile() or member.size > LIMIT:
                        raise ValueError("invalid results member")
                    payload = archive.extractfile(member).read(LIMIT + 1)
                    break
            else:
                raise ValueError("missing comparison results")
    if len(payload) > LIMIT:
        raise ValueError("oversized JSON")
    return json.loads(payload)


if __name__ == "__main__":
    kind = sys.argv[1]
    if kind not in ("measurement", "state"):
        raise SystemExit("unknown artifact kind")
    result = read_archive(sys.stdin.buffer.read(LIMIT + 1), kind)
    print(json.dumps(result, separators=(",", ":")))
