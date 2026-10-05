import importlib.util
import io
import json
from pathlib import Path
import tarfile
import unittest
import zipfile

SPEC = importlib.util.spec_from_file_location("archive", Path(__file__).with_name("stock-comparison-read-archive.py"))
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def zipped(name, payload):
    output = io.BytesIO()
    with zipfile.ZipFile(output, "w") as archive:
        archive.writestr(name, payload)
    return output.getvalue()


def tarred(name, payload, kind=tarfile.REGTYPE):
    output = io.BytesIO()
    with tarfile.open(fileobj=output, mode="w:gz") as archive:
        member = tarfile.TarInfo(name)
        member.type = kind
        member.size = len(payload) if kind == tarfile.REGTYPE else 0
        archive.addfile(member, io.BytesIO(payload))
    return output.getvalue()


class ArchiveTests(unittest.TestCase):
    def test_reads_only_results_json_without_extracting(self):
        data = zipped("stock-comparison-artifacts.tar.gz", tarred("target/ci-comparison/results.json", b'{"ok": true}'))
        self.assertEqual(MODULE.read_archive(data, "measurement"), {"ok": True})

    def test_state_snapshot(self):
        self.assertEqual(MODULE.read_archive(zipped("state.json", b'{"schema":1}'), "state"), {"schema": 1})

    def test_unexpected_zip_paths_or_members(self):
        for name in ("../state.json", "/state.json", "other.json"):
            with self.assertRaises(ValueError): MODULE.read_archive(zipped(name, b'{}'), "state")
        output = io.BytesIO()
        with zipfile.ZipFile(output, "w") as archive:
            archive.writestr("state.json", b'{}'); archive.writestr("extra", b'{}')
        with self.assertRaises(ValueError): MODULE.read_archive(output.getvalue(), "state")

    def test_missing_or_symlink_results(self):
        for name, kind in (("../results.json", tarfile.REGTYPE), ("target/ci-comparison/results.json", tarfile.SYMTYPE)):
            data = zipped("stock-comparison-artifacts.tar.gz", tarred(name, b'{}', kind))
            with self.assertRaises(ValueError): MODULE.read_archive(data, "measurement")

    def test_invalid_json_or_oversized_input(self):
        with self.assertRaises(json.JSONDecodeError): MODULE.read_archive(zipped("state.json", b'not JSON'), "state")
        old = MODULE.LIMIT
        try:
            MODULE.LIMIT = 10
            with self.assertRaises(ValueError): MODULE.read_archive(b'x' * 11, "state")
        finally: MODULE.LIMIT = old


if __name__ == "__main__":
    unittest.main()
