import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location("lake_unstage", Path(__file__).with_name("lake-unstage.py"))
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ChooseTest(unittest.TestCase):
    def test_keeps_the_copy_with_the_most_importer_work(self):
        with tempfile.TemporaryDirectory() as tmp:
            root, top = Path(tmp) / "ws", Path(tmp) / "stages"
            (root / "L").mkdir(parents=True)
            (root / "scripts").mkdir()
            (root / "lakefile.toml").write_text('name = "w"\n[[lean_lib]]\nname = "L"\n')
            sources = {"Base": "", "Shared": "import L.Base", "Cheap": "import L.Shared",
                       "Dear": "import L.Shared", "Other": "import L.Base"}
            for m, src in sources.items():
                (root / "L" / f"{m}.lean").write_text(src + "\n")
            # Other (not an importer of Shared) must not count for shard 0
            (root / "scripts/lake-module-peaks.tsv").write_text(
                "L.Cheap\t1000\t10\nL.Dear\t1000\t500\nL.Other\t1000\t9000\n")
            # shards 0 and 1 built Shared (same input hash "h") with differing outputs; each
            # built its own importer against its copy
            for shard, entries in enumerate([{"h": "Shared", "c": "Cheap", "o": "Other"},
                                             {"h": "Shared", "d": "Dear"}]):
                s = top / f"stage-w1-{shard}"
                s.mkdir(parents=True)
                lines = ['"2026-03-17"']
                for h, m in entries.items():
                    art = f"{m}-{shard}.ltar"
                    (s / art).write_bytes(b"LTR4\0" + m.encode() + b".trace\0rest")
                    lines.append(json.dumps([h, art]))
                (s / "outputs.jsonl").write_text("\n".join(lines) + "\n")

            kept = MODULE.choose(MODULE.read_stages(top), root)

        self.assertEqual([(h, o) for h, o, _, _ in kept], [("h", "Shared-1.ltar")])


if __name__ == "__main__":
    unittest.main()
