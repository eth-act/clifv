import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).with_name("stock-comparison-breakdown.py")
FRAME, MOV, RET = 0xa9bf7bfd, 0x910003fd, 0xd65f03c0


def code(*words):
    return b"".join(w.to_bytes(4, "little") for w in words)


def fixture(root):
    """One compile-stage variant: a match, a longer framed Lean output, a setting and an operation rejection."""
    files = root / "files/isa/aarch64/t"
    stock = files / "stock/variant-0"; stock.mkdir(parents=True)
    rows, compilations = [], []
    cases = [("%a", "identical_code_artifact", code(RET), code(RET)),
             ("%b", "different_code_artifact", code(FRAME, MOV, RET), code(FRAME, MOV, 0xd10043ff, RET)),
             ("%c", "unsupported_configuration", code(RET), None),
             ("%d", "lean_unsupported", code(RET), None)]
    for index, (name, status, stock_code, lean_code) in enumerate(cases):
        (stock / f"{index}.bin").write_bytes(stock_code)
        (stock / f"{index}.json").write_text(json.dumps({"index": index, "name": name, "relocations": []}))
        lean = files / f"variant-0/compilation-{index}/lean"
        (lean / "dump").mkdir(parents=True)
        if lean_code:
            (lean / "dump" / f"{name[1:]}.bin").write_bytes(lean_code)
        if status == "lean_unsupported":
            (lean.parent / "lean.stderr").write_text(
                f"lean-backend: /x/input.clif: %{name[1:]}: unsupported: unsupported: type i32x4\n")
        row = {"name": name, "status": status}
        if status == "unsupported_configuration":
            row["reason"] = "unsupported setting opt_level=speed; implemented policy is none"
        rows.append(row); compilations.append({"functions": [name]})
    report = {"tests": [{"test": "isa/aarch64/t.clif", "category": "isa", "variants": [
        {"index": 0, "stage": "compile", "functions_compared": rows, "lean_compilations": compilations}]}]}
    (root / "results.json").write_text(json.dumps(report))


class BreakdownTests(unittest.TestCase):
    def test_each_output_lands_in_its_category(self):
        with tempfile.TemporaryDirectory() as temp:
            fixture(Path(temp))
            out = subprocess.run([sys.executable, SCRIPT, temp], check=True, capture_output=True, text=True).stdout
        for expected in ("Stock outputs: 4 ", "1  compile, isa", "1  stock frame, Lean frame, Lean longer",
                         "1  word 2: stock d65f03c0, Lean d10043ff", "1  unsupported setting opt_level=speed\n",
                         "1  unsupported: type iNxN"):
            self.assertIn(expected, out)


if __name__ == "__main__":
    unittest.main()
