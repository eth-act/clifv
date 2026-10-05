#!/usr/bin/env python3
"""Exact ELF comparisons. No dependencies, stripping, or instruction normalization.

Symbol maps only identify corresponding functions/relocation targets; they never
alter bytes. Only ELF64 little-endian files are supported (the project's targets).
"""

import argparse
from bisect import bisect_left
import hashlib
import json
from pathlib import Path
import re
import shutil
import struct
import subprocess


def digest(data):
    return hashlib.sha256(data).hexdigest()


def byte_diff(a, b):
    same = a == b
    first = None if same else next((i for i, (x, y) in enumerate(zip(a, b)) if x != y), None)
    if first is None and len(a) != len(b):
        first = min(len(a), len(b))
    return {"equal": same, "left_size": len(a), "right_size": len(b),
            "left_sha256": digest(a), "right_sha256": digest(b),
            "first_difference": first,
            "left_context": None if first is None else a[max(0, first - 8):first + 24].hex(),
            "right_context": None if first is None else b[max(0, first - 8):first + 24].hex()}


class ElfError(ValueError):
    pass


class ELF:
    def __init__(self, path):
        self.path = str(path)
        self.data = Path(path).read_bytes()
        if self.data[:6] != b"\x7fELF\x02\x01":
            raise ElfError("expected little-endian ELF64")
        h = self.unpack("16sHHIQQQIHHHHHH", 0)
        self.kind, self.machine = h[1:3]
        self.header = h
        off, entsize, count, strings = h[6], h[11], h[12], h[13]
        if not off or entsize != 64:
            raise ElfError("missing/unsupported section table")
        zero = self.unpack("IIQQQQIIQQ", off)
        count = count or zero[5]
        strings = zero[6] if strings == 0xffff else strings
        if count > len(self.data) // 64 or strings >= count:
            raise ElfError("invalid section count/string table")
        self.sections = []
        for i in range(count):
            s = self.unpack("IIQQQQIIQQ", off + i * entsize)
            sec = dict(zip(("name_offset", "type", "flags", "address", "offset",
                            "size", "link", "info", "alignment", "entry_size"), s))
            sec["index"] = i
            sec["bytes"] = b"" if sec["type"] == 8 else self.slice(sec["offset"], sec["size"])
            self.sections.append(sec)
        string_data = self.sections[strings]["bytes"]
        for sec in self.sections:
            sec["name"] = self.string(string_data, sec["name_offset"])
        self.tables = {}
        self.functions = {}
        for sec in self.sections:
            if sec["type"] not in (2, 11):
                continue
            if sec["entry_size"] != 24 or sec["size"] % 24:
                raise ElfError("invalid symbol table")
            strings = self.section(sec["link"])["bytes"]
            symbols = []
            for off in range(0, sec["size"], 24):
                name, info, other, index, value, size = struct.unpack_from("<IBBHQQ", sec["bytes"], off)
                if index == 0xffff:
                    raise ElfError("extended symbol section indices are unsupported")
                symbol = {"name": self.string(strings, name), "type": info & 15,
                          "binding": info >> 4, "visibility": other & 3,
                          "section": index, "value": value, "size": size}
                symbols.append(symbol)
                if symbol["type"] == 2 and 0 < index < count and symbol["name"]:
                    # fv markers identify origins, not additional compiled functions.
                    if not symbol["name"].startswith("__fvlean$"):
                        bucket = self.functions.setdefault(symbol["name"], [])
                        if symbol not in bucket:
                            bucket.append(symbol)
            self.tables[sec["index"]] = symbols
        self.relocations = []
        for sec in self.sections:
            if sec["type"] not in (4, 9):
                continue
            size = 24 if sec["type"] == 4 else 16
            if sec["entry_size"] != size or sec["size"] % size:
                raise ElfError("invalid relocation table")
            table = self.tables.get(sec["link"])
            if table is None:
                raise ElfError("relocation has no symbol table")
            for off in range(0, sec["size"], size):
                address, info = struct.unpack_from("<QQ", sec["bytes"], off)
                target_index = info >> 32
                if target_index >= len(table):
                    raise ElfError("invalid relocation symbol index")
                target = table[target_index]
                target_name = target["name"]
                if target["type"] == 3 and not target_name:
                    target_name = "section:" + self.section(target["section"])["name"]
                self.relocations.append({"offset": address, "type": info & 0xffffffff,
                                         "target": target_name, "target_value": target["value"],
                                         "addend": struct.unpack_from("<q", sec["bytes"], off + 16)[0]
                                         if size == 24 else None,
                                         "section": sec["info"]})
        # Large Cargo CGUs have thousands of functions/relocations. Index once
        # rather than rescanning the entire relocation table for every function.
        grouped = {}
        for relocation in self.relocations:
            key = relocation["section"] if self.kind == 1 else None
            grouped.setdefault(key, []).append(relocation)
        self.relocation_index = {}
        for key, entries in grouped.items():
            entries.sort(key=lambda entry: entry["offset"])
            self.relocation_index[key] = ([entry["offset"] for entry in entries], entries)

    def unpack(self, fmt, offset):
        size = struct.calcsize("<" + fmt)
        return struct.unpack("<" + fmt, self.slice(offset, size))

    def slice(self, offset, size):
        if offset < 0 or size < 0 or offset + size > len(self.data):
            raise ElfError("ELF field points outside file")
        return self.data[offset:offset + size]

    def section(self, index):
        if not 0 <= index < len(self.sections):
            raise ElfError("invalid section index")
        return self.sections[index]

    @staticmethod
    def string(data, offset):
        if not 0 <= offset < len(data):
            if not data and offset == 0:
                return ""
            raise ElfError("invalid string offset")
        end = data.find(b"\0", offset)
        if end == -1:
            raise ElfError("unterminated ELF string")
        return data[offset:end].decode("utf-8", errors="surrogateescape")

    def function(self, name):
        syms = self.functions.get(name, [])
        if len(syms) != 1:
            raise ElfError("missing function" if not syms else "ambiguous function symbol")
        sym = syms[0]
        if not sym["size"]:
            raise ElfError("function size is zero; extent cannot be established")
        sec = self.section(sym["section"])
        start = sym["value"] - (sec["address"] if self.kind != 1 else 0)
        if start < 0 or start + sym["size"] > len(sec["bytes"]):
            raise ElfError("function extends outside section")
        return sym, sec["bytes"][start:start + sym["size"]]

    def function_relocations(self, sym, names):
        result = []
        offsets, entries = self.relocation_index.get(sym["section"] if self.kind == 1 else None, ([], []))
        lo = bisect_left(offsets, sym["value"])
        hi = bisect_left(offsets, sym["value"] + sym["size"])
        for r in entries[lo:hi]:
            result.append({"offset": r["offset"] - sym["value"], "type": r["type"],
                           "target": names.get(r["target"], r["target"]), "addend": r["addend"]})
        return sorted(result, key=lambda r: (r["offset"], r["type"], r["target"], r["addend"] or 0))


def category(sec):
    name = sec["name"]
    if sec["type"] in (4, 9):
        return "relocations"
    if name.startswith((".debug", ".zdebug")):
        return "debugging"
    if name in (".eh_frame", ".eh_frame_hdr", ".gcc_except_table"):
        return "unwind"
    if sec["type"] in (2, 3, 11):
        return "symbols_and_strings"
    if sec["flags"] & 4:
        return "code"
    if sec["flags"] & 2:
        return "data"
    return "metadata"


def section_differences(a, b):
    def indexed(elf):
        result, counts = {}, {}
        for sec in elf.sections[1:]:
            n = sec["name"]
            counts[n] = counts.get(n, 0) + 1
            result[(n, counts[n])] = sec
        return result
    aa, bb = indexed(a), indexed(b)
    changes = []
    for key in sorted(set(aa) | set(bb)):
        left, right = aa.get(key), bb.get(key)
        row = {"section": key[0], "occurrence": key[1], "category": category(left or right)}
        if left is None or right is None:
            row["status"] = "missing_left" if left is None else "missing_right"
        else:
            row["bytes"] = byte_diff(left["bytes"], right["bytes"])
            fields = ("type", "flags", "address", "offset", "size", "alignment", "entry_size")
            row["layout"] = {k: [left[k], right[k]] for k in fields if left[k] != right[k]}
            if row["bytes"]["equal"] and not row["layout"]:
                continue
            row["status"] = "different"
        changes.append(row)
    if a.header != b.header:
        changes.append({"category": "metadata", "section": "ELF header", "status": "different"})
    def outside_sections(elf):
        ranges = sorted((s["offset"], s["offset"] + s["size"]) for s in elf.sections
                        if s["type"] != 8 and s["size"])
        end, chunks = 0, []
        for start, stop in ranges:
            if start > end:
                chunks.append(elf.data[end:start])
            end = max(end, stop)
        chunks.append(elf.data[end:])
        return b"".join(chunks)
    outside = byte_diff(outside_sections(a), outside_sections(b))
    if not outside["equal"]:
        changes.append({"category": "padding_and_layout", "section": "outside section payloads",
                        "status": "different", "bytes": outside})
    # Bytes not belonging to sections include headers, segment tables, padding,
    # and trailers. A whole-file mismatch is always authoritative regardless of
    # whether section-level diagnostics explain it.
    return changes


def disassemble(path, symbol, first, tool=None, env=None):
    tool = tool or shutil.which("llvm-objdump") or shutil.which("objdump")
    if not tool:
        return {"available": False, "reason": "no disassembler"}
    argv = [tool, "-d", "--disassemble-symbols=" + symbol, str(path)] if "llvm" in Path(tool).name else [tool, "-d", "--disassemble=" + symbol, str(path)]
    p = subprocess.run(argv, capture_output=True, text=True, errors="replace", timeout=30, env=env)
    if p.returncode:
        return {"available": False, "reason": p.stderr[-1000:]}
    lines = p.stdout.splitlines()
    # Keep diagnostics bounded for large functions; retain the area of the first
    # differing byte rather than only the prologue.
    try:
        sym, _ = ELF(path).function(symbol)
        address = sym["value"] + (first or 0)
        preceding = [(int(m[1], 16), i) for i, line in enumerate(lines)
                     if (m := re.match(r"\s*([0-9a-fA-F]+):", line)) and int(m[1], 16) <= address]
        hit = max(preceding)[1] if preceding else 0
    except ValueError:
        hit = 0
    return {"available": True, "command": argv, "context": "\n".join(lines[max(0, hit - 8):hit + 20])}


def compare_files(left, right, names=None, selected=None, diagnostics=False, tool=None, env=None):
    names = names or {}
    a, b = ELF(left), ELF(right)
    if a.kind != b.kind or a.machine != b.machine:
        raise ElfError("ELF types or machine architectures differ")
    result = {"left": str(left), "right": str(right), "elf_type": a.kind,
              "machine": a.machine, "whole_file": byte_diff(a.data, b.data),
              "sections": section_differences(a, b), "functions": []}
    requested = sorted(selected) if selected is not None else sorted(a.functions)
    mapped = set()
    diagnostic_remaining = 1  # first differing function per artifact; keep large suites tractable
    for name in requested:
        other = names.get(name, name)
        row = {"left_name": name, "right_name": other}
        mapped.add(other)
        try:
            sa, ca = a.function(name)
            sb, cb = b.function(other)
            row["bytes"] = byte_diff(ca, cb)
            ra = a.function_relocations(sa, names)
            rb = b.function_relocations(sb, {})
            row["relocations"] = {"equal": ra == rb, "left": ra, "right": rb}
            row["symbol_metadata"] = {k: [sa[k], sb[k]] for k in ("binding", "visibility", "value", "size") if sa[k] != sb[k]}
            row["status"] = "identical" if ca == cb and ra == rb else "different"
            if diagnostics and diagnostic_remaining and ca != cb:
                diagnostic_remaining -= 1
                row["disassembly"] = {"left": disassemble(left, name, row["bytes"]["first_difference"], tool, env),
                                      "right": disassemble(right, other, row["bytes"]["first_difference"], tool, env)}
        except ElfError as e:
            row.update(status="unpaired", reason=str(e))
        result["functions"].append(row)
    if selected is None:
        for other in sorted(set(b.functions) - mapped):
            result["functions"].append({"left_name": None, "right_name": other,
                                        "status": "unpaired", "reason": "missing function on left"})
    result["function_counts"] = {s: sum(f["status"] == s for f in result["functions"])
                                 for s in ("identical", "different", "unpaired")}
    for field, key in (("bytes", "function_byte_counts"), ("relocations", "relocation_counts")):
        result[key] = {"equal": sum(f.get(field, {}).get("equal") is True for f in result["functions"]),
                       "different": sum(f.get(field, {}).get("equal") is False for f in result["functions"]),
                       "unpaired": result["function_counts"]["unpaired"]}
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("left", type=Path)
    p.add_argument("right", type=Path)
    p.add_argument("--names", type=Path, help="JSON map of left symbols to right symbols")
    p.add_argument("--functions", nargs="+", help="explicit function names; default: union of both files")
    p.add_argument("--out", type=Path)
    p.add_argument("--disassembly", action="store_true")
    args = p.parse_args()
    try:
        names = json.loads(args.names.read_text()) if args.names else {}
        report = compare_files(args.left, args.right, names, args.functions, args.disassembly)
        code = 0 if report["whole_file"]["equal"] and not report["function_counts"]["unpaired"] else 1
    except (OSError, ValueError, struct.error) as e:
        report, code = {"error": str(e)}, 2
    text = json.dumps(report, indent=2, ensure_ascii=True) + "\n"
    if args.out:
        args.out.write_text(text)
    else:
        print(text, end="")
    return code


if __name__ == "__main__":
    raise SystemExit(main())
