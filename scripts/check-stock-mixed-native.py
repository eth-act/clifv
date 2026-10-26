#!/usr/bin/env python3
"""Execute StockMixedRuntime's exported Lean objects and compare Cranelift.

First run StockMixedRuntime.lean with STOCK_MIXED_NATIVE_OUT set to a fresh
artifact directory. Run this script through scripts/memcap.sh; native tools run
sequentially and lld uses one thread. CLIF_NATIVE_QEMU and CLIF_NATIVE_LLD follow
the existing clif-native tool convention.
"""
from pathlib import Path
import argparse
import hashlib
import itertools
import json
import os
import re
import shlex
import shutil
import subprocess


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def signed(value, bits):
    value %= 1 << bits
    return value if value < 1 << (bits - 1) else value - (1 << bits)


def run_commands(bits, kind="mixed", vectors=None):
    if kind == "generaldiv":
        cases = run_commands(bits, "returneddiv")
        first = [(name,args,value) for name,args,value in cases
                 if name.startswith("returned_stock_mixed_div_")]
        vectors = list(dict.fromkeys(tuple(args) for _,args,_ in first))
        prefixes = {tuple(args):value for name,args,value in run_commands(bits,"highmul",vectors)
                    if name == "stock_highmul_ni"}
        low, mask = -(1 << (bits-1)), (1 << bits)-1
        for name,args,value in first:
            suffix = name.removeprefix("returned_stock_mixed_div_")
            safe = suffix.endswith("_two")
            op = suffix.removesuffix("_two")
            consumed = value if isinstance(value,str) else signed((value+args[0])*args[1],bits)
            multiple = consumed
            if not isinstance(consumed,str):
                denominator = 2 if safe else args[8]
                if denominator == 0:multiple = "int_divz"
                elif op == "sdiv" and consumed == low and denominator == -1:multiple = "int_ovf"
            unused = value if isinstance(value,str) else prefixes[tuple(args)]
            cases.extend(("general_"+layout+"_"+name,args,result)
                         for layout,result in (("unused",unused),("consumed",consumed),("multiple",multiple)))
        assert len(first) == 88
        return cases
    if kind == "returneddiv":
        cases = run_commands(bits, "mixeddiv")
        later = [("returned_"+name,args,value) for name,args,value in cases
                 if name.startswith("stock_mixed_div_")]
        assert len(later) == 88
        return cases + later
    if kind == "mixeddiv":
        cases = run_commands(bits, "div")
        low, high = -(1 << (bits - 1)), (1 << (bits - 1)) - 1
        # Keep every old case; add live-prefix outcomes, zero divisors, signed
        # boundaries, and the original constant-2 source cases for safe roots.
        vectors = [
            [0,5,2,11,22,33,44,55,7], [1,5,2,11,22,33,44,55,7],
            [-1,-1,1,11,22,33,44,55,1], [0,low,1,11,22,33,44,55,-1],
            [1,high,-1,11,22,33,44,55,1], [2,0,high,11,22,33,44,55,low],
            [1,low,low,11,22,33,44,55,low], [1,1,0,11,22,33,44,55,7],
            [0,0,0,0,0,0,0,0,0], [1,7,-2,11,22,33,44,55,0],
            [1,-7,2,11,22,33,44,55,-2],
        ]
        values = [(args,value) for name,args,value in run_commands(bits,"highmul",vectors)
                  if name == "stock_highmul_ni"]
        assert len(values) == len(vectors)
        mask = (1 << bits) - 1
        for safe in (False,True):
            for op in ("sdiv","udiv","srem","urem"):
                for args,a in values:
                    b = 2 if safe else args[8]
                    if b == 0:
                        result = "int_divz"
                    elif op == "sdiv" and a == low and b == -1:
                        result = "int_ovf"
                    else:
                        x,y = (a & mask,b & mask) if op[0] == "u" else (a,b)
                        q = abs(x) // abs(y)
                        if (x < 0) != (y < 0):q = -q
                        result = signed(q if op.endswith("div") else x-q*y,bits)
                    cases.append(("stock_mixed_div_"+op+("_two" if safe else ""),args,result))
        return cases
    if kind == "div":
        cases = run_commands(bits, "highmul")
        low, high = -(1 << (bits - 1)), (1 << (bits - 1)) - 1
        pairs = [(7,2),(-7,2),(7,-2),(-7,-2),(low,-1),(low,1),
                 (low,low),(high,low),(0,0),(1,0),(low,0),(0,low),(-1,high)]
        mask = (1 << bits) - 1
        for op in ("sdiv", "udiv", "srem", "urem"):
            for a,b in pairs:
                args = [0,a,2,11,22,33,44,55,b]
                if b == 0:
                    value = "int_divz"
                elif op == "sdiv" and a == low and b == -1:
                    value = "int_ovf"
                else:
                    x,y = (a & mask,b & mask) if op[0] == "u" else (a,b)
                    q = abs(x) // abs(y)
                    if (x < 0) != (y < 0):
                        q = -q
                    value = signed(q if op.endswith("div") else x - q*y,bits)
                cases.append(("stock_div_"+op,args,value))
        return cases
    low, high = -(1 << (bits - 1)), (1 << (bits - 1)) - 1
    if vectors is None:
        vectors = [
            [0, 5, 2, 11, 22, 33, 44, 55, 7],
            [1, 5, 2, 11, 22, 33, 44, 55, 7],
            [-1, -1, 1, 11, 22, 33, 44, 55, 1],
            [0, low, 1, 11, 22, 33, 44, 55, -1],
            [1, high, -1, 11, 22, 33, 44, 55, 1],
            [2, 0, high, 11, 22, 33, 44, 55, low],
            [1, low, low, 11, 22, 33, 44, 55, low],
        ]
        if kind in ("bit", "popcount", "minmax", "cmp", "highmul"):
            vectors.append([1, 1, 0, 11, 22, 33, 44, 55, 7])  # observable CTZ(0)
    cases = []
    for args in vectors:
        selected = args[1] + args[8] if args[0] else args[1]
        if kind in ("scalar", "not", "mul", "shift", "cast", "bit", "popcount", "minmax", "cmp", "highmul"):
            mask = (1 << bits) - 1
            constant = 0x123456789abcdef & mask
            band = ((args[1] + constant) & args[8]) & mask
            logical = ((band ^ (args[2] & mask)) | constant) & mask
            chosen = logical if args[0] else band
            previous = signed(chosen - args[2] + 4097, bits)
            if kind in ("not", "mul", "shift", "cast", "bit", "popcount", "minmax", "cmp", "highmul"):
                inverted = (~previous) & mask
                complemented = (~(inverted ^ (args[2] & mask))) & mask
                result = ~((complemented + 4097) & args[8])
                not_result = signed(result, bits)
                if kind in ("mul", "shift", "cast", "bit", "popcount", "minmax", "cmp", "highmul"):
                    product = not_result * args[2]
                    added = product + constant
                    multiplied = added * args[1]
                    subtracted = args[8] - (args[8] + multiplied) * args[2]
                    mul_result = signed(subtracted ^ product, bits)
                    if kind in ("shift", "cast", "bit", "popcount", "minmax", "cmp", "highmul"):
                        unsigned = (((mul_result & mask) << (0x105 % bits)) & mask) >> (0x103 % bits)
                        shifted_signed = signed(((mul_result & mask) << 2) & mask, bits) >> 9
                        lsl = (shifted_signed << ((args[2] & mask) % bits)) & mask
                        lsr = lsl >> ((args[1] & mask) % bits)
                        asr = signed(lsr, bits) >> ((args[0] & mask) % bits)
                        combined = (~((asr << 2) & mask) ^ unsigned) & mask
                        immediate = (((combined << (0x105 % bits)) & mask) ^ (args[3] & mask))
                        shift_result = signed(immediate >> (0x103 % bits), bits) >> 9
                        if kind in ("cast", "bit", "popcount", "minmax", "cmp", "highmul"):
                            cast_result = signed(shift_result ^ (0xffffffff if (args[1] & 0x80000000) else 0), bits)
                            if kind in ("bit", "popcount", "minmax", "cmp", "highmul"):
                                negated = (-args[1]) & mask
                                reversed_bits = int(f"{negated:0{bits}b}"[::-1], 2)
                                swapped = int.from_bytes(reversed_bits.to_bytes(bits // 8, "little"), "big")
                                def rol(value, amount):
                                    amount %= bits
                                    return ((value << amount) | (value >> ((bits - amount) % bits))) & mask
                                def ror(value, amount):
                                    return rol(value, -amount)
                                rotated = ror(rol(swapped, args[2] & mask), args[1] & mask)
                                immediate = ror(rol(rotated, 0x105), 0x103)
                                leading = bits - (args[1] & mask).bit_length()
                                x = args[2] & mask
                                trailing = bits if x == 0 else (x & -x).bit_length() - 1
                                bit_result = signed(immediate ^ leading ^ trailing ^ cast_result, bits)
                                if kind in ("popcount", "minmax", "cmp", "highmul"):
                                    count_result = signed(bit_result ^ (args[1] & mask).bit_count() ^ (args[2] & mask).bit_count(), bits)
                                    if kind in ("minmax", "cmp", "highmul"):
                                        small, negative, large = 7, (-7) & mask, 0x123456789abcdef & mask
                                        smin = lambda a, b: min(signed(a,bits), signed(b,bits)) & mask
                                        smax = lambda a, b: max(signed(a,bits), signed(b,bits)) & mask
                                        umin = lambda a, b: min(a & mask,b & mask)
                                        umax = lambda a, b: max(a & mask,b & mask)
                                        a,b,c,d = smin(args[1],args[2]),smax(args[1],args[8]),umin(args[2],args[3]),umax(args[0],args[8])
                                        e,f,g,h = smin(args[1],small),smax(args[2],negative),umin(args[8],small),umax(args[0],negative)
                                        i,j,k,l = smin(large,args[1]),smax(large,args[2]),umin(large,args[8]),umax(large,args[0])
                                        combined = (a+b) & mask
                                        for index,value in enumerate([c,d,e,f,g,h,i,j,k,l]):
                                            combined = ((combined+value) & mask) if index % 2 else (combined ^ value)
                                        minmax_result = signed((count_result & mask) ^ combined,bits)
                                        if kind in ("cmp", "highmul"):
                                            specs = [(cc,1,2) for cc in ("eq","ne","slt","sle","sgt","sge","ult","ule","ugt","uge")]
                                            specs += [("eq",1,301),("ne",2,301),("eq",301,1),("ne",301,2),
                                                      ("slt",1,205),("ule",2,302),("sge",1,303),("ugt",2,302),
                                                      ("slt",304,1),("ult",304,2)]
                                            def read(key):
                                                constants = {301:0,302:4097,303:-4097,304:0x123456789abcdef,205:7}
                                                return constants[key] if key in constants else args[key]
                                            cmp_result = minmax_result & mask
                                            for k,(cc,x,y) in enumerate(specs):
                                                a,b = read(x) & mask,read(y) & mask
                                                if cc.startswith("s"):
                                                    a,b = signed(a,bits),signed(b,bits)
                                                relation = cc[1:] if cc[0] in "su" else cc
                                                truth = {"eq":a==b,"ne":a!=b,"lt":a<b,"le":a<=b,"gt":a>b,"ge":a>=b}[relation]
                                                cmp_result ^= int(truth) << k
                                            if kind == "highmul":
                                                def highproduct(a,b,signed_inputs):
                                                    a,b = a & mask,b & mask
                                                    if signed_inputs:
                                                        a,b = signed(a,bits),signed(b,bits)
                                                    return ((a*b) >> bits) & mask
                                                constant = 0x123456789abcdef & mask
                                                result = cmp_result ^ highproduct(args[1],args[2],True) ^ highproduct(args[1],args[2],False)
                                                result ^= highproduct(args[2],constant,True) ^ highproduct(args[1],constant,False)
                                                cases.append(("stock_highmul_ni",args,signed(result,bits)))
                                                cases.append(("retained_cmp",args,signed(cmp_result,bits)))
                                            else:
                                                cases.append(("stock_cmp_ni",args,signed(cmp_result,bits)))
                                            cases.append(("retained_minmax",args,minmax_result))
                                        else:
                                            cases.append(("stock_minmax_ni",args,minmax_result))
                                        cases.append(("retained_popcount",args,count_result))
                                    else:
                                        cases.append(("stock_popcount_ni", args, count_result))
                                    cases.append(("retained_bit", args, bit_result))
                                else:
                                    cases.append(("stock_bit_ni", args, bit_result))
                                cases.append(("retained_cast", args, cast_result))
                            else:
                                cases.append(("stock_cast_ni", args, cast_result))
                            cases.append(("retained_shift", args, shift_result))
                        else:
                            cases.append(("stock_shift_ni", args, shift_result))
                        cases.append(("retained_mul", args, mul_result))
                    else:
                        cases.append(("stock_mul_ni", args, mul_result))
                    cases.append(("retained_not", args, not_result))
                else:
                    cases.append(("stock_not_ni", args, not_result))
                cases.append(("retained_constant", args, previous))
            else:
                cases.append(("stock_scalar_ni", args, previous))
            prior_band = (args[1] & args[8]) & mask
            prior_logical = ((prior_band ^ (args[2] & mask)) | (args[1] & mask)) & mask
            cases.append(("retained_logical", args, signed((prior_logical if args[0] else prior_band) - args[2], bits)))
            cases.append(("retained_mixed", args, signed(selected - args[2], bits)))
        elif kind == "logical":
            mask = (1 << bits) - 1
            band = (args[1] & args[8]) & mask
            logical = ((band ^ (args[2] & mask)) | (args[1] & mask)) & mask
            chosen = logical if args[0] else band
            cases.append(("stock_logical_ni", args, signed(chosen - args[2], bits)))
            cases.append(("retained_mixed", args, signed(selected - args[2], bits)))
        else:
            cases.append(("stock_mixed_ni", args, signed(selected - args[2], bits)))
        cases.append(("retained_arithmetic", args, signed(args[0] + args[8] - args[1], bits)))
    for a, b in [(0, 0), (-1, 1), (high, 1), (low, low)]:
        cases.append(("retained_scalar", [a, b], signed(a + b, bits)))
    for value in [0, -1, (1 << 63) - 1]:
        cases.append(("retained_prologue", [value], value))
    for value in [0, -1, (1 << 31) - 1, -(1 << 31)]:
        cases.append(("retained_d0", [value], value))
    if kind in ("scalar", "not", "mul", "shift", "cast", "bit", "popcount", "minmax", "cmp", "highmul"):
        for a, b in [(0, 7), (-1, 9), ((1 << 63) - 1, 3)]:
            cases.append(("retained_legacy", [a, b], signed(a * b, 64)))
    else:
        cases.append(("retained_legacy", [], 7))
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("artifacts", type=Path)
    parser.add_argument("--native-bin", type=Path, default=Path("rust/target/release/clif-native"))
    parser.add_argument("--class", dest="kind", choices=["mixed", "logical", "scalar", "not", "mul", "shift", "cast", "bit", "popcount", "minmax", "cmp", "highmul", "div", "mixeddiv", "returneddiv", "generaldiv", "narrow", "mask", "cfg", "cfgentry", "cfgscalarentry"], default="mixed")
    options = parser.parse_args()
    root = options.artifacts.resolve()
    native = options.native_bin.resolve()
    assert native.is_file(), native
    env = dict(os.environ)
    lld = env.get("CLIF_NATIVE_LLD") or shutil.which("rust-lld")
    assert lld, "Set CLIF_NATIVE_LLD to the installed rust-lld executable"
    wrapper = root / "lld-one-thread.sh"
    wrapper.write_text("#!/bin/sh\nexec " + shlex.quote(lld) + ' "$@" --threads=1\n')
    wrapper.chmod(0o700)
    env.update(CLIF_NATIVE_LLD=str(wrapper), RAYON_NUM_THREADS="1", OMP_NUM_THREADS="1")
    pattern = re.compile(r"^(lean|regalloc2)-Backend\.Stock\.D0\.Configuration\.((?:default|systemV|fast)I(32|64))-(plain|cleanup)$")
    expected_grid = set(itertools.product(
        ["lean", "regalloc2"],
        [a + b for a in ["default", "systemV", "fast"] for b in ["I32", "I64"]],
        ["plain", "cleanup"],
    ))
    if options.kind in ("narrow", "mask"):
        expected_grid = {key for key in expected_grid if key[1].endswith("I32")}
    seen, records = set(), []
    reference_cache = {}
    reference_executions = 0
    for obj in sorted(root.glob("*.o")):
        match = pattern.fullmatch(obj.stem)
        assert match, obj.name
        allocator, config, width, cleanup = match.groups()
        key = allocator, config, cleanup
        assert key not in seen, key
        seen.add(key)
        table, original = obj.with_suffix(".json"), obj.with_suffix(".clif")
        names = {f["name"] for f in json.loads(table.read_text())["functions"]}
        wanted = {"stock_mixed_ni", "retained_arithmetic", "retained_scalar",
                  "retained_prologue", "retained_d0", "retained_legacy"}
        if options.kind in ("highmul", "div", "mixeddiv", "returneddiv", "generaldiv"):
            wanted = (wanted - {"stock_mixed_ni"}) | {"stock_highmul_ni", "retained_cmp", "retained_minmax", "retained_popcount", "retained_bit", "retained_cast", "retained_shift", "retained_mul", "retained_not", "retained_constant", "retained_logical", "retained_mixed"}
        elif options.kind == "cmp":
            wanted = (wanted - {"stock_mixed_ni"}) | {"stock_cmp_ni", "retained_minmax", "retained_popcount", "retained_bit", "retained_cast", "retained_shift", "retained_mul", "retained_not", "retained_constant", "retained_logical", "retained_mixed"}
        elif options.kind == "minmax":
            wanted = (wanted - {"stock_mixed_ni"}) | {"stock_minmax_ni", "retained_popcount", "retained_bit", "retained_cast", "retained_shift", "retained_mul", "retained_not", "retained_constant", "retained_logical", "retained_mixed"}
        elif options.kind == "popcount":
            wanted = (wanted - {"stock_mixed_ni"}) | {"stock_popcount_ni", "retained_bit", "retained_cast", "retained_shift", "retained_mul", "retained_not", "retained_constant", "retained_logical", "retained_mixed"}
        elif options.kind == "bit":
            wanted = (wanted - {"stock_mixed_ni"}) | {"stock_bit_ni", "retained_cast", "retained_shift", "retained_mul", "retained_not", "retained_constant", "retained_logical", "retained_mixed"}
        elif options.kind == "cast":
            wanted = (wanted - {"stock_mixed_ni"}) | {"stock_cast_ni", "retained_shift", "retained_mul", "retained_not", "retained_constant", "retained_logical", "retained_mixed"}
        elif options.kind == "shift":
            wanted = (wanted - {"stock_mixed_ni"}) | {"stock_shift_ni", "retained_mul", "retained_not", "retained_constant", "retained_logical", "retained_mixed"}
        elif options.kind == "mul":
            wanted = (wanted - {"stock_mixed_ni"}) | {"stock_mul_ni", "retained_not", "retained_constant", "retained_logical", "retained_mixed"}
        elif options.kind == "not":
            wanted = (wanted - {"stock_mixed_ni"}) | {"stock_not_ni", "retained_constant", "retained_logical", "retained_mixed"}
        elif options.kind == "scalar":
            wanted = (wanted - {"stock_mixed_ni"}) | {"stock_scalar_ni", "retained_logical", "retained_mixed"}
        elif options.kind == "logical":
            wanted = (wanted - {"stock_mixed_ni"}) | {"stock_logical_ni", "retained_mixed"}
        if options.kind in ("div", "mixeddiv", "returneddiv", "generaldiv"):
            wanted |= {"stock_div_"+op for op in ("sdiv", "udiv", "srem", "urem")}
        if options.kind in ("mixeddiv", "returneddiv", "generaldiv"):
            wanted |= {"stock_mixed_div_"+op+suffix for op in ("sdiv","udiv","srem","urem") for suffix in ("","_two")}
        if options.kind in ("returneddiv","generaldiv"):
            wanted |= {"returned_stock_mixed_div_"+op+suffix for op in ("sdiv","udiv","srem","urem") for suffix in ("","_two")}
        if options.kind == "generaldiv":
            wanted |= {"general_"+layout+"_returned_stock_mixed_div_"+op+suffix
                       for layout in ("unused","consumed","multiple")
                       for op in ("sdiv","udiv","srem","urem") for suffix in ("","_two")}
        if options.kind in ("narrow", "mask", "cfg", "cfgentry", "cfgscalarentry"):
            count = 79 if options.kind == "narrow" else 36 if options.kind == "mask" else 96 if options.kind == "cfgscalarentry" else 16 if options.kind == "cfgentry" else 12
            wanted = {f"stock_{options.kind}_{i}" for i in range(count)}
            case_path = obj.with_suffix(".cases.json")
            cases = json.loads(case_path.read_text())
            assert len(cases) == count*(10 if options.kind in ("cfg", "cfgentry", "cfgscalarentry") else 9), (case_path, len(cases))
            for name, args, value in cases:
                assert name in wanted and len(args) == 9, (name, args)
                assert all(type(arg) is int for arg in args), args
                assert type(value) is int or value in ("int_divz", "int_ovf"), value
            assert {name for name, _, _ in cases} == wanted
        else:
            cases = run_commands(int(width), options.kind)
        assert names == wanted, names
        attached = set()
        ordered_cases = []
        def add_commands(match):
            name = match.group(1)
            attached.add(name)
            ordered_cases.extend(case for case in cases if case[0] == name)
            commands = "\n".join(
                f"; run: %{name}({', '.join(map(str, args))}) == {value if isinstance(value,int) else 0}"
                for function, args, value in cases if function == name
            )
            return match.group(0) + "\n" + commands + "\n"
        source = root / (obj.stem + "-runs.clif")
        text = re.sub(r"(?ms)^function %([A-Za-z_][A-Za-z_0-9]*)\b[^\n]*\{.*?^\}",
                      add_commands, original.read_text())
        assert attached == names, (attached, names)
        source.write_text(text)
        streams = {}
        reference_reused = False
        for engine, extra in [
            ("lean", ["--functions-obj", str(obj), "--functions-table", str(table)]),
            ("cranelift", []),
        ]:
            log = root / (obj.stem + "-" + engine + ".jsonl")
            error = root / (obj.stem + "-" + engine + ".stderr")
            reference_key = sha(source)
            if engine == "cranelift" and reference_key in reference_cache:
                log.write_bytes(reference_cache[reference_key].read_bytes())
                error.write_text("Reused identical source/reference input from this run.\n")
                reference_reused = True
            else:
                with log.open("w") as out, error.open("w") as err:
                    result = subprocess.run([str(native), str(source), *extra], env=env,
                                            stdout=out, stderr=err)
                assert result.returncode == 0, (engine, source, error.read_text()[-3000:])
                if engine == "cranelift":
                    reference_cache[reference_key] = log
                    reference_executions += len(cases)
            rows = [json.loads(line) for line in log.read_text().splitlines() if line.strip()]
            assert len(rows) == len(cases), (engine, source, len(rows), len(cases))
            for row, (_, _, value) in zip(rows,ordered_cases):
                assert "file_error" not in row and row.get("expected"), row
                assert row["expected"]["cmp"] == "==", row
                if isinstance(value,str):
                    assert row["actual"] == {"trapped":value}, row
                else:
                    assert row["actual"].get("returned") == row["expected"]["values"], row
            streams[engine] = rows
        assert [r["actual"] for r in streams["lean"]] == [r["actual"] for r in streams["cranelift"]]
        records.append({**({"source_outcome_cases_sha256": sha(case_path)} if options.kind in ("narrow", "mask", "cfg", "cfgentry", "cfgscalarentry") else {}), "allocator": allocator, "configuration": config, "cleanup": cleanup,
                        "runs": len(cases), "cranelift_reference_reused": reference_reused, "object_sha256": sha(obj),
                        "table_sha256": sha(table), "original_source_sha256": sha(original),
                        "executed_source_sha256": sha(source),
                        "lean_records_sha256": sha(root / (obj.stem + "-lean.jsonl")),
                        "cranelift_records_sha256": sha(root / (obj.stem + "-cranelift.jsonl"))})
        print(f"{allocator} {config} {cleanup}: {len(cases)} Lean byte executions agree with Cranelift", flush=True)
    assert seen == expected_grid, ("missing", sorted(expected_grid - seen), "extra", sorted(seen - expected_grid))
    result = {"state": "passed", "actual_lean_encoded_objects": len(records),
              "lean_byte_executions": sum(r["runs"] for r in records),
              "cranelift_reference_executions": reference_executions,
              "reference_cases_compared": sum(r["runs"] for r in records),
              "failures": 0, "disagreements": 0, "native_binary_sha256": sha(native),
              "records": records,
              "limits": "Fixed native integration grid; normal proof and full current activation gates remain required."}
    (root / "native-receipt.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "records"}), flush=True)


if __name__ == "__main__":
    main()
