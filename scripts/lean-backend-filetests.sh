#!/usr/bin/env bash
# Differential tests of the Lean AArch64 backend (FV/Backend, docs/contracts/backend.md).
#
# For each .clif file: `lake exe lean-backend` (ISLE isel + stack-slot allocation + Lean
# encoder + Lean ELF writer) -> object, with no assembler (with --asm: assembly text ->
# llvm-mc -> object, the pre-M5 path); `clif-native --functions-obj` links that object with
# the harness and Cranelift-compiled trampolines and runs every `; run:` line under
# qemu-aarch64-static.
# The same file is also run through plain `clif-native` (Cranelift's own aarch64 code), and
# the two record streams are compared (`clif-results compare`).
#
# usage: scripts/lean-backend-filetests.sh [-v] [--asm] [--regalloc regalloc2|spill|stack]
#                                          [--corpus | --runtests | FILE.clif...]
#   default: --corpus and --runtests
#   --corpus:   corpus/clif/*.clif, and corpus/clif/extrt/*.clif linked with the Rust
#               flat-runtime (as scripts/diff-corpus.sh does)
#   --runtests: every file in Cranelift's runtests/ directory; functions outside
#               clif-subset-v1 E (or i128, floats, vectors) are reported as unsupported
#   -v: per-file lines for every file, and every non-passing run
#   --asm: assemble the Lean backend's assembly with llvm-mc instead of using its object
#   --regalloc: register allocator of the Lean backend (default regalloc2, validated by the
#               Lean checker, with the spill allocator as fallback; `spill` = the fallback for
#               every function; `stack` = the stack-slot baseline), docs/contracts/regalloc.md
#   --opt [--opt-* ...]: run the Lean mid-end (Opt.optimize) before the Lean backend
#               (lean-backend --opt, docs/contracts/midend.md); Cranelift-native is unchanged
#
# Output per set: one line per file that is not fully passing (or every file with -v):
#   FILE: lean pass P fail F error E unsupported U | native pass ... | agree A disagree D
# then totals. Exit status 0 iff no Lean run fails or errors, no file errors, and every run
# the Lean backend compiled agrees with Cranelift-native.
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
RUNTESTS=third_party/wasmtime/cranelift/filetests/filetests/runtests
LLVM_MC=${LLVM_MC:-/usr/lib/llvm-18/bin/llvm-mc}

VERBOSE=0
ASM=0
RA=regalloc2
OPTARGS=()
SETS=()
FILES=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    -v) VERBOSE=1 ;;
    --asm) ASM=1 ;;
    --regalloc) RA=$2; shift ;;
    --opt-rules|--opt-rounds) OPTARGS+=("$1" "$2"); shift ;;
    --opt|--opt-*) OPTARGS+=("$1") ;;
    --corpus) SETS+=(corpus) ;;
    --runtests) SETS+=(runtests) ;;
    -*) echo "unknown option $1" >&2; exit 2 ;;
    *) FILES+=("$1") ;;
  esac
  shift
done
if [[ ${#FILES[@]} -gt 0 ]]; then SETS+=(files); fi
if [[ ${#SETS[@]} -eq 0 ]]; then SETS=(corpus runtests); fi

echo "== build (objects: $([[ $ASM == 1 ]] && echo "llvm-mc from the Lean assembly" || echo "Lean encoder, no assembler"); allocator: $RA${OPTARGS[*]:+; mid-end: ${OPTARGS[*]}})"
lake build lean-backend 2>&1 | tail -1
cargo build --quiet --release --manifest-path rust/Cargo.toml -p clif-native -p clif-runlines -p lean-regalloc
BIN=rust/target/release
RTLIB=rust/target/aarch64-unknown-linux-musl/release/libflat_runtime.a
# the `__*ti3` helpers of 128-bit division/remainder (rust-route step 5): the legalised
# i128 objects call them, and Cranelift's own i128 lowering uses the same libcalls
TI3="$ROOT/rust/target/aarch64-ti3/ti3.o"
if [[ ! -f "$TI3" || "$ROOT/scripts/rust-clif/rust-runtime.c" -nt "$TI3" ]]; then
  mkdir -p "$(dirname "$TI3")"
  clang --target=aarch64-linux-gnu -ffreestanding -fno-builtin -nostdlib -O1 \
    -c "$ROOT/scripts/rust-clif/rust-runtime.c" -o "$TI3"
fi
if [[ " ${SETS[*]} " == *" corpus "* ]]; then
  cargo rustc --quiet --release --manifest-path rust/Cargo.toml -p flat-runtime \
    --target aarch64-unknown-linux-musl --crate-type staticlib -- -C panic=abort
fi

WORK=${WORK:-$(mktemp -d)}
if [[ -n "${WORK_KEEP:-}" ]]; then WORK="$WORK_KEEP"; else trap 'rm -rf "$WORK"' EXIT; fi

# run_one SET FILE [LINK]: Lean backend + native runs of one file into $WORK/SET/{lean,native}.
run_one() {
  local set=$1 f=$2 link=${3:-} b d
  b=$(basename "$f" .clif)
  d="$WORK/$set"
  local links=()
  for l in $link; do links+=(--link "$l"); done
  local ok=1
  if [[ $ASM == 1 ]]; then
    .lake/build/bin/lean-backend "$f" "$d/obj/$b.s" --regalloc "$RA" $OPTS --traps "$d/obj/$b.traps.json" \
      2> "$d/obj/$b.unsupported.txt"
    if ! "$LLVM_MC" -triple=aarch64-linux-gnu -filetype=obj "$d/obj/$b.s" -o "$d/obj/$b.o" \
         2> "$d/obj/$b.mc.txt"; then
      echo "{\"file_error\": \"llvm-mc rejected the Lean backend's assembly for $f\"}" > "$d/lean/$b.json"
      cat "$d/obj/$b.mc.txt" >&2
      ok=0
    fi
  elif ! .lake/build/bin/lean-backend "$f" "$d/obj/$b.o" --regalloc "$RA" $OPTS --traps "$d/obj/$b.traps.json" \
         2> "$d/obj/$b.unsupported.txt"; then
    echo "{\"file_error\": \"the Lean encoder failed for $f\"}" > "$d/lean/$b.json"
    grep -v ': unsupported: ' "$d/obj/$b.unsupported.txt" >&2 || true
    ok=0
  fi
  if [[ $ok == 1 ]]; then
    "$BIN/clif-native" "$f" "${links[@]}" --functions-obj "$d/obj/$b.o" \
      --functions-table "$d/obj/$b.traps.json" > "$d/lean/$b.json" || [[ $? -eq 1 ]]
  fi
  "$BIN/clif-native" "$f" "${links[@]}" > "$d/native/$b.json" || [[ $? -eq 1 ]]
}
export -f run_one
OPTS="${OPTARGS[*]:-}"
export BIN WORK LLVM_MC ASM RA OPTS TI3

status=0
# report SET: per-file and total counts from the two record streams.
report() {
  local set=$1
  python3 - "$WORK/$set" "$VERBOSE" <<'EOF' || status=1
import json, os, sys
d, verbose = sys.argv[1], sys.argv[2] == "1"
def recs(path):
    out = []
    for line in open(path):
        line = line.strip()
        if line: out.append(json.loads(line))
    return out
def outcome(r):
    if "file_error" in r: return "file_error"
    a = r["actual"]
    if "error" in a:
        e = a["error"]
        if e.startswith("not compiled:"): return "unsupported"
        # clif-native's fixed-prefix errors about the test itself (same for both engines)
        if e.startswith(("no function %", "argument types", "run command does not parse")) \
                or " is not available: " in e:
            return "notrunnable"
        return "error"
    if r.get("expected") is None: return "print"
    if "trapped" in a: return "fail"
    vals = a["returned"]; exp = r["expected"]
    same = vals == exp["values"]
    return "pass" if same == (exp["cmp"] == "==") else "fail"
T = dict(files=0, full=0, partial=0, none=0, noruns=0)
tot = {k: 0 for k in ["pass", "fail", "error", "unsupported", "notrunnable", "print",
                       "file_error", "npass", "nnotcompiled", "agree", "disagree", "oneside"]}
bad = False
for name in sorted(os.listdir(os.path.join(d, "lean"))):
    lean = recs(os.path.join(d, "lean", name))
    native = recs(os.path.join(d, "native", name))
    c = {k: 0 for k in tot}
    for r in lean: c[outcome(r)] = c.get(outcome(r), 0) + 1
    for r in native:
        o = outcome(r)
        if o == "pass": c["npass"] += 1
        if o == "unsupported": c["nnotcompiled"] += 1
    if len(lean) == len(native) and all("file_error" not in r for r in lean + native):
        for a, b in zip(lean, native):
            if "error" in a["actual"] and "error" in b["actual"]: continue
            if "error" in a["actual"] or "error" in b["actual"]: c["oneside"] += 1
            elif a["actual"] == b["actual"]: c["agree"] += 1
            else: c["disagree"] += 1
    elif lean and "file_error" in lean[0]:
        c["file_error"] = 1
    for k in tot: tot[k] += c[k]
    T["files"] += 1
    ran = c["pass"] + c["fail"] + c["error"] + c["print"]
    if not lean: T["noruns"] += 1
    elif c["unsupported"] == 0 and ran > 0: T["full"] += 1
    elif ran > 0: T["partial"] += 1
    else: T["none"] += 1
    notok = c["fail"] or c["error"] or c["file_error"] or c["disagree"]
    if notok: bad = True
    if verbose or notok or (c["unsupported"] and ran):
        print(f"{name[:-5]}: lean pass {c['pass']} fail {c['fail']} error {c['error']} "
              f"unsupported {c['unsupported']} | native pass {c['npass']} not-compiled "
              f"{c['nnotcompiled']} | agree {c['agree']} disagree {c['disagree']} "
              f"one-side-error {c['oneside']}")
    if verbose or notok:
        for a, b in zip(lean, native):
            o = outcome(a)
            if o in ("fail", "error") or ("error" not in a["actual"] and "error" not in b["actual"]
                                          and a["actual"] != b["actual"]):
                print(f"    {o}: %{a['func']}({','.join(x['bits'] for x in a['args'])}): "
                      f"lean {json.dumps(a['actual'])} native {json.dumps(b['actual'])}")
print(f"files {T['files']}: every invoked function compiled {T['full']}, some {T['partial']}, "
      f"none {T['none']}, no run lines {T['noruns']}")
print(f"runs: lean pass {tot['pass']} fail {tot['fail']} error {tot['error']} "
      f"unsupported {tot['unsupported']} not-runnable {tot['notrunnable']} "
      f"file-error {tot['file_error']} | native pass {tot['npass']} not-compiled "
      f"{tot['nnotcompiled']} | agree {tot['agree']} disagree {tot['disagree']} "
      f"one-side-error {tot['oneside']}")
sys.exit(1 if bad else 0)
EOF
  echo "clif-results summary (Lean backend):"
  "$BIN/clif-results" summary "$WORK/$set"/lean/*.json | tail -1 || true
  echo "clif-results compare (Lean backend vs Cranelift-native):"
  "$BIN/clif-results" compare "$WORK/$set/lean" "$WORK/$set/native" | tail -1 || status=1
}

for set in "${SETS[@]}"; do
  mkdir -p "$WORK/$set/obj" "$WORK/$set/lean" "$WORK/$set/native"
  case "$set" in
    corpus)
      printf '%s\0' corpus/clif/*.clif | xargs -0 -n1 -P "$(nproc)" bash -c 'set -e; run_one corpus "$1"' _
      mkdir -p "$WORK/extrt/obj" "$WORK/extrt/lean" "$WORK/extrt/native"
      export RTLIB
      printf '%s\0' corpus/clif/extrt/*.clif |
        xargs -0 -n1 -P "$(nproc)" bash -c 'set -e; run_one extrt "$1" "$RTLIB"' _
      echo "== corpus/clif (Lean backend vs expectations and vs Cranelift-native)"
      report corpus
      echo "== corpus/clif/extrt (linked with flat-runtime)"
      report extrt
      ;;
    runtests)
      printf '%s\0' "$RUNTESTS"/*.clif | xargs -0 -n1 -P "$(nproc)" bash -c 'set -e; run_one runtests "$1" "$TI3"' _
      echo "== Cranelift runtests"
      report runtests
      ;;
    files)
      printf '%s\0' "${FILES[@]}" | xargs -0 -n1 -P "$(nproc)" bash -c 'set -e; run_one files "$1" "${RUST_RUNTIME:-$TI3}"' _
      echo "== files"
      report files
      ;;
  esac
done
exit $status
