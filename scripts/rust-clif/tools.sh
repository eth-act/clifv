#!/usr/bin/env bash
# Feed the dumped cg_clif CLIF through our tools: the pinned reader + verifier (`clif-oracle
# check`), the Lean parser (`Clif.parseFile`, via ParseCheck.lean), `clif2obj` and
# `lean-backend`. Needs scripts/rust-clif/dump.sh output and built tools:
#   cargo build --release --manifest-path rust/Cargo.toml -p clif-oracle -p clif2obj
#   lake build FV.Clif lean-backend
#
# usage: scripts/rust-clif/tools.sh [OUT_DIR]      (default /tmp/rust-clif-survey/out)
# Writes OUT_DIR/../tools/: normalised files, `raw-parse.tsv` and `parse*.tsv` (file, function,
# ok|unsupported|malformed, reason), per-file tool logs; prints summaries.
set -uo pipefail

root=$(cd "$(dirname "$0")/../.." && pwd)
here="$root/scripts/rust-clif"
out=${1:-/tmp/rust-clif-survey/out}
tools="$out/../tools"
rm -rf "$tools"
mkdir -p "$tools"
oracle="$root/rust/target/release/clif-oracle"
clif2obj="$root/rust/target/release/clif2obj"
backend="$root/.lake/build/bin/lean-backend"
norm() { python3 "$here/normalize.py" "$@"; }
reasons() { sed -E 's/%[A-Za-z0-9_]+/%X/g; s/\bv[0-9]+/vN/g; s/\bfn[0-9]+/fnN/g; s/\bgv[0-9]+/gvN/g; s/\bsig[0-9]+/sigN/g; s/\bblock[0-9]+/blockN/g' | sort | uniq -c | sort -rn; }
bystage() { # parse TSV -> "profile stage status count"
  awk -F'\t' '{ n = split($1, p, "/"); f = p[n]; split(f, q, "."); sub(/-[a-i]_[a-z0-9_]*$/, "", q[1]);
    c[q[1] " " q[2] "\t" $3]++ } END { for (k in c) print k "\t" c[k] }' "$1" | sort; }

echo "== 1. pinned reader + verifier on the raw dumps (clif-oracle check, one file per function)"
ok=0 bad=0
for f in "$out"/*/*/*.clif/*.clif; do
  if "$oracle" check "$f" >/dev/null 2>&1; then ok=$((ok + 1)); else bad=$((bad + 1)); echo "rejected: $f"; fi
done
echo "accepted $ok, rejected $bad"

echo "== 2. Lean Clif.parseFile on the raw dumps: first rejection reason"
(cd "$root" && lake env lean --run "$here/ParseCheck.lean" "$out"/*/*/*.clif/*.unopt.clif) >"$tools/raw-parse.tsv"
cut -f3,4 "$tools/raw-parse.tsv" | sort | uniq -c | sort -rn

echo "== 3. normalise (normalize.py), pinned reader check, Lean parse"
for d in "$out"/*/*/*.clif; do
  prof=$(basename "$(dirname "$(dirname "$d")")")
  crate=$(basename "$d" .clif)
  for stage in unopt opt; do
    base="$tools/$prof-$crate.$stage"
    norm "$d" "$stage" "$base.reader.clif"
    norm "$d" "$stage" "$base.nonop.clif" --drop-nop
    "$oracle" check "$base.reader.clif" >"$base.check.log" 2>&1 || echo "reader rejects $base.reader.clif"
  done
  norm "$d" unopt "$tools/split/$prof-$crate" --split
done
(cd "$root" && lake env lean --run "$here/ParseCheck.lean" "$tools"/*.reader.clif) >"$tools/parse.tsv"
echo "-- functions by profile/stage and parse status"
bystage "$tools/parse.tsv"
echo "-- first rejection reason (normalised unopt, all profiles)"
grep '\.unopt\.reader\.clif' "$tools/parse.tsv" | cut -f3,4 | grep -v '^ok' | reasons

echo "== 4. clif2obj (pinned Cranelift, aarch64) per function on the normalised unopt files"
: >"$tools/clif2obj.tsv"
for f in "$tools"/split/*/*.clif; do
  b=${f%.clif}
  if "$clif2obj" "$f" aarch64-unknown-linux-gnu "$b.o" "$b.dump" >"$b.log" 2>&1; then
    printf '%s\tok\t\n' "$f" >>"$tools/clif2obj.tsv"
  else
    printf '%s\tfail\t%s\n' "$f" "$(head -1 "$b.log" | sed -E 's/^clif2obj: %[^:]*: //')" >>"$tools/clif2obj.tsv"
  fi
done
for p in debug release release-oc; do
  awk -F'\t' -v p="$p" '{ n = split($1, a, "/"); d = a[n - 1]; sub(/-[a-i]_.*/, "", d)
    if (d == p) { t++; if ($2 == "ok") o++ } } END { print p ": " o + 0 " ok of " t + 0 }' "$tools/clif2obj.tsv"
done
echo "-- clif2obj failure reasons (all profiles)"
awk -F'\t' '$2 == "fail" { print $3 }' "$tools/clif2obj.tsv" | reasons

echo "== 5. lean-backend on the normalised unopt files (as dumped (\`reader\`, nop kept), and with nop dropped)"
for kind in reader nonop; do
  for f in "$tools"/*.unopt.$kind.clif; do
    b=${f%.clif}
    "$backend" "$f" "$b.s" --traps "$b.traps.json" >"$b.backend.log" 2>&1
  done
  for p in debug release release-oc; do
    n=$(cat "$tools"/$p-[a-i]_*.unopt.$kind.clif | grep -c '^function ')
    u=$(cat "$tools"/$p-[a-i]_*.unopt.$kind.backend.log | grep -c ': unsupported: ')
    echo "$kind $p: functions $n, compiled $((n - u)), unsupported $u"
  done
  echo "-- $kind: lean-backend unsupported reasons"
  cat "$tools"/*.unopt.$kind.backend.log | grep ': unsupported: ' | sed -E 's/.*: unsupported: //' | reasons
done

core="$out/../core/clif"
if [[ -d "$core" ]]; then
  echo "== 6. core/alloc (scripts/rust-clif/core.sh): Lean parse and lean-backend (nop kept, and dropped)"
  for c in core alloc; do
    norm "$core/$c" unopt "$tools/lib-$c.unopt.reader.clif"
    norm "$core/$c" unopt "$tools/lib-$c.unopt.nonop.clif" --drop-nop
    for kind in reader nonop; do
      "$backend" "$tools/lib-$c.unopt.$kind.clif" "$tools/lib-$c.$kind.s" >"$tools/lib-$c.$kind.backend.log" 2>&1
      n=$(grep -c '^function ' "$tools/lib-$c.unopt.$kind.clif")
      u=$(grep -c ': unsupported: ' "$tools/lib-$c.$kind.backend.log")
      echo "$c ($kind): functions $n, lean-backend compiled $((n - u)), unsupported $u"
    done
  done
  (cd "$root" && lake env lean --run "$here/ParseCheck.lean" "$tools"/lib-*.unopt.reader.clif) >"$tools/parse-lib.tsv"
  echo "-- Lean parse status"
  cut -f3 "$tools/parse-lib.tsv" | sort | uniq -c
  echo "-- first Lean parse rejection reason"
  cut -f3,4 "$tools/parse-lib.tsv" | grep -v '^ok' | reasons
  echo "-- lean-backend unsupported reasons (nop kept)"
  cat "$tools"/lib-*.reader.backend.log | grep ': unsupported: ' | sed -E 's/.*: unsupported: //' | reasons
fi
