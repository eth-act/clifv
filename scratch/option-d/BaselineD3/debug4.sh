#!/usr/bin/env bash
# BaselineD3: BaselineD2's debug3.sh plus NOBC=1 (adds --no-binary-check: the plain-mode binary
# check ran link-check on one core for 15 h on deps; it does not change the objects parity compares).
# BaselineD2: BaselineD1's debug2.sh with ACT (the cg_clif copy's path; default target/cg_clif-active)
# so that a debug line can run beside a release run in the same worktree.
# BaselineD1 (option D measurement, scratch): the gate's cargo fv lines with cg_clif linked against
# Cranelift 0.135.0 (as shipped; target/cg_clif) and 0.136.1 (target/cg_clif-cl0.136.1), both
# copied to the same path (target/cg_clif-active: the backend path feeds cargo's metadata hash).
#   debug.sh OUT LINE...   (CLS: the Cranelifts, default both; REF: with one CLS, s2s of REF/keep-LINE-CL
#   (another run, e.g. main's Lean) against this run, same cg_clif: Lean gained/lost per function)   LINE = fv-demo | survey | deps | bigframe-unwind | fv-demo+std
# Per line and Cranelift: compare.sh log, gate-line-check verdict, stock-crate-parity.py, kept
# cgclif.o/lean.o/c.clif per CGU; then nightlypin-s2s.py across the two and notrap-dead.py.
set -uo pipefail
W=${W:-$HOME/clifv/wt/BaselineD1-meas}
B=$HOME/clifv/tmp/BaselineD1
out=$1; shift
mkdir -p "$out"
export PATH="$W/rust/target/release:$PATH" FV_ROOT="$W"
act=${ACT:-$W/target/cg_clif-active}
cd "$W" || exit 2
for line in "$@"; do
  ex=${line%+std}
  flags=(--lean-link --verified); lk=(--lean-link); extra=()
  [[ $ex == bigframe-unwind ]] && { flags=(); lk=(); }
  [[ $line == *+std ]] && { flags+=(--build-std); extra=(--rise-ok); }
  # PLAIN=1: plain cargo fv (every function compiled by Lean in lean.o; no lean-link, no --verified)
  [[ -n ${PLAIN:-} ]] && { flags=(); lk=(); [[ $line == *+std ]] && flags=(--build-std); }
  [[ -n ${NOBC:-} ]] && flags+=(--no-binary-check)
  for cl in ${CLS:-0.135.0 0.136.1}; do
    d=cg_clif; [[ $cl == 0.136.1 ]] && d=cg_clif-cl0.136.1
    rm -rf "$act" && mkdir -p "$act" && cp -r "$W/target/$d/unwind" "$W/target/$d/abort" "$act/"
    tag=$line-$cl
    rm -rf "$W/examples/$ex/target"
    t0=$(date +%s)
    FV_CG_CLIF=$act/unwind/librustc_codegen_cranelift.so \
      "$W/examples/compare.sh" "$W/examples/$ex" "${flags[@]}" --keep-temps >"$out/$tag.compare.log" 2>&1
    rc=$?
    logs=$(sed -n 's/.*(logs: \(.*\))$/\1/p' "$out/$tag.compare.log" | tail -n 1)
    [[ -n $logs && -f $logs/fv.log ]] && cp "$logs/fv.log" "$out/$tag.fv.log"
    v=$(python3 "$W/scripts/gate-line-check.py" cargo-fv "$line" "${lk[@]}" "${extra[@]}" "$out/$tag.compare.log" "$out/$tag.fv.log" 2>&1 | tail -n 3 | tr '\n' ' ')
    echo "$tag compare rc=$rc wall=$(( $(date +%s) - t0 ))s: $(grep -E '^SAME|^DIFFERENT' "$out/$tag.compare.log") | gate-line-check: $v"
    grep -E '^cargo fv: [0-9]+ of [0-9]+ functions|^cargo fv: binary check|^  total' "$out/$tag.compare.log" | sed "s/^/  $tag: /" | cut -c1-300
    cp "$W/examples/$ex/target/fv-report.json" "$out/$tag.fv-report.json" 2>/dev/null
    rm -rf "$out/keep-$tag" && mkdir -p "$out/keep-$tag"
    for tmpd in "$W/examples/$ex"/target/fv/*/tmp; do
      [ -d "$tmpd" ] || continue
      (cd "$tmpd" && find . -maxdepth 2 \( -name cgclif.o -o -name lean.o -o -name c.clif \) \
        -exec cp -r --parents {} "$out/keep-$tag/" \;)
    done
    python3 "$W/scripts/stock-crate-parity.py" --json "$out/$tag.parity.json" "$out/keep-$tag" >"$out/$tag.parity.txt" 2>&1
    echo "  $tag parity: $(grep -m1 '^functions' "$out/$tag.parity.txt")"
  done
  if [[ -n ${REF:-} ]]; then
    for cl in ${CLS:-0.136.1}; do
      python3 "$W/scripts/nightlypin-s2s.py" "$REF/keep-$line-$cl" "$out/keep-$line-$cl" \
        --json "$out/s2sref-$line-$cl.json" >"$out/s2sref-$line-$cl.txt" 2>&1
      sed "s/^/  $line-$cl vs REF (A = REF, B = this run): /" "$out/s2sref-$line-$cl.txt"
    done
  elif [[ -z ${CLS:-} ]]; then
  python3 "$W/scripts/nightlypin-s2s.py" "$out/keep-$line-0.135.0" "$out/keep-$line-0.136.1" \
    --diffs "$out/s2s-$line.diffs" --json "$out/s2s-$line.json" >"$out/s2s-$line.txt" 2>&1
  sed "s/^/  $line s2s: /" "$out/s2s-$line.txt"
  python3 "$B/notrap-dead.py" --s2s "$out/s2s-$line.json" --json "$out/notrap-$line.json" "$out/keep-$line-0.136.1" >"$out/notrap-$line.txt" 2>&1
  sed "s/^/  $line notrap: /" "$out/notrap-$line.txt"
  fi
  rm -rf "$W/examples/$ex/target"
done
rm -rf "$act"
