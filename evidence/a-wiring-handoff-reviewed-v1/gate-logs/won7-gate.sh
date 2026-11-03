set -u
cd /home/lee/clifv/.worktrees/loop-20261102
S=/tmp/claude-30034/-home-lee-clifv/799a31dc-4444-481b-be40-4377830da9cf/scratchpad
E=/home/lee/clifv/.git/agent-evidence/worker-A-alu
TC=/home/lee/.elan/toolchains/leanprover--lean4---v4.34.1/bin
export PATH=$TC:$PATH FV_LAKE_CACHE=/home/lee/clifv/.worktrees/driver-proof-resume/.lake/artifact-cache OMP_NUM_THREADS=2 OMP_THREAD_LIMIT=2 LEAN_NUM_THREADS=2 FV_MEMCAP=16G
rm -rf $S/won7-build $S/won7-ab $S/won7-audit
nice -n 10 python3 scripts/lake-serial-build.py --budget 12G --max-jobs 3 --out $S/won7-build $(cat $S/won7-closure.txt) > $S/won7-build.out 2>&1; echo build rc=$?; tail -1 $S/won7-build.out
python3 - > $S/won7-audits.txt <<EOF
import re,glob
clos=set(open('$S/won7-closure.txt').read().split())
for p in sorted(glob.glob('scripts/audit/*.lean')):
    imps=re.findall(r'^import\s+(\S+)',open(p).read(),re.M)
    if any(i in clos for i in imps): print(p)
EOF
python3 - > $S/won7-audit-imports.txt <<EOF
import re
mods=set()
for p in open('$S/won7-audits.txt').read().split():
    mods.update(re.findall(r'^import\s+(\S+)',open(p).read(),re.M))
print('\n'.join(sorted(mods)))
EOF
echo audits $(wc -l < $S/won7-audits.txt)
nice -n 10 python3 scripts/lake-serial-build.py --budget 12G --max-jobs 3 --out $S/won7-ab $(cat $S/won7-audit-imports.txt) > $S/won7-ab.out 2>&1; echo audit-deps rc=$?
nice -n 10 python3 scripts/axiom-audit.py --log-dir $S/won7-audit $(cat $S/won7-audits.txt) > $S/won7-audit.out 2>&1; echo audit rc=$?; tail -1 $S/won7-audit.out
python3 - > $S/won7-exes.txt <<EOF
import tomllib
d=tomllib.load(open('lakefile.toml','rb'))
clos=set(open('$S/won7-closure.txt').read().split())
print(' '.join(e['name'] for e in d.get('lean_exe',[]) if e.get('root',e['name']) in clos))
EOF
echo exes $(wc -w < $S/won7-exes.txt)
nice -n 10 scripts/memcap.sh env PATH=$TC:$PATH $TC/lake build $(cat $S/won7-exes.txt) > $S/won7-link.out 2>&1; echo link rc=$?; tail -1 $S/won7-link.out
for x in stock-popcount-runtime stock-minmax-runtime stock-cmp-runtime stock-highmul-runtime stock-div-runtime stock-mixed-div-runtime stock-returned-div-runtime stock-general-div-runtime; do timeout 900 nice -n 10 .lake/build/bin/$x > $E/run-won7-$x.log 2>&1; echo "$x rc=$?"; done
for c in parameter conditional-forward conditional forward linear scalar-entry entry cfg; do timeout 900 nice -n 10 .lake/build/bin/stock-memory-retained $c > $E/run-won7-memret-$c.log 2>&1; echo "memret $c rc=$?"; done
