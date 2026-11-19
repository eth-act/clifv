#!/usr/bin/env bash
# Install Ubuntu packages in a CI step: `apt-get update` + `apt-get install -y PACKAGE...`,
# retried when the package mirror fails. The step still fails when the last attempt fails.
#
# usage: .github/scripts/apt-install.sh PACKAGE...
#
# Why (#726): on 2026-11-19 main's Full gate went red twice from the mirror alone. In run
# 44443491512 `apt-get update` stopped printing at 06:41Z and hung until the run was cancelled
# 2 h 20 min later; in run 44516881147 four jobs failed on `503 Service Unavailable` /
# `Connection failed` for the .deb files (12:19-12:31Z). Here apt retries each download itself
# (Acquire::Retries, 30 s network timeouts), each attempt of update + install is killed after
# ATTEMPT_S seconds, and a failed or killed attempt is retried after 15, 45, then 120 s. Worst
# case about 33 min (4 attempts of at most 6.5 min, 3 dpkg repairs of at most 70 s, 3 min of
# waits); the workflow steps that call this script set `timeout-minutes: 35`
# (scripts/test_apt_install.py checks both).
set -uo pipefail
(( $# )) || { echo "usage: $0 PACKAGE..." >&2; exit 2; }
# a normal install takes up to 4 min on a slow mirror (14.7 MB at 63 kB/s on 2026-11-19); a
# killed attempt keeps its partial downloads and the next one resumes them
ATTEMPT_S=360
waits=(15 45 120)
attempts=$(( ${#waits[@]} + 1 ))
sudo=()
(( EUID == 0 )) || sudo=(sudo)
apt_opts=(-q -o Acquire::Retries=5 -o Acquire::http::Timeout=30 -o Acquire::https::Timeout=30
  -o DPkg::Lock::Timeout=120)
# run_apt SECONDS ARG...: apt-get as root, killed after SECONDS (timeout runs as root, so it can
# signal apt-get and its download methods directly)
run_apt() {
  local secs=$1
  shift
  "${sudo[@]}" timeout --kill-after=30 "$secs" \
    env DEBIAN_FRONTEND=noninteractive apt-get "${apt_opts[@]}" "$@"
}
for (( i = 1; i <= attempts; i++ )); do
  echo "apt-install: attempt $i of $attempts: apt-get update + install $*"
  start=$SECONDS
  run_apt "$ATTEMPT_S" update
  rc=$?
  if (( rc == 0 )); then
    left=$(( ATTEMPT_S - (SECONDS - start) ))
    (( left > 0 )) || left=1
    run_apt "$left" install -y "$@"
    rc=$?
  fi
  (( rc == 0 )) && exit 0
  if (( rc == 124 || rc == 137 )); then
    why="killed after ${ATTEMPT_S} s"
  else
    why="exit $rc"
  fi
  if (( i == attempts )); then
    echo "::error title=apt-get failed::apt-get update + install $* failed $attempts times (last: $why); see the apt output above"
    exit 1
  fi
  echo "::warning title=apt-get retry::attempt $i of $attempts failed ($why); retrying in ${waits[i-1]} s"
  if [[ $why == killed* ]]; then
    # a kill while dpkg unpacked leaves it half done, and every later install would refuse
    "${sudo[@]}" timeout --kill-after=10 60 env DEBIAN_FRONTEND=noninteractive \
      dpkg --configure -a || true
  fi
  sleep "${waits[i-1]}"
done
