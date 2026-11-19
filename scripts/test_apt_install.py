""".github/scripts/apt-install.sh with `sudo`, `apt-get`, `dpkg`, `timeout` and `sleep` replaced
(#726): mirror failures and hangs are retried, the last failure fails the step, and every workflow
step that calls the script ends it before the job limit."""
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
SCRIPT = ROOT / ".github/scripts/apt-install.sh"
PACKAGES = ["qemu-user-static", "llvm-18", "clang"]
APT_OPTS = "-q -o Acquire::Retries=5 -o Acquire::http::Timeout=30 -o Acquire::https::Timeout=30 -o DPkg::Lock::Timeout=120"

STUBS = {
    "sudo": 'exec "$@"\n',
    # $STUB/fail-update, $STUB/fail-install: the exit codes of the n-th call, one per line (none: 0)
    "apt-get": r'''for a in "$@"; do case $a in update|install) sub=$a;; esac; done
n=$(( $(cat "$STUB/n-$sub" 2>/dev/null || echo 0) + 1 )); echo "$n" > "$STUB/n-$sub"
echo "apt-get DEBIAN_FRONTEND=$DEBIAN_FRONTEND $*" >> "$STUB/calls"
rc=$(sed -n "${n}p" "$STUB/fail-$sub" 2>/dev/null); exit "${rc:-0}"
''',
    "dpkg": 'echo "dpkg $*" >> "$STUB/calls"\n',
    "sleep": 'echo "sleep $*" >> "$STUB/calls"\n',
    # the n-th `timeout` call whose number is in $STUB/hang is killed (124) without running
    "timeout": r'''echo "timeout $*" >> "$STUB/calls"
n=$(( $(cat "$STUB/n-timeout" 2>/dev/null || echo 0) + 1 )); echo "$n" > "$STUB/n-timeout"
grep -qx "$n" "$STUB/hang" 2>/dev/null && exit 124
while [[ $1 == --* ]]; do shift; done
shift
exec "$@"
''',
}


def limits():
    """(attempt seconds, waits) as the script sets them"""
    text = SCRIPT.read_text()
    return int(re.search(r"^ATTEMPT_S=(\d+)$", text, re.M)[1]), \
        [int(w) for w in re.search(r"^waits=\(([\d ]+)\)$", text, re.M)[1].split()]


class AptInstallTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.stub = Path(self.tmp.name)
        for name, body in STUBS.items():
            (self.stub / name).write_text("#!/usr/bin/env bash\n" + body)
            (self.stub / name).chmod(0o755)

    def tearDown(self):
        self.tmp.cleanup()

    def run_script(self, fail_update=(), fail_install=(), hang=()):
        (self.stub / "fail-update").write_text("".join(f"{rc}\n" for rc in fail_update))
        (self.stub / "fail-install").write_text("".join(f"{rc}\n" for rc in fail_install))
        (self.stub / "hang").write_text("".join(f"{n}\n" for n in hang))
        env = {"PATH": f"{self.stub}:/usr/local/bin:/usr/bin:/bin", "STUB": str(self.stub)}
        r = subprocess.run(["bash", str(SCRIPT), *PACKAGES], env=env, capture_output=True, text=True)
        calls = (self.stub / "calls").read_text().splitlines() if (self.stub / "calls").exists() else []
        return r, calls

    def apt(self, calls, sub):
        return [c for c in calls if c.startswith("apt-get ") and sub in c.split()]

    def sleeps(self, calls):
        return [int(c.split()[1]) for c in calls if c.startswith("sleep ")]

    def annotations(self, r, kind):
        return [line for line in r.stdout.splitlines() if line.startswith(f"::{kind} ")]

    def test_success_runs_once_with_the_options(self):
        r, calls = self.run_script()
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        attempt, _ = limits()
        self.assertEqual(calls[1], f"apt-get DEBIAN_FRONTEND=noninteractive {APT_OPTS} update")
        self.assertEqual(calls[3], f"apt-get DEBIAN_FRONTEND=noninteractive {APT_OPTS} install -y {' '.join(PACKAGES)}")
        self.assertTrue(calls[0].startswith(f"timeout --kill-after=30 {attempt} env "), calls[0])
        # the install gets what is left of the attempt
        self.assertLessEqual(int(calls[2].split()[2]), attempt)
        self.assertEqual(self.sleeps(calls), [])
        self.assertEqual(self.annotations(r, "warning") + self.annotations(r, "error"), [])

    def test_fetch_failures_twice_then_success(self):
        # run 44516881147: `E: Failed to fetch ... 503 Service Unavailable`, exit 100
        r, calls = self.run_script(fail_install=[100, 100])
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertEqual(len(self.apt(calls, "update")), 3)
        self.assertEqual(len(self.apt(calls, "install")), 3)
        self.assertEqual(self.sleeps(calls), limits()[1][:2])
        self.assertEqual(len(self.annotations(r, "warning")), 2)
        self.assertEqual(self.annotations(r, "error"), [])
        self.assertNotIn("dpkg --configure -a", calls)

    def test_hung_update_is_killed_and_retried(self):
        # run 44443491512: `apt-get update` printed nothing for 2 h 20 min
        r, calls = self.run_script(hang=[1])
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertEqual(len(self.apt(calls, "update")), 1)  # the killed one never ran in the stub
        self.assertEqual(len(self.apt(calls, "install")), 1)
        self.assertIn("dpkg --configure -a", calls)
        self.assertEqual(self.sleeps(calls), limits()[1][:1])
        self.assertIn(f"killed after {limits()[0]} s", self.annotations(r, "warning")[0])

    def test_failing_update_is_retried(self):
        r, calls = self.run_script(fail_update=[100])
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertEqual(len(self.apt(calls, "update")), 2)
        self.assertEqual(len(self.apt(calls, "install")), 1)

    def test_always_failing_fails_after_the_last_attempt(self):
        _, waits = limits()
        r, calls = self.run_script(fail_install=[100] * 10)
        self.assertEqual(r.returncode, 1)
        self.assertEqual(len(self.apt(calls, "install")), len(waits) + 1)
        self.assertEqual(self.sleeps(calls), waits)
        self.assertEqual(len(self.annotations(r, "warning")), len(waits))
        errors = self.annotations(r, "error")
        self.assertEqual(len(errors), 1)
        self.assertIn(f"failed {len(waits) + 1} times (last: exit 100)", errors[0])

    def test_always_hanging_fails_after_the_last_attempt(self):
        _, waits = limits()
        # every update hangs; the dpkg repairs between attempts take timeout calls 2, 4, 6
        r, calls = self.run_script(hang=[1, 3, 5, 7])
        self.assertEqual(r.returncode, 1)
        self.assertEqual(calls.count("dpkg --configure -a"), len(waits))
        self.assertEqual(len(self.annotations(r, "error")), 1)

    def test_no_packages_is_a_usage_error(self):
        r = subprocess.run(["bash", str(SCRIPT)], capture_output=True, text=True)
        self.assertEqual(r.returncode, 2)


class WorkflowTests(unittest.TestCase):
    def test_every_apt_install_goes_through_the_script(self):
        for path in sorted((ROOT / ".github").rglob("*.yml")):
            code = re.sub(r"(?m)^\s*#.*$", "", path.read_text())
            self.assertNotRegex(code, r"\bapt(-get)? ", path)

    def test_steps_end_the_script_before_the_job_limit(self):
        attempt, waits = limits()
        # attempts (each killed 30 s after its limit), dpkg repairs (60 s + 10 s), waits
        worst = (len(waits) + 1) * (attempt + 30) + len(waits) * 70 + sum(waits)
        steps = 0
        for path in sorted((ROOT / ".github/workflows").glob("*.yml")):
            for step in re.split(r"\n(?=      - )", path.read_text()):
                if ".github/scripts/apt-install.sh" in step:
                    steps += 1
                    limit = re.search(r"^        timeout-minutes: (\d+)$", step, re.M)
                    self.assertIsNotNone(limit, f"{path.name}: {step.splitlines()[0]}")
                    self.assertGreaterEqual(int(limit[1]) * 60, worst, f"{path.name}: {step.splitlines()[0]}")
        self.assertEqual(steps, 5)


if __name__ == "__main__":
    unittest.main()
