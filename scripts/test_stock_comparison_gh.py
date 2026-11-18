import contextlib
import io
import subprocess
import unittest

from stock_comparison_gh import RETRY_WAITS, gh_api

PATH = "repos/eth-act/clifv/actions/runs/43810352377/jobs?filter=latest&per_page=100&page=1"
BAD_GATEWAY = b"gh: Server Error (HTTP 502)\n"  # as in run 44341415709 (#1072)


class FakeGh:
    """`subprocess.run` for `gh api`: fails with each stderr of `failures` in turn, then answers."""
    def __init__(self, *failures):
        self.failures, self.calls, self.waits = list(failures), [], []

    def __call__(self, argv, check, capture_output):
        self.calls.append(argv)
        if self.failures:
            raise subprocess.CalledProcessError(1, argv, output=b"{}", stderr=self.failures.pop(0))
        return subprocess.CompletedProcess(argv, 0, stdout=b'{"jobs": []}', stderr=b"")

    def api(self):
        with contextlib.redirect_stderr(io.StringIO()):
            return gh_api(PATH, run=self, sleep=self.waits.append)


class RetryTests(unittest.TestCase):
    def test_two_bad_gateways_then_the_answer(self):
        gh = FakeGh(BAD_GATEWAY, BAD_GATEWAY)
        self.assertEqual(gh.api(), b'{"jobs": []}')
        self.assertEqual(gh.calls, [["gh", "api", PATH]] * 3)
        self.assertEqual(gh.waits, list(RETRY_WAITS[:2]))

    def test_four_bad_gateways_raise_the_last(self):
        gh = FakeGh(*[BAD_GATEWAY] * 4)
        with self.assertRaises(subprocess.CalledProcessError) as raised:
            gh.api()
        self.assertEqual(raised.exception.stderr, BAD_GATEWAY)
        self.assertEqual((len(gh.calls), gh.waits), (4, list(RETRY_WAITS)))

    def test_permanent_errors_fail_at_once(self):
        for stderr in (b"gh: Not Found (HTTP 404)\n", b"gh: Bad credentials (HTTP 401)\n",
                       b"gh: Resource not accessible by integration (HTTP 403)\n",
                       b"unknown flag: --nope\n"):
            gh = FakeGh(stderr)
            with self.assertRaises(subprocess.CalledProcessError):
                gh.api()
            self.assertEqual((len(gh.calls), gh.waits), (1, []), stderr)

    def test_rate_limits_and_connection_errors_are_retried(self):
        for stderr in (b"gh: Service Unavailable (HTTP 503)\n", b"gh: Gateway Timeout (HTTP 504)\n",
                       b"gh: Too Many Requests (HTTP 429)\n",
                       b"gh: API rate limit exceeded for installation ID 1. (HTTP 403)\n",
                       b"gh: You have exceeded a secondary rate limit. (HTTP 403)\n",
                       b"error connecting to api.github.com\ncheck your internet connection or https://githubstatus.com\n",
                       b'Get "https://api.github.com/repos/eth-act/clifv": read tcp 10.1.0.4:1->140.82.1.1:443: '
                       b"read: connection reset by peer\n"):
            gh = FakeGh(stderr)
            self.assertEqual(gh.api(), b'{"jobs": []}')
            self.assertEqual((len(gh.calls), gh.waits), (2, [RETRY_WAITS[0]]), stderr)


if __name__ == "__main__":
    unittest.main()
