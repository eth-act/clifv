"""`gh api` for the stock comparison's lookups, retrying transient GitHub API failures (#1072).

One `gh: Server Error (HTTP 502)` while listing the jobs of one candidate Full gate run used to
fail the whole measurement. A server error (HTTP 5xx), a rate limit (HTTP 429, or a 403 that
names a rate limit) and a failed connection are retried after each wait of RETRY_WAITS; any
other failure (404, 401, a 403 that is not a rate limit, ...) is raised at once, and so is the
last failure once the waits are used up. Callers keep their own handling of a failed lookup.
"""
import re
import subprocess
import sys
import time

RETRY_WAITS = (2, 8, 30)  # seconds before the 2nd, 3rd and 4th attempt


def transient(stderr):
    """Whether `gh api` failed with a server error, a rate limit or the connection (its stderr)."""
    status = re.search(r"\(HTTP (\d{3})\)", stderr)
    if status is None:
        # gh prints a failed DNS lookup as "error connecting to <host>" and any other transport
        # error as Go's url.Error, `Get "https://…": <cause>`.
        return "error connecting to " in stderr or re.search(r'^[A-Z][a-z]+ "https?://', stderr, re.M) is not None
    code = int(status[1])
    return code >= 500 or code == 429 or (code == 403 and "rate limit" in stderr.lower())


def gh_api(path, run=subprocess.run, sleep=time.sleep):
    """The response body of `gh api <path>` (bytes)."""
    for wait in (*RETRY_WAITS, None):
        try:
            return run(["gh", "api", path], check=True, capture_output=True).stdout
        except subprocess.CalledProcessError as error:
            stderr = error.stderr.decode(errors="replace") if isinstance(error.stderr, bytes) else error.stderr or ""
            if wait is None or not transient(stderr):
                raise
            print(f"gh api {path}: {stderr.strip()}; retrying in {wait} s", file=sys.stderr)
            sleep(wait)
