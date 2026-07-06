import multiprocessing
import sys

from pyboolnet.external.potassco import run_piped

# A simple chunked stdin->stdout echo, used as a synthetic stand-in for
# gringo/clasp so tests are fast and don't depend on ASP problem size.
# Streaming (rather than reading all of stdin before writing anything)
# matters: only a streaming process can create the backpressure that
# triggers the deadlock this covers.
ECHO_SCRIPT = (
    "import sys\n"
    "while True:\n"
    "    chunk = sys.stdin.buffer.read(65536)\n"
    "    if not chunk:\n"
    "        break\n"
    "    sys.stdout.buffer.write(chunk)\n"
    "    sys.stdout.buffer.flush()\n"
)


def _echo_cmd():
    return [sys.executable, "-c", ECHO_SCRIPT]


def test_run_piped_relays_data():
    output, error = run_piped(_echo_cmd(), _echo_cmd(), b"hello world")
    assert output == "hello world"
    assert error == ""


def test_run_piped_without_input():
    # cmd1 gets no stdin at all (mirrors potassco_handle's fname_asp branch,
    # where gringo reads from a file argument instead of stdin).
    output, error = run_piped([sys.executable, "-c", "print('hi')"], _echo_cmd())
    assert output == "hi\n"
    assert error == ""


def _run_piped_large_input(result_queue):
    large_input = b"x" * (5 * 1024 * 1024)
    output, error = run_piped(_echo_cmd(), _echo_cmd(), large_input)
    result_queue.put(len(output))


def test_run_piped_does_not_deadlock_on_large_input():
    """
    Regression test for a real deadlock in run_piped's cmd1 | cmd2 chain:
    writing input directly on the caller's thread before draining cmd2's
    output (via communicate()) can hang forever if cmd2 fills its own
    output pipes before anyone drains them. Verified directly against the
    pre-fix implementation with this exact synthetic setup: the old code
    hung indefinitely, the fix (writing on a background thread) completes
    in well under a second.

    Runs in a subprocess with an external timeout, since a genuinely
    deadlocked low-level write() can't be interrupted cleanly by a plain
    thread-based timeout within the same process.
    """
    result_queue = multiprocessing.Queue()
    proc = multiprocessing.Process(target=_run_piped_large_input, args=(result_queue,))
    proc.start()
    proc.join(timeout=15)

    if proc.is_alive():
        proc.terminate()
        proc.join()
        assert False, "run_piped deadlocked on large streaming input"

    assert result_queue.get() == 5 * 1024 * 1024
