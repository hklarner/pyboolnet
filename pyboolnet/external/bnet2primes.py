

import subprocess
import ast
import sys
import os
import logging

from pyboolnet import find_command

CMD_BNET2PRIMES = find_command(name="bnet2prime")

log = logging.getLogger(__name__)


def bnet_text2primes(text: str) -> dict:
    """
    Calls bnet2primes on a bnet text and returns prime implicants.

    **arguments**:
        * *text*: contents of a *bnet* file

    **returns**:
        * *primes*: prime implicants
    """

    cmd = [CMD_BNET2PRIMES]
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = proc.communicate(input=text.encode())
    proc.stdin.close()

    if not proc.returncode == 0:
        log.error(f"failed to run bnet2primes: cmd={' '.join(cmd)}, return_code={proc.returncode}, out={out}")
        return

    out = out.decode()
    out = out.replace("\x08", "")
    out = out.replace(" ", "")
    primes = ast.literal_eval(out)

    return primes


def bnet_file2primes(fname_bnet: str) -> dict:
    """
    Calls bnet2primes on a bnet file and returns prime implicants.

    **arguments**:
        * *fname_bnet*: name of *bnet* file

    **returns**:
        * *primes*: prime implicants
    """

    if not os.path.isfile(fname_bnet):
        log.error(f"bnet file does not exist: fname_bnet={fname_bnet}")
        return

    cmd = [CMD_BNET2PRIMES, fname_bnet]
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = proc.communicate()
    out = out.decode()

    if not proc.returncode == 0:
        log.error(f"failed to run bnet_file2primes: cmd={' '.join(cmd)}, return_code={proc.returncode}, out={out}")
        sys.exit()

    out = out.replace("\x08", "")
    out = out.replace(" ", "")
    primes = ast.literal_eval(out)

    return primes
