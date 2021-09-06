

from pyboolnet.external.bnet2primes import bnet_text2primes, bnet_file2primes
from tests.helpers import get_tests_path_in


def test_bnet_text2primes():
    bnet_text = "\n".join(["v1, v2", "v2, !v1&(v1|v2)"])
    bnet_text2primes(bnet_text=bnet_text)


def test_bnet_file2primes():
    bnet_file2primes(fname_bnet=get_tests_path_in(fname="irma.bnet"))
