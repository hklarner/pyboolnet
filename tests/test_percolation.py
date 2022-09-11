

from pyboolnet.external.bnet2primes import bnet_text2primes
from pyboolnet.prime_implicants import percolate


def test_self_loops_percolate():
    """
    https://github.com/hklarner/pyboolnet/issues/100
    """

    primes = bnet_text2primes("""
    A, A
    B, A | B
    C, B | C
    D, C | D
    E, D | E
    F, E | F
    G, F | G
    """)

    new_primes = percolate(primes, add_constants={"A": 1}, remove_constants=True, copy=True)

    assert not new_primes
