

import pytest

from PyBoolNet.InteractionGraphs import primes2igraph
from PyBoolNet.generators import line_graph


@pytest.mark.parametrize("n", [3])
@pytest.mark.parametrize("edge_sign", [1, -1])
@pytest.mark.parametrize("loop_sign", [1, -1])
def test_line_graph(n: int, edge_sign: int, loop_sign: int):

    primes = line_graph(n=n, edge_sign=edge_sign, loop_sign=loop_sign)
    ig = primes2igraph(primes)
    x = sorted(ig.edges(data=True))

    assert len(primes) == n

    for u, v, d in ig.edges(data=True):

        if u == v:
            assert d["sign"] == {loop_sign, }
        else:
            assert d["sign"] == {edge_sign, }
