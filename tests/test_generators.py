

import pytest
import networkx

from PyBoolNet.InteractionGraphs import primes2igraph
from PyBoolNet.generators import path_graph, balanced_tree


def assert_edge_signs_agree(ig: networkx.DiGraph, edge_sign: int, loop_sign: int):
    for u, v, d in ig.edges(data=True):

        if u == v:
            assert d["sign"] == {loop_sign, }
        else:
            assert d["sign"] == {edge_sign, }


@pytest.mark.parametrize("n", [3])
@pytest.mark.parametrize("edge_sign", [1, -1])
@pytest.mark.parametrize("loop_sign", [1, -1])
def test_path_graph(n: int, edge_sign: int, loop_sign: int):

    primes = path_graph(n=n, edge_sign=edge_sign, loop_sign=loop_sign)
    ig = primes2igraph(primes)

    path = networkx.path_graph(n=n, create_using=networkx.DiGraph)
    path.add_edge(0, 0)

    assert networkx.is_isomorphic(ig, path)
    assert_edge_signs_agree(ig, edge_sign, loop_sign)


@pytest.mark.parametrize("height", [3])
@pytest.mark.parametrize("branching_factor", [2])
@pytest.mark.parametrize("edge_sign", [1, -1])
@pytest.mark.parametrize("loop_sign", [1, -1])
def test_balanced_tree(height: int, branching_factor: int, edge_sign: int, loop_sign: int):

    primes = balanced_tree(height=height, branching_factor=branching_factor, edge_sign=edge_sign, loop_sign=loop_sign)
    ig = primes2igraph(primes)

    tree = networkx.balanced_tree(r=branching_factor, h=height, create_using=networkx.DiGraph)
    tree.add_edge(0, 0)

    assert networkx.is_isomorphic(ig, tree)
    assert_edge_signs_agree(ig, edge_sign, loop_sign)

