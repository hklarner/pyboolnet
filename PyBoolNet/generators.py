

import networkx


def path_graph(n: int, edge_sign: int = 1, loop_sign: int = 1) -> dict:
    """
    Creates a path graph network with `n` nodes.
    All edges are either positive or negative, depending on `"edge_sign"`.
    The self-loop of the root component is either positive or negative, depending on `"loop_sign"`.

    **arguments**:
        * *n* (int): number of components
        * *edge_sign* (int): either `1` or `-1` for positive or negative edges
        * *loop_sign* (int): either `1` or `-1` for positive or negative self-loop of root component

    **returns**:
        * *primes* (dict): primes implicants

    **example**::

        >>> primes = path_graph(n=3, edge_sign=-1, loop_sign=1)
        >>> ig = primes2igraph(primes)
        >>> print(sorted(ig.edges))
        [('v0', 'v0', {'sign': {1}}), ('v0', 'v1', {'sign': {-1}}), ('v1', 'v2', {'sign': {-1}})]
    """

    assert n > 1
    assert edge_sign in [1, -1]
    assert loop_sign in [1, -1]

    primes = {}
    k = 1 if edge_sign == 1 else 0

    path = networkx.path_graph(n=n, create_using=networkx.DiGraph)

    for i, j in path.edges:
        primes[f"v{j}"] = [[{f"v{i}": 1-k}], [{f"v{i}": k}]]

    k = 1 if loop_sign == 1 else 0
    primes[f"v0"] = [[{f"v0": 1 - k}], [{f"v0": k}]]

    return primes


def balanced_tree(height: int, branching_factor: int = 2, edge_sign: int = 1, loop_sign: int = 1) -> dict:
    """
    Creates a balanced tree network of given `height` and `branching_factor`.
    All edges are either positive or negative, depending on `"edge_sign"`.
    The self-loop of the root component is either positive or negative, depending on `"loop_sign"`.

    **arguments**:
        * *height* (int): height of tree
        * *branching_factor* (int): branching factor of tree
        * *edge_sign* (int): either `1` or `-1` for positive or negative edges
        * *loop_sign* (int): either `1` or `-1` for positive or negative self-loop of first component

    **returns**:
        * *primes* (dict): primes implicants

    **example**::

        >>> primes = balanced_tree(height=3)
        >>> ig = primes2igraph(primes)
        >>> print(sorted(ig.edges))
        [('v0', 'v0', {'sign': {1}}), ('v0', 'v1', {'sign': {-1}}), ('v1', 'v2', {'sign': {-1}})]
    """

    assert height >= 1
    assert branching_factor >= 1
    assert edge_sign in [1, -1]
    assert loop_sign in [1, -1]

    tree = networkx.balanced_tree(r=branching_factor, h=height, create_using=networkx.DiGraph)

    primes = {}
    k = 1 if edge_sign == 1 else 0

    for i, j in tree.edges:
        primes[f"v{j}"] = [[{f"v{i}": 1-k}], [{f"v{i}": k}]]

    k = 1 if loop_sign == 1 else 0
    primes[f"v0"] = [[{f"v0": 1 - k}], [{f"v0": k}]]

    return primes

