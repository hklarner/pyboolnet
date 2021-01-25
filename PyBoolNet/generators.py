

def line_graph(n: int, edge_sign: int = 1, loop_sign: int = 1) -> dict:
    """
    Creates a line graph with `n` nodes.
    All edges are either positive or negative, depending on `"edge_sign"`.
    The self-loop of the first component is either positive or negative, depending on `"loop_sign"`.

    **arguments**:
        * *n* (int): prime implicants
        * *edge_sign* (int): either `1` or `-1` for positive or negative edges
        * *loop_sign* (int): either `1` or `-1` for positive or negative self-loop of first component

    **returns**:
        * *primes* (dict): primes implicants of line graph

    **example**::

        >>> primes = line_graph(n=3, edge_sign=-1, loop_sign=1)
        >>> ig = primes2igraph(primes)
        >>> print(sorted(ig.edges))
        [('v0', 'v0', {'sign': {1}}), ('v0', 'v1', {'sign': {-1}}), ('v1', 'v2', {'sign': {-1}})]
    """

    assert n > 1
    assert edge_sign in [1, -1]
    assert loop_sign in [1, -1]

    primes = {}
    k = 1 if edge_sign == 1 else 0

    for i in range(n - 1):
        j = i + 1
        primes[f"v{j}"] = [[{f"v{i}": 1-k}], [{f"v{i}": k}]]

    k = 1 if loop_sign == 1 else 0
    primes[f"v0"] = [[{f"v0": 1 - k}], [{f"v0": k}]]

    return primes

