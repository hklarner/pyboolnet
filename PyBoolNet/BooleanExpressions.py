def hello():
"""
    Creates the interaction graph from the prime implicants of a network.
    Interaction graphs are implemented as :ref:`installation_networkx` digraph objects.
    Edges are given the attribute *sign* whose value is a Python set containing 1 or -1 or both, depending on
    whether the interaction is activating or inhibiting or both.

    **arguments**:
        * *Primes*: prime implicants

    **returns**:
        * *IGraph* (networkx.DiGraph): interaction graph

    **example**::

            >>> bnet = "\\n".join(["v1, v1","v2, 1", "v3, v1&!v2 | !v1&v2"])
            >>> primes = bnet2primes(bnet)
            >>> igraph = primes2igraph(primes)
            >>> igraph.nodes()
            ['v1', 'v2', 'v3']
            >>> igraph.edges()
            [('v1', 'v1'), ('v1', 'v3'), ('v2', 'v3'), ('v3', 'v1')]
            >>> igraph.edge["v1"]["v3"]["sign"]
            set([1, -1])
    """
	print('wuuhuu')
