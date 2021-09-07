

import logging
import random
from typing import List, Dict

import networkx

from pyboolnet.file_exchange import bnet2primes

log = logging.getLogger(__name__)

try:
    from pyeda.inter import truthtable, truthtable2expr, exprvar
except ImportError:
    log.warning(f"failed to import pyeda: network_generators.random_boolean_expression is not available")


def path_graph(n: int, edge_sign: int = 1, loop_sign: int = 1) -> dict:
    """
    Creates a path graph network with `n` nodes.
    All edges are either positive or negative, depending on `edge_sign`.
    The self-loop of the root component is either positive or negative, depending on `loop_sign`.

    **arguments**:
        * *n*: number of components
        * *edge_sign*: either `1` or `-1` for positive or negative edges
        * *loop_sign*: either `1` or `-1` for positive or negative self-loop of root component

    **returns**:
        * *primes*: primes implicants

    **example**::

        >>> primes = path_graph(n=3, edge_sign=-1, loop_sign=1)
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
    primes["v0"] = [[{"v0": 1 - k}], [{"v0": k}]]

    return primes


def balanced_tree(height: int, branching_factor: int = 2, edge_sign: int = 1, loop_sign: int = 1) -> dict:
    """
    Creates a balanced tree network of given `height` and `branching_factor`.
    All edges are either positive or negative, depending on `edge_sign`.
    The self-loop of the root component is either positive or negative, depending on `loop_sign`.

    **arguments**:
        * *height*: height of tree
        * *branching_factor*: branching factor of tree
        * *edge_sign*: either `1` or `-1` for positive or negative edges
        * *loop_sign*: either `1` or `-1` for positive or negative self-loop of first component

    **returns**:
        * *primes*: primes implicants

    **example**::

        >>> primes = balanced_tree(height=3)
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


def cycle_graph(n: int, edge_sign: int = 1) -> dict:
    """
    Creates a cycle network with `n` components.
    All edges are either positive or negative, depending on `edge_sign`.

    **arguments**:
        * *n*: number of components
        * *edge_sign*: either `1` or `-1` for positive or negative edges

    **returns**:
        * *primes*: primes implicants

    **example**::

        >>> primes = cycle_graph(n=3)
    """

    assert n > 1
    assert edge_sign in [1, -1]

    cycle = networkx.cycle_graph(n=n, create_using=networkx.DiGraph)

    primes = {}
    k = 1 if edge_sign == 1 else 0

    for i, j in cycle.edges:
        primes[f"v{j}"] = [[{f"v{i}": 1-k}], [{f"v{i}": k}]]

    return primes


def random_truth_table_network(n: int, k: int, seed: int = 0) -> dict:
    """
    Creates a random netowrk with `n` components each with a random truthtable of `k` inputs.
    The `seed` is used for the randomizer.
    Use `0` to generate a random seed.

    **arguments**:
        * *n*: number of components
        * *k*: inputs of each truthtable
        * *seed*: the seed of the randomizer

    **returns**:
        * *primes*: primes implicants

    **example**::

        >>> primes = random_truth_table_network(n=3, k=2)
    """

    assert n > 1
    assert k < n
    assert k < 10

    if seed:
        random.seed(seed)

    names = [f"v{i}" for i in range(n)]

    primes = {}
    for v in names:
        bnet = f"x, {random_boolean_expression(names=names, k=k)}"
        primes[v] = bnet2primes(bnet)["x"]

    return primes


def _primes_of_conjunction(inputs: List[str], value: int) -> List[dict]:
    return [{n: value for n in inputs}]


def _primes_of_disjunction(inputs: List[str], value: int) -> List[dict]:
    return [{n: value} for n in inputs]


def random_regular_network(n: int, k: int, connector: str = "and", edge_sign: int = 1, seed: int = 0) -> dict:
    """
    Creates a random netowrk with `n` components each with a random truthtable of `k` inputs.
    The `seed` is used for the randomizer.
    Use `0` to generate a random seed.

    **arguments**:
        * *n*: number of components
        * *k*: inputs of each truthtable
        * *connector*: either `"and"` or `"or"`
        * *edge_sign*: either `1` or `-1` for positive or negative edges
        * *seed*: the seed of the randomizer

    **returns**:
        * *primes*: primes implicants

    **example**::

        >>> primes = random_regular_network(n=3, k=2, connector="or")
    """

    assert n > 1
    assert k < n
    assert edge_sign in [1, -1]
    assert connector in ["and", "or"]

    if seed:
        random.seed(seed)

    names = [f"v{i}" for i in range(n)]

    value1 = 1 if edge_sign == 1 else 0
    value0 = 1 - value1
    generator0 = _primes_of_disjunction if connector == "and" else _primes_of_conjunction
    generator1 = _primes_of_conjunction if connector == "and" else _primes_of_disjunction

    primes = {}
    for v in names:
        inputs = random.sample(population=names, k=k)
        primes[v] = [generator0(inputs=inputs, value=value0), generator1(inputs=inputs, value=value1)]

    return primes


def _dnf2bnet(ast: tuple, name_map: Dict[int, str]) -> str:

    assert ast[0] in ["lit", "or", "and"]

    if ast[0] == "lit":
        return name_map[ast[1]]

    op = " | " if ast[0] == "or" else " & "

    return op.join([f"{_dnf2bnet(x, name_map)}" for x in ast[1:]])


def random_boolean_expression(names: List[str], k: int, seed: int = 0) -> str:
    """
    Creates a random Boolean expression by sampling `k` variables from `names` and filling a truth table randomly.
    The expression is guaranteed to be non-constant but it may effectivly be dependent by less than `k` variables.

    **arguments**:
        * *names* (List[str]): components to sample from
        * *k*: inputs to the expression
        * *seed*: the seed of the randomizer

    **returns**:
        * *expression*: random expression in bnet format

    **example**::

        >>> primes = random_boolean_expression(names=list("abcdefgh"), k=4)
    """

    if seed:
        random.seed(seed)

    variables = list(map(exprvar, random.sample(population=names, k=k)))
    name_map = dict([(v.uniqid, v.name) for v in variables] + [(-v.uniqid, "!" + v.name) for v in variables])
    truth_table = "".join(random.choices(population="01", k=2**k))

    for k in "01":
        if k not in truth_table:
            truth_table = k + truth_table[1:]

    tt = truthtable(variables, truth_table)
    expr = truthtable2expr(tt)
    ast = expr.to_dnf().to_ast()
    bnet = _dnf2bnet(ast, name_map)

    return bnet
