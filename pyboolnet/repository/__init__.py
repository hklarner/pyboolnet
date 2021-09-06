

import os
from typing import List

from pyboolnet.trap_spaces import trap_spaces
from pyboolnet.prime_implicants import find_inputs, find_constants, find_outputs
from pyboolnet.file_exchange import bnet2primes

BASE = os.path.abspath(os.path.join(os.path.dirname(__file__)))
BASE = os.path.normpath(BASE)
MAX_OUTPUT = 100000


def print_info(markdown: bool = False):
    """
    prints repository info
    """

    header = [("name", "size", "inputs", "constants", "steady states", "cyclic attractors (mints)")]
    data = []
    for name in get_all_names():
        primes = get_primes(name)
        tspaces = trap_spaces(primes, "min", max_output=MAX_OUTPUT)

        size = str(len(primes))
        inputs = str(len(find_inputs(primes)))
        constants = str(len(find_constants(primes)))
        steady = len([x for x in tspaces if len(x) == len(primes)])
        steady = str(steady) + '+'*(steady == MAX_OUTPUT)
        cyclic = len([x for x in tspaces if len(x) < len(primes)])
        cyclic = str(cyclic) + '+'*(steady == MAX_OUTPUT)

        data.append((name, size, inputs, constants, steady, cyclic))

    data.sort(key=lambda x: int(x[1]))
    data = header + data

    width = {}
    for i in range(len(data[0])):
        width[i] = max(len(x[i]) for x in data) + 2

    if markdown:
        header = '| ' + ' | '.join(x.ljust(width[i]) for i, x in enumerate(data[0])) + ' |'
        print(header)
        print('| ' + ' | '.join('-'*width[i] for i, x in enumerate(data[0])) + ' |')

        body   = data[1:]
        for row in body:
            print('| ' + ' | '.join(x.ljust(width[i]) for i, x in enumerate(row)) + ' |')

    else:
        for row in data:
            print(''.join(x.ljust(width[i]) for i,x in enumerate(row)))


def names_with_fast_analysis():
    result = ["arellano_rootstem","dahlhaus_neuroplastoma",
              "dinwoodie_life", "faure_cellcycle",
              "irons_yeast", "randomnet_n7k3", "randomnet_n15k3",
              "saadatpour_guardcell", "tournier_apoptosis", "xiao_wnt5a",
              "raf","n5s3","n3s1c1a","n3s1c1b","n6s1c2","n7s3",
              "dinwoodie_stomatal", "multivalued"]

    return result


def get_all_names() -> List[str]:
    """
    Returns the names of all models currently in the repository.

    **returns**:
        * *Fnames*: model names

    **example**::

        >>> get_all_names()
        ['arellano_rootstem', 'dahlhaus_neuroplastoma', ...]
    """

    result = sorted([os.path.basename(subdir) for subdir, _, _ in os.walk(BASE) if subdir != BASE and "__" not in subdir])

    return result


def get_primes(name: str) -> dict:
    """
    Returns the prime implicants of the network *name* in the model repository.
    Run :ref:`get_all_names` to see all networks currently available.

    **arguments**:
        * *name*: name of network

    **returns**:
        * *primes*: the prime implicants

    **example**::

        >>> primes = get_primes("raf")
    """

    path = os.path.join(BASE, name, name + ".bnet")

    if os.path.isfile(path):
        return bnet2primes(path)

    print(" %s does not exist"%path)
    raise FileNotFoundError


def get_attractors(name: str, update: str) -> dict:
    """
    Returns the attractor data of the network *name*.

    **arguments**:
        * *name*: name of network

    **returns**:
        * *attractors*: json attractor data, see :ref:`compute_attractors`
        * *update*: the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*

    **example**::

        >>> attractors = get_attractors("tournier_apoptosis", "asynchronous")
    """

    if update == "asynchronous":
        ext = "async.json"
    elif update == "synchronous":
        ext = "sync.json"
    elif update == "mixed":
        ext = "mixed.json"

    path = os.path.join(BASE, name, name + "_attractors_" + ext)

    if os.path.isfile(path):
        return read_attractors_json(path)

    print(" %s does not exist"%path)
    raise FileNotFoundError


def get_bnet(name: str) -> str:
    """
    Returns the bnet file contents of the network *name* as a string.
    Run :ref:`get_all_names` to see all networks currently available.

    **arguments**:
        * *name*: name of network

    **returns**:
        * *bnet*: the bnet file

    **example**::

            >>> get_bnet("raf")
            {'Raf': [[{'Raf': 1, 'Erk': 1}], [{'Raf': 0}, {'Erk': 0}]],...
    """

    path = os.path.join(BASE, name, name + ".bnet")
    with open(path) as f:
        bnet = f.read()

    return bnet

