
import os
BASE = os.path.abspath(os.path.join(os.path.dirname(__file__)))
BASE = os.path.normpath(BASE)

import PyBoolNet.file_exchange



def print_info(MarkDown=False):
    """
    prints repository info
    """

    MAXOUTPUT = 100000

    header = [('name','size','inputs','constants','steady states','cyclic attractors (mints)')]
    data   = []
    for name in get_all_names():
        primes = get_primes(name)
        tspaces = PyBoolNet.trap_spaces.trap_spaces(primes, "min", max_output=MAXOUTPUT)

        size          = str(len(primes))
        inputs        = str(len(PyBoolNet.prime_implicants.find_inputs(primes)))
        constants     = str(len(PyBoolNet.prime_implicants.find_constants(primes)))
        steady        = len([x for x in tspaces if len(x)==len(primes)])
        steady        = str(steady) + '+'*(steady==MAXOUTPUT)
        cyclic        = len([x for x in tspaces if len(x)<len(primes)])
        cyclic        = str(cyclic) + '+'*(steady==MAXOUTPUT)

        data.append((name,size,inputs,constants,steady,cyclic))

    data.sort(key=lambda x: int(x[1]))
    data = header + data

    width = {}
    for i in range(len(data[0])):
        width[i] = max(len(x[i]) for x in data) + 2

    if MarkDown:
        header = '| ' + ' | '.join(x.ljust(width[i]) for i,x in enumerate(data[0])) + ' |'
        print(header)
        print('| ' + ' | '.join('-'*width[i] for i,x in enumerate(data[0])) + ' |')

        body   = data[1:]
        for row in body:
            print('| ' + ' | '.join(x.ljust(width[i]) for i,x in enumerate(row)) + ' |')

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


def get_all_names():
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
        return PyBoolNet.file_exchange.bnet2primes(path)

    print(" %s does not exist"%path)
    raise FileNotFoundError


def get_attrs(Name, Update):
    """
    todo: finish code
    todo: add unit tests

    Returns the attractor data of the network *name*.

    **arguments**:
        * *name*: name of network

    **returns**:
        * *Attrs*: json attractor data, see :ref:`attractors_compute_json`
        * *update*: the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*

    **example**::

        >>> attrs = get_attrs("tournier_apoptosis", "asynchronous")
    """

    if Update=="asynchronous":
        ext = "async.json"
    elif Update=="synchronous":
        ext = "sync.json"
    elif Update=="mixed":
        ext = "mixed.json"

    path = os.path.join(BASE,Name,Name+"_attrs_"+ext)

    if os.path.isfile(path):
        return PyBoolNet.attractors.read_attractors_json(path)

    print(" %s does not exist"%path)
    raise FileNotFoundError


def get_bnet(Fname):
    """
    Fetches the bnet file as a string of the network *Fname* in the model repository.
    Run :ref:`get_all_names` to see all networks currently available.

    **arguments**:
        * *Fname*: name of network

    **returns**:
        * *BNET*: the bnet file

    **example**::

            >>> get_bnet("raf")
            {'Raf': [[{'Raf': 1, 'Erk': 1}], [{'Raf': 0}, {'Erk': 0}]],...
    """

    path = os.path.join(BASE,Fname,Fname+".bnet")
    with open(path) as f:
        bnet = f.read()

    return bnet


if __name__=="__main__":
    print_info(MarkDown=True)
