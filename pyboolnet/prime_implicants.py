

import logging
import sys
import itertools
from typing import List, Optional, Dict, Union

from pyboolnet.interaction_graphs import primes2igraph
from pyboolnet.state_transition_graphs import subspace2str
from pyboolnet.digraphs import successors, predecessors
from pyboolnet.misc import dicts_are_consistent
from pyboolnet.boolean_normal_forms import functions2primes
from pyboolnet.file_exchange import bnet2primes

log = logging.getLogger(__name__)

CONSTANT_ON = [[], [{}]]
CONSTANT_OFF = [[{}], []]


def copy(primes: dict) -> dict:
    """
    Creates a copy of *primes*.

    **arguments**:
        * *primes*: prime implicants

    **returns**:
        * *new_primes*: a copy of *primes*

    **example**::

        >>> new_primes = copy(primes)
    """

    new_primes = {}
    for name in primes:
        new_primes[name] = [[], []]

        for value in [0, 1]:
            for prime in primes[name][value]:
                new_primes[name][value].append(dict(prime))

    return new_primes


def are_equal(primes1, primes2) -> bool:
    """
    Tests whether *primes1* and *primes2* are equal.
    The dictionary comparison *primes1 == primes2* does in general not work because the clauses of each may not be in the same order.

    **arguments**:
        * *primes1*, *primes2*: prime implicants

    **returns**:
        * *answer*: whether *primes1 == primes2*

    **example**::

        >>> are_equal(primes1, primes2)
        True
    """

    if len(primes1) != len(primes2):
        return False

    for name in primes1:
        if name not in primes2:
            return False

        for value in [0, 1]:
            p1 = sorted([sorted(d.items()) for d in primes1[name][value]])
            p2 = sorted([sorted(d.items()) for d in primes2[name][value]])
            if not p1 == p2:
                return False

    return True


def find_inputs(primes: dict) -> List[str]:
    """
    Finds all inputs in the network defined by *Primes*.

    **arguments**:
        * *primes*: prime implicants

    **returns**:
        * *names*: the names of the inputs

    **example**::

        >>> find_inputs(primes)
        ["DNA_damage","EGFR","FGFR3"]
    """

    return sorted(name for name in primes if primes[name][1] == [{name: 1}])


def find_outputs(primes: dict) -> List[str]:
    """
    Finds all outputs in the network defined by *Primes*.

    **arguments**:
        * *primes*: prime implicants

    **returns**:
        * *names*: the names of the outputs

    **example**::

        >>> find_inputs(primes)
        ["Proliferation","Apoptosis","GrowthArrest"]
    """

    igraph = primes2igraph(primes)
    outputs = [x for x in igraph.nodes() if not list(igraph.successors(x))]

    return sorted(outputs)


def find_constants(primes: dict) -> Dict[str, int]:
    """
    Finds all constants in the network defined by *primes*.

    **arguments**:
        * *primes*: prime implicants

    **returns**:
        * *constants*: the names and activities of constants

    **example**::

        >>> find_constants(primes)
        {"CGC":1,"IFNAR1":1,"IFNAR2":0,"IL4RA":1}
    """

    constants = {}
    for name in primes:
        if primes[name] == CONSTANT_ON:
            constants[name] = 1
        elif primes[name] == CONSTANT_OFF:
            constants[name] = 0

    return constants


def create_constants(primes: dict, constants: Dict[str, int], in_place: bool = True) -> Optional[dict]:
    """
    Creates a constant in *primes* for every name, value pair in *constants*.
    Names that already exist in *primes* are overwritten.

    **arguments**:
        * *primes*: prime implicants
        * *constants*: names and values
        * *copy*: change *primes* in place or copy and return

    **returns**:
        * *new_primes* if *copy ==True*

    **example**::

        >>> create_constants(primes, {"p53":1, "p21":0})
    """

    if not in_place:
        primes = copy(primes=primes)

    for name, value in constants.items():
        if value:
            primes[name] = CONSTANT_ON
        else:
            primes[name] = CONSTANT_OFF

    if not in_place:
        return primes


def create_inputs(primes: dict, names: List[str], in_place: bool = True) -> Optional[dict]:
    """
    Creates an input for every member of *Names*.
    Variables that already exist in *Primes* are overwritten.

    .. note::
        Suppose that a given network has constants, e.g.::

            >>> len(find_constants(primes))>0
            True

        Too analyze how the network behaves under all possible values for these constants, turn them into inputs::

            >>> constants = find_constants(primes)
            >>> create_inputs(primes, constants)

    **arguments**:
        * *primes*: prime implicants
        * *names*: variables to become constants
        * *in_place*: change *primes* in place or copy and return

    **returns**:
        * *new_primes* if *in_place == False*

    **example**::

        >>> names = ["p21", "p53"]
        >>> create_inputs(primes, names)
    """

    if not in_place:
        primes = copy(primes)

    for name in names:
        primes[name][0] = [{name: 1}]
        primes[name][1] = [{name: 0}]

    if not in_place:
        return primes


def create_blinkers(primes: dict, names: List[str], in_place: bool = True) -> Optional[dict]:
    """
    Creates a blinker for every member of *names*.
    Variables that alrerady exist in *primes* are overwritten.
    A blinker is a variable with in-degree one and negative auto-regulation.
    Blinkers can therefore change their activity in every state of the transition system.

    .. note::
        Suppose that a given network has a lot of inputs, e.g.::

            >>> len(find_inputs(primes))
            20

        Since input combinations define trap spaces, see e.g. :ref:`Klarner2015(b) <klarner2015approx>` Sec. 5.1,
        all of which contain at least one minimal trap space,
        it follows that the network has at least 2^20 minimal trap spaces - too many to enumerate.
        To find out how non-input variables stabilize in minimal trap spaces turn the inputs into blinkers::

            >>> inputs = find_inputs(primes)
            >>> create_blinkers(primes, inputs)
            >>> tspaces = trap_spaces(primes, "min")

    **arguments**:
        * *primes*: prime implicants
        * *names*: variables to become blinkers
        * *in_place*: change *Primes* in place or copy and return

    **returns**:
        * *new_primes* if *in_place == True*

    **example**::

        >>> names = ["p21", "p53"]
        >>> create_blinkers(primes, names)
    """

    if not in_place:
        primes = copy(primes)

    for name in names:
        primes[name][0] = [{name:1}]
        primes[name][1] = [{name:0}]

    if not in_place:
        return primes


def create_variables(primes: dict, update_functions: Dict[str, Union[callable, str]], in_place: bool = True) -> Optional[dict]:
    """
    Creates the variables defined in *update_functions* and add them to *primes*.
    Variables that already exist in *primes* are overwritten.
    Raises an exception if the resulting primes contain undefined variables.
    The *update_functions* are given as a dictionary of names and functions that are either a bnet string or a Python callable.

    **arguments**:
        * *primes*: prime implicants
        * *update_functions*: a dictionary of names and update functions
        * *in_place*: change *Primes* in place or copy and return

    **returns**:
        * *new_primes* if *in_place == False*

    **example**::

        >>> primes = bnet2primes("A, A")
        >>> create_variables(primes, {"B": "A"})
        >>> create_variables(primes, {"C": lambda A, B: A and not B})
        >>> primes2bnet(primes)
        A, A
        B, A
        C, A&!B
    """

    if not in_place:
        primes = copy(primes)

    new_primes = {}
    dependencies = set([])
    names = set(primes)

    for name, function in update_functions.items():
        names.add(name)
        if type(function) is str:
            line = f"{name}, {function}"
            new_primes[name] = bnet2primes(line)[name]
        else:
            new_primes[name] = functions2primes({name: function})[name]

        for x in new_primes[name][1]:
            dependencies.update(set(x))

    undefined = dependencies - names
    if undefined:
        log.error(f"can not add variables that depend on undefined variables: undefined={undefined}")
        sys.exit()

    primes.update(new_primes)

    if not in_place:
        return primes


def create_disjoint_union(primes1: dict, primes2: dict) -> dict:
    """
    Creates a new primes dictionary that is the disjoint union of the networks represented by *primes1* and *primes2*.
    Here, "disjoint" means that the names of *primes1* and *primes2* must not intersect.

    **arguments**:
        * *primes1*: prime implicants
        * *primes2*: prime implicants

    **returns**:
        * *new_primes*: the disjoint union of *primes1* and *primes2*

    **example**::

        >>> primes1 = bnet2primes("A, B \\n B, A")
        >>> primes1 = bnet2primes("C, D \\n D, E")
        >>> new_primes = create_disjoint_union(primes1, primes2)
        >>> primes2bnet(new_primes)
        A, B
        B, A
        C, D
        D, E
    """

    intersection = set(primes1).intersection(set(primes2))
    if intersection:
        log.error(f"cannot take disjoint union of primes: intersection={intersection}")
        sys.exit()

    new_primes = {}
    new_primes.update(primes1)
    new_primes.update(primes2)

    return new_primes


def remove_variables(primes: dict, names: List[str], in_place: bool = True) -> Optional[dict]:
    """
    Removes all variables contained in *names* from *primes*.
    Members of *names* that are not in *primes* are ignored.
    Note that *names* must be closed under the successors relation, i.e.,
    it must be a set of variables that contains all its successors.

    **arguments**:
        * *primes*: prime implicants
        * *names*: the names of variables to remove
        * *in_place*: change *Primes* in place or copy and return

    **returns**:
        * *new_primes* if *in_place == False*

    **example**::

        >>> names = ["PKC", "GADD45", "ELK1", "FOS"]
        >>> remove_variables(primes, names)
    """

    if not in_place:
        primes = copy(primes)

    igraph = primes2igraph(primes)
    hit = [x for x in successors(igraph, names) if x not in names]
    if hit:
        log.error(f"can not remove variable that are not closed under successor operation: variables={hit}")
        sys.exit()
    else:
        for name in names:
            primes.pop(name)

    if not in_place:
        return primes


def remove_all_variables_except(primes: dict, names: List[str], in_place: bool = True) -> Optional[dict]:
    """
    Removes all variables except those in *names* from *primes*.
    Members of *names* that are not in *primes* are ignored.
    Note that *names* must be closed under the predecessors relation, i.e.,
    it must be a set of variables that contains all its predecessors.

    **arguments**:
        * *primes*: prime implicants
        * *names*: the names of variables to keep
        * *in_place*: change *primes* in place or copy and return

    **returns**:
        * *new_primes* if *in_place == False*

    **example**::

        >>> names = ["PKC", "GADD45", "ELK1", "FOS"]
        >>> remove_all_variables_except(primes, names)
    """

    if not in_place:
        primes = copy(primes=primes)

    igraph = primes2igraph(primes)
    hit = [x for x in predecessors(igraph, names) if x not in names]
    if hit:
        log.error(f"cannot remove variables that are not closed under the predecessor operation: variables={hit}")
        sys.exit()

    else:
        for name in list(primes):
            if name not in names:
                primes.pop(name)

    if not in_place:
        return primes


def rename_variable(primes: dict, old_name: str, new_name: str, in_place: bool = True) -> Optional[dict]:
    """
    Renames a single component, i.e., replace every occurence of *old_name* with *new_name*.
    Throws an exception if *new_name* is already contained in *primes*.

    **arguments**:
        * *primes*: prime implicants
        * *old_name*: the old name of the component
        * *new_name*: the new name of the component
        * *in_place*: change *primes* in place or copy and return

    **returns**:
        * *new_primes* if *in_place == False*

    **example**::

        >>> names = ["PKC", "GADD45", "ELK1", "FOS"]
        >>> remove_all_variables_except(primes, names)
    """

    if not in_place:
        primes = copy(primes)

    if old_name==new_name:
        return

    if new_name in primes:
        log.error(f"cannot rename variable because name is already in use: name={new_name}")
        sys.exit()

    else:
        primes[new_name] = primes.pop(old_name)
        for name in primes:
            for value in [0,1]:
                for prime in primes[name][value]:
                    if old_name in prime:
                        prime[new_name] = prime.pop(old_name)

    if not in_place:
        return primes


def _substitute(primes: dict, name: str, constants: Dict[str, int]):
    """
    replaces the primes of *name* by the ones obtained from substituting *constants*.
    """

    for value in [0, 1]:
        new_primes = []
        for prime in primes[name][value]:
            consistent, inconsistent = [], []
            for k in constants:
                if k in prime:
                    if prime[k]==constants[k]:
                        consistent.append(k)
                    else:
                        inconsistent.append(k)

            if inconsistent:
                continue
            else:
                for k in consistent: prime.pop(k)
                if prime=={}:
                    new_primes = [{}]
                    break
                elif prime not in new_primes:
                    new_primes.append(prime)

        primes[name][value] = new_primes


def substitute_and_remove(primes, names, in_place: bool = True):
    """
    Substitutes the values of all *names* to its successors and then removes them.
    Checks that *names* are a subset of constants.
    Note that the resulting primes may contain new constants.

    **arguments**:
        * *primes*: prime implicants
        * *names*: variables to be substituted and removed
        * *in_place*: change *Primes* in place or copy and return

    **returns**:
        * *new_primes* if *in_place == False*

    **example**::

        >>> substitute_and_remove(primes)
    """

    if not in_place:
        primes = copy(primes)

    constants = find_constants(primes)

    not_in_constants = [x for x in names if x not in constants]
    if not_in_constants:
        log.error(f"cannot substitute and remove non-constant components: names={not_in_constants}")
        sys.exit()

    names = {k: v for k, v in constants.items() if k in names}

    igraph = primes2igraph(primes)
    for x in successors(igraph, names):
        _substitute(primes, x, names)

    for x in names:
        primes.pop(x)

    if not in_place:
        return primes


def percolation(primes: dict, remove_constants: bool) -> Dict[str, int]:
    """
    Percolates the values of constants, see :ref:`Klarner2015(b) <klarner2015approx>` Sec. 3.1 for a formal definition.
    Use *remove_constants* to determine whether constants should be kept in the remaining network or whether you want to remove them.

    **arguments**:
        * *primes*: prime implicants
        * *remove_constants*: whether constants should be kept

    **returns**:
        * *constants*: names and values of variables that became constants due to the percolation

    **example**::

        >>> percolate_constants(primes)
        >>> constants = percolate_constants(primes, True)
        >>> constants
        {"Erk":0, "Mapk":0, "Raf":1}
    """

    igraph = primes2igraph(primes)
    constants = find_constants(primes)
    fringe = successors(igraph, constants)

    while fringe:
        new_constants = {}
        for name in fringe:
            _substitute(primes, name, constants)
            if primes[name] == CONSTANT_ON:
                new_constants[name] = 1
            elif primes[name] == CONSTANT_OFF:
                new_constants[name] = 0

        constants.update(new_constants)
        fringe = set(successors(igraph, new_constants)) - set(constants)

    if remove_constants:
        for name in constants: primes.pop(name)

    return constants


def percolate_and_keep_constants(primes: dict):
    """
    Percolates the values of constants, see :ref:`Klarner2015(b) <klarner2015approx>` Sec. 3.1 for a formal definition.
    Keeps constants in the *primes*.

    **arguments**:
        * *primes*: prime implicants

    **returns**:
        * *constants*: names and values of the constants

    **example**::

        >>> constants = percolate_and_keep_constants(primes)
        >>> constants
        {"Erk":0, "Mapk":0, "Raf":1}
    """

    return percolation(primes, remove_constants=False)


def percolate_and_remove_constants(primes: dict) -> Dict[str, int]:
    """
    Percolates the values of constants, see :ref:`Klarner2015(b) <klarner2015approx>` Sec. 3.1 for a formal definition.
    Removes constants from the *primes*.

    **arguments**:
        * *primes*: prime implicants

    **returns**:
        * *constants*: names and values of the constants

    **example**::

        >>> constants = percolate_and_remove_constants(primes)
        >>> constants
        {"Erk":0, "Mapk":0, "Raf":1}
    """

    return percolation(primes, remove_constants=True)


def input_combinations(primes: dict, format: str = "dict") -> Union[List[str], List[dict]]:
    """
    A generator for all possible input combinations of *primes*.
    Returns the empty dictionary if there are no inputs.

    **arguments**:
        * *primes*: prime implicants
        * *format*: format of returned subspaces, "str" or "dict"

    **returns**:
        * *subspaces*: input combination in desired format

    **example**::

        >>> for x in input_combinations(primes, "str"): print(x)
        0--0--
        0--1--
        1--0--
        1--1--
    """

    if not format in ["str", "dict"]:
        log.error(f"format must be in ['str', 'dict']: format={format}")
        sys.exit()

    inputs = find_inputs(primes)

    subspaces = []
    if inputs:
        if format == "dict":
            for x in itertools.product(*len(inputs)*[[0,1]]):
                subspaces.append(dict(zip(inputs,x)))

        else:
            for x in itertools.product(*len(inputs)*[[0,1]]):
                x = dict(zip(inputs,x))
                x = subspace2str(primes, x)
                subspaces.append(x)

    return subspaces


def active_primes(primes: dict, subspace: Dict[str, int]) -> Dict[str, List[List[dict]]]:
    """
    returns all primes that are active in, i.e., consistent with *subspace*.
    """

    active_primes = dict((name, [[], []]) for name in primes)

    for name in primes:
        for v in [0,1]:
            for p in primes[name][v]:
                if name in subspace:
                    if subspace[name] == v:
                        if dicts_are_consistent(p, subspace):
                            active_primes[name][v].append(dict(p))
                else:
                    if dicts_are_consistent(p, subspace):
                        active_primes[name][v].append(dict(p))

    return active_primes
