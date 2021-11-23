

import itertools
import logging
import sys
from typing import List, Optional, Dict, Union, Iterable

from pyboolnet.boolean_normal_forms import functions2primes, get_dnf
from pyboolnet.external.bnet2primes import bnet_text2primes
from pyboolnet.helpers import dicts_are_consistent
from pyboolnet.state_space import subspace2str

log = logging.getLogger(__name__)

CONSTANT_ON = [[], [{}]]
CONSTANT_OFF = [[{}], []]


def is_constant(primes: dict, name: str) -> bool:
    """
    Decides whether *name* is a constant in *primes*.

    **arguments**:
        * *primes*: prime implicants
        * *name*: the component

    **returns**:
        * *constant*: whether *name* is constant

    **example**::

        >>> is_constant(primes, "MEK")
        False
    """

    return primes[name][1] in [[], [{}]]



def get_constant_primes(value: int) -> List[List[dict]]:
    """
    Gets the prime implicants for a constant of give *value*.

    **arguments**:
        * *value*: either 0 or 1

    **returns**:
        * *implicants*: the implicants

    **example**::

        >>> primes[name] = get_constant_primes(value=1)
    """

    if value:
        return [[], [{}]]
    return [[{}], []]


def copy_primes(primes: dict) -> dict:
    """
    Creates a copy of *primes*.

    **arguments**:
        * *primes*: prime implicants

    **returns**:
        * *new_primes*: a copy of *primes*

    **example**::

        >>> new_primes = copy_primes(primes)
    """

    new_primes = {}
    for name in primes:
        new_primes[name] = [[], []]

        for value in [0, 1]:
            for prime in primes[name][value]:
                new_primes[name][value].append(dict(prime))

    return new_primes


def primes_are_equal(primes1: dict, primes2: dict) -> bool:
    """
    Tests whether *primes1* and *primes2* are equal.
    The dictionary comparison *primes1 == primes2* does in general not work because the clauses of each may not be in the same order.

    **arguments**:
        * *primes1*, *primes2*: prime implicants

    **returns**:
        * *answer*: whether *primes1 == primes2*

    **example**::

        >>> primes_are_equal(primes1, primes2)
        True
    """

    if set(primes1) != set(primes2):
        return False

    for name in primes1:
        for value in [0, 1]:
            if sorted([sorted(d.items()) for d in primes1[name][value]]) != sorted([sorted(d.items()) for d in primes2[name][value]]):
                return False

    return True


def find_inputs(primes: dict) -> List[str]:
    """
    Finds all inputs in the network defined by *primes*.

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
    Finds all outputs in the network defined by *primes*.

    **arguments**:
        * *primes*: prime implicants

    **returns**:
        * *names*: the names of the outputs

    **example**::

        >>> find_inputs(primes)
        ["Proliferation","Apoptosis","GrowthArrest"]
    """

    return sorted(name for name in primes if not find_successors(primes=primes, sources=[name]))


def find_successors(primes: dict, sources: Iterable[str]) -> List[str]:
    """
    Finds all successors of *sources* in *primes*.

    **arguments**:
        * *primes*: prime implicants
        * *sources*: compute successors of these nodes

    **returns**:
        * *successors*: the successors

    **example**::

        >>> find_successors(primes)
        ["ERK", "MEK", "RAF"]
    """

    successors = []
    sources = set(sources)

    for name in primes:
        for prime in primes[name][1]:
            if set(prime).intersection(sources):
                successors.append(name)
                break

    return successors


def find_predecessors(primes: dict, targets: Iterable[str]) -> List[str]:
    """
    Finds all predecessors of *targets* in *primes*.

    **arguments**:
        * *primes*: prime implicants
        * *targets*: compute predecessors of these nodes

    **returns**:
        * *predecessors*: the predecessors

    **example**::

        >>> find_predecessors(primes)
        ["ERK", "MEK", "RAF"]
    """

    return sorted({k for target in targets for prime in primes[target][1] for k in prime})


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


def create_constants(primes: dict, constants: Dict[str, int], copy: bool = False) -> Optional[dict]:
    """
    Creates a constant in *primes* for every name, value pair in *constants*.
    Names that already exist in *primes* are overwritten.

    **arguments**:
        * *primes*: prime implicants
        * *constants*: names and values
        * *copy*: change *primes* in place or copy and return

    **returns**:
        * *new_primes* if *copy == True*

    **example**::

        >>> create_constants(primes, {"p53":1, "p21":0})
    """

    if copy:
        primes = copy_primes(primes=primes)

    for name, value in constants.items():
        primes[name] = get_constant_primes(value=value)

    if copy:
        return primes


def create_inputs(primes: dict, names: Iterable[str], copy: bool = False) -> Optional[dict]:
    """
    Creates an input for every member of *names*.
    Variables that already exist in *primes* are overwritten.

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
        * *copy*: change *primes* in place or copy and return

    **returns**:
        * *new_primes* if *copy == True*

    **example**::

        >>> names = ["p21", "p53"]
        >>> create_inputs(primes, names)
    """

    if copy:
        primes = copy_primes(primes)

    for name in names:
        primes[name][0] = [{name: 1}]
        primes[name][1] = [{name: 0}]

    if copy:
        return primes


def create_blinkers(primes: dict, names: Iterable[str], copy: bool = False) -> Optional[dict]:
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
        * *copy*: change *primes* in place or copy and return

    **returns**:
        * *new_primes* if *copy == True*

    **example**::

        >>> names = ["p21", "p53"]
        >>> create_blinkers(primes, names)
    """

    if copy:
        primes = copy_primes(primes)

    for name in names:
        primes[name][0] = [{name:1}]
        primes[name][1] = [{name:0}]

    if copy:
        return primes


def create_variables(primes: dict, update_functions: Dict[str, Union[callable, str]], copy: bool = False) -> Optional[dict]:
    """
    Creates the variables defined in *update_functions* and add them to *primes*.
    Variables that already exist in *primes* are overwritten.
    Raises an exception if the resulting primes contain undefined variables.
    The *update_functions* are given as a dictionary of names and functions that are either a bnet string or a Python callable.

    **arguments**:
        * *primes*: prime implicants
        * *update_functions*: a dictionary of names and update functions
        * *copy*: change *primes* in place or copy and return

    **returns**:
        * *new_primes* if *copy == True*

    **example**::

        >>> primes = bnet2primes("A, A")
        >>> create_variables(primes, {"B": "A"})
        >>> create_variables(primes, {"C": lambda A, B: A and not B})
        >>> primes2bnet(primes)
        A, A
        B, A
        C, A&!B
    """

    if copy:
        primes = copy_primes(primes)

    new_primes = {}
    dependencies = set([])
    names = set(primes)

    for name, function in update_functions.items():
        names.add(name)
        if type(function) is str:
            new_primes[name] = bnet_text2primes(text=f"{name}, {function}")[name]
        else:
            new_primes[name] = functions2primes({name: function})[name]

        for x in new_primes[name][1]:
            dependencies.update(set(x))

    undefined = dependencies - names
    if undefined:
        log.error(f"can not add variables that depend on undefined variables: undefined={undefined}")
        sys.exit()

    primes.update(new_primes)

    if copy:
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
        >>> primes2 = bnet2primes("C, D \\n D, E")
        >>> primes = create_disjoint_union(primes1, primes2)
        >>> primes2bnet(primes)
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


def remove_variables(primes: dict, names: Iterable[str], copy: bool = False) -> Optional[dict]:
    """
    Removes all variables contained in *names* from *primes*.
    Members of *names* that are not in *primes* are ignored.
    Note that *names* must be closed under the successors relation, i.e.,
    it must be a set of variables that contains all its successors.

    **arguments**:
        * *primes*: prime implicants
        * *names*: the names of variables to remove
        * *copy*: change *primes* in place or copy and return

    **returns**:
        * *new_primes* if *copy == True*

    **example**::

        >>> names = ["PKC", "GADD45", "ELK1", "FOS"]
        >>> remove_variables(primes, names)
    """

    if copy:
        primes = copy_primes(primes)

    hit = [x for x in find_successors(primes=primes, sources=names) if x not in names]
    if hit:
        log.error(f"can not remove variable that are not closed under successor operation: variables={hit}")
        sys.exit()
    else:
        for name in names:
            primes.pop(name)

    if copy:
        return primes


def remove_all_variables_except(primes: dict, names: Iterable[str], copy: bool = False) -> Optional[dict]:
    """
    Removes all variables except those in *names* from *primes*.
    Members of *names* that are not in *primes* are ignored.
    Note that *names* must be closed under the predecessors relation, i.e.,
    it must be a set of variables that contains all its predecessors.

    **arguments**:
        * *primes*: prime implicants
        * *names*: the names of variables to keep
        * *copy*: change *primes* in place or copy and return

    **returns**:
        * *new_primes* if *copy == True*

    **example**::

        >>> names = ["PKC", "GADD45", "ELK1", "FOS"]
        >>> remove_all_variables_except(primes, names)
    """

    if copy:
        primes = copy_primes(primes=primes)

    hit = [x for x in find_predecessors(primes=primes, targets=names) if x not in names]

    if hit:
        log.error(f"cannot remove variables that are not closed under the predecessor operation: variables={hit}")
        sys.exit()

    else:
        for name in list(primes):
            if name not in names:
                primes.pop(name)

    if copy:
        return primes


def rename_variable(primes: dict, old_name: str, new_name: str, copy: bool = False) -> Optional[dict]:
    """
    Renames a single component, i.e., replace every occurence of *old_name* with *new_name*.
    Throws an exception if *new_name* is already contained in *primes*.

    **arguments**:
        * *primes*: prime implicants
        * *old_name*: the old name of the component
        * *new_name*: the new name of the component
        * *copy*: change *primes* in place or copy and return

    **returns**:
        * *new_primes* if *copy == True*

    **example**::

        >>> names = ["PKC", "GADD45", "ELK1", "FOS"]
        >>> remove_all_variables_except(primes, names)
    """

    if copy:
        primes = copy_primes(primes)

    if old_name == new_name:
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

    if copy:
        return primes


def remove_all_constants(primes: dict, copy: bool = False) -> Optional[dict]:
    """
    Removes all constants from *primes*.

    **arguments**:
        * *copy*: change *primes* in place or copy and return

    **returns**:
        * *new_primes* if *copy == True*

    **example**::

        >>> remove_all_constants(primes)
    """

    return remove_variables(primes=primes, names=find_constants(primes=primes), copy=copy)


def update_primes(primes: dict, name: str, constants: dict, copy: bool = False) -> Optional[dict]:
    """
    Applies the *constants* to the component *name* of *primes*.
    Updates the primes of the component *name* given the *constants* and returns the new prime implicants.

    **arguments**:
        * *primes*: prime implicants
        * *name*: name of the component to update
        * *constants*: the assumed constants
        * *copy*: change *primes* in place or copy and return

    **returns**:
        * *new_primes* if *copy == True*

    **example**::

        >>> primes["ERK"] = update_primes(primes, name="ERK", subspace={"MEK": 1, "RAF": 0})
    """

    if copy:
        primes = copy_primes(primes=primes)

    items = set(constants.items())
    items_negated = set((k, 1-v) for k, v in constants.items())
    implicants = [[], []]

    hit = False
    for value in [0, 1]:
        if hit:
            break

        for prime in primes[name][value]:
            prime_items = set(prime.items())
            if prime_items.intersection(items_negated):
                continue

            remainder = prime_items.difference(items)
            if not remainder:
                primes[name] = get_constant_primes(value=value)
                hit = True
                break

            implicants[value].append(dict(remainder))

    if not hit:
        dnf = get_dnf(one_implicants=implicants[1])
        unique_name = "kev034uf034hgu4hg9oef393"
        primes[name] = bnet_text2primes(text=f"{unique_name}, {dnf}")[unique_name]

    if copy:
        return primes


def percolate(primes: dict, add_constants: Optional[Dict[str, int]] = None, remove_constants: bool = False, max_iterations: Optional[int] = None, copy: bool = False) -> Optional[dict]:
    """
    Detects constants in primes and percolates their values in *primes*.
    Does not remove any components from *primes*.

    **arguments**:
        * *primes*: prime implicants
        * *max_iterations*: max number of percolation steps
        * *remove_constants*: whether to remove all constants
        * *copy*: change *primes* in place or copy and return

    **returns**:
        * *new_primes* if *copy == True*

    **example**::

        >>> new_primes = percolate(primes, copy=True)
    """

    if copy:
        primes = copy_primes(primes=primes)

    if add_constants:
        create_constants(primes=primes, constants=add_constants)

    constants = find_constants(primes=primes)
    successors = set(find_successors(primes=primes, sources=constants))
    max_iterations = max_iterations or len(primes) + 1
    iterations = 0

    while successors and iterations < max_iterations:
        name = successors.pop()
        current_successors = set(find_successors(primes=primes, sources=[name]))
        update_primes(primes=primes, name=name, constants=constants)

        if is_constant(primes=primes, name=name):
            iterations += 1
            successors.update(current_successors)
            constants[name] = 1 if primes[name][1] else 0

    if remove_constants:
        remove_all_constants(primes=primes)

    if copy:
        return primes


def list_input_combinations(primes: dict, format: str = "dict") -> Union[List[str], List[dict]]:
    """
    A generator for all possible input combinations of *primes*.
    Returns the empty dictionary if there are no inputs.

    **arguments**:
        * *primes*: prime implicants
        * *format*: format of returned subspaces, "str" or "dict"

    **returns**:
        * *subspaces*: input combination in desired format

    **example**::

        >>> for x in list_input_combinations(primes, "str"): print(x)
        0--0--
        0--1--
        1--0--
        1--1--
    """

    if format not in ["str", "dict"]:
        log.error(f"format must be in ['str', 'dict']: format={format}")
        sys.exit()

    inputs = find_inputs(primes)
    if not inputs:
        return [{}]

    subspaces = []
    if format == "dict":
        for x in itertools.product(*len(inputs) * [[0, 1]]):
            subspaces.append(dict(zip(inputs, x)))

    else:
        for x in itertools.product(*len(inputs) * [[0, 1]]):
            x = dict(zip(inputs, x))
            x = subspace2str(primes, x)
            subspaces.append(x)

    return subspaces


def active_primes(primes: dict, subspace: Dict[str, int]) -> Dict[str, List[List[dict]]]:
    """
    returns all primes that are active in, i.e., consistent with *subspace*.
    """

    active_primes = dict((name, [[], []]) for name in primes)

    for name in primes:
        for v in [0, 1]:
            for p in primes[name][v]:
                if name in subspace:
                    if subspace[name] == v:
                        if dicts_are_consistent(p, subspace):
                            active_primes[name][v].append(dict(p))
                else:
                    if dicts_are_consistent(p, subspace):
                        active_primes[name][v].append(dict(p))

    return active_primes
