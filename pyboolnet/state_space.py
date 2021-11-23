

import itertools
import random
from typing import Union, List, Dict

from pyboolnet.external.bnet2primes import bnet_text2primes

VAN_HAM_EXTENSIONS = {3: ["_medium", "_high"],
                      4: ["_level1", "_level2", "_level3"],
                      5: ["_level1", "_level2", "_level3", "_level4"]}


def find_vanham_variables(primes: dict) -> Dict[int, List[str]]:
    """
    Detects variables that represent multi-valued variables using the Van Ham encoding, see :ref:`Didier2011` for more details.
    E.g. three-valued variables x are encoded via two Boolean variables x_medium and x_high.
    This function is used for example by :ref:`ModelChecking.primes2smv <primes2smv>` to add
    INIT constraints to the smv file that forbid all states that are not admissible, e.g. in which "!x_medium & x_high" is true.

    **arguments**:
        * *primes*: prime implicants

    **returns**:
        * *names*: activity levels and names

    **example**::

        >>> find_vanham_variables(primes)
        {2: ['E2F1', 'ATM'],
         3: ['ERK'],
         4: [],
         5: []}
    """

    seen_base = []
    seen_names = []
    vanham = {}

    for val in sorted(VAN_HAM_EXTENSIONS, reverse=True):
        post = VAN_HAM_EXTENSIONS[val][0]
        base = [x.replace(post, "") for x in primes if x.endswith(post)]
        base = [x for x in base if x not in seen_base]
        base = [x for x in base if all(x + y in primes for y in VAN_HAM_EXTENSIONS[val])]
        names = [x + y for x in base for y in VAN_HAM_EXTENSIONS[val]]

        vanham[val] = sorted(base)
        seen_base.extend(base)
        seen_names.extend(names)

    vanham[2] = sorted(x for x in primes if x not in seen_names)

    return vanham


def state_is_in_subspace(primes: dict, state: Union[str, dict], subspace: Union[str, dict]) -> bool:
    """
    Checks whether *state* is a state in *subspace*.

    **arguments**:
        * *primes*: prime implicants
        * *state*: a state
        * *subspace*: a subspace

    **returns**:
        * *answer*: whether *state* is a state in *subspace*

    **example**::

          >>> state_is_in_subspace(primes, state, subspace)
          False
    """

    if type(state) is str:
        state = state2dict(primes, state)

    if type(subspace) is str:
        subspace = subspace2dict(primes, subspace)

    for k in subspace:
        if state[k] != subspace[k]:
            return False

    return True


def is_subspace(primes: dict, this: Union[dict, str], other: [dict, str]) -> bool:
    """
    Checks whether *this* is a subspace of *other*.

      **arguments**:
        * *primes*: prime implicants
        * *this*: a subspace
        * *other*: a subspace

      **returns**:
        * *answer*: whether *this* is subspace of *other*

      **example**::

        >>> is_subspace(primes, this=sub1, other=sub2)
        True
    """

    if type(this) is str:
        this = subspace2dict(primes, this)

    if type(other) is str:
        other = subspace2dict(primes, other)

    return set(this.items()).issuperset(set(other.items()))


def hamming_distance(this: dict, other: dict) -> int:
    """
    Returns the Hamming distance between to subspaces.
    Variables that are free in either subspace are ignored.

    **arguments**:
        * *this, other*: subspaces in dictionary representation

    **returns**:
        * *distance*: the distance between *Subspace1* and *Subspace2*

    **example**:

        >>> hamming_distance({"v1":0,"v2":0}, {"v1":1,"v2":1})
        2
        >>> hamming_distance({"v1":1}, {"v2":0})
        0
    """

    return len([k for k, v in this.items() if k in other and other[k] != v])


def bounding_box(primes: dict, subspaces: List[Union[dict, str]]) -> Dict[str, int]:
    """
    Returns the smallest subspace that contains the union of *subspaces*.

    **arguments**:
        * *primes*: prime implicants

    **returns**:
        * *box*: the smallest subspace that contains the union of *subspaces*

    **example**:

        >>> subspaces = [{"v1": 0, "v2": 0}, {"v1": 1, "v2": 0})]
        >>> bounding_box(primes, subspaces)
        {"v2": 0}
    """

    seen = set([])
    box = {}

    for subspace in subspaces:
        if type(subspace) is str:
            subspace = subspace2dict(primes, subspace)

        for name in subspace:
            if name in seen:
                continue

            if name in box:
                if box[name] != subspace[name]:
                    seen.add(name)
                    box.pop(name)
            else:
                box[name] = subspace[name]

    return box


def size_state_space(primes: dict, van_ham: bool = True, fixed_inputs: bool = False):
    """
    This function computes the number of states in states space of *primes*.
    Detects if there are variables that encode multi-valued variables via the Van Ham encoding.
    Variables that have the same name module the Van Ham extension (see example below) are identified.
    E.g. the state space of x_medium, x_high is 3 instead of 4 since "!x_medium & x_high" is not an admissible state, see :ref:`Didier2011` for more details.


    **arguments**:
        * *primes*: prime implicants
        * *van_ham*: exclude states that are not admissible in Van Ham encoding
        * *fixed_inputs*: return number of states for single input combination

    **returns**:
        * *size*: number of states

    **example**::

        >>> StateTransitionGraphs.VAN_HAM_EXTENSIONS
        ["_medium", "_high", "_level1", "_level2", "_level3", "_level4", "_level5"]
        >>> size_state_space(primes, van_ham=False)
        256
        >>> size_state_space(primes)
        192
        >>> size_state_space(primes, fixed_inputs=True)
        96
    """

    if van_ham:
        vanham = find_vanham_variables(primes)

        size = 1
        for x in vanham:
            size *= x ** (len(vanham[x]))
    else:
        size = 2 ** len(primes)

    if fixed_inputs:
        factor = 2 ** len(_find_inputs(primes))
        size = size / factor

    return size


def _find_inputs(primes: dict) -> List[str]:
    """
    A copy of pyboolnet.prime_implicants.find_inputs.
    Required to break circular import.
    """

    return sorted(name for name in primes if primes[name][1] == [{name: 1}])


def enumerate_states(primes: dict, proposition: str):
    """
    Generates all states that are referenced by *proposition* in the context of the variables given by *primes*.
    The syntax of *proposition* should be as in bnet files and TRUE and FALSE in will be treated as 1 and 0.

    .. note::
        This function uses :ref:`bnet2primes <bnet2primes>` and :ref:`list_states_in_subspace <list_states_in_subspace>` to enumerate
        the states referenced by an expression. The efficiency of this approach can decreases a lot starting from around 15 variables
        that appear in *proposition*.

    **arguments**:
        * *primes*: prime implicants
        * *proposition*: a propositional formula

    **returns**:
        * *states*: the referenced states in str format

    **example**:

        >>> prop = "!Erk | (Raf & Mek)"
        >>> enumerate_states(primes,prop)[0]
        "010"
    """

    assert "?" not in primes

    proposition = proposition.replace("TRUE", "1")
    proposition = proposition.replace("FALSE", "0")
    new_primes = bnet_text2primes(text=f"?, {proposition}")

    states = set([])
    for p in new_primes["?"][1]:
        states.update(set(list_states_in_subspace(primes, p)))

    return list(states)


def list_states_in_subspace(primes: dict, subspace):
    """
    Generates all states contained in *subspace*.

    **arguments**:
        * *primes*: prime implicants or a list of names
        * *subspace*: a subspace

    **returns**:
        * *states*: the states contained in *subspace*

    **example**:

        >>> subspace = "1-1"
        >>> list_states_in_subspace(primes,subspace)
        ['101','111']
    """

    if type(subspace) == str:
        subspace = subspace2dict(primes, subspace)
    else:
        assert (type(subspace) == dict)
        assert (set(subspace).issubset(set(primes)))

    ranges = [[subspace[x]] if x in subspace else [0, 1] for x in sorted(primes)]

    states = []
    for values in itertools.product(*ranges):
        states.append("".join(map(str, values)))

    return states


def subspace2dict(primes: dict, subspace):
    """
    Converts the string representation of a subspace into the dictionary representation of a subspace.
    Use "-" to indicate free variables.
    If *subspace* is already of type *dict* it is simply returned.

    **arguments**
        * *primes*: prime implicants or a list of names
        * *subspace*: a subspace

    **returns**
        * *subspace*: the dictionary representation of subspace

    **example**::

        >>> sub = "-01"
        >>> subspace2dict(primes, sub)
        {'v2':0, 'v3':1}
    """

    if type(subspace) is dict:
        return subspace

    return dict([(name, int(value)) for name, value in zip(sorted(primes), subspace) if not value == "-"])


def subspace2str(primes: dict, subspace):
    """
    Converts the dictionary representation of a subspace into the string representation of a subspace.
    Uses "-" to indicate free variables.
    If *subspace* is already of type *str* it is simply returned.

    **arguments**
        * *primes*: prime implicants or a list of names
        * *subspace*: a subspace

    **returns**
        * *subspace*: the string representation of *subspace*

    **example**::

        >>> sub = {"v2":0, "v3":1}
        >>> subspace2str(primes, sub)
        '-01'
    """

    if type(subspace) is str:
        assert len(subspace) == len(primes)
        return subspace

    assert type(subspace) is dict
    assert set(subspace).issubset(set(primes))

    return "".join([str(subspace[x]) if x in subspace else "-" for x in sorted(primes)])


def states2dict(primes: dict, states: List[str]) -> List[dict]:
    """
    Converts the string representation of a list of states into the dictionary representations.
    If *state* is already of type *dict* it is simply returned.

    **arguments**
        * *primes*: prime implicants or a list of names
        * *states*: string representation of states

    **returns**
        * *states*: dictionary representation of states

    **example**::

        >>> states = ["101", "100"]
        >>> states2dict(primes, state)
        [{'v2':0, 'v1':1, 'v3':1},{'v2':0, 'v1':1, 'v3':0}]
    """

    return [state2dict(primes, x) for x in states]


def state2dict(primes: dict, state) -> dict:
    """
    Converts the string representation of a state into the dictionary representation of a state.
    If *state* is already of type *dict* it is simply returned.

    **arguments**
        * *primes*: prime implicants or a list of names
        * *state*: string representation of state

    **returns**
        * *state*: dictionary representation of state

    **example**::

        >>> state = "101"
        >>> state2dict(primes, state)
        {'v2':0, 'v1':1, 'v3':1}

    """

    if type(state) is dict:
        assert set(state) == set(primes)
        return state

    assert len(state) == len(primes)

    return dict((k, int(v)) for k, v in zip(sorted(primes), state))


def states2str(primes: dict, states: List[dict]) -> List[str]:
    """
    Converts the string representation of a list of states into the dictionary representations.
    If *state* is already of type *dict* it is simply returned.

    **arguments**
        * *primes*: prime implicants or a list of names
        * *states*: dictionary representation of states

    **returns**
        * *states*: string representation of states

    **example**::

        >>> states = [{'v2':0, 'v1':1, 'v3':1},{'v2':0, 'v1':1, 'v3':0}]
        >>> states2str(primes, state)
        ["101", "100"]
    """

    return [state2str(x) for x in states]


def state2str(state: Union[dict, str]) -> str:
    """
    Converts the dictionary representation of a state into the string representation of a state.
    If *state* is already of type string it is simply returned.

    **arguments**
        * *state*: dictionary representation of state

    **returns**
        * *state*: string representation of state

    **example**::

        >>> state = {"v2":0, "v1":1, "v3":1}
        >>> state2str(primes, state)
        '101'
    """

    if type(state) is str:
        return state

    return "".join([str(state[x]) for x in sorted(state)])


def random_state(primes: dict, subspace: Union[dict, str] = {}) -> dict:
    """
    Generates a random state of the transition system defined by *primes*.
    If *subspace* is given then the state will be drawn from that subspace.

    **arguments**:
        * *primes*: prime implicants
        * *subspace*: a subspace

    **returns**:
        * *state*: random state inside *subspace*

    **example**::

        >>> random_state(primes)
        {'v1':1, 'v2':1, 'v3':1}
        >>> random_state(primes, {"v1":0})
        {'v1':0, 'v2':1, 'v3':0}
        >>> random_state(primes, "0--")
        {'v1':0, 'v2':0, 'v3':1}
    """

    if type(subspace) is str:
        assert (len(subspace) == len(primes))
        x = {}
        for name, value in zip(sorted(primes), subspace):
            if value.isdigit():
                x[name] = int(value)
        subspace = x
    else:
        assert set(subspace).issubset(set(primes))

    items = list(subspace.items()) + [(x, random.choice([0, 1])) for x in primes if x not in subspace]

    return dict(items)
