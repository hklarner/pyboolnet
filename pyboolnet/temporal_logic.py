

from typing import List, Union


import pyboolnet.state_space


def exists_finally_nested_reachability(primes: dict, subspaces: List[Union[dict, str]]) -> str:
    """
    Constructs a CTL formula that queries whether there is a path that visits the given *subspaces* in the order given.

    **arguments**:
        * *subspaces*: a list of subspaces

    **returns**:
        * *ctl_formula*: the CTL formula

    **example**::

        >>> subspaces = ["1--", "-01"]
        >>> exists_finally_nested_reachability(subspaces)
        "EF(v1&EF(!v2&v3))"
    """

    if not subspaces:
        return "TRUE"

    subspaces = [pyboolnet.state_space.subspace2dict(primes, x) if type(x) == str else x for x in subspaces]
    x = subspaces.pop(0)
    result = f"EF({subspace2proposition(primes, x)}  &$)"

    for x in subspaces:
        result = result.replace("$", f"EF({subspace2proposition(primes, x)}  &$)")

    return result.replace("  &$", "")


def all_globally_exists_finally_one_of_sub_spaces(primes: dict, sub_spaces: List[dict]) -> str:
    """
    Constructs a CTL formula that queries whether there it is alsways possible to reach one of the given *subspaces*.

    .. note::

        This query is equivalent to asking whether every attractor is inside one of the *subspaces*.

    .. note::

        Typically this query is used to decide whether a known set of attractors A1, A2, ... An is complete, i.e., whether there are any more attractors.
        To find out pick arbitrary representative states x1, x2, ... xn for each attractor and call the function *AGEF_oneof_subspaces* with the argument *Subspaces = [x1, x2, ..., xn]*.

    **arguments**:
        * *subspaces*: a list of subspace

    **returns**:
        * *formula*: the CTL formula

    **example**::

        >>> subspaces = [{"v1":0,"v2":0},{"v2":1}]
        >>> all_globally_exists_finally_one_of_sub_spaces(subspaces)
        "AG(EF(!v1&!v2 | v2))"
    """

    if not sub_spaces:
        return "TRUE"

    sub_spaces = [pyboolnet.state_space.subspace2dict(primes, x) if type(x) == str else x for x in sub_spaces]

    return f"AG({exists_finally_one_of_subspaces(primes, sub_spaces)})"


def exists_finally_one_of_subspaces(primes: dict, subspaces: List[Union[dict, str]]) -> str:
    """
    Constructs a CTL formula that queries whether there is a path that leads to one of the Subspaces.

    **arguments**:
        * *subspaces*: a list of subspaces

    **returns**:
        * *formula*: the CTL formula

    **example**::

        >>> subspaces = [{"v1":0,"v2":0}, "1-1--"]
        >>> exists_finally_one_of_subspaces(primes, subspaces)
        "EF(!v1&!v2 | v1&v3)"
    """

    if not subspaces:
        return "TRUE"

    subspaces = [pyboolnet.state_space.subspace2dict(primes, x) if type(x) == str else x for x in subspaces]

    return f"EF({' | '.join(subspace2proposition(primes, x) for x in subspaces)})"


def exists_finally_unsteady_components(names: List[str]) -> str:
    """
    Constructs a CTL formula that queries whether for every variables v specified in *names* there is a path to a state x in which v is unsteady.

    .. note::

        Typically this query is used to find out if the variables given in *names* are oscillating in a given attractor.

    **arguments**:
        * *names*: a list of names of variables

    **returns**:
        * *ctl_formula*: the CTL formula

    **example**::

        >>> names = ["v1","v2"]
        >>> exists_finally_unsteady_components(names)
        "EF(v1_steady!=0) & EF(v2_steady!=0))"

    """
    names = [x for x in names if x.strip()]

    if not names:
        return "TRUE"

    return " & ".join([f"EF(!{x}_STEADY)" for x in names])


def subspace2proposition(primes: dict, subspace: Union[dict, str]) -> str:
    """
    Constructs a CTL formula that is true in a state x if and only if x belongs to the given Subspace.

    .. note::

        Typically this query is used to define INIT constraints from a given subspace.

    **arguments**:
        * *subspace*: a subspace in string or dictionary representation

    **returns**:
        * *proposition*: the proposition

    **example**::

        >>> subspace = {"v1":0,"v2":1}
        >>> init = f"INIT {subspace2proposition(subspace)}"
        >>> init
        "INIT v1&!v2"
    """

    if not subspace or subspace == len(primes) * "-":
        return "TRUE"

    if type(subspace) is str:
        subspace = pyboolnet.state_space.subspace2dict(primes, subspace)

    return "&".join([name if value == 1 else f"!{name}" for name, value in sorted(subspace.items())])

