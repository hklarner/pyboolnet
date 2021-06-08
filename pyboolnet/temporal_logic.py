

from typing import List

import PyBoolNet.state_transition_graphs


def EF_nested_reachability(Primes, Subspaces):
    """
    Constructs a CTL formula that queries whether there is a path that visits the given *Subspaces* in the order given.

    **arguments**:
        * *Subspaces* (list): a list of subspaces

    **returns**:
        * *CTLFormula* (str): the CTL formula

    **example**::

        >>> subspaces = ["1--", "-01"]
        >>> EF_nested_reachability(subspaces)
        'EF(v1&EF(!v2&v3))'
    """

    if Subspaces==[]:
        return 'TRUE'

    Subspaces = [PyBoolNet.state_transition_graphs.subspace2dict(Primes, x) if type(x) == str else x for x in Subspaces]

    x = Subspaces.pop(0)
    result = "EF("+ subspace2proposition(Primes, x) +"  &$)"
    for x in Subspaces:
        result = result.replace("$", "EF("+ subspace2proposition(Primes, x) +"  &$)")

    return result.replace("  &$","")


def all_globally_exists_finally_one_of_sub_spaces(primes: dict, sub_spaces: List[dict]) -> str:
    """
    Constructs a CTL formula that queries whether there it is alsways possible to reach one of the given *Subspaces*.

    .. note::

        This query is equivalent to asking whether every attractor is inside one of the *Subspaces*.

    .. note::

        Typically this query is used to decide whether a known set of attractors A1, A2, ... An is complete, i.e., whether there are any more attractors.
        To find out pick arbitrary representative states x1, x2, ... xn for each attractor and call the function *AGEF_oneof_subspaces* with the argument *Subspaces = [x1, x2, ..., xn]*.

    **arguments**:
        * *Subspaces*: a list of subspace

    **returns**:
        * *Formula* (str): the CTL formula

    **example**::

        >>> subspaces = [{"v1":0,"v2":0},{"v2":1}]
        >>> AGEF_oscillation(subspaces)
        'AG(EF(!v1&!v2 | v2))'
    """

    if sub_spaces == []:
        return "TRUE"

    sub_spaces = [PyBoolNet.state_transition_graphs.subspace2dict(primes, x) if type(x) == str else x for x in sub_spaces]

    return 'AG(' + exists_finally_one_of_subspaces(primes, sub_spaces) + ')'


def exists_finally_one_of_subspaces(primes: dict, sub_spaces: List[dict]) -> str:
    """
    Constructs a CTL formula that queries whether there is a path that leads to one of the Subspaces.

    **arguments**:
        * *Subspaces* (list): a list of subspaces

    **returns**:
        * *Formula* (str): the CTL formula

    **example**::

        >>> subspaces = [{"v1":0,"v2":0}, "1-1--"]
        >>> exists_finally_one_of_subspaces(primes, subspaces)
        'EF(!v1&!v2 | v1&v3)'
    """

    if not sub_spaces:
        return "TRUE"

    sub_spaces = [PyBoolNet.state_transition_graphs.subspace2dict(primes, x) if type(x) == str else x for x in sub_spaces]

    return 'EF(' + ' | '.join(subspace2proposition(primes, x) for x in sub_spaces) + ')'


def exists_finally_unsteady_components(names: List[str]) -> str:
    """
    Constructs a CTL formula that queries whether for every variables v specified in *Names* there is a path to a state x in which v is unsteady.

    .. note::

        Typically this query is used to find out if the variables given in *Names* are oscillating in a given attractor.

    **arguments**:
        * *Names* (list): a list of names of variables

    **returns**:
        * *Formula* (str): the CTL formula

    **example**::

        >>> names = ["v1","v2"]
        >>> exists_finally_unsteady_components(names)
        'EF(v1_steady!=0) & EF(v2_steady!=0))'

    """

    names = [x for x in names if x.strip()]
    if names==[]:
        return 'TRUE'

    return ' & '.join(['EF(!%s_STEADY)' % x for x in names])


def subspace2proposition(primes: dict, sub_space: dict) -> str:
    """
    Constructs a CTL formula that is true in a state x if and only if x belongs to the given Subspace.

    .. note::

        Typically this query is used to define INIT constraints from a given subspace.

    **arguments**:
        * *Subspace* (str / dict): a subspace in string or dictionary representation

    **returns**:
        * *Proposition* (str): the proposition

    **example**::

        >>> subspace = {"v1":0,"v2":1}
        >>> init = "INIT " + subspace2proposition(subspace)
        >>> init
        'INIT v1&!v2'
    """

    if not sub_space or sub_space==len(primes)* "-":
        return "TRUE"

    if type(sub_space)==str:
        sub_space = PyBoolNet.state_transition_graphs.subspace2dict(primes, sub_space)

    return '&'.join([name if value==1 else '!'+name for name,value in sorted(sub_space.items())])


if __name__=="__main__":
    primes = ["v1", "v2", "v3"]
    subspaces = [{}, {}, "--1", {"v2":0, "v1":0}, "1-1", "-0-"]
    print(exists_finally_one_of_subspaces(primes, subspaces))
    print(EF_all_unsteady(primes))
    print(EF_nested_reachability(primes, subspaces))
