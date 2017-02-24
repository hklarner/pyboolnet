

import PyBoolNet.StateTransitionGraphs


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

    Subspaces = [PyBoolNet.StateTransitionGraphs.subspace2dict(Primes, x) if type(x)==str else x for x in Subspaces]

    x = Subspaces.pop(0)
    result = "EF("+ subspace2proposition(Primes, x) +"  &$)"
    for x in Subspaces:
        result = result.replace("$", "EF("+ subspace2proposition(Primes, x) +"  &$)")

    return result.replace("  &$","")

    
def AGEF_oneof_subspaces(Primes, Subspaces):
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

    if Subspaces==[]:
        return 'TRUE'

    Subspaces = [PyBoolNet.StateTransitionGraphs.subspace2dict(Primes, x) if type(x)==str else x for x in Subspaces]

    return 'AG('+ EF_oneof_subspaces(Primes, Subspaces) +')'


def EF_oneof_subspaces(Primes, Subspaces):
    """
    Constructs a CTL formula that queries whether there is a path that leads to one of the Subspaces.

    **arguments**:
        * *Subspaces* (list): a list of subspaces

    **returns**:
        * *Formula* (str): the CTL formula

    **example**::

        >>> subspaces = [{"v1":0,"v2":0}, "1-1--"]
        >>> EF_oneof_subspaces(primes, subspaces)
        'EF(!v1&!v2 | v1&v3)'
    """

    if not Subspaces:
        return 'TRUE'
    
    Subspaces = [PyBoolNet.StateTransitionGraphs.subspace2dict(Primes, x) if type(x)==str else x for x in Subspaces]
    
    return 'EF('+ ' | '.join(subspace2proposition(Primes, x) for x in Subspaces) +')'


def EF_unsteady_states(Names):
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
        >>> EF_unsteady_states(names)
        'EF(v1_steady!=0) & EF(v2_steady!=0))'

    """

    Names = [x for x in Names if x.strip()]
    if Names==[]:
        return 'TRUE'

    return ' & '.join(['EF(!%s_STEADY)'%x for x in Names])


def subspace2proposition(Primes, Subspace):
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

    
    if not Subspace:
        return "TRUE"

    if type(Subspace)==str:
        Subspace = PyBoolNet.StateTransitionGraphs.subspace2dict(Primes, Subspace)
    
    return '&'.join([name if value==1 else '!'+name for name,value in sorted(Subspace.items())])


def init_for_bargraph_encoding(Primes):
    """
    creates an initial condition for components that were booleanized by the "bargraph" encoding.
    enforces for each pair of components whose name differs only by the postfix "_medium" or "_high"
    that *<name>_high -> <name>_medium*.
    """

    names = []
    for x in Primes:
        if x.endswith("_medium") and (x[:-7]+'_high' in Primes):
            names.append(x[:-7])

    init = ' & '.join('('+x+'_high -> '+x+'_medium'+')' for x in names)
    
    return '(%s)'%init



if __name__=="__main__":
    primes = ["v1", "v2", "v3"]
    subspaces = [{}, {}, "--1", {"v2":0, "v1":0}, "1-1", "-0-"]
    print(EF_oneof_subspaces(primes, subspaces))
    print(EF_all_unsteady(primes))
    print(EF_nested_reachability(primes, subspaces))



