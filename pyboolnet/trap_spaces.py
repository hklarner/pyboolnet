

import logging
import sys
from typing import List, Union, Optional

from pyboolnet import find_command
from pyboolnet.external.potassco import potassco_handle
from pyboolnet.prime_implicants import active_primes
from pyboolnet.prime_implicants import create_constants, percolate_and_keep_constants
from pyboolnet.state_space import subspace2dict, subspace2str

CMD_GRINGO = find_command("gringo")
CMD_CLASP = find_command("clasp")

log = logging.getLogger(__name__)


def circuits(primes: dict, max_output: int = 1000, fname_asp: Optional[str] = None, representation: str = "dict"):
    """
    Computes minimal trap spaces but also distinguishes between nodes that are fixed due to being part of a circuit
    and nodes that are fix due to percolation effects.

    **arguments**:
        * *primes*: prime implicants
        * *max_output*: maximum number of returned solutions
        * *fname_asp*: file name or *None*
        * *representation*: either "str" or "dict", the representation of the trap spaces

    **returns**:
        * *circuits*: of tuples consisting of circuit nodes and percolation nodes


    **example**::

        >>> circuits(primes)
        [({'Mek': 0, 'Erk': 0},{'Raf': 1}),..]
    """
    
    return potassco_handle(primes, type_="circuits", bounds=(0, "n"), project=None, max_output=max_output, fname_asp=fname_asp, representation=representation)


def percolate_trapspace(primes: dict, trap_space: dict):
    """
    Percolates the *trap_space*.
    Does not check whether *trap_space* is really a trap space.
    Instead, it creates constants from *trap_space* and percolates the values.

    **arguments**:
        * *primes*: prime implicants
        * *trap_space*: a subspace

    **returns**:
        * *trap_space*: the percolated trap space

    **example**::

        >>> percolate_trapspace(primes, {'Mek': 0, 'Erk': 0})
        {'Raf': 1, 'Mek': 0, 'Erk': 0}
    """
    
    primes = create_constants(primes, trap_space, in_place=True)
    constants = percolate_and_keep_constants(primes)
    
    return constants


def trapspaces_that_contain_state(primes: dict, state: dict, type_: str, fname_asp: Optional[str] = None, representation: str = "dict", max_output: int = 1000):
    """
    Computes trap spaces that contain *state*.

    **arguments**:
        * *primes*: prime implicants
        * *state*: a state in dict format
        * *type_*: either "min", "max", "all" or "percolated"
        * *fname_asp*: file name or *None*
        * *representation*: either "str" or "dict", the representation of the trap spaces
        * *max_output*: maximum number of returned solutions

    **returns**:
        * *trap_spaces*: the trap spaces that contain *state*

    **example**::

        >>> trapspaces_that_contain_state(primes, {"v1":1,"v2":0,"v3":0})
    """

    return trapspaces_that_intersect_subspace(primes=primes, subspace=state, type_=type_, fname_asp=fname_asp, representation=representation, max_output=max_output)


def trapspaces_that_intersect_subspace(primes: dict, subspace: dict, type_: str, fname_asp: Optional[str] = None, representation: str = "dict", max_output: int = 1000) -> List[dict]:
    """
    Computes trap spaces that have non-empty intersection with *subspace*

    **arguments**:
        * *primes*: prime implicants
        * *subspace*: a subspace in dict format
        * *type_*: either "min", "max", "all" or "percolated"
        * *fname_asp*: file name or *None*
        * *representation*: either "str" or "dict", the representation of the trap spaces
        * *max_output*: maximum number of returned solutions

    **returns**:
        * *trap_spaces*: the trap spaces that have non-empty intersection with *subspace*

    **example**::

        >>> trapspaces_that_intersect_subspace(primes, {"v1":1,"v2":0,"v3":0})
    """
    
    assert (len(primes) >= len(subspace))
    assert (type(subspace) in [dict, str])
    
    if type(subspace) == str:
        subspace = subspace2dict(primes, subspace)
    
    relevant_primes = active_primes(primes, subspace)
    
    bounds = None
    if type_ == "max":
        bounds = (1, "n")

    tspaces = potassco_handle(primes=relevant_primes, type_=type_, bounds=bounds, project=[], max_output=max_output, fname_asp=fname_asp, representation=representation)
    
    if not tspaces:
        answer = {}
        
        if representation == "str":
            answer = subspace2str(primes, answer)
        
        return [answer]
    
    if len(subspace) == len(primes) and type_ == "min":
        if len(tspaces) > 1:
            log.error("the smallest trap space containing a state (or other space) must be unique!")
            log.error(f"found {len(tspaces)} smallest tspaces.")
            log.error(tspaces)
            sys.exit()
        
        return [tspaces.pop()]
    
    return tspaces


def trapspaces_within_subspace(primes: dict, subspace: dict, type_, fname_asp=None, representation: str = "dict", max_output: int = 1000) -> Union[List[dict], List[str]]:
    """
    Computes trap spaces contained within *subspace*

    **arguments**:
        * *primes*: prime implicants
        * *subspace*: a subspace in dict format
        * *type_*: either "min", "max", "all" or "percolated"
        * *fname_asp*: file name or *None*
        * *representation*: either "str" or "dict", the representation of the trap spaces
        * *max_output*: maximum number of returned solutions

    **returns**:
        * *trap_spaces*: the trap spaces contained within *subspace*

    **example**::

        >>> trapspaces_in_subspace(primes, {"v1":1,"v2":0,"v3":0})
    """
    
    if not subspace:
        return trap_spaces(primes, type_, max_output=max_output, fname_asp=fname_asp, representation=representation)
    
    assert (len(primes) >= len(subspace))
    assert (type(subspace) in [dict, str])
    
    if type(subspace) == str:
        subspace = subspace2dict(primes, subspace)
    
    relevant_primes = active_primes(primes, subspace)
    bounds = (len(subspace), "n")

    extra_lines = [f':- not hit("{node}",{value}).' for node, value in subspace.items()]
    extra_lines += [""]

    tspaces = potassco_handle(primes=relevant_primes, type_=type_, bounds=bounds, project=[], max_output=max_output, fname_asp=fname_asp, representation=representation, extra_lines=extra_lines)
    
    return tspaces


def smallest_trapspace(primes: dict, state: dict, representation: str = "dict"):
    """
    Returns the (unique) smallest trap space that contains *state*.
    Calls :ref:`trapspaces_that_contain_state`

    **arguments**:
        * *primes*: prime implicants
        * *state*: a state in dict format
        * *representation*: either "str" or "dict", the representation of the trap spaces

    **returns**:
        * *trap_space*: the unique minimal trap space that contains *state*

    **example**::

        >>> smallest_trapspace(primes, {"v1":1,"v2":0,"v3":0})
    """
    
    return trapspaces_that_contain_state(primes, state, type_="min", fname_asp=None, representation=representation)


def trap_spaces(primes: dict, option: str, max_output: int = 1000, fname_asp: str = None, representation: str = "dict") -> Union[List[dict], List[str]]:
    """
    Returns a list of trap spaces using the :ref:`installation_potassco` ASP solver, see :ref:`Gebser2011 <Gebser2011>`.
    For a formal introcution to trap spaces and the ASP encoding that is used for their computation see :ref:`Klarner2015(a) <klarner2015trap>`.

    The parameter *type_* must be one of *"max"*, *"min"*, *"all"* or *"percolated"* and
    specifies whether subset minimal, subset maximal, all trap spaces or all percolated trap spaces should be returned.

    .. warning::
        The number of trap spaces is easily exponential in the number of components.
        Use the safety parameter *max_output* to control the number of returned solutions.

    To create the *asp* file for inspection or manual editing, pass a file name to *fname_asp*.

    **arguments**:
        * *primes*: prime implicants
        * *type_*: either *"max"*, *"min"*, *"all"* or *"percolated"*
        * *max_output*: maximal number of trap spaces to return
        * *fname_asp*: name of *asp* file to create, or *None*
        * *representation*: either "str" or "dict", the representation of the trap spaces

    **returns**:
        * *subspaces*: the trap spaces

    **example**::

        >>> bnet = ["x, !x | y | z",
        ...         "y, !x&z | y&!z",
        ...         "z, x&y | z"]
        >>> bnet = "\\n".join(bnet)
        >>> primes = bnet2primes(bnet)
        >>> tspaces = trap_spaces(primes, "all", representation="str")
        ---, --1, 1-1, -00, 101
    """
    
    # exclude trivial trap space {} for search of maximal trap spaces
    bounds = None
    if option == "max":
        bounds = (1, "n")
    
    return potassco_handle(primes, option, bounds=bounds, project=None, max_output=max_output, fname_asp=fname_asp, representation=representation)


def steady_states(primes: dict, max_output: int = 1000, fname_asp: Optional[str] = None, representation: str = "dict") -> Union[List[dict], List[str]]:
    """
    Returns steady states.

    **arguments**:
        * *primes*: prime implicants
        * *max_output*: maximal number of trap spaces to return
        * *fname_asp*: file name or *None*
        * *representation*: either "str" or "dict", the representation of the trap spaces

    **returns**:
        * *states*: the steady states

    **example**::

        >>> steady = steady_states(primes)
        >>> len(steady)
        2
    """
    
    return potassco_handle(primes, type_="all", bounds=("n", "n"), project=[], max_output=max_output, fname_asp=fname_asp, representation=representation)


def trap_spaces_bounded(primes: dict, type_: str, bounds: tuple, max_output: int = 1000, fname_asp: Optional[str] = None):
    """
    Returns a list of bounded trap spaces using the Potassco_ ASP solver :ref:`[Gebser2011]<Gebser2011>`.
    See :ref:`trap_spaces <sec:trap_spaces>` for details of the parameters *type_*, *max_output* and *fname_asp*.
    The parameter *bounds* is used to restrict the set of trap spaces from which maximal, minimal or all solutions are drawn
    to those whose number of fixed variables are within the given range.
    Example: ``bounds=(5,8)`` instructs Potassco_ to consider only trap spaces with 5 to 8 fixed variables as feasible.
    *type_* selects minimal, maximal or all trap spaces from the restricted set.
    .. warning::
        The *Bound* constraint is applied *before* selecting minimal or maximal trap spaces.
        A trap space may therefore be minimal w.r.t. to certain bounds but not minimal in the unbounded sense.

    Use ``"n"`` as a shortcut for "all variables", i.e., instead of ``len(primes)``.
    Example: Use ``bounds=("n","n")`` to compute steady states.
    Note that the parameter *type_* becomes irrelevant for ``bounds=(x,y)`` with ``x=y``.

    **arguments**:
        * *primes*: prime implicants
        * *type_* in ``["max","min","all"]``: subset minimal, subset maximal or all solutions
        * *bounds*: the upper and lower bound for the number of fixed variables
        * *max_output*: maximal number of trap spaces to return
        * *fname_asp*: file name or *None*
    **returns**:
        * list of trap spaces
    **example**::
        >>> tspaces = trap_spaces_bounded(primes, "min", (2,4))
        >>> len(tspaces)
        12
        >>> tspaces[0]
        {'TGFR':0,'FGFR':0}
    """
    
    return potassco_handle(primes, type_, bounds, project=None, max_output=max_output, fname_asp=fname_asp, representation="dict")


def steady_states_projected(primes: dict, project, max_output: int = 1000, fname_asp: Optional[str] = None):
    """
    Returns a list of projected steady states using the Potassco_ ASP solver :ref:`[Gebser2011]<Gebser2011>`.

    **arguments**:
        * *primes*: prime implicants
        * *project*: list of names
        * *max_output*: maximal number of trap spaces to return
        * *fname_asp*: file name or *None*

    **returns**:
        * *Activities*: projected steady states

    **example**::

        >>> psteady = steady_states_projected(primes, ["v1","v2"])
        >>> len(psteady)
        2
        >>> psteady
        [{"v1":1,"v2":0},{"v1":0,"v2":0}]
    """

    unknown_names = set(project).difference(set(primes))
    if unknown_names:
        log.error(f"can not project steady states: unknown_names={unknown_names}")
        sys.exit()
    
    return potassco_handle(primes, type_="all", bounds=("n", "n"), project=project, max_output=max_output, fname_asp=fname_asp, representation="dict")

