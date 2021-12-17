

import datetime
import logging
from functools import partial
from itertools import product
from typing import Optional, Union, List, Tuple

import networkx

from pyboolnet.digraphs import digraph2condensationgraph
from pyboolnet.digraphs import find_ancestors
from pyboolnet.file_exchange import primes2bnet
from pyboolnet.helpers import merge_dicts
from pyboolnet.helpers import open_json_data
from pyboolnet.helpers import save_json_data
from pyboolnet.interaction_graphs import primes2igraph
from pyboolnet.model_checking import model_checking
from pyboolnet.prime_implicants import copy_primes
from pyboolnet.prime_implicants import create_constants, find_constants
from pyboolnet.prime_implicants import percolate, remove_all_constants
from pyboolnet.prime_implicants import remove_all_variables_except
from pyboolnet.state_space import subspace2str, state2dict, state2str, random_state
from pyboolnet.state_transition_graphs import UPDATE_STRATEGIES
from pyboolnet.state_transition_graphs import random_successor_asynchronous, successor_synchronous, \
    random_successor_mixed
from pyboolnet.temporal_logic import all_globally_exists_finally_one_of_sub_spaces
from pyboolnet.temporal_logic import exists_finally_one_of_subspaces
from pyboolnet.temporal_logic import exists_finally_unsteady_components
from pyboolnet.temporal_logic import subspace2proposition
from pyboolnet.trap_spaces import compute_trap_spaces
from pyboolnet.version import read_version_txt

VERSION = read_version_txt()

log = logging.getLogger(__file__)


def compute_attractors(primes: dict, update: str, fname_json: Optional[str] = None, check_completeness: bool = True, check_faithfulness: bool = True, check_univocality: bool = True, max_output: int = 1000) -> dict:
    """
    computes all attractors of *primes* including information about completeness, univocality, faithfulness

    **arguments**:
      * *primes*: prime implicants
      * *update*: the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
      * *fname_json*: json file name to save result
      * *check_completeness*: enable completeness check
      * *check_faithfulness*: enable faithfulness check
      * *check_univocality*: enable univocality check

    **returns**:
        * *attractors*: attractor data

    **example**::
      >>> attractors = compute_attractors(primes, update, "attractors.json")
    """

    assert update in UPDATE_STRATEGIES
    assert primes

    attractors = dict()
    attractors["primes"] = copy_primes(primes)
    attractors["update"] = update

    min_tspaces = compute_trap_spaces(primes=primes, type_="min", max_output=max_output)

    if check_completeness:
        log.info("attractors.completeness(..)")
        if completeness(primes, update, max_output=max_output):
            attractors["is_complete"] = "yes"
        else:
            attractors["is_complete"] = "no"
        log.info(f"{attractors['is_complete']}")
    else:
        attractors["is_complete"] = "unknown"

    attractors["attractors"] = []

    for i, mints in enumerate(min_tspaces):

        mints_obj = dict()
        mints_obj["str"] = subspace2str(primes=primes, subspace=mints)
        mints_obj["dict"] = mints
        mints_obj["prop"] = subspace2proposition(primes=primes, subspace=mints)

        log.info(f" working on minimal trapspace {i+1}/{len(min_tspaces)}: {mints_obj['str']}")

        if check_univocality:
            log.info("attractors.univocality(..)")
            if univocality(primes=primes, update=update, trap_space=mints):
                mints_obj["is_univocal"] = "yes"
            else:
                mints_obj["is_univocal"] = "no"
            log.info(f" {mints_obj['is_univocal']}")
        else:
            mints_obj["is_univocal"] = "unknown"

        if check_faithfulness:
            log.info("attractors.faithfulness(..)")
            if faithfulness(primes=primes, update=update, trap_space=mints):
                mints_obj["is_faithful"] = "yes"
            else:
                mints_obj["is_faithful"] = "no"
            log.info(f"{mints_obj['is_faithful']}")
        else:
            mints_obj["is_faithful"] = "unknown"

        log.info("attractors.find_attractor_state_by_randomwalk_and_ctl(..)")
        state = find_attractor_state_by_randomwalk_and_ctl(primes=primes, update=update, initial_state=mints)

        state_obj = dict()
        state_obj["str"] = state2str(state)
        state_obj["dict"] = state
        state_obj["prop"] = subspace2proposition(primes, state)

        attractor_obj = dict()
        attractor_obj["min_trap_space"] = mints_obj
        attractor_obj["state"] = state_obj
        attractor_obj["is_steady"] = len(mints) == len(primes)
        attractor_obj["is_cyclic"] = len(mints) != len(primes)

        attractors["attractors"].append(attractor_obj)

    attractors["attractors"] = tuple(sorted(attractors["attractors"], key=lambda x: x["state"]["str"]))

    if fname_json:
        write_attractors_json(attractors, fname_json)

    return attractors


def write_attractors_json(attractors: dict, fname_json: str):
    """
    saves the attractor object as a JSON file.

    **arguments**:
        * *attractors*: json attractor data, see :ref:`attractors_compute_json`
        * *fname_json*: file name

    **example**::
        >>> save_attractor(attractors, "attractors.json")
    """

    save_json_data(data=attractors, fname=fname_json)


def read_attractors_json(fname: str) -> dict:
    """
    opens the attractor object

    **arguments**:
        * *fname*: file name

    **returns**:
        * *attractors*: json attractor data, see :ref:`compute_attractors`

    **example**::
        >>> attractors = read_attractors_json("attractors.json")
    """

    attractors = open_json_data(fname=fname)

    return attractors


def find_attractor_state_by_randomwalk_and_ctl(primes: dict, update: str, initial_state: Union[dict, str] = {}, length: int = 0, attempts: int = 10) -> dict:
    """
    Attempts to find a state inside an attractor by the "long random walk" method,
    see :ref:`Klarner2015(b) <klarner2015approx>` Sec. 3.2 for a formal definition.
    The method generates a random walk of *length* states, starting from a state defined by *initial_state*.
    If *initial_state* is a subspace then :ref:`random_state` will be used to draw a random state from inside it.
    The function then uses CTL model checking, i.e., :ref:`check_primes <check_primes>`,
    to decide whether the last state of the random walk is inside an attractor.
    If so it is returned, otherwise the process is repeated.
    If no attractor state has been found after *Attempts* many trials an exception is raised.

    .. note::
        The default value for length, namely *length=0*, will be replaced by::

            length = 10*len(primes)

        which proved sufficiently large in our computer experiments.

    **arguments**:
        * *primes*: prime implicants
        * *update*: the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
        * *initial_state*: an initial state or subspace
        * *length*: length of random walk
        * *attempts*: number of attempts before exception is raised

    **returns**:
        * *attractor_state*: a state that belongs to some attractor
        * raises *Exception* if no attractor state is found

    **example**::
            >>> find_attractor_state_by_randomwalk_and_ctl(primes, "asynchronous")
            {"v1": 1, "v2": 1, "v3": 1}
    """

    if type(initial_state) == str:
        initial_state = state2dict(primes=primes, state=initial_state)

    assert update in UPDATE_STRATEGIES
    assert set(initial_state).issubset(set(primes))

    if length == 0:
        length = 10 * len(primes)

    if update == "asynchronous":
        transition = partial(random_successor_asynchronous, primes)

    elif update == "synchronous":
        transition = partial(successor_synchronous, primes)

    elif update == "mixed":
        transition = partial(random_successor_mixed, primes)
    else:
        log.error(f"unknown update strategy: update={update}")
        raise Exception

    log.info("find_attractor_state_by_randomwalk_and_ctl(..)")
    log.info(f"len(primes)={len(primes)}, update={update}, length={length}, attempts={attempts}")

    trials = 0
    while trials < attempts:
        log.info(f"trial {trials}")

        current_state = random_state(primes, initial_state)
        log.info(f"start: {state2str(current_state)}")

        transitions = 0
        while transitions < length:
            current_state = transition(current_state)
            transitions += 1

        log.info(f"end: {state2str(current_state)}")

        formula = all_globally_exists_finally_one_of_sub_spaces(primes=primes, sub_spaces=[current_state])
        spec = f"CTLSPEC {formula}"
        init = f"INIT {subspace2proposition(primes=primes, subspace=current_state)}"

        if model_checking(primes, update, init, spec):
            log.info("is attractor state")
            return current_state

        trials += 1

    log.error("could not find attractor state: increase Length or Attempts parameter.")
    raise Exception


def univocality(primes: dict, update: str, trap_space: Union[dict, str]) -> bool:
    """
    The model checking and random-walk-based method for deciding whether *trap_space* is univocal,
    i.e., whether there is a unique attractor contained in it,
    in the state transition graph defined by *primes* and *update*.
    The approach is described and discussed in :ref:`Klarner2015(a) <klarner2015trap>`.
    The function performs two steps: first it searches for a state that belongs to an attractor inside of *trap_space* using
    the random-walk-approach and the function :ref:`random_walk <random_walk>`,
    then it uses CTL model checking, specifically the pattern :ref:`AGEF_oneof_subspaces <AGEF_oneof_subspaces>`,
    to decide if the attractor is unique inside *trap_space*.

    .. note::
        In the (very unlikely) case that the random walk does not end in an attractor state an exception will be raised.

    .. note::
        Univocality depends on the update strategy, i.e.,
        a trapspace may be univocal in the synchronous STG but not univocal in the asynchronous STG or vice versa.

    .. note::
        A typical use case is to decide whether a minimal trap space is univocal.

    .. note::
        *trap_space* is in fact not required to be a trap set, i.e., it may be an arbitrary subspace.
        If it is an arbitrary subspace then the involved variables are artificially fixed to be constant.

    **arguments**:
        * *primes*: prime implicants
        * *update*: the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
        * *trap_space*: a subspace

    **returns**:
        * *answer*: whether *trap_space* is univocal in the STG defined by *primes* and *update*

    **example**::

        >>> mintspaces = compute_trap_spaces(primes, "min")
        >>> x = mintrapspaces[0]
        >>> univocality(primes, "asynchronous", x)
        True
    """

    primes = copy_primes(primes=primes)
    create_constants(primes=primes, constants=trap_space)
    percolate(primes=primes, remove_constants=True)

    if primes == {}:
        return True

    attractor_state = find_attractor_state_by_randomwalk_and_ctl(primes=primes, update=update)

    formula = exists_finally_one_of_subspaces(primes=primes, subspaces=[attractor_state])
    spec = f"CTLSPEC {formula}"
    init = "INIT TRUE"
    answer = model_checking(primes=primes, update=update, initial_states=init, specification=spec)

    return answer


def faithfulness(primes: dict, update: str, trap_space: Union[dict, str]) -> bool:
    """
    The model checking approach for deciding whether *trap_space* is faithful,
    i.e., whether all free variables oscillate in all of the attractors contained in it,
    in the state transition graph defined by *primes* and *update*.
    The approach is described and discussed in :ref:`Klarner2015(a) <klarner2015trap>`.
    It is decided by a single CTL query of the pattern :ref:`EF_all_unsteady <EF_all_unsteady>`
    and the random-walk-approach of the function :ref:`random_walk <random_walk>`.

    .. note::
        In the (very unlikely) case that the random walk does not end in an attractor state an exception will be raised.

    .. note::
        Faithfulness depends on the update strategy, i.e.,
        a trapspace may be faithful in the synchronous STG but not faithful in the asynchronous STG or vice versa.

    .. note::
        A typical use case is to decide whether a minimal trap space is faithful.

    .. note::
        *trap_space* is in fact not required to be a trap set, i.e., it may be an arbitrary subspace.
        If it is an arbitrary subspace then the involved variables are artificially fixed to be constant.

    **arguments**:
        * *primes*: prime implicants
        * *update*: the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
        * *trap_space*: a subspace

    **returns**:
        * *answer*: whether *trap_space* is faithful in the STG defined by *primes* and *update*

    **example**::

        >>> mintspaces = compute_trap_spaces(primes, "min")
        >>> x = mintspaces[0]
        >>> faithfulness(primes, x)
        True
    """

    if len(trap_space) == len(primes):
        return True

    primes = copy_primes(primes=primes)
    create_constants(primes=primes, constants=trap_space)
    percolate(primes=primes, remove_constants=True)
    constants = find_constants(primes=primes)

    if len(constants) > len(trap_space):
        return False

    formula = exists_finally_unsteady_components(names=list(primes))
    spec = f"CTLSPEC AG({formula})"
    init = "INIT TRUE"
    answer = model_checking(primes=primes, update=update, initial_states=init, specification=spec)

    return answer


def completeness(primes: dict, update: str, max_output: int = 1000) -> bool:
    """
    The ASP and CTL model checking based algorithm for deciding whether the minimal trap spaces of a network are complete.
    The algorithm is discussed in :ref:`Klarner2015(a) <klarner2015trap>`.
    It splits the problem of deciding completeness into smaller subproblems by searching for so-called autonomous sets in the
    interaction graph of the network.
    If the minimal trap spaces of the corresponding restricted networks are complete
    then each of them defines a network reduction that is in turn subjected to a search for autonomous sets.
    The efficiency of the algorithm depends on the existence of small autonomous sets in the interaction graph, i.e.,
    the existence of "hierarchies" rather than a single connected component.

    .. note::
        Completeness depends on the update strategy, i.e.,
        the minimal trap spaces may be complete in the synchronous STG but not complete in the asynchronous STG or vice versa.

    .. note::
        The algorithm returns a counterexample, i.e., a state from which there is no path to one of the minimal trap spaces,
        if the minimal trap spaces are not complete.

    .. note::
        Each line that corresponds to a line of the pseudo code of Figure 3 in :ref:`Klarner2015(a) <klarner2015trap>` is marked by a comment.

    **arguments**:
        * *primes*: prime implicants
        * *update*: the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*

    **returns**:
        * *answer*: whether *subspaces* is complete in the STG defined by *primes* and *update*,

    **example**::

            >>> completeness(primes, "asynchronous")
            False
    """

    return iterative_completeness_algorithm(primes=primes, update=update, compute_counterexample=False, max_output=max_output)


def univocality_with_counterexample(primes: dict, update: str, trap_space: Union[dict, str]) -> (bool, List[dict]):
    """
    Performs the same steps as :ref:`univocality` but also returns a counterexample which is *None* if it does not exist.
    A counterexample of a univocality test are two states that belong to different attractors.

    **arguments**:
        * *primes*: prime implicants
        * *update*: the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
        * *trap_space*: a subspace

    **returns**:
        * *answer*: whether *trap_space* is univocal in the STG defined by *primes* and *update*
        * *counter_example*: two states that belong to different attractors or *None* if no counterexample exists

    **example**::

        >>> mintspaces = compute_trap_spaces(primes, "min")
        >>> trapspace = mintrapspaces[0]
        >>> answer, counterex = univocality_with_counterexample(primes, trapspace, "asynchronous")
    """

    primes = percolate(primes=primes, add_constants=trap_space, copy=True)
    constants = find_constants(primes=primes)
    remove_all_constants(primes=primes)

    if primes == {}:
        return True, None

    attractor_state = find_attractor_state_by_randomwalk_and_ctl(primes=primes, update=update)
    spec = f"CTLSPEC {exists_finally_one_of_subspaces(primes=primes, subspaces=[attractor_state])}"
    init = "INIT TRUE"
    answer, counterexample = model_checking(primes=primes, update=update, initial_states=init, specification=spec, enable_counterexample=True)

    if answer:
        return True, None

    else:
        attractor_state2 = find_attractor_state_by_randomwalk_and_ctl(primes=primes, update=update, initial_state=counterexample[-1])
        attractor_state2 = merge_dicts(dicts=[attractor_state2, constants])
        attractor_state = merge_dicts(dicts=[attractor_state, constants])
        counterexample = attractor_state, attractor_state2

        return False, counterexample


def faithfulness_with_counterexample(primes: dict, update: str, trap_space: dict) -> (bool, List[dict]):
    """
    Performs the same steps as :ref:`faithfulness` but also returns a counterexample which is *None* if it does not exist.
    A counterexample of a faithful test is a state that belongs to an attractor which has more fixed variables than there are in *trap_space*.

    **arguments**:
        * *primes*: prime implicants
        * *update*: the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
        * *trap_space*: a subspace

    **returns**:
        * *answer*: whether *trap_space* is faithful in the STG defined by *primes* and *update*
        * *counter_example*: a state that belongs to an attractor that does not oscillate in all free variables or *None* if no counterexample exists

    **example**::

        >>> mintspaces = compute_trap_spaces(primes, "min")
        >>> x = mintspaces[0]
        >>> faithfulness(primes, x)
        True
    """

    if len(trap_space) == len(primes):
        return True, None

    primes = percolate(primes=primes, add_constants=trap_space, copy=True)
    constants = find_constants(primes=primes)
    remove_all_constants(primes=primes)

    if len(constants) > len(trap_space):
        counterexample = find_attractor_state_by_randomwalk_and_ctl(primes=primes, update=update)
        attractor_state = merge_dicts(dicts=[counterexample, constants])

        return False, attractor_state

    spec = f"CTLSPEC AG({exists_finally_unsteady_components(names=list(primes))})"
    answer, counterexample = model_checking(primes=primes, update=update, initial_states="INIT TRUE", specification=spec, enable_counterexample=True)

    if answer:
        return True, None

    else:
        attractor_state = find_attractor_state_by_randomwalk_and_ctl(primes=primes, update=update, initial_state=counterexample[-1])
        attractor_state = merge_dicts(dicts=[attractor_state, constants])

        return False, attractor_state


def completeness_with_counterexample(primes: dict, update: str, max_output: int = 1000) -> (bool, List[dict]):
    """
    Performs the same steps as :ref:`completeness` but also returns a counterexample which is *None* if it does not exist.
    A counterexample of a completeness test is a state that can not reach one of the minimal trap spaces of *primes*.

    **arguments**:
        * *primes*: prime implicants
        * *update*: the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*

    **returns**:
        * *answer*: whether *subspaces* is complete in the STG defined by *primes* and *update*,
        * *counterexample*: a state that can not reach one of the minimal trap spaces of *primes* or *None* if no counterexample exists

    **example**::

        >>> answer, counterexample = completeness_with_counterexample(primes, "asynchronous")
        >>> answer
        False
        >>> state2str(counterexample)
        10010111101010100001100001011011111111
    """

    return iterative_completeness_algorithm(primes=primes, update=update, compute_counterexample=True, max_output=max_output)


def iterative_completeness_algorithm(primes: dict, update: str, compute_counterexample: bool, max_output: int = 1000) -> Union[Tuple[bool, Optional[dict]], bool]:
    """
    The iterative algorithm for deciding whether the minimal trap spaces are complete.
    The function is implemented by line-by-line following of the pseudo code algorithm given in
    "Approximating attractors of Boolean networks by iterative CTL model checking", Klarner and Siebert 2015.

    **arguments**:
        * *primes*: prime implicants
        * *update*: the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
        * *compute_counterexample*: whether to compute a counterexample

    **returns**:
        * *answer*: whether *subspaces* is complete in the STG defined by *primes* and *update*,
        * *counterexample*: a state that can not reach one of the minimal trap spaces of *primes* or *None* if no counterexample exists

    **example**::

        >>> answer, counterexample = completeness_with_counterexample(primes, "asynchronous")
        >>> answer
        False
        >>> state2str(counterexample)
        10010111101010100001100001011011111111
    """

    primes = percolate(primes=primes, copy=True)
    constants_global = find_constants(primes=primes)
    remove_all_constants(primes=primes)

    min_trap_spaces = compute_trap_spaces(primes=primes, type_="min", max_output=max_output)
    if min_trap_spaces == [{}]:
        if compute_counterexample:
            return True, None
        else:
            return True

    current_set = [({}, set([]))]
    while current_set:
        p, w = current_set.pop()
        primes_reduced = copy_primes(primes=primes)
        create_constants(primes=primes_reduced, constants=p)
        igraph = primes2igraph(primes=primes_reduced)

        cgraph = digraph2condensationgraph(digraph=igraph)
        cgraph_dash = cgraph.copy()

        for U in cgraph.nodes():
            if set(U).issubset(set(w)):
                cgraph_dash.remove_node(U)

        w_dash = w.copy()
        refinement = []
        top_layer = [U for U in cgraph_dash.nodes() if cgraph_dash.in_degree(U) == 0]

        for U in top_layer:
            u_dash = find_ancestors(igraph, U)

            primes_restricted = copy_primes(primes_reduced)
            remove_all_variables_except(primes=primes_restricted, names=u_dash)

            q = compute_trap_spaces(primes=primes_restricted, type_="min", max_output=max_output)

            phi = exists_finally_one_of_subspaces(primes=primes_restricted, subspaces=q)

            init = "INIT TRUE"
            spec = f"CTLSPEC {phi}"

            if compute_counterexample:
                answer, counterexample = model_checking(primes=primes_restricted, update=update, initial_states=init, specification=spec, enable_counterexample=True)
                if not answer:
                    downstream = [x for x in igraph if x not in U]
                    arbitrary_state = random_state(downstream)
                    top_layer_state = counterexample[-1]
                    counterexample = merge_dicts([constants_global, p, top_layer_state, arbitrary_state])

                    return False, counterexample
            else:
                answer = model_checking(primes=primes_restricted, update=update, initial_states=init, specification=spec)
                if not answer:
                    return False

            refinement += intersection([p], q)
            w_dash.update(u_dash)

        for q in intersection(refinement):
            q_tilde = find_constants(primes=percolate(primes=primes, add_constants=q, copy=True))

            if q_tilde not in min_trap_spaces:
                current_set.append((q_tilde, w_dash))

    if compute_counterexample:
        return True, None
    else:
        return True


def create_attractor_report(primes: dict, fname_txt: Optional[str] = None) -> str:
    """
    Creates an attractor report for the network defined by *primes*.

    **arguments**:
        * *primes*: prime implicants
        * *fname_txt*: the name of the report file or *None*

    **returns**:
        * *txt*: attractor report as text

    **example**::
         >>> create_attractor_report(primes, "report.txt")
    """

    min_trap_spaces = compute_trap_spaces(primes, "min")
    steady = sorted(x for x in min_trap_spaces if len(x) == len(primes))
    cyclic = sorted(x for x in min_trap_spaces if len(x) < len(primes))
    width = max([12, len(primes)])

    lines = ["", ""]
    lines += ["### Attractor Report"]
    lines += [f" * created on {datetime.date.today().strftime('%d. %b. %Y')} using pyboolnet {VERSION}, see https://github.com/hklarner/pyboolnet"]
    lines += [""]

    lines += ["### Steady States"]
    if not steady:
        lines += [" * there are no steady states"]
    else:
        lines += ["| " + "steady state".ljust(width) + " |"]
        lines += ["| " + width * "-" + " | "]

    for x in steady:
        lines += ["| " + subspace2str(primes, x).ljust(width) + " |"]

    lines += [""]
    lines += ["### Asynchronous STG"]
    answer = completeness(primes, "asynchronous")
    lines += [f" * completeness: {answer}"]

    if not cyclic:
        lines += [" * there are only steady states"]
    else:
        lines += [""]
        line = "| "+"trapspace".ljust(width) + " | univocal  | faithful  |"
        lines += [line]
        lines += ["| " + width*"-" + " | --------- | --------- |"]

    for x in cyclic:
        line = "| " + subspace2str(primes, x).ljust(width)
        line += " | " + str(univocality(primes, "asynchronous", x)).ljust(9)
        line += " | " + str(faithfulness(primes, "asynchronous", x)).ljust(9) + " |"
        lines += [line]

    lines += [""]

    lines += ["### Synchronous STG"]
    lines += [f" * completeness: {completeness(primes, 'synchronous')}"]

    if not cyclic:
        lines += [" * there are only steady states"]
    else:
        lines += [""]
        line = "| " + "trapspace".ljust(width) + " | univocal  | faithful  |"
        lines += [line]
        lines += ["| " + width*"-" + "  | --------- | --------- |"]

    for x in cyclic:
        line = "| " + (subspace2str(primes, x)).ljust(width)
        line += " | " + str(univocality(primes, "synchronous", x)).ljust(9)
        line += " | " + str(faithfulness(primes, "synchronous", x)).ljust(9) + " |"
        lines += [line]

    lines += [""]

    bnet = []

    for row in primes2bnet(primes=primes).split("\n"):
        row = row.strip()
        if not row:
            continue

        t, f = row.split(",")
        bnet.append((t.strip(), f.strip()))

    t_width = max([7] + [len(x) for x, _ in bnet])
    f_width = max([7] + [len(x) for _, x in bnet])
    lines += ["### Network"]
    t, f = bnet.pop(0)
    lines += ["| " + t.ljust(t_width) + " | " + f.ljust(f_width) + " |"]
    lines += ["| " + t_width*"-" + " | " + f_width * "-" + " |"]
    for t, f in bnet:
        lines += ["| " + t.ljust(t_width) + " | " + f.ljust(f_width) + " |"]

    lines += ["", ""]
    text = "\n".join(lines)

    if fname_txt:
        with open(fname_txt, "w") as f:
            f.writelines(text)

        log.info(f"created {fname_txt}")

    return text


def compute_attractors_tarjan(stg: networkx.DiGraph):
    """
    Uses `networkx.strongly_connected_components <https://networkx.github.io/documentation/latest/reference/generated/networkx.algorithms.components.strongly_connected.strongly_connected_components.html>`_
    , i.e., Tarjan's algorithm with Nuutila's modifications, to compute the SCCs of *stg* and
    `networkx.has_path <https://networkx.github.io/documentation/latest/reference/generated/networkx.algorithms.shortest_paths.generic.has_path.html>`_
    to decide whether a SCC is reachable from another.
    Returns the attractors as lists of states.


    **arguments**:
        * *stg*: state transition graph

    **returns**:
        * *steady_states*: the steady states
        * *cyclic_attractors*: the cyclic attractors

    **example**:

        >>> bnet = ["x, !x&y | z",
        ...         "y, !x | !z",
        ...         "z, x&!y"]
        >>> bnet = "\\n".join(bnet)
        >>> primes = bnet2primes(bnet)
        >>> stg = primes2stg(primes, "asynchronous")
        >>> steady_states, cyclic_attractors = compute_attractors_tarjan(stg)
        >>> steady_states
        ["101","000"]
        >>> cyclic_attractors
        [{"111", "110"}, {"001", "011"}]
    """

    condensation_graph = digraph2condensationgraph(digraph=stg)
    steady_states = []
    cyclic = []
    for scc in condensation_graph.nodes():
        if not list(condensation_graph.successors(scc)):
            if len(scc) == 1:
                steady_states.append(scc[0])
            else:
                cyclic.append(set(scc))

    return steady_states, cyclic


def completeness_naive(primes, update, trap_spaces):
    """
    The naive approach to deciding whether *Trapspaces* is complete,
    i.e., whether there is no attractor outside of *Trapspaces*.
    The approach is described and discussed in :ref:`Klarner2015(a) <klarner2015trap>`.
    It is decided by a single CTL query of the :ref:`EF_oneof_subspaces <EF_oneof_subspaces>`.
    The state explosion problem limits this function to networks with around 40 variables.
    For networks with more variables (or a faster answer) use :ref:`completeness_iterative <completeness_iterative>`.

    .. note::
        Completeness depends on the update strategy, i.e.,
        a set of subspaces may be complete in the synchronous STG but not complete in the asynchronous STG or vice versa.

    .. note::
        A typical use case is to decide whether the minimal trap spaces of a network are complete.

    .. note::
        The subspaces of *Trapspaces* are in in fact not required to be a trap sets, i.e., it may contain arbitrary subspaces.
        If there are arbitrary subspaces then the semantics of the query is such that it checks whether each attractor *intersects* one of the subspaces.

    **arguments**:
        * *primes*: prime implicants
        * *update*: the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
        * *trap_spaces*: list of subspaces in string or dict representation

    **returns**:
        * *answer*: whether *subspaces* is complete in the STG defined by *primes* and *update*,

    **example**::

        >>> min_trap_spaces = trap_spaces(primes, "min")
        >>> answer, counterexample = completeness_naive(primes, "asynchronous", min_trap_spaces)
        >>> answer
        True
    """

    spec = f"CTLSPEC {exists_finally_one_of_subspaces(primes=primes, subspaces=trap_spaces)}"

    return model_checking(primes=primes, update=update, initial_states="INIT TRUE", specification=spec)


def completeness_naive_with_counterexample(primes: dict, update: str, trap_spaces: List[Union[dict, str]]):
    """
    The naive approach to deciding whether *Trapspaces* is complete,
    i.e., whether there is no attractor outside of *Trapspaces*.
    The approach is described and discussed in :ref:`Klarner2015(a) <klarner2015trap>`.
    It is decided by a single CTL query of the :ref:`EF_oneof_subspaces <EF_oneof_subspaces>`.
    The state explosion problem limits this function to networks with around 40 variables.
    For networks with more variables (or a faster answer) use :ref:`completeness_iterative <completeness_iterative>`.

    .. note::
        Completeness depends on the update strategy, i.e.,
        a set of subspaces may be complete in the synchronous STG but not complete in the asynchronous STG or vice versa.

    .. note::
        A typical use case is to decide whether the minimal trap spaces of a network are complete.

    .. note::
        The subspaces of *Trapspaces* are in in fact not required to be a trap sets, i.e., it may contain arbitrary subspaces.
        If there are arbitrary subspaces then the semantics of the query is such that it checks whether each attractor *intersects* one of the subspaces.

    **arguments**:
        * *primes*: prime implicants
        * *update*: the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
        * *Trapspaces*: list of subspaces in string or dict representation

    **returns**:
        * *answer*: whether *subspaces* is complete in the STG defined by *primes* and *update*,
        * *counter_example*: a state from which none of the *subspaces* is reachable (if *answer* is *False*)

    **example**::

        >>> mintspaces = trap_spaces(primes, "min")
        >>> answer, counterexample = completeness_naive(primes, "asynchronous", mintspaces)
        >>> answer
        True
    """

    spec = f"CTLSPEC {exists_finally_one_of_subspaces(primes=primes, subspaces=trap_spaces)}"
    init = "INIT TRUE"
    answer, counterexample = model_checking(primes=primes, update=update, initial_states=init, specification=spec, enable_counterexample=True)

    if counterexample:
        counterexample = counterexample[-1]

    return answer, counterexample


def intersection(*list_of_dicts):
    """
    each argument must be a list of subspaces (dicts)::

        >>> intersection([{"v1":1}], [{"v1":0}, {"v2":1, "v3":0}])
    """

    return [merge_dicts(dicts=x) for x in product(*list_of_dicts)]
