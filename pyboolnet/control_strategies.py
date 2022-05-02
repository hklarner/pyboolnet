import logging
from itertools import combinations, product
from typing import List, Optional

from pyboolnet.prime_implicants import find_inputs, find_constants, create_constants, percolate, remove_variables
from pyboolnet.trap_spaces import compute_trap_spaces
from pyboolnet.attractors import completeness
from pyboolnet.model_checking import model_checking
from pyboolnet.temporal_logic import subspace2proposition
from pyboolnet.helpers import dicts_are_consistent

log = logging.getLogger(__file__)


def is_included_in_subspace(subspace1: dict, subspace2: dict) -> bool:
    """
    Test whether *subspace1* is contained in *subspace2*.

    **arguments**:
        * *subspace1*, *subspace2* (dicts): subspaces.
    **returns**:
        * Answer (bool): whether *subspace1* is contained in *subspace2*.
    **example**::
        >>> is_included_in_subspace({'v1': 0, 'v2': 1}, {'v2': 1})
        True
    """

    answer = all(x in subspace1 and subspace1[x] == subspace2[x] for x in subspace2.keys())

    return answer


def EFAG_set_of_subspaces(primes: dict, subspaces: List[dict]) -> str:
    """
    Construct a CTL formula that queries whether there is a path that leads to the union of the *subspaces* and stays there.

    **arguments**:
        * *primes*: prime implicants.
        * *subspaces*: list of subspaces.

    **returns**:
        * *formula*: the CTL formula.
    """

    formula = 'EF(AG(' + ' | '.join([subspace2proposition(primes, x) for x in subspaces]) + '))'

    return formula


def fix_components_and_reduce(primes: dict, subspace: dict, keep_vars: List[str] = []) -> dict:
    """
    Fix the variables fixed in *subspace* and percolates their values in *primes*. Returns the resulting set of primes after removing all the constant variables that are not in *keep_vars*.

    **arguments**:
        * *primes*: prime implicants.
        * *subspace*: subspace.
        * *keep_vars*: list of variables to keep in *primes*.

    **returns**:
        * *new_primes*: prime implicants after fixing the variables in *subspace*, percolating them and removing the constant variables not in *keep_vars*.
    """

    new_primes = percolate(primes, add_constants=subspace, copy=True)
    removable_vars = [k for k in find_constants(new_primes) if k not in keep_vars]
    new_primes = remove_variables(new_primes, removable_vars, copy=True)

    return new_primes


def select_control_strategies_by_percolation(primes: dict, strategies: List[dict], target: List[dict]) -> List[dict]:
    """
    Select the elements of *strategies* that are control strategies for *target* by direct percolation.

    **arguments**:
        * *primes*: prime implicants.
        * *strategies*: list of control strategies.
        * *target*: list of subspaces defining the target subset.

    **returns**:
        * *selected_strategies*: list of control strategies by direct percolation.
    """

    selected_strategies = []
    for x in strategies:
        percolation = find_constants(primes=percolate(primes=primes, add_constants=x, copy=True))
        if any(is_included_in_subspace(percolation, subs) for subs in target):
            selected_strategies.append(x)

    return selected_strategies


def control_is_valid_in_trap_spaces(primes: dict, trap_spaces: List[dict], target: List[dict], update: str) -> bool:
    """
    Return whether the *trap_spaces* are compatible with the *target* by checking that no trap space is disjoint from the *target* and applying the control query to all the trap spaces oscillating in and out the *target*.

    **arguments**:
        * *primes*: prime implicants.
        * *trap_spaces*: list of trap spaces.
        * *target*: list of subspaces defining the target subset.
        * *update*: type of update, either *"synchronous"*, *"asynchronous"* or *"mixed"*.

    **returns**:
        * *cs_perc*: list of control strategies by direct percolation.
    """

    if not all(any(dicts_are_consistent(ts, subs) for subs in target) for ts in trap_spaces):
        return False

    half_ts = [ts for ts in trap_spaces if not any(is_included_in_subspace(ts, subs) for subs in target)]
    for ts in half_ts:
        if not reduce_and_run_control_query(primes, ts, target, update):
            return False

    return True


def reduce_and_run_control_query(primes: dict, subspace: dict, target: List[dict], update: str):
    """
    Run the model checking query for control after reducing the network by percolating the values in *subspace*.

    **arguments**:
        * *primes*: prime implicants.
        * *subspace*: subspace.
        * *target*: list of subspaces defining the target subset.
        * *update*: type of update, either *"synchronous"*, *"asynchronous"* or *"mixed"*.

    **returns**:
        * True if the query is true, false otherwise.
    """

    target_vars = list(set([item for subs in target for item in subs]))
    new_primes = fix_components_and_reduce(primes, subspace, keep_vars=target_vars)
    answer = run_control_query(new_primes, target, update)

    return answer


def run_control_query(primes: dict, target: List[dict], update: str) -> bool:
    """
    Run the model checking query for control as described in :ref:`CifuentesFontanals2022 <CifuentesFontanals2022>` Sec 4.2.

    **arguments**:
        * *primes*: prime implicants.
        * *target*: list of subspaces defining the target subset.
        * *update*: type of update, either *"synchronous"*, *"asynchronous"* or *"mixed"*.

    **returns**:
        * True if the query is true, False otherwise.
    """

    spec = 'CTLSPEC ' + EFAG_set_of_subspaces(primes, target)
    init = "INIT TRUE"
    answer = model_checking(primes, update, init, spec)

    return answer


def control_direct_percolation(primes: dict, candidate: dict, target: List[dict]) -> bool:
    """
    Check whether the subspace *candidate* is a control strategy for *target* by direct percolation.

    **arguments**:
        * *primes*: prime implicants.
        * *candidate*: subspace.
        * *target*: list of subspaces defining the target subset.

    **returns**:
        * True if the *candidate* percolates into the *target*, False otherwise.
    """

    perc = find_constants(primes=percolate(primes=primes, add_constants=candidate, copy=True))

    if any(is_included_in_subspace(perc, subs) for subs in target):
        log.info(f"Intervention (only percolation): {candidate}")
        return True

    return False


def control_completeness(primes: dict, candidate: dict, target: dict, update: str) -> Optional[bool]:
    """
    Check whether the subspace *candidate* is a control strategy for *target* by the completeness approach,
    described in :ref:`CifuentesFontanals2022 <CifuentesFontanals2022>` Sec 3.2.

    **arguments**:
        * *primes*: prime implicants.
        * *candidate*: subspace.
        * *target*: subspace defining the target subset.
        * *update*: type of update, either *"synchronous"*, *"asynchronous"* or *"mixed"*.

    **returns**:
        * True if the *candidate* is a control strategy by completeness for *target*, False otherwise.
    """

    if type(target) != dict:
        log.error("The target must be a subspace (dict).")
        return

    perc = find_constants(primes=percolate(primes=primes, add_constants=candidate, copy=True))
    new_primes = fix_components_and_reduce(primes, perc, keep_vars=list(target.keys()))
    minimal_trap_spaces = compute_trap_spaces(new_primes, "min")

    if not all(is_included_in_subspace(T, target) for T in minimal_trap_spaces):
        return False

    if completeness(new_primes, update):
        log.info(f"Intervention (by completeness): {candidate}")
        return True

    return False


def control_model_checking(primes: dict, candidate: dict, target: List[dict], update: str, max_output_trapspaces: int = 10000000) -> Optional[bool]:
    """
    Check whether the subspace *candidate* is a control strategy for *target* using the model checking approach
    described in :ref:`CifuentesFontanals2022 <CifuentesFontanals2022>` Sec 4.3.

    **arguments**:
        * *primes*: prime implicants.
        * *candidate*: subspace.
        * *target*: list of subspaces defining the target subset.
        * *update*: type of update, either *"synchronous"*, *"asynchronous"* or *"mixed"*.

    **returns**:
        * True if the *candidate* is a control strategy by completeness for *target*, False otherwise.
    """

    if type(target) != list:
        log.error("The target must be a list of subspaces.")
        return

    perc = find_constants(primes=percolate(primes=primes, add_constants=candidate, copy=True))
    new_primes = fix_components_and_reduce(primes, perc, keep_vars=list(set([item for subs in target for item in subs])))
    minimal_trap_spaces = compute_trap_spaces(new_primes, "min", max_output=max_output_trapspaces)

    if not control_is_valid_in_trap_spaces(new_primes, minimal_trap_spaces, target, update):
        return False

    if run_control_query(new_primes, target, update):
        log.info(f"Intervention (by CTL formula): {candidate}")
        return True

    return False


def find_necessary_interventions(primes: dict, target: List[dict]) -> dict:
    """
    Find the names and values of the inputs and constants from *primes* that are fixed in the *target*.

    **arguments**:
        * *primes*: prime implicants
        * *target*: list of subspaces

    **returns**:
        * *selected_vars*: Names and values that are inputs or constants in *primes* and are fixed in the *target*.
    """

    selected_vars = dict()
    candidates = find_inputs(primes) + list(find_constants(primes).keys())
    for x in candidates:
        if all(x in y.keys() for y in target):
            if all(y[x] == z[x] for y in target for z in target):
                selected_vars[x] = target[0][x]

    return selected_vars


def find_common_variables_in_control_strategies(primes: dict, target: List[dict]) -> dict:
    """
    Find the names and values of the constants from *primes* that are fixed to a different value in the *target* and therefore need to be part of any control strategy.

    **arguments**:
        * *primes*: prime implicants
        * *target*: list of subspaces

    **returns**:
        * Names and values that are constants in *primes* and are fixed to a different value in the *target*.
    """

    common_inputs_and_constants_in_target = find_necessary_interventions(primes, target)
    constants = find_constants(primes)
    right_constants = [x for x in constants if x in common_inputs_and_constants_in_target.keys() and common_inputs_and_constants_in_target[x] == constants[x]]
    common_variables = {k: common_inputs_and_constants_in_target[k] for k in common_inputs_and_constants_in_target.keys() if k not in right_constants}

    return common_variables


def is_control_strategy(primes: dict, candidate: dict, target: List[dict], update: str, max_output: int = 1000000) -> Optional[bool]:
    """
    Check whether the *candidate* subspace is a control strategy for the *target* subset,
    as defined in ref:`CifuentesFontanals2022 <CifuentesFontanals2022>`.

    **arguments**:
        * *primes*: prime implicants.
        * *candidate*: candidate subspace.
        * *target*: list of subspaces defining the target subset.
        * *update*: type of update, either *"synchronous"*, *"asynchronous"* or *"mixed"*.
        * *max_output*: maximum number of trap spaces computed. Default value: 1000000.

    **returns**:
        * *answer*: True if the *candidate* is a control strategy for the *target*, False otherwise. When False, a counterexample (minimal trap space disjoint with target or state not satisfying the CTL query) is also returned.

    **example**::
        >>> is_control_strategy(primes, {'v1': 1}, [{'v2': 0}, {'v3':1}], "asynchronous")
    """

    if type(target) != list:
        log.error("The target must be a list of subspaces.")
        return

    if control_direct_percolation(primes, candidate, target):
        return True

    new_primes = fix_components_and_reduce(primes, candidate, list(set([x for subs in target for x in subs])))
    minimal_trap_spaces = compute_trap_spaces(new_primes, "min", max_output=max_output)

    if not control_is_valid_in_trap_spaces(new_primes, minimal_trap_spaces, target, update):
        return False

    answer = run_control_query(new_primes, target, update)

    return answer


def compute_control_strategies_with_completeness(primes: dict, target: dict, update: str = "asynchronous", limit: int = 3, avoid_nodes: List[str] = None, starting_length: int = 0, known_strategies: List[dict] = None) -> Optional[List[dict]]:
    """
    Identify control strategies for the *target* subspace using the completeness approach
    described in :ref:`CifuentesFontanals2022 <CifuentesFontanals2022>` Sec 3.2.

    **arguments**:
        *primes*: prime implicants.
        *target*: target subspace.
        *update*: the type of update, either *"synchronous"*, *"asynchronous"* or *"mixed"*.
        *limit*: maximal size of the control strategies. Default value: 3.
        *starting_length*: minimum possible size of the control strategies. Default value: 0.
        *known_strategies*: list of already identified control strategies. Default value: empty list.
        *avoid_nodes*: list of nodes that cannot be part of any control strategy. Default value: empty list.

    **returns**:
        * *list_strategies*: list of control strategies for the *target* subspace obtained using completeness.

    **example**::
        >>> control_strategies_completeness(primes, {'v1': 1}, "asynchronous")
    """

    if type(target) == list:
        log.error("The target must be a subspace.")
        return

    avoid_nodes = avoid_nodes or []
    known_strategies = known_strategies or []

    candidate_variables = [x for x in primes.keys() if x not in avoid_nodes]
    list_strategies = known_strategies
    perc_true = known_strategies
    perc_false = []

    common_vars_in_cs = find_common_variables_in_control_strategies(primes, [target])
    candidate_variables = [x for x in primes.keys() if x not in common_vars_in_cs.keys() and x not in avoid_nodes]
    log.info(f"Number of common variables in the CS: {len(common_vars_in_cs)}")
    log.info(f"Number of candiadate variables: {len(candidate_variables)}")


    for i in range(max(0, starting_length - len(common_vars_in_cs)), limit + 1 - len(common_vars_in_cs)):

        log.info(f"Checking control strategies of size {i + len(common_vars_in_cs)}")

        for vs in combinations(candidate_variables, i):

            subsets = product(*[(0, 1)]*i)
            for ss in subsets:
                candidate = dict(zip(vs, ss))
                candidate.update(common_vars_in_cs)

                if not any(is_included_in_subspace(candidate, x) for x in list_strategies):
                    perc = find_constants(primes=percolate(primes=primes, add_constants=candidate, copy=True))

                    if perc in perc_true:
                        log.info(f"Intervention: {candidate}")
                        list_strategies.append(candidate)

                    elif perc not in perc_false:

                        if control_direct_percolation(primes, candidate, [target]):
                            perc_true.append(perc)
                            list_strategies.append(candidate)

                        elif control_completeness(primes, candidate, target, update):
                            perc_true.append(perc)
                            list_strategies.append(candidate)

                        else:
                            perc_false.append(perc)

    return list_strategies


def compute_control_strategies_with_model_checking(primes: dict, target: List[dict], update: str = "asynchronous", limit: int = 3, avoid_nodes: List[str] = None, max_output_trapspaces: int = 1000000, starting_length: int = 0, known_strategies: List[dict] = None) -> Optional[List[dict]]:
    """
    Identify all minimal control strategies for the *target* subset using the model checking approach
    described in :ref:`CifuentesFontanals2022 <CifuentesFontanals2022>` Sec 4.3.

    **arguments**:
        *primes*: prime implicants
        *target*: list of subspaces defining the target subset
        *update*: the type of update, either *"synchronous"*, *"asynchronous"* or *"mixed"*
        *limit*: maximal size of the control strategies. Default value: 3.
        *starting_length*: minimum possible size of the control strategies. Default value: 0.
        *known_strategies*: list of already identified control strategies. Default value: empty list.
        *avoid_nodes*: list of nodes that cannot be part of the control strategies. Default value: empty list.

    **returns**:
        * *list_strategies*: list of control strategies (dict) of *subspace* obtained using completeness.

    **example**::
        >>> ultimate_control_multispace(primes, {'v1': 1}, "asynchronous")

    """

    if type(target) != list:
        log.error("The target must be a list.")
        return

    avoid_nodes = avoid_nodes or []
    known_strategies = known_strategies or []

    list_strategies = known_strategies
    perc_true = known_strategies
    perc_false = []

    common_vars_in_cs = find_common_variables_in_control_strategies(primes, target)
    candidate_variables = [x for x in primes.keys() if x not in common_vars_in_cs.keys() and x not in avoid_nodes]
    log.info(f"Number of common variables in the CS: {len(common_vars_in_cs)}")
    log.info(f"Number of candiadate variables: {len(candidate_variables)}")


    for i in range(max(0, starting_length - len(common_vars_in_cs)), limit + 1 - len(common_vars_in_cs)):

        log.info(f"Checking control strategies of size {i + len(common_vars_in_cs)}")

        for vs in combinations(candidate_variables, i):
            subsets = product(*[(0, 1)]*i)

            for ss in subsets:
                candidate = dict(zip(vs, ss))
                candidate.update(common_vars_in_cs)

                if not any(is_included_in_subspace(candidate, x) for x in list_strategies):
                    perc = find_constants(primes=percolate(primes=primes, add_constants=candidate, copy=True))

                    if perc in perc_true:
                        log.info(f"Intervention: {candidate}")
                        list_strategies.append(candidate)

                    elif perc not in perc_false:

                        if control_direct_percolation(primes, candidate, target):
                            perc_true.append(perc)
                            list_strategies.append(candidate)

                        elif control_model_checking(primes, candidate, target, update):
                            perc_true.append(perc)
                            list_strategies.append(candidate)

                        else:
                            perc_false.append(perc)

    return list_strategies
