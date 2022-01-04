from itertools import combinations, product

from typing import List

from pyboolnet.prime_implicants import find_inputs, find_constants, create_constants, percolate, remove_variables
from pyboolnet.trap_spaces import compute_trap_spaces
from pyboolnet.attractors import completeness
from pyboolnet.model_checking import model_checking
from pyboolnet.temporal_logic import subspace2proposition
from pyboolnet.helpers import dicts_are_consistent


def is_included_in_subspace(subspace1: dict, subspace2: dict):
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

    return all(x in subspace1 and subspace1[x] == subspace2[x] for x in subspace2.keys())


def EFAG_set_of_subspaces(primes: dict, subspaces: List[dict]) -> str:
    """
    Construct a CTL formula that queries whether there is a path that leads to one of the *subspaces* and stays there.

    **arguments**:
        * *primes*: prime implicants.
        * *subspaces*: list of subspaces.

    **returns**:
        * *formula*: the CTL formula.

    """

    return 'EF(AG(' + ' | '.join([subspace2proposition(primes, x) for x in subspaces]) + '))'


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


def find_cs_perc(primes: dict, cs: List[dict], target: List[dict]) -> List[dict]:
    """
    Select the elements of *cs* that are control strategies for *target* by direct percolation.

    **arguments**:
        * *primes*: prime implicants.
        * *cs*: list of control strategies.
        * *target*: list of subspaces defining the target subset.

    **returns**:
        * *cs_perc*: list of control strategies by direct percolation.
    """

    cs_perc = list()
    for x in cs:
        perc = find_constants(primes=percolate(primes=primes, add_constants=x, copy=True))
        if any(is_included_in_subspace(perc, subs) for subs in target):
            cs_perc.append(x)
    return cs_perc


def control_is_valid_in_trap_spaces(primes, trap_spaces, target, update):
    """
    Returns wheter the *trap_spaces* are compatible with the *target*.

    **arguments**:
        * *primes*: prime implicants.
        * *trap_spaces*: list of trap spaces.
        * *target*: list of subspaces defining the target subset.
        * *update*: type of update, either *"synchronous"*, *"asynchronous"* or *"mixed"*.

    **returns**:
        * *cs_perc*: list of control strategies by direct percolation.
    """

    # Checking no trap spaces are disjoint from the target subset
    if not all(any(dicts_are_consistent(ts, subs) for subs in target) for ts in trap_spaces):
        return False

    # Checking trap spaces oscillating in-out the target subset
    half_ts = [ts for ts in trap_spaces if not any(is_included_in_subspace(ts, subs) for subs in target)]
    for ts in half_ts:
        if not reduce_and_run_control_query(primes, ts, target, update):
            return False

    return True


def reduce_and_run_control_query(primes, subspace, target, update):
    """
    Runs the model checking query for control after reducing the network by percolating the values in *subspace*.

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
    return run_control_query(new_primes, target, update)


def run_control_query(primes, target, update):
    """
    Runs the model checking query for control.

    **arguments**:
        * *primes*: prime implicants.
        * *target*: list of subspaces defining the target subset.
        * *update*: type of update, either *"synchronous"*, *"asynchronous"* or *"mixed"*.

    **returns**:
        * True if the query is true, False otherwise.
    """

    spec = 'CTLSPEC ' + EFAG_set_of_subspaces(primes, target)
    init = "INIT TRUE"
    return model_checking(primes, update, init, spec)


def control_direct_percolation(primes, candidate, target, silent=False):
    """
    Checks whether the subspace *candidate* is a control strategy for *target* by direct percolation.

    **arguments**:
        * *primes*: prime implicants.
        * *candidate*: subspace.
        * *target*: list of subspaces defining the target subset.
        * *silent*: if True, it does not print infos to screen. Default value: False.

    **returns**:
        * True if the *candidate* percolates into the *target*, False otherwise.
    """

    perc = find_constants(primes=percolate(primes=primes, add_constants=candidate, copy=True))
    if any(is_included_in_subspace(perc, subs) for subs in target):
        if not silent:
            print("Intervention (only percolation):", candidate)
            print("Percolation:", perc)
        return True
    return False


def control_completeness(primes: dict, candidate: dict, target: dict, update: str, silent=False):
    """
    Checks whether the subspace *candidate* is a control strategy for *target* by completeness.

    **arguments**:
        * *primes*: prime implicants.
        * *candidate*: subspace.
        * *target*: subspace defining the target subset.
        * *update*: type of update, either *"synchronous"*, *"asynchronous"* or *"mixed"*.
        * *silent*: if True, it does not print infos to screen. Default value: False.

    **returns**:
        * True if the *candidate* is a control strategy by completeness for *target*, False otherwise.
    """

    if type(target) == list:
        print("The target must be a subspace.")
        return

    perc = find_constants(primes=percolate(primes=primes, add_constants=candidate, copy=True))
    new_primes = fix_components_and_reduce(primes, perc, keep_vars=list(target.keys()))
    tsmin = compute_trap_spaces(new_primes, "min")

    if not all(is_included_in_subspace(T, target) for T in tsmin):
        return False

    if completeness(new_primes, update):
        if not silent:
            print("Intervention (by completeness):", candidate)
            print("Percolation:", perc)
        return True

    return False


def control_model_checking(primes: dict, candidate: dict, target: List[dict], update: str, silent: bool = False, max_output_trapspaces: int = 10000000):
    """
    Checks whether the subspace *candidate* is a control strategy for *target* using model checking.

    **arguments**:
        * *primes*: prime implicants.
        * *candidate*: subspace.
        * *target*: list of subspaces defining the target subset.
        * *update*: type of update, either *"synchronous"*, *"asynchronous"* or *"mixed"*.
        * *silent*: if True, it does not print infos to screen. Default value: False.

    **returns**:
        * True if the *candidate* is a control strategy by completeness for *target*, False otherwise.
    """

    if type(target) == dict:
        print("The target must be a list of subspaces.")
        return

    perc = find_constants(primes=percolate(primes=primes, add_constants=candidate, copy=True))
    new_primes = fix_components_and_reduce(primes, perc, keep_vars=list(set([item for subs in target for item in subs])))
    tsmin = compute_trap_spaces(new_primes, "min", max_output=max_output_trapspaces)

    if not control_is_valid_in_trap_spaces(new_primes, tsmin, target, update):
        return False

    if run_control_query(new_primes, target, update):
        if not silent:
            print("Intervention (by CTL formula):", candidate)
            print("Percolation:", perc)
        return True

    return False


def find_necessary_interventions(primes: dict, target: List[dict]) -> dict:
    """
    Find name and values of the inputs and constants from *primes* that are fixed in the *target*.

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


def find_common_variables_in_cs(primes: dict, target: List[dict]) -> dict:
    """
    Find name and values of the constants from *primes* that are fixed to a different value in the *target*.

    **arguments**:
        * *primes*: prime implicants
        * *target*: list of subspaces

    **returns**:
        * Names and values that are constants in *primes* and are fixed to a different value in the *target*.
    """

    inputs_consts_common_in_subs = find_necessary_interventions(primes, target)
    right_consts = [x for x in find_constants(primes) if x in inputs_consts_common_in_subs.keys() and inputs_consts_common_in_subs[k] == consts[x]]
    return dict((k, inputs_consts_common_in_subs[k]) for k in inputs_consts_common_in_subs.keys() if k not in right_consts)


def is_control_strategy(primes: dict, candidate: dict, target: List[dict], update: str, max_output: int = 1000000):
    """
    Check whether the *candidate* subspace is a control strategy for the *target* subset.

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

    # Preliminary setting

    if type(target) == dict:
        print("The target must be a list of subspaces.")
        return

    if control_direct_percolation(primes, candidate, target, silent=True):
        return True

    new_primes = fix_components_and_reduce(primes, candidate, list(set([x for subs in subspaces for x in subs])))
    tsmin = compute_trap_spaces(new_primes, "min", max_output=max_output)

    # Checking control is valid in the trap spaces
    if not control_is_valid_in_trap_spaces(new_primes, tsmin, target, update):
        return False

    # Checking general CTL query
    return run_control_query(new_primes, target, update)


def compute_control_strategies_with_completeness(primes: dict, target: dict, update: str = "asynchronous", limit: int = 3, avoid_nodes: List[str] = None, silent: bool = False, starting_length: int = 0, previous_cs: List[dict] = None, known_cs: List[dict] = None) -> List[dict]:
    """
    Identify control strategies for the *target* subspace using completeness.

    **arguments**:
        *primes*: prime implicants.
        *target*: target subspace.
        *update*: the type of update, either *"synchronous"*, *"asynchronous"* or *"mixed"*.
        *limit*: maximal size of the control strategies. Default value: 3.
        *silent*: if True, it does not print infos to screen. Default value: False.
        *starting_length*: minimum possible size of the control strategies. Default value: 0.
        *previous_cs*: list of already identified control strategies. Default value: empty list.
        *avoid_nodes*: list of nodes that cannot be part of any control strategy. Default value: empty list.

    **returns**:
        * *cs_total*: list of control strategies for the *target* subspace obtained using completeness.

    **example**::
        >>> control_strategies_completeness(primes, {'v1': 1}, "asynchronous")

    """

    # Initializing

    if previous_cs is None:
        previous_cs = []
    if avoid_nodes is None:
        avoid_nodes = []
    if known_cs is None:
        known_cs = []

    # Preliminary setting

    candidate_variables = [x for x in primes.keys() if x not in avoid_nodes]
    cs_total = previous_cs
    perc_true = known_cs
    perc_false = []

    common_vars_in_cs = find_common_variables_in_cs(primes, [target])
    candidate_variables = [x for x in primes.keys() if x not in common_vars_in_cs.keys() and x not in avoid_nodes]
    if not silent:
        print("Number of common variables in the CS:", len(common_vars_in_cs))
        print("Number of candiadate variables:", len(candidate_variables))

    # Computing control strategies

    for i in range(starting_length, limit + 1):

        if not silent:
            print("Checking control strategies of size", i)

        for vs in combinations(candidate_variables, i):

            # Consider all consistent combinations
            subsets = product(*[(0, 1)]*i)
            for ss in subsets:
                candidate = dict(zip(vs, ss))
                candidate.update(common_vars_in_cs)

                if not any(is_included_in_subspace(candidate, x) for x in cs_total):
                    perc = find_constants(primes=percolate(primes=primes, add_constants=candidate, copy=True))

                    if perc in perc_true:

                        if not silent:
                            print("Intervention:", candidate)
                            print("Percolation:", perc)
                        cs_total.append(candidate)

                    elif perc not in perc_false:

                        if control_direct_percolation(primes, candidate, [target], silent=silent):
                            perc_true.append(perc)
                            cs_total.append(candidate)

                        elif control_completeness(primes, candidate, target, update, silent=silent):
                            perc_true.append(perc)
                            cs_total.append(candidate)

                        else:
                            perc_false.append(perc)

    return cs_total


def compute_control_strategies_with_model_checking(primes: dict, target: List[dict], update: str = "asynchronous", limit: int = 3, avoid_nodes: List[str] = None, silent: bool = False, max_output_trapspaces: int = 1000000, starting_length: int = 0, previous_cs: List[dict] = None, known_cs: List[dict] = None):

    """
    Identifies control strategies for the *target* subset using model checking.

    **arguments**:
        *primes*: prime implicants
        *target*: list of subspaces defining the target subset
        *update*: the type of update, either *"synchronous"*, *"asynchronous"* or *"mixed"*
        *limit*: maximal size of the control strategies. Default value: 3.
        *silent*: if True, does not print infos to screen. Default value: False.
        *starting_length*: minimum possible size of the control strategies. Default value: 0.
        *previous_cs*: list of already identified control strategies. Default value: empty list.
        *avoid_nodes*: list of nodes that cannot be part of the control strategies. Default value: empty list.

    **returns**:
        * *cs_total*: list of control strategies (dict) of *subspace* obtained using completeness.

    **example**::
        >>> ultimate_control_multispace(primes, {'v1': 1}, "asynchronous")

    """

    # Intializing

    if previous_cs is None:
        previous_cs = []
    if avoid_nodes is None:
        avoid_nodes = []
    if known_cs is None:
        known_cs = []

    # Preliminary setting

    cs_total = previous_cs
    perc_true = known_cs
    perc_false = []
    if type(target) != list:
        print("The target must be a list.")

    common_vars_in_cs = find_common_variables_in_cs(primes, target)
    candidate_variables = [x for x in primes.keys() if x not in common_vars_in_cs.keys() and x not in avoid_nodes]
    if not silent:
        print("Number of common variables in the CS:", len(common_vars_in_cs))
        print("Number of candiadate variables:", len(candidate_variables))

    # Computing control strategies

    for i in range(max(0, starting_length - len(common_vars_in_cs)), limit + 1 - len(common_vars_in_cs)):

        if not silent:
            print("Checking control strategies of size", i + len(common_vars_in_cs))

        for vs in combinations(candidate_variables, i):
            subsets = product(*[(0, 1)]*i)

            for ss in subsets:
                candidate = dict(zip(vs, ss))
                candidate.update(common_vars_in_cs)

                if not any(is_included_in_subspace(candidate, x) for x in cs_total):
                    perc = find_constants(primes=percolate(primes=primes, add_constants=candidate, copy=True))

                    if perc in perc_true:

                        if not silent:
                            print("Intervention:", candidate)
                            print("Percolation:", perc)
                        cs_total.append(candidate)

                    elif perc not in perc_false:

                        if control_direct_percolation(primes, candidate, target, silent=silent):
                            perc_true.append(perc)
                            cs_total.append(candidate)

                        elif control_model_checking(primes, candidate, target, update, silent=silent):
                            perc_true.append(perc)
                            cs_total.append(candidate)

                        else:
                            perc_false.append(perc)

    return cs_total
