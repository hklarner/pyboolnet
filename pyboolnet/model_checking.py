

import datetime
import logging
import os
import subprocess
import sys
import tempfile
from typing import Tuple, Optional

from pyboolnet import find_command, NUSMV_KEYWORDS
from pyboolnet.prime_implicants import CONSTANT_ON, CONSTANT_OFF
from pyboolnet.state_space import VAN_HAM_EXTENSIONS, find_vanham_variables
from pyboolnet.state_transition_graphs import UPDATE_STRATEGIES
from pyboolnet.temporal_logic import subspace2proposition

CMD_NUSMV = find_command("nusmv")

log = logging.getLogger(__file__)


def print_warning_accepting_states_bug(primes: dict, ctl_spec: str):
    """
    This bug occurs when the Specification is equivalent to TRUE or FALSE.
    """

    if all(x not in ctl_spec for x in primes):
        log.warning("accepting states bug might affect this result, see http://github.com/hklarner/PyBoolNet/issues/14")


def model_checking(
        primes: dict,
        update: str,
        initial_states: str,
        specification: str,
        dynamic_reorder: bool = True,
        disable_reachable_states: bool = True,
        cone_of_influence: bool = True,
        enable_counterexample: bool = False,
        enable_accepting_states: bool = False):
    """
    Calls :ref:`installation_nusmv` to check whether the *specification* is true or false in the transition system defined by *primes*,
    the *initial_states* and *update*.
    The remaining arguments are :ref:`installation_nusmv` options, see the manual at http://nusmv.fbk.eu for details.

    See :ref:`primes2smv` and :ref:`Sec. 3.4 <sec:model_checking>` for details on model checking with |Software|.

    The accepting states are a dictionary with the following keywords:
        * `INIT`: a Boolean expression for the initial states, or `None`, see note below
        * `INIT_SIZE`: integer number of initial states, or `None`, see note below
        * `ACCEPTING`: a Boolean expression for the accepting states
        * `ACCEPTING_SIZE`: integer number of accepting states
        * `INITACCEPTING`: a Boolean expression for the intersection of initial and accepting states, or `None`, see note below
        * `INITACCEPTING_SIZE`: integer number of states in the intersection of initial and accepting states, or `None`, see note below

    .. note::
        *disable_reachable_states* is enforced as the accepting states are otherwise over-approximated.

    .. note::
        Model checking with accepting states is only possible for CTL model checking.

    .. note::
        If the *ctl_spec* is equivalent to either `TRUE` or `FALSE` then NuSMV will not compute the initial states,
        because it does not have to to find out what the *answer* to the query is.
        In that case the four values that involve the initial states are set to `None`.

    .. note::
        *cone_of_influence* is not available when using counterexamples as it "messes" with the output.

    **arguments**:
        * *primes*: prime implicants
        * *update*: the update strategy, either *"synchronous"*, *"asynchronous"* or *"mixed"*
        * *initial_states*: a :ref:`installation_nusmv` expression for the initial states, including the keyword *INIT*
        * *specification*: a :ref:`installation_nusmv` formula, including the keyword *LTLSPEC* or *CTLSPEC*
        * *dynamic_reorder*: enables dynamic reordering of variables using *-dynamic*
        * *disable_reachable_states*: disables the computation of reachable states using *-df*
        * *cone_of_influence*: enables cone of influence reduction using *-coi*
        * *enable_counterexample*: enables cone of influence reduction using *-coi*
        * *enable_accepting_states*: enables cone of influence reduction using *-coi*

    **returns**:
        * *answer*: model checking result
        * *counterexample*: a countereample, if *enable_counterexample*
        * *accepting_states*: the accepting states, if *enable_accepting_states*

    **example**::

        >>> initial_states = "INIT TRUE"
        >>> update = "asynchronous"
        >>> specification = "CTLSPEC AF(EG(v1&!v2))"
        >>> model_checking(primes, update, initial_states, specification)
        False
        >>> answer, counterexample = model_checking(primes, update, initial_states, specification, enable_counterexample=True)
        >>> answer, accepting_states = model_checking(primes, update, initial_states, specification, enable_accepting_states=True)
    """

    if enable_accepting_states and specification[:7] != "CTLSPEC":
        log.error(f"model checking with accepting states is only possible for CTL specifications: specification={specification}")
        sys.exit()

    tmp_file = tempfile.NamedTemporaryFile(delete=False, prefix="pyboolnet_")
    tmp_fname = tmp_file.name
    log.debug(f"created {tmp_fname}")
    tmp_file.close()
    primes2smv(primes=primes, update=update, initial_states=initial_states, specification=specification, fname_smv=tmp_fname)

    answer = model_checking_smv_file(
        fname_smv=tmp_fname,
        dynamic_reorder=dynamic_reorder,
        disable_reachable_states=disable_reachable_states,
        cone_of_influence=cone_of_influence,
        enable_counterexample=enable_counterexample,
        enable_accepting_states=enable_accepting_states)

    if os.path.isfile(tmp_fname):
        os.remove(tmp_fname)

    return answer


def model_checking_smv_file(
        fname_smv: str,
        dynamic_reorder: bool = True,
        disable_reachable_states: bool = True,
        cone_of_influence: bool = True,
        enable_counterexample: bool = False,
        enable_accepting_states: bool = False):
    """
    Convenience function for model checking of smv files.
    See `model_checking` for details of parameters and returned objects.
    """

    cmd = [CMD_NUSMV]

    if not enable_counterexample:
        cmd += ["-dcx"]

    if dynamic_reorder:
        cmd += ["-dynamic"]
    if disable_reachable_states or enable_accepting_states:
        cmd += ["-df"]
    if cone_of_influence and not enable_counterexample:
        cmd += ["-coi"]

    if enable_accepting_states:
        cmd += ["-a", "print"]

    cmd += [fname_smv]
    cmd_text = " ".join(cmd)
    process = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    output, error = process.communicate()
    output = output.decode()

    if process.returncode == 0:
        if output.count("specification") > 1:
            log.error("SMV file contains more than one CTL or LTL specification.")
            sys.exit()

        if "is false" in output:
            answer = False
        elif "is true" in output:
            answer = True
        else:
            log.error(f"nusmv output not recognized: cmd={cmd_text}, output={output}, error={error}")
            sys.exit()
    else:
        log.error(f"nusmv did not respond with return code 0: cmd={cmd_text}, return_code={process.returncode} output={output}, error={error}")
        sys.exit()

    if not enable_counterexample and not enable_accepting_states:
        return answer

    result = [answer]

    if enable_counterexample:
        counterexample = _read_counterexample(nusmv_output=output)
        result.append(counterexample)

    if enable_accepting_states:
        accepting_states = _read_accepting_states(nusmv_output=output)
        result.append(accepting_states)

    return result


def primes2smv(primes: dict, update: str, initial_states, specification: str, fname_smv: Optional[str] = None) -> str:
    """
    Creates a NuSMV_ file from Primes and additional parameters that specify the update strategy, the initial states and the temporal logic specification.

    The initial states must be defined in :ref:`installation_nusmv` syntax, i.e.,
    starting with the keyword *INIT*.
    :ref:`installation_nusmv` uses *|* for disjunction, *&* for conjunction and *!* for negation.
    To set the initial states to the whole state space use *"INIT TRUE"*.
    CTL formulas must start with the keyword *CTLSPEC* and LTL formulas with the keyword *LTLSPEC*.

    .. note::
        The :ref:`installation_nusmv` language is case-sensitive and does not allow single character names for variables.

    .. note::
        This function detects Boolean variables that represent multi-valued components (van Ham encoding), see :ref:`StateTransitionGraphs.find_vanham_variables <find_vanham_variables>` for details.
        For each multi-valued variable it adds an INIT constraint that restricts the initial states to the admissible states of the van Ham encoding.


    In addition to variables that encode the activities of the components,
    auxillary variables are defined and available for use in CTL or LTL formulas,
    see :ref:`Sec. 3.4 <sec:model_checking>` for details:

    They are the Boolean *name_IMAGE* which is the value of the update function of the variable *name* in a state,
    the Boolean *name_STEADY* which is the value for whether the variable *name* is steady in a state,
    the integer *SUCCESSORS* which is the number of successors excluding itself (i.e., the number of variables that are changing in a state), and
    the Boolean *STEADYSTATE* which is the value for whether the current state is a steady state (which is equivalent to *SUCCESSORS=0*).

    **arguments**:
        * *primes*: prime implicants
        * *update*: the update strategy, either *"synchronous"*, *"asynchronous"* or *"mixed"*
        * *initial_states*: a :ref:`installation_nusmv` expression for the initial states, including the keyword *INIT*
        * *specification*: a :ref:`installation_nusmv` formula, including the keyword *LTLSPEC* or *CTLSPEC*
        * *fname_smv*: name for *smv* file or *None*

    **returns**:
       * *fname_smv*: file as string or *None* if *FnameSMV is None*

    **example**::

        >>> ctlspec = "CTLSPEC EF(AG(!ERK) | AG(ERK))"
        >>> ltlspec = "LTLSPEC F(G(ERK))"
        >>> primes2smv(primes, "asynchronous", "INIT TRUE",  ctlspec, "mapk.smv")
        >>> primes2smv(primes, "synchronous",  "INIT ERK=1", ltlspec, "mapk.smv")
        >>> lines = primes2smv(primes, "synchronous",  "INIT ERK=1", ltlspec)
    """

    assert fname_smv is None or type(fname_smv) is str
    assert update in UPDATE_STRATEGIES
    assert initial_states[:5] == "INIT "
    assert specification[:8] in ["CTLSPEC ", "LTLSPEC "]

    if not primes:
        log.info('You are trying to create an SMV file for the empty Boolean network.')
        log.info('Raising an exception to force you to decide what you want to do with empty Boolean networks (e.g. via a try-except block).')
        sys.exit()

    critical = [x for x in primes if len(x) == 1]
    if critical:
        log.info("NuSMV requires variables names of at least two characters.")
        log.info(f"The network contains the following single character variables names: {critical}")
        sys.exit()

    critical = [x for x in primes if x.lower() == 'successors']
    if critical:
        log.info("Variable are not allowed to be called SUCCESSORS.")
        log.info(f"Please change the name of the following variable: {critical}")
        sys.exit()

    critical = [x for x in primes if x.lower() == 'steadystate']
    if critical:
        log.info("Variable are not allowed to be called STEADYSTATE.")
        log.info(f"Please change the name of the following variable: {critical}")
        sys.exit()

    critical = [x for x in primes if '_image' in x.lower()]
    if critical:
        log.info("Variable names that include _IMAGE are not allowed.")
        log.info(f"Please change the name of the following variable: {critical}")
        sys.exit()

    critical = [x for x in primes if '_steady' in x.lower()]
    if critical:
        log.info("Variable names that include _STEADY are not allowed.")
        log.info(f"Please change the name of the following variable: {critical}")
        sys.exit()

    keywords = [x for x in primes if x in NUSMV_KEYWORDS]
    if keywords:
        log.info("NuSMV keywords are not allowed as variable names.")
        log.info(f"The network contains the following variables names that are also NuSMV keywords: {keywords}")
        sys.exit()

    names = sorted(primes)
    lines = [f"-- created on {datetime.date.today().strftime('%d. %b. %Y')} using PyBoolNet",
             "-- project home page https://github.com/hklarner/PyBoolNet",
             "",
             "",
             "MODULE main"]

    lines += ["", "VAR"]
    lines += [f"\t{name}: boolean;" for name in names]

    lines += [""]
    lines += ["DEFINE"]

    for name in names:
        if primes[name] == CONSTANT_ON:
            expression = "TRUE"

        elif primes[name] == CONSTANT_OFF:
            expression = "FALSE"

        else:
            expression = " | ".join(subspace2proposition(primes, x) for x in primes[name][1])

        lines += [f"\t{name}_IMAGE := {expression};"]

    lines += [""]
    lines += ["\t{n}_STEADY := ({n}_IMAGE = {n});".format(n=name) for name in names]
    lines += [""]
    x = ", ".join([f"(!{name}_STEADY)" for name in names])
    lines += [f"\tSUCCESSORS := count({x});"]
    lines += ["\tSTEADYSTATE := (SUCCESSORS = 0);"]

    lines += [""]
    lines += ["ASSIGN"]
    if update == "synchronous":
        lines += [f"\tnext({name}) := {name}_IMAGE;" for name in names]

    elif update == "asynchronous":
        lines += [f"\tnext({name}) := {{{name}, {name}_IMAGE}};" for name in names]
        lines += ["", "TRANS STEADYSTATE | count(" + ", ".join([f"(next({name})!={name})" for name in names])+")=1;"]

    elif update == "mixed":
        lines += [f"\tnext({name}) := {{{name}, {name}_IMAGE}};" for name in names]
        lines += ["", "TRANS " + ' | '.join(['STEADYSTATE']+[f"(next({name})!={name})" for name in names])+";"]

    lines += ["", ""]
    lines += [initial_states]

    vanham = find_vanham_variables(primes)

    for k in vanham:
        if k == 2:
            continue

        if not vanham[k]:
            continue

        lines += [""]
        lines += [f"-- adding van ham constraints for {k}-valued variables: {', '.join(vanham[k])}"]
        zipped = list(zip(VAN_HAM_EXTENSIONS[k][1:], VAN_HAM_EXTENSIONS[k][:-1]))

        for name in vanham[k]:
            lines += [f"INIT {name+x} -> {name+y}" for x, y in zipped]

        log.info(f"added INIT constraints (Van Ham encoding) for {k}-valued components {', '.join(vanham[k])}")

    lines += [""]
    lines += [specification]

    text_smv = "\n".join(lines)

    with open(fname_smv, "w") as f:
        f.write(text_smv)

    log.info(f"created {fname_smv}")

    return text_smv


def _read_counterexample(nusmv_output: str) -> Optional[Tuple[dict, ...]]:
    """
    Converts the output of a NuSMV call into a sequence of states that proves that the query is false.

    **arguments**:
        * *nusmv_output*: output of a call to NuSMV

    **returns**:
        * *counterexample*: a sequence of states that disprove the query.
    """

    if "Trace Type: Counterexample" not in nusmv_output:
        return None

    assert nusmv_output.count("Trace Type: Counterexample") == 1

    counterexample = []
    last_state = False
    blocks = nusmv_output.split("Trace Type: Counterexample")[1]
    blocks = blocks.split("-> ")

    for block in blocks:
        lines = block.split("\n")
        lines = [x.strip() for x in lines]
        lines = [x for x in lines if "=" in x]
        lines = [x for x in lines if "_IMAGE" not in x]
        lines = [x for x in lines if "_STEADY" not in x]
        lines = [x for x in lines if not x.startswith("SUCCESSORS")]
        lines = [x for x in lines if not x.startswith("STEADYSTATE")]
        lines = [x for x in lines if x != []]

        if lines:
            if last_state:
                state = last_state.copy()
            else:
                state = {}

            for line in lines:
                name, value = line.split(" = ")
                assert value in ["TRUE", "FALSE"]
                state[name] = 1 if value == "TRUE" else 0

            counterexample.append(state)
            last_state = state

    return tuple(counterexample)


def _read_number(line: str):
    line = line.split(":")[1].strip()
    if "e" in line:
        return float(line)
    elif sys.version_info > (3,):
        return int(line)
    else:
        return float(line)


def _read_formula(line):
    """
    Helper function for output2acceptingstates(..)
    """

    formula = str(line.split(":")[1].strip())

    return formula


def _read_accepting_states(nusmv_output: str) -> dict:
    """
    Converts the output of a NuSMV call into an accepting states dictionary that contains information about the initial states,
    accepting states and accepting and initial.

    Example of NuSMVa output:

    initial states: CHEK1_2_medium
    number of initial states: 4294967296
    accepting states: !(E2F1_medium)
    number of accepting states: 4294967296
    initial and accepting states: !((E2F1_medium) | !CHEK1_2_medium)
    number of initial and accepting states: 2147483648

    **arguments**:
        * *nusmv_output: output of a call to NuSMV

    **returns**:
        * *accepting_states*: information about the accepting states with the following keys:
            * CTLSPEC: the CTL formula
            * INIT: the initial states
            * INIT_SIZE: number of initial states
            * ACCEPTING: factored formula of the accepting states
            * ACCEPTING_SIZE: number of accepting states
            * INITACCEPTING: factored formula of the initial and accepting states
            * INITACCEPTING_SIZE: number of initial and accepting states
            * ANSWER: whether the query is true
    """

    accepting = {}
    for line in nusmv_output.split("\n"):
        if line.startswith("initial states:"):
            accepting["INIT"] = _read_formula(line)

        elif line.startswith("number of initial states:"):
            accepting["INIT_SIZE"] = _read_number(line)

        elif line.startswith("accepting states:"):
            accepting["ACCEPTING"] = _read_formula(line)

        elif line.startswith("number of accepting states:"):
            accepting["ACCEPTING_SIZE"] = _read_number(line)

        elif line.startswith("initial and accepting states:"):
            accepting["INITACCEPTING"] = _read_formula(line)

        elif line.startswith("number of initial and accepting states:"):
            accepting["INITACCEPTING_SIZE"] = _read_number(line)

    return accepting

