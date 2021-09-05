

import datetime
import logging
import os
import subprocess
import sys
import tempfile
from typing import List, Optional

from pyboolnet import find_command, NUSMV_KEYWORDS
from pyboolnet.prime_implicants import CONSTANT_ON, CONSTANT_OFF
from pyboolnet.state_transition_graphs import UPDATE_STRATEGIES, VAN_HAM_EXTENSIONS
from pyboolnet.state_transition_graphs import find_vanham_variables
from pyboolnet.temporal_logic import subspace2proposition

BASE = os.path.abspath(os.path.join(os.path.dirname(__file__)))
BASE = os.path.normpath(BASE)
CMD_NUSMV = find_command("nusmv")

log = logging.getLogger(__file__)


def print_warning_accepting_states_bug(primes: dict, ctl_spec: str):
    """
    This bug occurs when the Specification is equivalent to TRUE or FALSE.
    """

    if all(x not in ctl_spec for x in primes):
        log.warning("accepting states bug might affect this result, see http://github.com/hklarner/PyBoolNet/issues/14")


def model_checking(primes: dict, update: str, init: str, spec: str, dynamic_reorder: bool = True, disable_reachable_states: bool = True, cone_of_influence: bool = True):
    """
    Calls :ref:`installation_nusmv` to check whether the *specification* is true or false in the transition system defined by *primes*,
    the *initial_states* and *update*.
    The remaining arguments are :ref:`installation_nusmv` options, see the manual at http://nusmv.fbk.eu for details.

    See :ref:`primes2smv` and :ref:`Sec. 3.4 <sec:model_checking>` for details on model checking with |Software|.

    **arguments**:
        * *primes*: prime implicants
        * *update*: the update strategy, either *"synchronous"*, *"asynchronous"* or *"mixed"*
        * *initial_states*: a :ref:`installation_nusmv` expression for the initial states, including the keyword *INIT*
        * *specification*: a :ref:`installation_nusmv` formula, including the keyword *LTLSPEC* or *CTLSPEC*
        * *dynamic_reorder*: enables dynamic reordering of variables using *-dynamic*
        * *disable_reachable_states*: disables the computation of reachable states using *-df*
        * *cone_of_influence*: enables cone of influence reduction using *-coi*

    **returns**:
        * *answer*: result of query

    **example**::

        >>> init = "INIT TRUE"
        >>> update = "asynchronous"
        >>> spec = "CTLSPEC AF(EG(v1&!v2))"
        >>> model_checking(primes, update, init, spec)
        False

    """

    cmd = [CMD_NUSMV]
    cmd += ["-dcx"]

    if dynamic_reorder:
        cmd += ["-dynamic"]
    if disable_reachable_states:
        cmd += ["-df"]
    if cone_of_influence:
        cmd += ["-coi"]

    tmp_file = tempfile.NamedTemporaryFile(delete=False, prefix="pyboolnet_")
    tmp_fname = tmp_file.name
    log.info(f"created {tmp_fname}")
    tmp_file.close()

    cmd += [tmp_fname]
    try:
        log.info(f"cmd: {' '.join(cmd)}")
        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    except Exception as e:
        log.info("could not start process for nusmv")
        log.info(f"cmd: {' '.join(cmd)}")
        sys.exit()

    out, err = proc.communicate()
    out = out.decode()

    if os.path.isfile(tmp_fname):
        os.remove(tmp_fname)

    return nusmv_handle(cmd, proc, out, err, disable_counterexamples=True, accepting_states=False)


def model_checking_with_counterexample(primes: dict, update: str, init, spec, dynamic_reorder: bool = True, disable_reachable_states: bool = True):
    """
    Calls :ref:`installation_nusmv` to check whether the *specification* is true or false in the transition system defined by *primes*,
    the *initial_states* and *update*.
    The remaining arguments are :ref:`installation_nusmv` options, see the manual at http://nusmv.fbk.eu for details.
    See :ref:`primes2smv` and :ref:`Sec. 3.4 <sec:model_checking>` for details on model checking with |Software|.

    .. note::
        *cone_of_influence* is not available when using counterexamples as it "messes" with the output.

    **arguments**:
        * *primes*: prime implicants
        * *update*: the update strategy, either *"synchronous"*, *"asynchronous"* or *"mixed"*
        * *initial_states*: a :ref:`installation_nusmv` expression for the initial states, including the keyword *INIT*
        * *specification*: a :ref:`installation_nusmv` formula, including the keyword *LTLSPEC* or *CTLSPEC*
        * *dynamic_reorder*: enables dynamic reordering of variables using *-dynamic*
        * *disable_reachable_states*: disables the computation of reachable states using *-df*

    **returns**:
        * *answer, counterexample*: result of query with counterexample

    **example**::

        >>> init = "INIT TRUE"
        >>> update = "asynchronous"
        >>> spec = "CTLSPEC AF(EG(v1&!v2))"
        >>> answer, counterex = model_checking_with_counterexample(primes, update, init, spec)
        >>> counterex
         ({'v1':0,'v2':0},{'v1':1,'v2':0},{'v1':1,'v2':1})
    """

    cmd = [CMD_NUSMV]

    if dynamic_reorder:
        cmd += ['-dynamic']
    if disable_reachable_states:
        cmd += ['-df']

    tmp_file = tempfile.NamedTemporaryFile(delete=False, prefix="pyboolnet_")
    tmp_fname = tmp_file.name
    log.info(f"created {tmp_fname}")
    tmp_file.close()
    cmd += [tmp_fname]

    try:
        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    except Exception:
        print("could not start process for nusmv")
        print(f"cmd: {' '.join(cmd)}")
        sys.exit()

    out, err = proc.communicate()
    out = out.decode()

    if os.path.isfile(tmp_fname):
        os.remove(tmp_fname)

    return nusmv_handle(cmd, proc, out, err, disable_counterexamples=False, accepting_states=False)


def model_checking_with_acceptingstates(primes: dict, update: str, initial_states, ctl_spec: str, dynamic_reorder: bool = True, cone_of_influence: bool = True):
    """
    Calls :ref:`installation_nusmv` to check whether the *ctl_spec* is true or false in the transition system defined by *primes*,
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
        If the *ctl_spec* is equivalent to either `TRUE` or `FALSE` then NuSMV will not compute the initial states,
        because it does not have to to find out what the *answer* to the query is.
        In that case the four values that involve the initial states are set to `None`.

    **arguments**:
        * *primes*: prime implicants
        * *update*: the update strategy, either *"synchronous"*, *"asynchronous"* or *"mixed"*
        * *initial_states*: a :ref:`installation_nusmv` expression for the initial states, including the keyword *INIT*
        * *ctl_spec*: a :ref:`installation_nusmv` formula, including the keyword *CTLSPEC*
        * *dynamic_reorder*: enables dynamic reordering of variables (*-dynamic*)
        * *cone_of_influence*: enables cone of influence reduction using *-coi*

    **returns**:
        * *answer, accepting_states*: result of query with accepting states

    **example**::

        >>> init = "INIT TRUE"
        >>> update = "asynchronous"
        >>> spec = "CTLSPEC AF(EG(v1&!v2))"
        >>> answer, accepting_states = model_checking_with_acceptingstates(primes, update, init, spec)
        >>> accepting_states["INITACCEPTING"]
        'v1 | v3'
    """

    assert ctl_spec[:7] == "CTLSPEC"

    print_warning_accepting_states_bug(primes, ctl_spec)

    cmd = [CMD_NUSMV]
    cmd += ["-dcx"]
    cmd += ["-a", "print"]

    if dynamic_reorder:
        cmd += ["-dynamic"]
    if cone_of_influence:
        cmd += ["-coi"]

    cmd += ["-df"]

    tmp_file = tempfile.NamedTemporaryFile(delete=False, prefix="pyboolnet_")
    tmp_fname = tmp_file.name
    log.info(f"created {tmp_fname}")
    tmp_file.close()
    cmd += [tmp_fname]

    try:
        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    except Exception:
        log.error("could not start process for nusmv")
        log.error(f"cmd: {' '.join(cmd)}")
        sys.exit()

    out, err = proc.communicate()
    out = out.decode()

    if os.path.isfile(tmp_fname):
        os.remove(tmp_fname)

    return nusmv_handle(cmd, proc, out, err, disable_counterexamples=True, accepting_states=True)


def check_smv(fname_smv: str, dynamic_reorder: bool = True, disable_reachable_states: bool = True, cone_of_influence: bool = True):
    """
    Calls :ref:`installation_nusmv` with the query defined in the *smv* file *fname_smv*.
    The remaining arguments are :ref:`installation_nusmv` options, see the manual at http://nusmv.fbk.eu for details.
    See :ref:`primes2smv` and :ref:`Sec. 3.4 <sec:model_checking>` for details on model checking with |Software|.

    .. note::
        It is currently required that *fname_smv* contains a single LTL or CTL formula.
        For future versions it is planned that :ref:`check_smv` returns a dictionary of answers.

    **arguments**:
        * *fname_smv*: name of smv file
        * *DisableCounterExamples*: disables computation of counterexamples (*-dcx*)
        * *dynamic_reorder*: enables dynamic reordering of variables (*-dynamic*)
        * *disable_reachable_states*: disables the computation of reachable states (*-df*)
        * *cone_of_influence*: enables cone of influence reduction (*-coi*)

    **returns**:
        * *answer*: result of query

    **example**::

        >>> check_smv("mapk.smv")
        False
    """

    cmd = [CMD_NUSMV]
    cmd += ["-dcx"]

    if dynamic_reorder:
        cmd += ["-dynamic"]
    if disable_reachable_states:
        cmd += ["-df"]
    if cone_of_influence:
        cmd += ["-coi"]

    cmd += [fname_smv]

    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = proc.communicate()
    out = out.decode()

    return nusmv_handle(cmd, proc, out, err, disable_counterexamples=True, accepting_states=False)


def check_smv_with_counterexample(fname_smv: str, dynamic_reorder: bool = True, disable_reachable_states: bool = True):
    """
    Calls :ref:`installation_nusmv` with the query defined in the *smv* file *fname_smv*.
    The remaining arguments are :ref:`installation_nusmv` options, see the manual at http://nusmv.fbk.eu for details.
    See :ref:`primes2smv` and :ref:`Sec. 3.4 <sec:model_checking>` for details on model checking with |Software|.

    .. note::
        It is currently required that *fname_smv* contains a single LTL or CTL formula.
        For future versions it is planned that :ref:`check_smv` returns a dictionary of answers.

    .. note::
        *cone_of_influence* is not available when using counterexamples as it "messes" with the output.

    **arguments**:
        * *fname_smv*: name of smv file
        * *dynamic_reorder*: enables dynamic reordering of variables
        * *disable_reachable_states*: disables the computation of reachable states

    **returns**:
        * *answer, counterexample*: result of query with counterexample

    **example**::

        >>> answer, counterexample = check_smv_with_counterexample("mapk.smv")
        >>> counterexample
        ({'Erk':0,'Mek':0},{'Erk':1,'Mek':0},{'Erk':1,'Mek':1})
    """

    cmd = [CMD_NUSMV]

    if dynamic_reorder:
        cmd += ['-dynamic']
    if disable_reachable_states:
        cmd += ['-df']

    cmd += [fname_smv]

    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = proc.communicate()
    out = out.decode()

    return nusmv_handle(cmd, proc, out, err, disable_counterexamples=False, accepting_states=False)


def check_smv_with_acceptingstates(fname_smv: str, dynamic_reorder: bool = True, cone_of_influence: bool = True):
    """
    Calls :ref:`installation_nusmv` with the query defined in the *smv* file *fname_smv*.
    The remaining arguments are :ref:`installation_nusmv` options, see the manual at http://nusmv.fbk.eu for details.

    See :ref:`primes2smv` and :ref:`Sec. 3.4 <sec:model_checking>` for details on model checking with |Software|.

    See :ref:`check_primes_with_acceptingstates` for details regarding the returned *accepting_states* dictionary.

    .. note::
        It is required that *fname_smv* contains a single CTL formula.

    **arguments**:
        * *fname_smv*: name of smv file
        * *dynamic_reorder*: enables dynamic reordering of variables
        * *cone_of_influence*: enables cone of influence reduction

    **returns**:
        * *answer, accepting_states*: result of query with accepting states

    **example**::

        >>> answer, accepting_states = check_smv_with_acceptingstates("mapk.smv")
        >>> accepting_states["INITACCEPTING"]
        'Erk | !Mek'
    """

    cmd = [CMD_NUSMV]
    cmd += ['-dcx']

    if dynamic_reorder:
        cmd += ['-dynamic']
    if cone_of_influence:
        cmd += ['-coi']

    cmd += ['-a', 'print']
    cmd += ['-df']
    cmd += [fname_smv]

    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = proc.communicate()
    out = out.decode()

    return nusmv_handle(cmd, proc, out, err, disable_counterexamples=True, accepting_states=True)


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

    lines+= [""]
    lines+= [specification]

    text_smv = "\n".join(lines)

    with open(fname_smv, "w") as f:
        f.write(text_smv)

    log.info(f"created {fname_smv}")

    return text_smv


def output2counterexample(nusmv_output: str):
    """
    Converts the output of a NuSMV call into a sequence of states that proves that the query is false.

    **arguments**:
        * *nusmv_output*: output of a call to NuSMV

    **returns**:
        * *counterexample*: a sequence of states that disprove the query.
    """

    if "Trace Type: Counterexample" not in nusmv_output:
        return

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
        lines = [x for x in lines if x!=[]]

        if lines:
            if last_state:
                state = last_state.copy()
            else:
                state = {}

            for line in lines:
                name, value = line.split(" = ")
                assert value in ["TRUE", "FALSE"]
                state[name] = 1 if value== "TRUE" else 0

            counterexample.append(state)
            last_state = state

    return tuple(counterexample)


def _read_number(line):
    """
    Helper function for output2acceptingstates(..)
    """
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


def output2acceptingstates(nusmv_output: str) -> dict:
    """
    Converts the output of a NuSMV call into an accepting states dictionary that contains information about the initial states,
    accepting states and accepting and initial.

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


    """
    Example of NuSMVa output:

    initial states: CHEK1_2_medium
    number of initial states: 4294967296
    accepting states: !(E2F1_medium)
    number of accepting states: 4294967296
    initial and accepting states: !((E2F1_medium) | !CHEK1_2_medium)
    number of initial and accepting states: 2147483648
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


def nusmv_handle(command: List[str], process, output, error, disable_counterexamples: bool, accepting_states) -> tuple:
    """
    The part of the code of "check_smv" and "check_primes" that is identical in both functions.

    **arguments**:
        * *Command*: list of commands that was used to call subprocess.Popen.
        It is only used for creating an error message if the process does not finish correctly.
        * *process*: the object returned by subprocess.Popen
        * *output*: the object returned by Popen.communicate
        * *DisableCounterExamples*: whether a counterexample should be returned if the query is false
        * *accepting_states*: whether information about the accepting states should be returned

    **returns**:
        * *answer*: whether NuSMV returns "is true"
        * *counterexample*: a counterexample if NuSMV returns "is false" and DisableCounterExamples==False.
        * *accepting_states*: information about the accepting states, if *DisableAcceptingStates==False*.
    """

    if process.returncode == 0:

        if output.count("specification") > 1:
            log.error("SMV file contains more than one CTL or LTL specification.")
            sys.exit()

        if "is false" in output:
            answer = False
        elif "is true" in output:
            answer = True
        else:
            log.error(output)
            log.error(error)
            log.error('NuSMV output does not respond with "is false" or "is true".')
            sys.exit()

    else:
        log.error(output)
        log.error(error)
        log.error("NuSMV did not respond with return code 0")
        log.error(f"command: {' '.join(command)}")
        sys.exit()

    if disable_counterexamples and not accepting_states:
        return answer

    result = [answer]

    if not disable_counterexamples:
        counterexample = output2counterexample(nusmv_output=output)
        result.append(counterexample)

    if accepting_states:
        accepting = output2acceptingstates(nusmv_output=output)
        result.append(accepting)

    return tuple(result)
