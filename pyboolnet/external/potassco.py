import logging
import subprocess
from datetime import datetime
from typing import Optional, List

from pyboolnet import find_command
from pyboolnet.state_space import subspace2str

TRAP_SPACE_TYPES = ["max", "min", "all", "percolated", "circuits"]
CMD_GRINGO = find_command("gringo")
CMD_CLASP = find_command("clasp")

log = logging.getLogger(__name__)


def potassco_handle(primes: dict, type_: str, bounds: tuple, project: List[str], max_output: int, fname_asp: str, representation: str, extra_lines=None):
    """
    Returns a list of trap spaces using the Potassco_ ASP solver :ref:`[Gebser2011]<Gebser2011>`.
    """

    if type_ not in TRAP_SPACE_TYPES:
        log.error(f"unknown trap space type: type={type_}")
        raise Exception

    if representation not in ["str", "dict"]:
        log.error(f"unknown trap space representation: representation={representation}")
        raise Exception

    if bounds:
        bounds = tuple([len(primes) if x == "n" else x for x in bounds])

    params_clasp = ["--project"]

    if type_ == "max":
        params_clasp += ["--enum-mode=domRec", "--heuristic=Domain", "--dom-mod=5,16"]

    elif type_ == "min":
        params_clasp += ["--enum-mode=domRec", "--heuristic=Domain", "--dom-mod=3,16"]

    asp_text = primes2asp(primes=primes, fname_asp=fname_asp, bounds=bounds, project=project, type_=type_, extra_lines=extra_lines)

    try:
        if not fname_asp:
            cmd_gringo = [CMD_GRINGO]
            proc_gringo = subprocess.Popen(cmd_gringo, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            cmd_clasp = [CMD_CLASP, f"--models={max_output}"] + params_clasp
            proc_clasp = subprocess.Popen(cmd_clasp, stdin=proc_gringo.stdout, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

            proc_gringo.stdin.write(asp_text.encode())
            proc_gringo.stdin.close()

            output, error = proc_clasp.communicate()
            error = error.decode()
            output = output.decode()

        else:
            cmd_gringo = [CMD_GRINGO, fname_asp]
            proc_gringo = subprocess.Popen(cmd_gringo, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            cmd_clasp = [CMD_CLASP, f"--models={max_output}"] + params_clasp
            proc_clasp = subprocess.Popen(cmd_clasp, stdin=proc_gringo.stdout, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

            output, error = proc_clasp.communicate()
            error = error.decode()
            output = output.decode()

    except Exception as e:
        log.error(asp_text)
        log.error(e)
        log.error("call to gringo and / or clasp failed.")

        if fname_asp:
            log.info(f"command: {' '.join(cmd_gringo + ['|'] + cmd_clasp)}")

        raise Exception

    if "ERROR" in error:
        log.error("call to gringo and / or clasp failed.")
        if fname_asp:
            log.error(f"asp file: {asp_text}")
        log.error(f"command: {' '.join(cmd_gringo + ['|'] + cmd_clasp)}")
        log.error(f"error: {error}")
        raise Exception

    log.debug(asp_text)
    log.debug(f"cmd_gringo={' '.join(cmd_gringo)}")
    log.debug(f"cmd_clasp={' '.join(cmd_clasp)}")
    log.debug(error)
    log.debug(output)

    lines = output.split("\n")
    result = []

    if type_ == "circuits":
        while lines and len(result) < max_output:
            line = lines.pop(0)

            if line[:6] == "Answer":
                line = lines.pop(0)

                tspace = [x for x in line.split() if "hit" in x]
                tspace = [x[4:-1].split(",") for x in tspace]
                tspace = [(x[0][1:-1], int(x[1])) for x in tspace]

                perc = [x[12:-2] for x in line.split() if "perc" in x]
                perc = [x for x in tspace if x[0] in perc]
                perc = dict(perc)

                circ = [x for x in tspace if x[0] not in perc]
                circ = dict(circ)

                result.append((circ, perc))

    else:
        while lines and len(result) < max_output:
            line = lines.pop(0)

            if line[:6] == "Answer":
                line = lines.pop(0)
                d = [x[4:-1].split(",") for x in line.split()]
                d = [(x[0][1:-1], int(x[1])) for x in d]
                result.append(dict(d))

    if len(result) == max_output:
        log.info(f"there are possibly more than {max_output} trap spaces.")
        log.info("increase MaxOutput to find out.")

    if representation == "str":
        if type_ == "circuits":
            result = [(subspace2str(primes, x), subspace2str(primes, y)) for x, y in result]
        else:
            result = [subspace2str(primes, x) for x in result]

    return result


def primes2asp(primes: dict, fname_asp: str, bounds: Optional[tuple], project, type_: str, extra_lines: Optional[List[str]] = None):
    """
    Saves Primes as an *asp* file in the Potassco_ format intended for computing minimal and maximal trap spaces.
    The homepage of the Potassco_ solving collection is http://potassco.sourceforge.net.
    The *asp* file consists of data, the hyperarcs of the prime implicant graph,
    and a problem description that includes the consistency, stability and non-emptiness conditions.

    There are four additional parameters that modify the problem:

    *bounds* must be either a tuple of integers *(a,b)* or *None*.
    A tuple *(a,b)* uses Potassco_'s cardinality constraints to enforce that the number of fixed variables *x* of a trap space satisfies *a<=x<=b*.
    *None* results in no bounds.

    *project* must be either a list of names or *None*.
    A list of names projects the solutions onto these variables using the meta command "#show" and the clasp parameter "--project".
    Variables of *project* that do not appear in *primes* are ignored.
    *None* results in no projection.

    *type_* specifies whether additional constraints should be enforced.
    For example for computing circuits or percolated trap spaces.
    Recognized values are 'circuits' and 'percolated', everything else will be ignored.

    **arguments**:
       * *primes*: prime implicants
       * *fname_asp*: name of *ASP* file or None
       * *bounds*: cardinality constraint for the number of fixed variables
       * *project*: names to project to or *None* for no projection
       * *type_*: one of 'max', 'min', 'all', 'percolated', 'circuits' or *None*

    **returns**:
       * *asp_text*: contents of asp file

    **example**::

        >>> primes2asp(primes, "mapk.asp", False, False)
        >>> primes2asp(primes, "mapk_bounded.asp", (20,30), False)
        >>> primes2asp(primes, "mapk_projected.asp", False, ["AKT","GADD45","FOS","SMAD"])
    """

    assert type_ in [None, "max", "min", "all", "percolated", "circuits"]
    assert fname_asp is None or type(fname_asp) == str
    assert bounds is None or type(bounds) == tuple
    assert project is None or type(project) == list

    if project:
        project = [x for x in project if x in primes]

    lines = [f"%% created on {datetime.now().strftime('%d. %b. %Y')} using pyboolnet",
             "% pyboolnet is available at https://github.com/hklarner/pyboolnet",
             "",
             '% encoding of prime implicants as hyper-arcs that consist of a unique "target" and (possibly) several "sources".',
             '% "target" and "source" are triplets that consist of a variable name, an activity and a unique arc-identifier. ',
             '']

    index = 0
    for name in sorted(primes.keys()):
        for value in [0, 1]:
            for p in primes[name][value]:
                index += 1
                hyper = [f'target("{name}",{value},a{index}).']
                for n2, v2 in p.items():
                    hyper.append(f'source("{n2}",{v2},a{index}).')
                lines += [" ".join(hyper)]

    lines += [""]
    lines += [
        '% generator: "in_set(ID)" specifies which arcs are chosen for a trap set (ID is unique for target(_,_,_)).',
        "{in_set(ID) : target(V,S,ID)}.",
        "",
        "% consistency constraint",
        ":- in_set(ID1), in_set(ID2), target(V,1,ID1), target(V,0,ID2).",
        "",
        "% stability constraint",
        ":- in_set(ID1), source(V,S,ID1), not in_set(ID2) : target(V,S,ID2).",
        ""]

    if type_ in ["percolated", "circuits"]:
        lines += ["% percolation constraint.",
                  "% ensure that if all sources of a prime are hit then it must belong to the solution.",
                  "in_set(ID) :- target(V,S,ID), hit(V1,S1) : source(V1,S1,ID)."]
    else:
        lines += ["% bijection constraint (between asp solutions and trap spaces)",
                  "% to avoid the repetition of equivalent solutions we add all prime implicants",
                  "% that agree with the current solution.",
                  "in_set(ID) :- target(V,S,ID), hit(V,S), hit(V1,S1) : source(V1,S1,ID)."]

    if type_ == "circuits":
        lines += ["", "% circuits constraint, distinguishes between circuit nodes and percolated nodes",
                  "upstream(V1,V2) :- in_set(ID), target(V1,S1,ID), source(V2,S2,ID).",
                  "upstream(V1,V2) :- upstream(V1,V3), upstream(V3,V2).",
                  "percolated(V1) :- hit(V1,S), not upstream(V1,V1)."]

    lines += ["", '% "hit" captures the stable variables and their activities.',
              "hit(V,S) :- in_set(ID), target(V,S,ID)."]

    if bounds:
        lines += ["", f'%% cardinality constraint (enforced by "Bounds={bounds}")']
        if bounds[0] > 0:
            lines += [f':- {{hit(V,S)}} {bounds[0] - 1}.']
        lines += [f":- {bounds[1] + 1} {{hit(V,S)}}."]

    if extra_lines:
        lines += extra_lines

    if project:
        lines += ["", f'%% show projection (enforced by "Project={sorted(project)}").']
        lines += ["#show."]
        lines += [f'#show hit("{name}",S) : hit("{name}",S).' for name in project]

    elif type_ == "circuits":
        lines += ["", "% show fixed nodes and distinguish between circuits and percolated",
                  "#show percolated/1.",
                  "#show hit/2."]
    else:
        lines += ["", "% show fixed nodes", "#show hit/2."]

    asp_text = "\n".join(lines)

    if fname_asp:
        with open(fname_asp, "w") as f:
            f.write(asp_text)

        log.info(f"created {fname_asp}")

    return asp_text
