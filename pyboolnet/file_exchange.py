

import ast
import logging
import os
from typing import Optional

from pyboolnet import find_command
from pyboolnet.external.bnet2primes import bnet_file2primes, bnet_text2primes
from pyboolnet.boolean_normal_forms import primes2mindnf, get_dnf
from pyboolnet.digraphs import find_outdag
from pyboolnet.interaction_graphs import primes2igraph
from pyboolnet.prime_implicants import CONSTANT_ON, CONSTANT_OFF
from pyboolnet.prime_implicants import find_constants, find_inputs

CMD_BNET2PRIMES = find_command("bnet2prime")

log = logging.getLogger(__name__)


def bnet2primes(bnet: str, fname_primes: Optional[str] = None) -> dict:
    """
    Generates and returns the prime implicants of a Boolean network in **boolnet** format.
    The primes are saved as a *json* file if *fname_primes* is given.
    The argument *bnet* may be either the name of a *bnet* file or a string containing the file contents.
    Use the function `read_primes` to open a previously saved *json* file.

    .. example of boolnet format::

        Erk,  Erk & Mek | Mek & Raf
        Mek,  Erk | Mek & Raf
        Raf,  !Erk | !Raf

    **arguments**:
        * *bnet*: name of *bnet* file or string contents of file
        * *fname_primes*: *None* or name of *json* file to save primes

    **returns**:
        * *primes*: prime implicants

    **example**::

        >>> primes = bnet2primes("mapk.bnet", "mapk.primes" )
        >>> primes = bnet2primes("mapk.bnet")
        >>> primes = bnet2primes("Erk, !Mek \\n Raf, Ras & Mek")
        >>> primes = bnet2primes("Erk, !Mek \\n Raf, Ras & Mek", "mapk.primes")
    """

    primes = bnet_file2primes(fname_bnet=bnet) if os.path.isfile(bnet) else bnet_text2primes(text=bnet)

    if fname_primes and os.path.isfile(fname_primes):
        write_primes(primes=primes, fname_json=fname_primes)

    return primes


def primes2bnet(primes: dict, fname_bnet: str = None, minimize: bool = False, header: bool = False) -> str:
    """
    Saves *primes* as a *bnet* file, including the header *"targets, factors"* for compatibility with :ref:`installation_boolnet`.
    Without minimization, the resuting formulas are disjunctions of all prime implicants and may therefore be very long.
    If *Minimize=True* then a Python version of the Quine-McCluskey algorithm,
    namely :ref:`Prekas2012 <Prekas2012>` which is implemented in :ref:`QuineMcCluskey.primes2mindnf <primes2mindnf>`,
    will be used to minimize the number of clauses for each update function.

    **arguments**:
        * *primes*: prime implicants
        * *fname_bnet*: name of *bnet* file or *None* for the string of the file contents
        * *minimize*: minimize the Boolean expressions
        * *header*: whether to include the "targets, factors" header

    **returns**:
        * *text_bnet*: str contents of bnet file

    **example**::

        >>> primes2bnet(primes, "mapk.bnet")
        >>> primes2bnet(primes, "mapk.bnet", True)
        >>> expr = primes2bnet(primes)
        >>> expr = primes2bnet(primes, True)
    """

    width = max([len(x) for x in primes]) + 3
    igraph = primes2igraph(primes)
    constants = sorted(find_constants(primes))
    inputs = sorted(find_inputs(primes))
    outdag = sorted(find_outdag(igraph))
    outdag = [x for x in outdag if x not in constants]
    body = sorted(x for x in primes if all(x not in X for X in [constants, inputs, outdag]))
    blocks = [constants, inputs, body, outdag]
    blocks = [x for x in blocks if x]

    assert len(constants) + len(inputs) + len(body) + len(outdag) == len(primes)

    lines = []
    if header:
        lines += ["targets, factors"]

    if minimize:
        expressions = primes2mindnf(primes)
        for block in blocks:
            for name in block:
                lines += [f"{name + ',': <{width}} {expressions[name]}"]
            lines += [""]

    else:
        for block in blocks:
            for name in block:
                expression = get_dnf(one_implicants=primes[name][1])
                lines += [f"{name+',': <{width}} {expression}"]
            lines += [""]

    text = "\n".join(lines)

    if fname_bnet:
        with open(fname_bnet, "w") as fp:
            fp.writelines(text)
            log.info(f"created {fname_bnet}")
    
    return text


def write_primes(primes: dict, fname_json: str):
    """
    Saves *primes* as a *json* file.

    **arguments**:
       * *primes*: prime implicants
       * *fname_json*: name of *json* file

    **example**::

          >>> write_primes(primes, "mapk.primes")
    """

    overwritten = os.path.isfile(fname_json)

    with open(fname_json, "w") as fp:
        fp.write(str(primes))
    
    log.info(f"created {fname_json}{' (overwritten)' if overwritten else ''}")


def read_primes(fname_json: str) -> dict:
    """
    Reads the prime implicants of a Boolean network that were previously stored as a *json* file.

    **arguments**:
       * *fname_json*: name of *json* file

    **returns**:
       * *primes*: prime implicants

    **example**::

          >>> primes = read_primes("mapk.primes")
    """

    with open(fname_json, "r") as f:
        lines = f.read()

    return ast.literal_eval(lines)


def primes2genysis(primes: dict, fname_genysis: str):
    """
    Generates a GenYsis_ file from *primes* for the computation of all attractors of the synchronous or asynchronous transition system.
    GenYsis_ was introduced in :ref:`Garg2008 <Garg2008>`.
    It is available at http://www.vital-it.ch/software/genYsis.


    **arguments**:
       * *primes*: prime implicants
       * *fname_genysis*: name of GenYsis_ file

    **example**::

          >>> primes2genysis(primes, "mapk.genysis")
    """

    lines = []
    for name in sorted(primes):
        if primes[name] == CONSTANT_ON:
            lines += [name + " -> " + name]
            lines += ["^" + name + " -> " + name]

        elif primes[name] == CONSTANT_OFF:
            lines += [name + " -| " + name]
            lines += ["^" + name + " -| " + name]

        else:
            for prime in primes[name][1]:
                seq = []
                for n, v in sorted(prime.items()):
                    if v == 1:
                        seq.append(n)
                    else:
                        seq.append("^"+n)
                lines += ["&".join(seq)+" -> "+name]

    with open(fname_genysis, "w") as fp:
        fp.write("\n".join(lines))

    log.info(f"created {fname_genysis}")


def primes2bns(primes: dict, fname_bns: Optional[str] = None) -> str:
    """
    Saves Primes as a *bns* file for the computation of all attractors of the synchronous transition system.
    BNS_ is based on :ref:`Dubrova2011 <Dubrova2011>`.
    It is available at http://people.kth.se/~dubrova/bns.html.

    **arguments**:
       * *primes*: prime implicants
       * *fname_bns*: name of *bns* file or *None* to return file as string

    **example**::

          >>> primes2bns(primes, "mapk.bns")
    """

    names_sorted = sorted(primes)
    lines = ["# " + ", ".join(names_sorted), ""]
    lines += [f".v {len(names_sorted)}", ""]

    ig = primes2igraph(primes)
    for i, name in enumerate(names_sorted):
        i += 1
        lines += [f"# {name}"]
        regulators = sorted(ig.predecessors(name))
        number_regs = len(regulators)
        ids_regs = " ".join([str(names_sorted.index(reg)+1) for reg in regulators])
        lines += [f".n {i} {number_regs} {ids_regs}"]

        for v in [0, 1]:
            for prime in primes[name][v]:
                seq = []
                for reg in regulators:
                    if reg in prime:
                        if prime[reg] == 1:
                            seq.append("1")
                        else:
                            seq.append("0")
                    else:
                        seq.append("-")

                if regulators:
                    seq.append(" ")

                seq.append(str(v))

                lines += ["".join(seq)]

        lines += [""]

    text = "\n".join(lines)
    if fname_bns:
        with open(fname_bns, "w") as f:
            f.write(text)
        log.info(f"created {fname_bns}")

    return text


def primes2eqn(primes: dict, fname_eqn: Optional[str] = None) -> str:
    """
    Generates a *eqn* file as specified in the manual for the model checking software Antelope_ from *primes*.
    Antelope_ was introduced in :ref:`Arellano2011 <Arellano2011>`.

    **arguments**:
       * *primes*: prime implicants
       * *fname_eqn*: name of *eqn* file

    **example**::

          >>> primes2eqn(primes, "mapk.eqn")
    """

    lines = []
    for name in sorted(primes):

        if primes[name] == CONSTANT_ON:
            lines += [name + " := true;"]

        elif primes[name] == CONSTANT_OFF:
            lines += [name + " := false;"]

        else:
            disj = []
            for prime in primes[name][1]:

                conj = []
                for n, v in sorted(prime.items()):
                    if v == 1:
                        conj.append(n)
                    else:
                        conj.append("~"+n)

                disj += ["&".join(conj)]

            lines += [name + " := " + " | ".join(disj) + ";"]

    text = "\n".join(lines)

    if fname_eqn:
        with open(fname_eqn, "w") as fp:
            fp.write(text)

        log.info(f"created {fname_eqn}")

    return text
