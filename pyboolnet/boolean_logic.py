

import logging
import os
import re
import subprocess
import sys
from typing import Optional, List

from pyboolnet import find_command
from pyboolnet.helpers import os_is_windows

EQNTOTT_CMD = find_command("eqntott")
ESPRESSO_CMD = find_command("espresso")
FORBIDDEN_SYMBOLS = ["False", "FALSE", "True", "TRUE", "Zero", "ZERO", "One", "ONE"]

log = logging.getLogger(__name__)


def are_mutually_exclusive(this: str, other: str) -> bool:
    """
    uses minimize_espresso to compute whether A and B are mutually exclusive
    """
    
    return minimize_espresso(f"({this}) & ({other})") == "0"


def implies(this: str, other: str) -> bool:
    """
    uses minimize_espresso to compute whether *this* implies *other*.
    """
    
    return minimize_espresso(f"!({other}) & ({this})") == "0"


def are_equivalent(this: str, other: str) -> bool:
    """
    uses minimize_espresso to compute whether *this* and *other* are equivalent.
    """
    
    return implies(this, other) and implies(other, this)


def _eqntott_error(eqntott, eqntott_out, eqntott_err):
    """
    raises exception for eqntott
    """

    if eqntott.returncode != 0:
        log.error(eqntott_out)
        log.error(eqntott_err)
        log.error(f"call to eqntott resulted in return code {eqntott.returncode}")
        sys.exit()


def _espresso_error(espresso, espresso_out, espresso_err):
    """
    raises exception for espresso
    """
    if not (espresso.returncode == 0):
        log.error(espresso_out)
        log.error(espresso_err)
        log.error(f"call to espresso resulted in return code {espresso.returncode}")
        sys.exit()


def run_eqntott(eqntott_cmd: List[str], eqntott_in: str) -> str:
    eqntott = subprocess.Popen(eqntott_cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    eqntott_out, eqntott_err = eqntott.communicate(input=eqntott_in.encode())
    eqntott.stdin.close()
    _eqntott_error(eqntott, eqntott_out, eqntott_err)

    return eqntott_out.decode()


def run_espresso(espresso_cmd: List[str], eqntott_out: str) -> str:
    espresso = subprocess.Popen(espresso_cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    espresso_out, espresso_err = espresso.communicate(input=eqntott_out.encode())
    espresso.stdin.close()
    _espresso_error(espresso, espresso_out, espresso_err)

    return espresso_out.decode()


def minimize_espresso(expression: str, fname_out: Optional[str] = None, merge: bool = False, equiv: bool = False, exact: bool = False, reduce: bool = False) -> str:
    """
    Tries to minimize a given boolean expression utilizing the heuristic minimization algorithm
    `espresso <http://chmod755.tumblr.com/post/31417234230/espresso-heuristic-logic-minimizer>`_ and `eqntott <https://code.google.com/archive/p/eqntott/>`_ for its input preparation. Resulting expression is saved
    in file if filename for output is specified. The argument *expression* may be either the name
    of the input file containing the boolean expression or the string representing the expression
    itself. The input expression may not contain the following words: *False*, *FALSE*, *True*,
    *TRUE*, *Zero*, *ZERO*, *One*, *ONE*.

    **arguments**:
       * *expression*: name of file containing the expression or string contents of file
       * *fname_out*: name of the file to write the output to
       * *merge*: performs distance-1 merge on input, useful if very large
       * *equiv*: identifies equivalent output variables
       * *exact*: performs exact minimization algorithm, guarantees minimum number of product terms and heuristically minimizes number of literals, potentially expensive
       * *reduce*: eqntott tries to reduce the size of the truth table by merging minterms

    **returns**:
       * *minimized_expression*: the minimized expression

    **example**::

          >>> minimize_espresso("bool_function.txt", "minimized_function.txt" )
          >>> minimize_espresso("var = (a & b) | a;")
          >>> minimize_espresso("var = 1")
          >>> minimize_espresso("(a & b) | a")
    """

    if os.path.isfile(expression):
        with open(expression, "r") as fname:
            expression = fname.read()

    if not all(var not in expression for var in FORBIDDEN_SYMBOLS):
        log.error(f"forbidden keyword in expression: {expression}")
        return expression
    
    add_name = False
    add_colon = False

    if "=" not in expression:
        expression = "Test = " + expression
        add_name = True

    if ";" not in expression:
        expression = expression + ";"
        add_colon = True
    
    eqntott_cmd = [EQNTOTT_CMD, "-f", "-l"]
    espresso_cmd = [ESPRESSO_CMD, "-o", "eqntott"]
    
    if merge:
        espresso_cmd += ["-Dd1merge"]
    if equiv:
        espresso_cmd += ["-Dequiv"]
    if exact:
        espresso_cmd += ["-Dexact"]
    if reduce:
        eqntott_cmd += ["-r"]
    
    if not os_is_windows:
        eqntott_cmd += ["/dev/stdin"]
        
    eqntott_in = expression
    eqntott_out = run_eqntott(eqntott_cmd, eqntott_in)
    
    if int(re.search(r'\.p\s\d+', eqntott_out).group().strip(".p ")) != 0:
        espresso_out = run_espresso(espresso_cmd, eqntott_out)
        espresso_out = re.sub(r'\.na .*\n', "", espresso_out)
        espresso_out = re.sub(r'\s', '', espresso_out)
        espresso_out = espresso_out.replace("|", " | ")
        espresso_out = espresso_out.replace("=", " = ")
        espresso_out = espresso_out.replace("&", " & ")
        if espresso_out == "Test = ();":
            espresso_out = "Test = 1;"

    elif int(re.search(r'\.p\s\d+', eqntott_out).group().strip(".p ")) == 1:
        espresso_out = "1"

    elif int(re.search(r'\.p\s\d+', eqntott_out).group().strip(".p ")) == 0:
        espresso_out = "0"

    else:
        espresso_out = expression
    
    if add_name and "Test" in espresso_out:
        espresso_out = espresso_out.replace("Test = ", "")
    if add_colon and ";" in espresso_out:
        espresso_out = espresso_out.replace(";", "")
    
    if fname_out:
        with open(fname_out, "w") as results:
            results.write(espresso_out)
        log.info(f"created {fname_out}")

    return espresso_out
