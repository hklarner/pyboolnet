

import subprocess
import os
import PyBoolNet
import re

from PyBoolNet.Utility.Misc import os_is_windows

EQNTOTT_CMD = PyBoolNet.Utility.Misc.find_command("eqntott")
ESPRESSO_CMD = PyBoolNet.Utility.Misc.find_command("espresso")



def are_mutually_exclusive(A, B, silent=True):
    """
    uses minimize_espresso to compute whether A and B are mutually exclusive
    """
    
    res = minimize_espresso("({A}) & ({B})".format(A=A, B=B))
    if not silent:
        print(res)
    res = res == "0"
    
    return res


def A_implies_B(A, B):
    """
    uses minimize_espresso to compute whether A implies B.
    """
    
    res = minimize_espresso("!({B}) & ({A})".format(A=A, B=B))
    res = res == "0"
    
    return res


def are_equivalent(A, B):
    """
    uses minimize_espresso to compute whether A and B are equivalent.
    """
    
    res = A_implies_B(A, B) and A_implies_B(B, A)
    
    return res


def _eqntott_error(eqntott, eqntott_out, eqntott_err):
    """
    raises exception for eqntott
    """
    if not (eqntott.returncode == 0):
        print(eqntott_out)
        print(eqntott_err)
        print('\nCall to "eqntott" resulted in return code %i' % eqntott.returncode)
        raise Exception


def _espresso_error(espresso, espresso_out, espresso_err):
    """
    raises exception for espresso
    """
    if not (espresso.returncode == 0):
        print(espresso_out)
        print(espresso_err)
        print('\nCall to "espresso" resulted in return code %i' % espresso.returncode)
        raise Exception


def run_eqntott(eqntott_cmd, eqntott_in):
    eqntott = subprocess.Popen(eqntott_cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    eqntott_out, eqntott_err = eqntott.communicate(input=eqntott_in.encode())
    eqntott.stdin.close()
    _eqntott_error(eqntott, eqntott_out, eqntott_err)
    return eqntott_out.decode()


def run_espresso(espresso_cmd, eqntott_out):
    espresso = subprocess.Popen(espresso_cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    espresso_out, espresso_err = espresso.communicate(input=eqntott_out.encode())
    espresso.stdin.close()
    _espresso_error(espresso, espresso_out, espresso_err)
    return (espresso_out.decode())


def minimize_espresso(Expression, Outputfile=None, Merge=False, Equiv=False, Exact=False, Reduce=False):
    """
    Tries to minimize a given boolean expression utilizing the heuristic minimization algorithm
    `espresso <http://chmod755.tumblr.com/post/31417234230/espresso-heuristic-logic-minimizer>`_ and `eqntott <https://code.google.com/archive/p/eqntott/>`_ for its input preparation. Resulting expression is saved
    in file if filename for output is specified. The argument *Expression* may be either the name
    of the input file containing the boolean expression or the string representing the expression
    itself. The input expression may not contain the following words: *False*, *FALSE*, *True*,
    *TRUE*, *Zero*, *ZERO*, *One*, *ONE*.

    **arguments**:
       * *Expression*: name of file containing the expression or string contents of file
       * *Outputfile*: name of the file to write the output to
       * *Merge*: performs distance-1 merge on input, useful if very large
       * *Equiv*: identifies equivalent output variables
       * *Exact*: performs exact minimization algorithm, guarantees minimum number of product terms and heuristically minimizes number of literals, potentially expensive
       * *Reduce*: eqntott tries to reduce the size of the truth table by merging minterms

    **returns**:
       * *Minimized*: minimized result

    **example**::

          >>> minimized = minimize_boolean("bool_function.txt", "minimized_function.txt" )
          >>> minimized = minimize_boolean("var = (a & b) | a;")
          >>> minimized = minimize_boolean("var = 1")
          >>> minimized = minimize_boolean("(a & b) | a")

    """
    # file input
    if os.path.isfile(Expression):
        with open(Expression, 'r') as fname:
            Expression = fname.read()
    
    forbidden = ["False", "FALSE", "True", "TRUE", "Zero", "ZERO", "One", "ONE"]
    if not all(var not in Expression for var in forbidden):
        print("ERROR: forbidden keyword in expression: %s" % Expression)
        return Expression
    
    AddName = False
    AddColon = False
    if not ("=" in Expression):
        Expression = "Test = " + Expression
        AddName = True
    if not (";" in Expression):
        Expression = Expression + ";"
        AddColon = True
    
    eqntott_cmd = [EQNTOTT_CMD, '-f', '-l']
    espresso_cmd = [ESPRESSO_CMD, '-o', 'eqntott']
    eqntott_in = None
    espresso_out = ''
    PLA_Name = 'Standard Input'
    
    if Merge:
        espresso_cmd += ['-Dd1merge']
    if Equiv:
        espresso_cmd += ['-Dequiv']
    if Exact:
        espresso_cmd += ['-Dexact']
    if Reduce:
        eqntott_cmd += ['-r']
    
    if not os_is_windows:
        eqntott_cmd += ['/dev/stdin']
        
    eqntott_in = Expression
    eqntott_out = run_eqntott(eqntott_cmd, eqntott_in)
    
    if int(re.search(r'\.p\s\d+', eqntott_out).group().strip(".p ")) != 0:
        espresso_out = run_espresso(espresso_cmd, eqntott_out)
        espresso_out = re.sub(r'\.na .*\n', '', espresso_out)
        espresso_out = re.sub(r'\s', '', espresso_out)
        espresso_out = espresso_out.replace('|', ' | ')
        espresso_out = espresso_out.replace('=', ' = ')
        espresso_out = espresso_out.replace('&', ' & ')
        if espresso_out == "Test = ();":
            espresso_out = "Test = 1;"
    elif int(re.search(r'\.p\s\d+', eqntott_out).group().strip(".p ")) == 1:
        espresso_out = "1"
    elif int(re.search(r'\.p\s\d+', eqntott_out).group().strip(".p ")) == 0:
        espresso_out = "0"
    else:
        espresso_out = Expression
    
    if AddName and "Test" in str(espresso_out):
        espresso_out = espresso_out.replace('Test = ', '')
    if AddColon and ";" in str(espresso_out):
        espresso_out = espresso_out.replace(';', '')
    
    if Outputfile is None:
        return (espresso_out)
    else:
        with open(Outputfile, 'w') as results:
            results.write(espresso_out)


if __name__ == "__main__":
    print("some basic tests")
    res = are_mutually_exclusive(A="x & !Y", B="Y")
    print("OK" if res else "error")
