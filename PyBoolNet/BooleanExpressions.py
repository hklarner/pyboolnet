
import subprocess
import os
import PyBoolNet
import re


BASE = os.path.abspath(os.path.join(os.path.dirname(__file__)))
BASE = os.path.normpath(BASE)
config = PyBoolNet.Utility.Misc.myconfigparser.SafeConfigParser()
config.read( os.path.join(BASE, "Dependencies", "settings.cfg") )
EQNTOTT_CMD = os.path.normpath(os.path.join( BASE, "Dependencies", config.get("Executables", "eqntott") ))
ESPRESSO_CMD = os.path.normpath(os.path.join( BASE, "Dependencies", config.get("Executables", "espresso") ))



def _eqntott_error(eqntott, eqntott_out, eqntott_err):
    """
    raises exception for eqntott
    """
    if not (eqntott.returncode == 0):
        print(eqntott_out)
        print(eqntott_err)
        print('\nCall to "eqntott" resulted in return code %i'%eqntott.returncode)
        raise Exception



def _espresso_error(espresso, espresso_out, espresso_err):
    """
    raises exception for espresso
    """
    if not (espresso.returncode == 0):
        print(espresso_out)
        print(espresso_err)
        print('\nCall to "espresso" resulted in return code %i'%espresso.returncode)
        raise Exception



def run_eqntott(eqntott_cmd, eqntott_in):
    eqntott = subprocess.Popen(eqntott_cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    eqntott_out, eqntott_err = eqntott.communicate(input=eqntott_in)
    eqntott.stdin.close()
    _eqntott_error(eqntott, eqntott_out, eqntott_err)
    return(eqntott_out)



def run_espresso(espresso_cmd, eqntott_out):
    espresso = subprocess.Popen(espresso_cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    espresso_out, espresso_err = espresso.communicate(input=eqntott_out.encode())
    espresso.stdin.close()
    _espresso_error(espresso, espresso_out, espresso_err)
    return(espresso_out)



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
    #file input
    if (os.path.isfile(Expression)):
        with open(Expression, 'r') as fname:
            Expression = fname.read()
    assert(type(Expression) == str)
    forbidden = ["False", "FALSE", "True", "TRUE", "Zero", "ZERO", "One", "ONE"]
    assert(all(var not in Expression for var in forbidden))
    AddName = False
    AddColon = False
    if not ("=" in Expression):
        Expression = "Test = " + Expression
        AddName = True
    if not (";" in Expression):
        Expression = Expression + ";"
        AddColon = True

    eqntott_cmd = [EQNTOTT_CMD, '-f', '-l']
    espresso_cmd =[ESPRESSO_CMD, '-o', 'eqntott']
    eqntott_in = None
    espresso_out = ''
    PLA_Name = 'Standard Input'

    if Merge == True:
        espresso_cmd += ['-Dd1merge']
    if Equiv == True:
        espresso_cmd += ['-Dequiv']
    if Exact == True:
        espresso_cmd += ['-Dexact']
    if Reduce == True:
        eqntott_cmd += ['-r']


    eqntott_cmd += ['/dev/stdin']
    eqntott_in = Expression
    eqntott_out = run_eqntott(eqntott_cmd, eqntott_in)
    if int(re.search(r'\.i\s\d+', eqntott_out).group().strip(".i "))>1:
        espresso_out = run_espresso(espresso_cmd, eqntott_out)
        espresso_out = re.sub(r'\.na .*\n', '', espresso_out)
        espresso_out = re.sub(r'\s', '', espresso_out)
        espresso_out = espresso_out.replace('|', ' | ')
        espresso_out = espresso_out.replace('=', ' = ')
        espresso_out = espresso_out.replace('&', ' & ')
    else:
        espresso_out = Expression

    if (AddName == True):
        espresso_out = espresso_out.replace('Test = ', '')
    if (AddColon == True):
        espresso_out = espresso_out.replace(';', '')

    if (Outputfile == None):
        return(espresso_out)
    else:
        with open(Outputfile, 'w') as results:
            results.write(espresso_out)
