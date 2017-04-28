

from __future__ import absolute_import


import PyBoolNet.AttractorBasins
import PyBoolNet.AttractorDetection
import PyBoolNet.FileExchange
import PyBoolNet.InteractionGraphs
import PyBoolNet.ModelChecking
import PyBoolNet.PrimeImplicants
import PyBoolNet.QuineMcCluskey
import PyBoolNet.StateTransitionGraphs
import PyBoolNet.QueryPatterns
import PyBoolNet.TrapSpaces
import PyBoolNet.Repository
import PyBoolNet.Utility
import PyBoolNet.BooleanExpressions
import PyBoolNet.Zanudo
import PyBoolNet.Tests

import pprint as prettyprint



def version():

    return "2.11x"


def pprint(X):
    pp = prettyprint.PrettyPrinter(indent=4)
    pp.pprint(X)





    
