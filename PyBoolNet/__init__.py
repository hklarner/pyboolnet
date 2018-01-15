

from __future__ import absolute_import


import PyBoolNet.AttractorDetection
import PyBoolNet.Basins
import PyBoolNet.FileExchange
import PyBoolNet.InteractionGraphs
import PyBoolNet.ModelChecking
import PyBoolNet.PrimeImplicants
import PyBoolNet.QuineMcCluskey
import PyBoolNet.StateTransitionGraphs
import PyBoolNet.QueryPatterns
import PyBoolNet.AspSolver
import PyBoolNet.Repository
import PyBoolNet.Utility
import PyBoolNet.BooleanExpressions
import PyBoolNet.Tests

import pprint as prettyprint



def version():
    return "2.2.1"


def pprint(X):
    pp = prettyprint.PrettyPrinter(indent=4)
    pp.pprint(X)
