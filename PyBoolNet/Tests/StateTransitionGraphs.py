

import unittest
import os
import sys
import subprocess
import networkx
import itertools
import tempfile
import shutil

import PyBoolNet.FileExchange
import PyBoolNet.PrimeImplicants
import PyBoolNet.InteractionGraphs
import PyBoolNet.StateTransitionGraphs
import PyBoolNet.AspSolver
import PyBoolNet.ModelChecking
import PyBoolNet.Attractors
import PyBoolNet.Basins
import PyBoolNet.TemporalLogic
import PyBoolNet.QuineMcCluskey
import PyBoolNet.Repository
import PyBoolNet.Utility



def run():
    unittest.main(verbosity=2, buffer=True, exit=False, module=__name__)




class TestStateTransitionGraphs(unittest.TestCase):

    def test_find_vanham_variables(self):
        primes = PyBoolNet.Repository.get_primes("multivalued")
        result = PyBoolNet.StateTransitionGraphs.find_vanham_variables(primes)

        expected = {2: ['input', 'x2', 'x3', 'x6_level2'],
                    3: ['x1'],
                    4: ['x4'],
                    5: ['x5']}

        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:       "+str(result)

        self.assertTrue(result==expected, msg)

    def test_size_state_space(self):
        primes = PyBoolNet.Repository.get_primes("multivalued")

        result = PyBoolNet.StateTransitionGraphs.size_state_space(primes, VanHam=False, FixedInputs=False)
        expected = 2**13
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:       "+str(result)
        self.assertTrue(result==expected, msg)

        result = PyBoolNet.StateTransitionGraphs.size_state_space(primes, VanHam=False, FixedInputs=True)
        expected = 2**12
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:       "+str(result)
        self.assertTrue(result==expected, msg)

        result = PyBoolNet.StateTransitionGraphs.size_state_space(primes, VanHam=True, FixedInputs=False)
        expected = 2**4*3*4*5
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:       "+str(result)
        self.assertTrue(result==expected, msg)

        result = PyBoolNet.StateTransitionGraphs.size_state_space(primes, VanHam=True, FixedInputs=True)
        expected = 2**3*3*4*5
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:       "+str(result)
        self.assertTrue(result==expected, msg)



if __name__=="__main__":


    if 1:

        # run all tests
        unittest.main(verbosity=2, buffer=True)

    if 0:
        # run single test
        suite = unittest.TestSuite()

        suite.addTest(TestStateTransitionGraphs("test_commitment_diagram_critical_nodes"))

        runner = unittest.TextTestRunner(buffer=True)
        runner.run(suite)











# end of file
