

import unittest
import os
import sys
import tempfile
import shutil

import PyBoolNet.Phenotypes


def run():
    unittest.main(verbosity=2, buffer=True, exit=False, module=__name__)




class TestPhenotypes(unittest.TestCase):

    def test_xxx(self):
        primes = PyBoolNet.Repository.get_primes("multivalued")
        result = PyBoolNet.StateTransitionGraphs.find_vanham_variables(primes)

        expected = {2: ['input', 'x2', 'x3', 'x6_level2'],
                    3: ['x1'],
                    4: ['x4'],
                    5: ['x5']}

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

        suite.addTest(TestPhenotypes("test_xxx"))

        runner = unittest.TextTestRunner(buffer=True)
        runner.run(suite)











# end of file
