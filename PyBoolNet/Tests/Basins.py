

import unittest
import os
import sys
import tempfile
import shutil

import PyBoolNet.Basins


def run():
    unittest.main(verbosity=2, buffer=True, exit=False, module=__name__)



class TestBasins(unittest.TestCase):

    def test_xxx(self):

        bnet = """
        v1, !v1&v2 | v1&!v2&!v3
        v2, v1&v3
        v3, v2
        """
        primes = PyBoolNet.FileExchange.bnet2primes(bnet)
        update = "asynchronous"

        weak = PyBoolNet.Basins.weak_basin(primes, update, Subspace="000")
        weak = PyBoolNet.Basins.strong_basin(primes, update, Subspace="000")
        weak = PyBoolNet.Basins.cyclefree_basin(primes, update, Subspace="000")

        attrs = PyBoolNet.Attractors.compute_json(primes, update)
        PyBoolNet.Basins.compute_basins(attrs)

        tmpfile = tempfile.NamedTemporaryFile(delete=True, prefix="pyboolnet_", suffix=".pdf")
        tmpfname = tmpfile.name
        PyBoolNet.Basins.create_barplot(attrs, tmpfname)
        tmpfile.close()

        tmpfile = tempfile.NamedTemporaryFile(delete=True, prefix="pyboolnet_", suffix=".pdf")
        tmpfname = tmpfile.name
        PyBoolNet.Basins.create_piechart(attrs, tmpfname)
        tmpfile.close()




if __name__=="__main__":


    if 1:

        # run all tests
        unittest.main(verbosity=2, buffer=True)


    if 0:

        # run single test
        suite = unittest.TestSuite()

        suite.addTest(TestBasins("test_xxx"))

        runner = unittest.TextTestRunner(buffer=True)
        runner.run(suite)











# end of file
