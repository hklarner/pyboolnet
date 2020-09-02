

import unittest
import os
import sys
import subprocess
import networkx
import itertools

import PyBoolNet.Utility.Misc


def run():
    unittest.main(verbosity=2, argv=[''], buffer=True, exit=False, module=__name__)


class TestNetworkX(unittest.TestCase):
    def test_networkx_import(self):
        try:
            import networkx
        except ImportError:
            msg = '"import networkx" raises ImportError'
            self.fail(msg)

class TestPotassco(unittest.TestCase):
    def test_gringo_responds(self):
        cmd = PyBoolNet.Utility.Misc.find_command("gringo")
        cmd = [cmd, "--help"]

        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        out, err = proc.communicate()
        out = out.decode()

        msg = "\nCall to gringo resulted in return code %i."%proc.returncode
        msg+= '\ncommand: "%s"'%' '.join(cmd)
        self.assertEqual(proc.returncode, 0, msg)

        msg = '\ngringo did not respond with "Gringo"'
        msg+= '\ncommand: "%s"'%' '.join(cmd)
        self.assertTrue("Gringo" in out, msg)

    def test_clasp_responds(self):
        cmd = PyBoolNet.Utility.Misc.find_command("clasp")
        cmd = [cmd, "--help"]

        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        out, err = proc.communicate()
        out = out.decode()

        msg = "\nCall to clasp resulted in return code %i."%proc.returncode
        msg+= '\ncommand: "%s"'%' '.join(cmd)
        self.assertEqual(proc.returncode, 0, msg)

        msg = '\nclasp did not respond with "clasp version"'
        msg+= '\ncommand: "%s"'%' '.join(cmd)
        self.assertTrue("clasp version" in out, msg)

class TestNuSMV(unittest.TestCase):
    def test_nusmv_responds(self):
        cmd = PyBoolNet.Utility.Misc.find_command("nusmv")
        cmd = [cmd]

        proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        out, err = proc.communicate(input="MODULE main".encode())
        out = out.decode()

        msg = "\n%s"%out
        msg+= "\nCall to NuSMV failed."
        msg+= '\ncommand: "%s"'%' '.join(cmd)
        self.assertEqual(True, "NuSMV" in out, msg)

class TestBNetToPrime(unittest.TestCase):
    def test_bnet2primes_responds(self):
        cmd = PyBoolNet.Utility.Misc.find_command("bnet2prime")
        cmd = [cmd, "--ver"]

        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        out, err = proc.communicate()
        out = out.decode()

        msg = "\nCall to Bnet2Primes resulted in return code %i."%proc.returncode
        msg+= '\ncommand: "%s"'%' '.join(cmd)
        self.assertEqual(proc.returncode, 0, msg)

        msg = '\nBnet2Primes did not respond with "BNetToPrime 1.0"'
        msg+= '\ncommand: "%s"'%' '.join(cmd)
        self.assertTrue("BNetToPrime 1.0" in out, msg)


class TestGraphviz(unittest.TestCase):
    def test_layout_engines(self):
        for name in ["dot","neato","fdp","sfdp","circo","twopi"]:
            cmd = PyBoolNet.Utility.Misc.find_command(name)

            proc = subprocess.Popen([cmd, "-V"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            out, err = proc.communicate()
            err = err.decode() # for some reason graphviz" reports on stderr

            msg = "\nCall to dot resulted in return code %i."%proc.returncode
            msg+= '\ncommand: "%s"'%' '.join(cmd)
            self.assertEqual(proc.returncode, 0, msg)

            msg = '\ndot did not respond with "%s - graphviz version"'%name
            msg+= '\ncommand: "%s"'%' '.join(cmd)
            self.assertTrue("%s - graphviz version"%name in err, msg)


class TestImageMagick(unittest.TestCase):
    def test_imagemagick_responds(self):
        cmd = PyBoolNet.Utility.Misc.find_command("convert")
        cmd = [cmd, "-help"]

        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        out, err = proc.communicate()
        out = out.decode()

        #msg = "\nCall to convert resulted in return code %i."%proc.returncode
        #msg+= '\ncommand: "%s"'%' '.join(cmd)
        #self.assertEqual(proc.returncode, 0, msg)

        msg = '\ndot did not respond with "ImageMagick"'
        msg+= '\ncommand: "%s"'%' '.join(cmd)
        self.assertTrue("ImageMagick" in out, msg)


class TestEspresso(unittest.TestCase):
    def test_espresso_responds(self):
        cmd = PyBoolNet.Utility.Misc.find_command("espresso")
        cmd = [cmd, "--help"]

        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        out, err = proc.communicate()
        out = out.decode()

        msg = out
        msg+= '\nespresso did not respond with "Espresso Version"'
        msg+= '\ncommand: "%s"'%' '.join(cmd)
        self.assertTrue("Espresso Version" in out, msg)

    def test_eqntott_responds(self):
        cmd = PyBoolNet.Utility.Misc.find_command("eqntott")
        cmd = [cmd, "--help"]

        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        out, err = proc.communicate()
        err = err.decode()

        msg = '\neqntott did not respond with "usage:"'
        msg+= '\ncommand: "%s"'%' '.join(cmd)
        self.assertTrue("usage:" in err, msg)



class TestMatplotLib(unittest.TestCase):
    def test_matplotlib_responds(self):
        import matplotlib.pyplot


if __name__=="__main__":

    x = 1
    if x==1:
        # run all tests
        unittest.main(verbosity=2, buffer=True)
    if x==2:
        # run single test
        suite = unittest.TestSuite()
        suite.addTest(TestConvert("test_convert_responds"))
        runner = unittest.TextTestRunner()
        runner.run(suite)
