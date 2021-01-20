

import os
import pytest

import PyBoolNet


FILES_IN = os.path.join(os.path.dirname(__file__), "files_input")
FILES_OUT = os.path.join(os.path.dirname(__file__), "files_output")


def test_primes2eqn():
    fname_out = os.path.join(FILES_OUT, "fileexchange_primes2eqn.eqn")
    primes = PyBoolNet.Repository.get_primes("raf")
    PyBoolNet.FileExchange.primes2eqn(primes, fname_out)


def test_bnet2primes_operatorbinding():
    fname_in = os.path.join(FILES_IN,  "fileexchange_operatorbinding.bnet")
    fname_out = os.path.join(FILES_OUT, "fileexchange_operatorbinding.primes")

    primes = PyBoolNet.FileExchange.bnet2primes(BNET=fname_in, FnamePRIMES=fname_out)
    names = "abcde"
    results = []
    for x in names:
        for y in names:
            name = x
            results.append(PyBoolNet.PrimeImplicants.are_equal({name: primes[x]}, {name: primes[y]}))

    assert all(results)


def test_bnet2primes_results():
    fname_in = os.path.join(FILES_IN,  "fileexchange_feedback.bnet")
    fname_out = os.path.join(FILES_OUT, "fileexchange_feedback.primes")

    primes = PyBoolNet.FileExchange.bnet2primes(BNET=fname_in, FnamePRIMES=fname_out)
    primes_expected = {"v1": [[{"v2": 0}], [{"v2": 1}]], "v2": [[{"v2": 0}, {"v1": 1}], [{"v1": 0, "v2": 1}]]}

    assert PyBoolNet.PrimeImplicants.are_equal(primes, primes_expected)


def test_bnet2primes_empty():
    fname_in = os.path.join(FILES_IN,  "fileexchange_empty.bnet")
    fname_out = os.path.join(FILES_OUT, "fileexchange_empty.primes")

    primes = PyBoolNet.FileExchange.bnet2primes(BNET=fname_in, FnamePRIMES=fname_out)
    primes_expected = {}

    assert PyBoolNet.PrimeImplicants.are_equal(primes, primes_expected), str(primes)


def test_bnet2primes_missing_inputs():
    fname_in = os.path.join(FILES_IN,  "fileexchange_missing_inputs.bnet")
    fname_out = os.path.join(FILES_OUT, "fileexchange_missing_inputs.primes")

    primes = PyBoolNet.FileExchange.bnet2primes(BNET=fname_in, FnamePRIMES=fname_out)
    primes_expected = {"B": [[{"B": 0}], [{"B": 1}]], "C": [[{"C": 0}], [{"C": 1}]], "A": [[{"B": 0, "C": 1}], [{"C": 0}, {"B": 1}]]}

    assert PyBoolNet.PrimeImplicants.are_equal(primes, primes_expected), str(primes)


def test_bnet2primes_constants():
    fname_in = os.path.join(FILES_IN,  "fileexchange_constants.bnet")
    fname_out = os.path.join(FILES_OUT, "fileexchange_constants.primes")

    primes = PyBoolNet.FileExchange.bnet2primes(BNET=fname_in, FnamePRIMES=fname_out)
    primes_expected = {"A": [[{}], []], "B": [[], [{}]]}

    assert PyBoolNet.PrimeImplicants.are_equal(primes, primes_expected), str(primes)


def test_bnet2primes_a():
    fname_in = os.path.join(FILES_IN,  "fileexchange_constants.bnet")
    fname_out = os.path.join(FILES_OUT, "fileexchange_stdout1.primes")
    file_in = "A, 0\nB, 1"

    expected = {"A": [[{}], []], "B": [[], [{}]]}

    primes = PyBoolNet.FileExchange.bnet2primes(BNET=fname_in)
    assert PyBoolNet.PrimeImplicants.are_equal(primes, expected)

    primes = PyBoolNet.FileExchange.bnet2primes(BNET=file_in)

    assert PyBoolNet.PrimeImplicants.are_equal(primes, expected)

    primes = PyBoolNet.FileExchange.bnet2primes(BNET=fname_in, FnamePRIMES=fname_out)

    assert PyBoolNet.PrimeImplicants.are_equal(primes, expected)


def test_primes2bnet_b():
    fname = os.path.join(FILES_OUT, "fileexchange_primes2bnet.primes")
    primes = {"B": [[{}], []], "C": [[{"C": 0}], [{"C": 1}]], "A": [[{"B": 0, "C": 1}], [{"C": 0}, {"B": 1}]]}
    PyBoolNet.FileExchange.primes2bnet(Primes=primes, FnameBNET=fname)
    PyBoolNet.FileExchange.primes2bnet(Primes=primes, FnameBNET=fname, Minimize=True)


def test_read_primes():
    fname = os.path.join(FILES_IN, "fileexchange_missing_inputs.primes")

    primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname)
    primes_expected = {"B": [[{"B": 0}], [{"B": 1}]], "C": [[{"C": 0}], [{"C": 1}]], "A": [[{"B": 0, "C": 1}], [{"C": 0}, {"B": 1}]]}
    assert PyBoolNet.PrimeImplicants.are_equal(primes, primes_expected), str(primes)


def test_read_write_primes():
    fname = os.path.join(FILES_OUT, "fileexchange_read_write.primes")

    primes_write = {"B": [[{}], []], "C": [[{"C": 0}], [{"C": 1}]], "A": [[{"B": 0, "C": 1}], [{"C": 0}, {"B": 1}]]}
    PyBoolNet.FileExchange.write_primes(Primes=primes_write, FnamePRIMES=fname)
    primes_read = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname)

    assert PyBoolNet.PrimeImplicants.are_equal(primes_read, primes_write)


def test_primes2genysis():
    fname = os.path.join(FILES_OUT, "fileexchange_primes2genysis.genysis")
    primes = {"B": [[{}], []], "C": [[{"C": 0}], [{"C": 1}]], "A": [[{"B": 0, "C": 1}], [{"C": 0}, {"B": 1}]]}
    PyBoolNet.FileExchange.primes2genysis(Primes=primes, FnameGENYSIS=fname)


def test_primes2bns():
    fname = os.path.join(FILES_OUT, "fileexchange_primes2bns.bns")
    primes = {"B": [[{}], []], "C": [[{"C": 0}], [{"C": 1}]], "A": [[{"B": 0, "C": 1}], [{"C": 0}, {"B": 1}]]}
    PyBoolNet.FileExchange.primes2bns(Primes=primes, FnameBNS=fname)


def test_primes2smv():
    primes = {"vB": [[{}], []], "vC": [[{"vC": 0}], [{"vC": 1}]], "vA": [[{"vB": 0, "vC": 1}], [{"vC": 0}, {"vB": 1}]]}

    fname = os.path.join(FILES_OUT, "fileexchange_primes2smv_syn.smv")
    PyBoolNet.ModelChecking.primes2smv(Primes=primes, FnameSMV=fname, Update="synchronous", InitialStates="INIT TRUE", Specification="CTLSPEC TRUE")
    fname = os.path.join(FILES_OUT, "fileexchange_primes2smv_async.smv")
    PyBoolNet.ModelChecking.primes2smv(Primes=primes, FnameSMV=fname, Update="asynchronous", InitialStates="INIT TRUE", Specification="CTLSPEC TRUE")
    fname = os.path.join(FILES_OUT, "fileexchange_primes2smv_mixed.smv")
    PyBoolNet.ModelChecking.primes2smv(Primes=primes, FnameSMV=fname, Update="mixed", InitialStates="INIT TRUE", Specification="CTLSPEC TRUE")


@pytest.mark.parametrize("bounds", [None, (1, 2)])
@pytest.mark.parametrize("projection", [None, ["A", "B"]])
@pytest.mark.parametrize("type_", [None, "circuits", "percolated"])
def test_primes2asp(bounds, projection, type_):
    primes = {"B": [[{}], []], "C": [[{"C": 0}], [{"C": 1}]], "A": [[{"B": 0, "C": 1}], [{"C": 0}, {"B": 1}]]}

    fname = os.path.join(FILES_OUT, "fileexchange_primes2asp_case.asp")
    PyBoolNet.AspSolver.primes2asp(Primes=primes, FnameASP=fname, Bounds=bounds, Project=projection, Type=type_)

