

import pytest

from pyboolnet.file_exchange import primes2eqn, primes2bnet, read_primes, write_primes
from pyboolnet.file_exchange import primes2genysis, primes2bns
from pyboolnet.model_checking import primes2smv
from pyboolnet.prime_implicants import bnet2primes, primes_are_equal
from pyboolnet.repository import get_primes
from pyboolnet.trap_spaces import primes2asp
from tests.helpers import get_tests_path_in, get_tests_path_out


def test_primes2eqn():
    fname_out = get_tests_path_out(fname="fileexchange_primes2eqn.eqn")
    primes = get_primes("raf")
    primes2eqn(primes, fname_out)


def test_bnet2primes_operatorbinding():
    fname_in = get_tests_path_in(fname="fileexchange_operatorbinding.bnet")
    fname_out = get_tests_path_out(fname="fileexchange_operatorbinding.primes")

    primes = bnet2primes(bnet=fname_in, fname_primes=fname_out)
    names = "abcde"
    results = []
    for x in names:
        for y in names:
            name = x
            results.append(primes_are_equal({name: primes[x]}, {name: primes[y]}))

    assert all(results)


def test_bnet2primes_results():
    fname_in = get_tests_path_in(fname="fileexchange_feedback.bnet")
    fname_out = get_tests_path_out(fname="fileexchange_feedback.primes")
    primes = bnet2primes(bnet=fname_in, fname_primes=fname_out)
    primes_expected = {"v1": [[{"v2": 0}], [{"v2": 1}]], "v2": [[{"v2": 0}, {"v1": 1}], [{"v1": 0, "v2": 1}]]}

    assert primes_are_equal(primes, primes_expected)


def test_bnet2primes_empty():
    fname_in = get_tests_path_in(fname="fileexchange_empty.bnet")
    fname_out = get_tests_path_out(fname="fileexchange_empty.primes")
    primes = bnet2primes(bnet=fname_in, fname_primes=fname_out)
    primes_expected = {}

    assert primes_are_equal(primes, primes_expected), str(primes)


def test_bnet2primes_missing_inputs():
    fname_in = get_tests_path_in(fname="fileexchange_missing_inputs.bnet")
    fname_out = get_tests_path_out(fname="fileexchange_missing_inputs.primes")
    primes = bnet2primes(bnet=fname_in, fname_primes=fname_out)
    primes_expected = {"B": [[{"B": 0}], [{"B": 1}]], "C": [[{"C": 0}], [{"C": 1}]], "A": [[{"B": 0, "C": 1}], [{"C": 0}, {"B": 1}]]}

    assert primes_are_equal(primes, primes_expected), str(primes)


def test_bnet2primes_constants():
    fname_in = get_tests_path_in(fname="fileexchange_constants.bnet")
    fname_out = get_tests_path_out(fname="fileexchange_constants.primes")

    primes = bnet2primes(bnet=fname_in, fname_primes=fname_out)
    primes_expected = {"A": [[{}], []], "B": [[], [{}]]}

    assert primes_are_equal(primes, primes_expected), str(primes)


def test_bnet2primes_a():
    fname_in = get_tests_path_in(fname="fileexchange_constants.bnet")
    fname_out = get_tests_path_out(fname="fileexchange_stdout1.primes")
    file_in = "A, 0\nB, 1"

    expected = {"A": [[{}], []], "B": [[], [{}]]}

    primes = bnet2primes(bnet=fname_in)
    assert primes_are_equal(primes, expected)

    primes = bnet2primes(bnet=file_in)
    assert primes_are_equal(primes, expected)

    primes = bnet2primes(bnet=fname_in, fname_primes=fname_out)
    assert primes_are_equal(primes, expected)


def test_primes2bnet_b():
    fname = get_tests_path_out(fname="fileexchange_primes2bnet.primes")
    primes = {"B": [[{}], []], "C": [[{"C": 0}], [{"C": 1}]], "A": [[{"B": 0, "C": 1}], [{"C": 0}, {"B": 1}]]}
    primes2bnet(primes=primes, fname_bnet=fname)
    primes2bnet(primes=primes, fname_bnet=fname, minimize=True)


def test_read_primes():
    fname = get_tests_path_in(fname="fileexchange_missing_inputs.primes")
    primes = read_primes(fname_json=fname)
    primes_expected = {"B": [[{"B": 0}], [{"B": 1}]], "C": [[{"C": 0}], [{"C": 1}]], "A": [[{"B": 0, "C": 1}], [{"C": 0}, {"B": 1}]]}

    assert primes_are_equal(primes, primes_expected), str(primes)


def test_read_write_primes():
    fname = get_tests_path_out(fname="fileexchange_read_write.primes")
    primes_write = {"B": [[{}], []], "C": [[{"C": 0}], [{"C": 1}]], "A": [[{"B": 0, "C": 1}], [{"C": 0}, {"B": 1}]]}
    write_primes(primes=primes_write, fname_json=fname)
    primes_read = read_primes(fname_json=fname)

    assert primes_are_equal(primes_read, primes_write)


def test_primes2genysis():
    fname = get_tests_path_out(fname="fileexchange_primes2genysis.genysis")
    primes = {"B": [[{}], []], "C": [[{"C": 0}], [{"C": 1}]], "A": [[{"B": 0, "C": 1}], [{"C": 0}, {"B": 1}]]}
    primes2genysis(primes=primes, fname_genysis=fname)


def test_primes2bns():
    fname = get_tests_path_out(fname="fileexchange_primes2bns.bns")
    primes = {"B": [[{}], []], "C": [[{"C": 0}], [{"C": 1}]], "A": [[{"B": 0, "C": 1}], [{"C": 0}, {"B": 1}]]}
    primes2bns(primes=primes, fname_bns=fname)


def test_primes2smv():
    primes = {"vB": [[{}], []], "vC": [[{"vC": 0}], [{"vC": 1}]], "vA": [[{"vB": 0, "vC": 1}], [{"vC": 0}, {"vB": 1}]]}
    fname = get_tests_path_out(fname="fileexchange_primes2smv_syn.smv")
    primes2smv(primes=primes, fname_smv=fname, update="synchronous", initial_states="INIT TRUE", specification="CTLSPEC TRUE")
    fname = get_tests_path_out(fname="fileexchange_primes2smv_async.smv")
    primes2smv(primes=primes, fname_smv=fname, update="asynchronous", initial_states="INIT TRUE", specification="CTLSPEC TRUE")
    fname = get_tests_path_out(fname="fileexchange_primes2smv_mixed.smv")
    primes2smv(primes=primes, fname_smv=fname, update="mixed", initial_states="INIT TRUE", specification="CTLSPEC TRUE")


@pytest.mark.parametrize("bounds", [None, (1, 2)])
@pytest.mark.parametrize("projection", [None, ["A", "B"]])
@pytest.mark.parametrize("type_", [None, "circuits", "percolated"])
def test_primes2asp(bounds, projection, type_):
    primes = {"B": [[{}], []], "C": [[{"C": 0}], [{"C": 1}]], "A": [[{"B": 0, "C": 1}], [{"C": 0}, {"B": 1}]]}
    fname = get_tests_path_out(fname="fileexchange_primes2asp_case.asp")
    primes2asp(primes=primes, fname_asp=fname, bounds=bounds, project=projection, type_=type_)

