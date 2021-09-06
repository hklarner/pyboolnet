

from pyboolnet.model_checking import model_checking, model_checking_smv_file
from pyboolnet.model_checking import primes2smv
from pyboolnet.repository import get_primes
from tests.helpers import get_tests_path_in, get_tests_path_out


def test_check_acceptingstates():
    fname_out = get_tests_path_out(fname="modelchecking_acceptingstates.smv")
    primes = get_primes(name="raf")
    spec = "CTLSPEC EF(!Erk&!Mek&Raf) &  EF(Erk&Mek&Raf)"
    init = "INIT TRUE"
    update = "asynchronous"
    primes2smv(primes, update, init, spec, fname_out)
    answer, accepting = model_checking_smv_file(fname_out, enable_accepting_states=True)

    expected = {"ACCEPTING_SIZE": 3, "INIT": "TRUE", "INIT_SIZE": 8, "INITACCEPTING_SIZE": 3, "INITACCEPTING": "!(Erk & (Mek) | !Erk & ((Raf) | !Mek))", "ACCEPTING": "!(Erk & (Mek) | !Erk & ((Raf) | !Mek))"}
    assert accepting == expected

    answer, accepting = model_checking(primes, update, init, spec, enable_accepting_states=True)
    expected = {"ACCEPTING_SIZE": 3, "INIT": "TRUE", "INIT_SIZE": 8, "INITACCEPTING_SIZE": 3, "INITACCEPTING": "!(Erk & (Mek) | !Erk & ((Raf) | !Mek))", "ACCEPTING": "!(Erk & (Mek) | !Erk & ((Raf) | !Mek))"}

    assert accepting == expected


def test_check_smv_true():
    assert model_checking_smv_file(fname_smv=get_tests_path_in(fname="modelchecking_check_smv_true.smv"))


def test_check_smv_false():
    assert not model_checking_smv_file(fname_smv=get_tests_path_in(fname="modelchecking_check_smv_false.smv"))


def test_check_smv_counterexample():
    fname_in = get_tests_path_in(fname="modelchecking_check_smv_counterexample.smv")
    answer, counterexample = model_checking_smv_file(fname_smv=fname_in, enable_counterexample=True)
    expected = ({"v1": 0, "v2": 1, "v3": 0}, {"v1": 0, "v2": 0, "v3": 0}, {"v1": 1, "v2": 0, "v3": 0}, {"v1": 1, "v2": 1, "v3": 0}, {"v1": 1, "v2": 1, "v3": 1}, {"v1": 1, "v2": 0, "v3": 1})

    assert counterexample == expected


def test_check_primes_async():
    primes = {"v1": [[{"v1": 0, "v3": 1}, {"v1": 0, "v2": 1}], [{"v2": 0, "v3": 0}, {"v1": 1}]],
              "v2": [[{"v3": 1}, {"v1": 0}], [{"v1": 1, "v3": 0}]],
              "v3": [[{"v1": 1, "v2": 0, "v3": 0}], [{"v3": 1}, {"v2": 1}, {"v1": 0}]]}
    expected = ({"v1": 0, "v2": 1, "v3": 0}, {"v1": 0, "v2": 0, "v3": 0}, {"v1": 1, "v2": 0, "v3": 0}, {"v1": 1, "v2": 1, "v3": 0}, {"v1": 1, "v2": 1, "v3": 1}, {"v1": 1, "v2": 0, "v3": 1})

    answer, counterexample = model_checking(
        primes=primes, update="asynchronous",
        initial_states="INIT !v1&v2&!v3",
        specification="CTLSPEC AF(!v1&!v2&v3)",
        dynamic_reorder=True,
        disable_reachable_states=False,
        enable_counterexample=True)

    assert counterexample == expected


def test_check_primes_sync():
    primes = {"v1": [[{"v1": 0, "v3": 1}, {"v1": 0, "v2": 1}], [{"v2": 0, "v3": 0}, {"v1": 1}]],
              "v2": [[{"v3": 1}, {"v1": 0}], [{"v1": 1, "v3": 0}]],
              "v3": [[{"v1": 1, "v2": 0, "v3": 0}], [{"v3": 1}, {"v2": 1}, {"v1": 0}]]}

    answer, counterexample = model_checking(
        primes=primes, update="synchronous",
        initial_states="INIT !v1&v2&!v3",
        specification="CTLSPEC AF(!v1&!v2&v3)",
        dynamic_reorder=True,
        disable_reachable_states=False,
        enable_counterexample=True)

    assert counterexample is None


def test_check_primes_mixed():
    primes = {"v1": [[{"v1": 0, "v3": 1}, {"v1": 0, "v2": 1}], [{"v2": 0, "v3": 0}, {"v1": 1}]],
              "v2": [[{"v3": 1}, {"v1": 0}], [{"v1": 1, "v3": 0}]],
              "v3": [[{"v1": 1, "v2": 0, "v3": 0}], [{"v3": 1}, {"v2": 1}, {"v1": 0}]]}
    expected = ({"v1": 0, "v2": 1, "v3": 0}, {"v1": 0, "v2": 0, "v3": 0}, {"v1": 1, "v2": 0, "v3": 0}, {"v1": 1, "v2": 1, "v3": 0}, {"v1": 1, "v2": 1, "v3": 1}, {"v1": 1, "v2": 0, "v3": 1})

    answer, counterexample = model_checking(
        primes=primes, update="mixed",
        initial_states="INIT !v1&v2&!v3",
        specification="CTLSPEC AF(!v1&!v2&v3)",
        dynamic_reorder=True,
        disable_reachable_states=False,
        enable_counterexample=True)

    assert counterexample == expected
