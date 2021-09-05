

from pyboolnet.model_checking import check_smv, check_smv_with_counterexample, model_checking_with_counterexample
from pyboolnet.model_checking import primes2smv, check_smv_with_acceptingstates, model_checking_with_acceptingstates
from pyboolnet.repository import get_primes
from tests.helpers import get_tests_path_in, get_tests_path_out


def test_check_acceptingstates():
    fname_out = get_tests_path_out(fname="modelchecking_acceptingstates.smv")
    primes = get_primes(name="raf")
    spec = "CTLSPEC EF(!Erk&!Mek&Raf) &  EF(Erk&Mek&Raf)"
    init = "INIT TRUE"
    update = "asynchronous"
    primes2smv(primes, update, init, spec, fname_out)
    answer, accepting = check_smv_with_acceptingstates(fname_out)

    expected = {"ACCEPTING_SIZE": 3, "INIT": "TRUE", "INIT_SIZE": 8, "INITACCEPTING_SIZE": 3, "INITACCEPTING": "!(Erk & (Mek) | !Erk & ((Raf) | !Mek))", "ACCEPTING": "!(Erk & (Mek) | !Erk & ((Raf) | !Mek))"}
    assert accepting == expected

    answer, accepting = model_checking_with_acceptingstates(primes, update, init, spec)
    expected = {"ACCEPTING_SIZE": 3, "INIT": "TRUE", "INIT_SIZE": 8, "INITACCEPTING_SIZE": 3, "INITACCEPTING": "!(Erk & (Mek) | !Erk & ((Raf) | !Mek))", "ACCEPTING": "!(Erk & (Mek) | !Erk & ((Raf) | !Mek))"}

    assert accepting == expected


def test_check_smv_true():
    fname_in = get_tests_path_in(fname="modelchecking_check_smv_true.smv")

    assert check_smv(fname_smv=fname_in, dynamic_reorder=True, disable_reachable_states=True, cone_of_influence=True)


def test_check_smv_false():
    fname_in = get_tests_path_in(fname="modelchecking_check_smv_false.smv")

    assert not check_smv(fname_smv=fname_in, dynamic_reorder=True, disable_reachable_states=True, cone_of_influence=True)


def test_check_smv_counterexample():
    fname_in = get_tests_path_in(fname="modelchecking_check_smv_counterexample.smv")
    answer, counterexample = check_smv_with_counterexample(fname_smv=fname_in, dynamic_reorder=True, disable_reachable_states=True)
    expected = ({"v1": 0, "v2": 1, "v3": 0}, {"v1": 0, "v2": 0, "v3": 0}, {"v1": 1, "v2": 0, "v3": 0}, {"v1": 1, "v2": 1, "v3": 0}, {"v1": 1, "v2": 1, "v3": 1}, {"v1": 1, "v2": 0, "v3": 1})

    assert counterexample == expected


def test_check_primes_async():
    primes = {"v1": [[{"v1": 0, "v3": 1}, {"v1": 0, "v2": 1}], [{"v2": 0, "v3": 0}, {"v1": 1}]],
              "v2": [[{"v3": 1}, {"v1": 0}], [{"v1": 1, "v3": 0}]],
              "v3": [[{"v1": 1, "v2": 0, "v3": 0}], [{"v3": 1}, {"v2": 1}, {"v1": 0}]]}
    expected = ({"v1": 0, "v2": 1, "v3": 0}, {"v1": 0, "v2": 0, "v3": 0}, {"v1": 1, "v2": 0, "v3": 0}, {"v1": 1, "v2": 1, "v3": 0}, {"v1": 1, "v2": 1, "v3": 1}, {"v1": 1, "v2": 0, "v3": 1})

    answer, counterexample = model_checking_with_counterexample(
        primes=primes, update="asynchronous",
        init="INIT !v1&v2&!v3",
        spec="CTLSPEC AF(!v1&!v2&v3)",
        dynamic_reorder=True,
        disable_reachable_states=False)

    assert counterexample == expected


def test_check_primes_sync():
    primes = {"v1": [[{"v1": 0, "v3": 1}, {"v1": 0, "v2": 1}], [{"v2": 0, "v3": 0}, {"v1": 1}]],
              "v2": [[{"v3": 1}, {"v1": 0}], [{"v1": 1, "v3": 0}]],
              "v3": [[{"v1": 1, "v2": 0, "v3": 0}], [{"v3": 1}, {"v2": 1}, {"v1": 0}]]}

    answer, counterexample = model_checking_with_counterexample(
        primes=primes,
        update="synchronous",
        init="INIT !v1&v2&!v3",
        spec="CTLSPEC AF(!v1&!v2&v3)",
        dynamic_reorder=True,
        disable_reachable_states=False)

    assert counterexample is None


def test_check_primes_mixed():
    primes = {"v1": [[{"v1": 0, "v3": 1}, {"v1": 0, "v2": 1}], [{"v2": 0, "v3": 0}, {"v1": 1}]],
              "v2": [[{"v3": 1}, {"v1": 0}], [{"v1": 1, "v3": 0}]],
              "v3": [[{"v1": 1, "v2": 0, "v3": 0}], [{"v3": 1}, {"v2": 1}, {"v1": 0}]]}
    expected = ({"v1": 0, "v2": 1, "v3": 0}, {"v1": 0, "v2": 0, "v3": 0}, {"v1": 1, "v2": 0, "v3": 0}, {"v1": 1, "v2": 1, "v3": 0}, {"v1": 1, "v2": 1, "v3": 1}, {"v1": 1, "v2": 0, "v3": 1})

    answer, counterexample = model_checking_with_counterexample(
        primes=primes,
        update="mixed",
        init="INIT !v1&v2&!v3",
        spec="CTLSPEC AF(!v1&!v2&v3)",
        dynamic_reorder=True,
        disable_reachable_states=False)

    assert counterexample == expected
