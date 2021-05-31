
import os

import PyBoolNet


FILES_IN = os.path.join(os.path.dirname(__file__), "files_input")
FILES_OUT = os.path.join(os.path.dirname(__file__), "files_output")


def test_accepting_states():
    bnet = """
    Erk, Raf&Mek | Mek&Erk
    Mek, Raf&Mek | Erk
    Raf, !Raf | !Erk
    """

    fname_out = os.path.join(FILES_OUT, "modelchecking_acceptingstates.smv")
    primes = PyBoolNet.file_exchange.bnet2primes(bnet)

    spec = "CTLSPEC EF(!Erk&!Mek&Raf) &  EF(Erk&Mek&Raf)"
    init = "INIT TRUE"
    update = "asynchronous"

    PyBoolNet.model_checking.primes2smv(primes, update, init, spec, fname_out)
    answer, accepting = PyBoolNet.model_checking.check_smv_with_acceptingstates(fname_out)

    expected = {"ACCEPTING_SIZE": 3, "INIT": "TRUE", "INIT_SIZE": 8, "INITACCEPTING_SIZE": 3, "INITACCEPTING": "!(Erk & (Mek) | !Erk & ((Raf) | !Mek))", "ACCEPTING": "!(Erk & (Mek) | !Erk & ((Raf) | !Mek))"}

    assert accepting == expected

    answer, accepting = PyBoolNet.model_checking.check_primes_with_acceptingstates(primes, update, init, spec)
    expected = {"ACCEPTING_SIZE": 3, "INIT": "TRUE", "INIT_SIZE": 8, "INITACCEPTING_SIZE": 3, "INITACCEPTING": "!(Erk & (Mek) | !Erk & ((Raf) | !Mek))", "ACCEPTING": "!(Erk & (Mek) | !Erk & ((Raf) | !Mek))"}

    assert accepting == expected


def test_check_smv_true():
    fname_in = os.path.join(FILES_IN,  "modelchecking_check_smv_true.smv")

    assert PyBoolNet.model_checking.check_smv(FnameSMV=fname_in, DynamicReorder=True, DisableReachableStates=True, ConeOfInfluence=True)


def test_check_smv_false():
    fname_in = os.path.join(FILES_IN,  "modelchecking_check_smv_false.smv")

    assert not PyBoolNet.model_checking.check_smv(FnameSMV=fname_in, DynamicReorder=True, DisableReachableStates=True, ConeOfInfluence=True)


def test_check_smv_counterexample():
    fname_in = os.path.join(FILES_IN,  "modelchecking_check_smv_counterexample.smv")

    answer, counterex = PyBoolNet.model_checking.check_smv_with_counterexample(FnameSMV=fname_in, DynamicReorder=True, DisableReachableStates=True)

    expected = ({"v1": 0, "v2": 1, "v3": 0}, {"v1": 0, "v2": 0, "v3": 0}, {"v1": 1, "v2": 0, "v3": 0}, {"v1": 1, "v2": 1, "v3": 0}, {"v1": 1, "v2": 1, "v3": 1}, {"v1": 1, "v2": 0, "v3": 1})

    assert counterex == expected


def test_check_primes_async():
    primes = {"v1": [[{"v1": 0, "v3": 1}, {"v1": 0, "v2": 1}], [{"v2": 0, "v3": 0}, {"v1": 1}]],
              "v2": [[{"v3": 1}, {"v1": 0}], [{"v1": 1, "v3": 0}]],
              "v3": [[{"v1": 1, "v2": 0, "v3": 0}], [{"v3": 1}, {"v2": 1}, {"v1": 0}]]}
    expected = ({"v1": 0, "v2": 1, "v3": 0}, {"v1": 0, "v2": 0, "v3": 0}, {"v1": 1, "v2": 0, "v3": 0}, {"v1": 1, "v2": 1, "v3": 0}, {"v1": 1, "v2": 1, "v3": 1}, {"v1": 1, "v2": 0, "v3": 1})

    answer, counterex = PyBoolNet.model_checking.check_primes_with_counterexample(Primes=primes, Update="asynchronous",
                                                                                  InitialStates="INIT !v1&v2&!v3",
                                                                                  Specification="CTLSPEC AF(!v1&!v2&v3)",
                                                                                  DynamicReorder=True,
                                                                                  DisableReachableStates=False)

    assert counterex == expected


def test_check_primes_sync():
    primes = {"v1": [[{"v1": 0, "v3": 1}, {"v1": 0, "v2": 1}], [{"v2": 0, "v3": 0}, {"v1": 1}]],
              "v2": [[{"v3": 1}, {"v1": 0}], [{"v1": 1, "v3": 0}]],
              "v3": [[{"v1": 1, "v2": 0, "v3": 0}], [{"v3": 1}, {"v2": 1}, {"v1": 0}]]}

    answer, counterex = PyBoolNet.model_checking.check_primes_with_counterexample(Primes=primes, Update="synchronous",
                                                                                  InitialStates="INIT !v1&v2&!v3",
                                                                                  Specification="CTLSPEC AF(!v1&!v2&v3)",
                                                                                  DynamicReorder=True,
                                                                                  DisableReachableStates=False)

    assert counterex is None


def test_check_primes_mixed():
    primes = {"v1": [[{"v1": 0, "v3": 1}, {"v1": 0, "v2": 1}], [{"v2": 0, "v3": 0}, {"v1": 1}]],
              "v2": [[{"v3": 1}, {"v1": 0}], [{"v1": 1, "v3": 0}]],
              "v3": [[{"v1": 1, "v2": 0, "v3": 0}], [{"v3": 1}, {"v2": 1}, {"v1": 0}]]}
    expected = ({"v1": 0, "v2": 1, "v3": 0}, {"v1": 0, "v2": 0, "v3": 0}, {"v1": 1, "v2": 0, "v3": 0}, {"v1": 1, "v2": 1, "v3": 0}, {"v1": 1, "v2": 1, "v3": 1}, {"v1": 1, "v2": 0, "v3": 1})

    answer, counterex = PyBoolNet.model_checking.check_primes_with_counterexample(Primes=primes, Update="mixed",
                                                                                  InitialStates="INIT !v1&v2&!v3",
                                                                                  Specification="CTLSPEC AF(!v1&!v2&v3)",
                                                                                  DynamicReorder=True,
                                                                                  DisableReachableStates=False)

    assert counterex == expected
