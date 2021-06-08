

import os

import PyBoolNet
from PyBoolNet.attractors import compute_json

FILES_IN = os.path.join(os.path.dirname(__file__), "files_input")
FILES_OUT = os.path.join(os.path.dirname(__file__), "files_output")


def test_compute_attractors_tarjan():
    
    bnet = "\n".join(["x, !x&y | z", "y, !x | !z", "z, x&!y"])
    primes = PyBoolNet.file_exchange.bnet2primes(bnet)
    stg = PyBoolNet.state_transition_graphs.primes2stg(primes, "asynchronous")
    steady_states, cyclic = PyBoolNet.attractors.compute_attractors_tarjan(stg)

    assert steady_states == ["101"]
    assert cyclic == [{"010", "110"}]


def test_find_attractor_state_by_randomwalk_and_ctl():
    fname_in = os.path.join(FILES_IN, "randomnet.bnet")
    fname_out = os.path.join(FILES_OUT, "randomnet.primes")
    primes = PyBoolNet.file_exchange.bnet2primes(BNET=fname_in, FnamePRIMES=fname_out)

    subspace = {"Gene1": 0, "Gene3": 0, "Gene5": 0, "Gene7": 0, "Gene9": 0}
    length = 200
    attempts = 10

    mints = {"Gene1": 1, "Gene11": 0, "Gene12": 1, "Gene13": 0, "Gene14": 1, "Gene15": 0, "Gene16": 1, "Gene17": 1, "Gene18": 1, "Gene19": 0, "Gene2": 1, "Gene20": 1, "Gene3": 0, "Gene4": 1, "Gene5": 0, "Gene6": 0, "Gene8": 0, "Gene9": 0}

    x = PyBoolNet.attractors.find_attractor_state_by_randomwalk_and_ctl(primes, "asynchronous", subspace, length, attempts)
    assert PyBoolNet.state_transition_graphs.state_is_in_subspace(primes, x, mints)

    y = PyBoolNet.attractors.find_attractor_state_by_randomwalk_and_ctl(primes, "synchronous", subspace, length, attempts)
    reachable = PyBoolNet.state_transition_graphs.list_reachable_states(primes, "synchronous", y, 100)

    assert PyBoolNet.state_transition_graphs.state2str(y) in reachable

    z = PyBoolNet.attractors.find_attractor_state_by_randomwalk_and_ctl(primes, "mixed", subspace, length, attempts)
    assert PyBoolNet.state_transition_graphs.state_is_in_subspace(primes, z, mints)
    

def test_univocality():

    bnet = "\n".join(["v1, !v1&!v2 | v2&!v3", "v2, v1&v2", "v3, v2 | v3", "v4, 1"])
    primes = PyBoolNet.file_exchange.bnet2primes(bnet)
    PyBoolNet.attractors.univocality(primes, "asynchronous", {"v4": 1})

    assert not PyBoolNet.attractors.univocality(primes, "asynchronous", {"v4": 1})

    answer, example = PyBoolNet.attractors.univocality_with_counterexample(primes, "asynchronous", {})

    assert (len(example[0]), len(example[1])) == (4, 4)

    primes = PyBoolNet.file_exchange.bnet2primes("""v1, 0 \n v2, v2""")
    tspace = {"v1": 0}
    answer, example = PyBoolNet.attractors.univocality_with_counterexample(primes, "asynchronous", tspace)
    expected = [{"v1": 0, "v2": 0}, {"v1": 0, "v2": 1}]

    assert example[0] in expected
    assert example[1] in expected
    assert len(example) == 2

    bnet = "\n".join(["v1, !v1&!v2 | !v3", "v2, v1&v2", "v3, v1&v3 | v2", "v4, 0"])
    primes = PyBoolNet.file_exchange.bnet2primes(bnet)

    answer, example = PyBoolNet.attractors.univocality_with_counterexample(primes, "asynchronous", {})

    assert example is None

    answer = PyBoolNet.attractors.univocality(primes, "asynchronous", tspace)

    assert answer


def test_faithfulness():

    bnet = "\n".join(["v1, !v1&!v2 | !v2&!v3", "v2, !v1&!v2&v3 | v1&!v3", "v3, !v1&v3 | !v2"])
    primes = PyBoolNet.file_exchange.bnet2primes(bnet)

    assert not PyBoolNet.attractors.faithfulness(primes, "asynchronous", {})
    assert PyBoolNet.attractors.faithfulness(primes, "asynchronous", {"v3": 1})

    primes = PyBoolNet.file_exchange.bnet2primes("""v1, 0 \n v2, v1 \n v3, v3""")
    answer, example = PyBoolNet.attractors.faithfulness_with_counterexample(primes, "asynchronous", {"v1": 0})
    
    assert not answer
    assert example in [{"v1": 0, "v2": 0, "v3": 0}, {"v1": 0, "v2": 0, "v3": 1}]


def test_completeness_naive():

    bnet = "\n".join(["v1, v1 | v2&!v3", "v2, !v1&v2&v3", "v3, !v2&!v3 | v2&v3"])
    primes = PyBoolNet.file_exchange.bnet2primes(bnet)

    answer = PyBoolNet.attractors.completeness_naive(primes, "asynchronous", ["00-", "10-"])

    assert not answer
    assert PyBoolNet.attractors.completeness_naive(primes, "asynchronous", ["00-", "10-", {"v1": 0, "v2": 1, "v3": 1}])


def test_completeness():
    bnet = "\n".join(["v0,   v0", "v1,   v2", "v2,   v1", "v3,   v1&v0", "v4,   v2", "v5,   v3&!v6", "v6,   v4&v5"])
    primes = PyBoolNet.file_exchange.bnet2primes(bnet)

    assert PyBoolNet.attractors.completeness(primes, "asynchronous")
    assert not PyBoolNet.attractors.completeness(primes, "synchronous")

    answer, example = PyBoolNet.attractors.completeness_with_counterexample(primes, "synchronous")
    example = PyBoolNet.state_transition_graphs.state2str(example)
    stg = PyBoolNet.state_transition_graphs.primes2stg(primes, "synchronous")

    for x in PyBoolNet.trap_spaces.trap_spaces(primes, "min"):
        x = PyBoolNet.state_transition_graphs.subspace2str(primes, x)

        states = PyBoolNet.state_transition_graphs.list_states_in_subspace(primes, x)
        states = [PyBoolNet.state_transition_graphs.state2str(x) for x in states]

        assert not PyBoolNet.Utility.DiGraphs.has_path(stg, example, states)

    bnet = "\n".join(["v1, !v1&v2&v3 | v1&!v2&!v3", "v2, !v1&!v2 | v1&v3", "v3, !v1&v3 | v1&v2", "v4, 1", "v5, v4"])
    primes = PyBoolNet.file_exchange.bnet2primes(bnet)

    assert not PyBoolNet.attractors.completeness(primes, "asynchronous")

    answer, example = PyBoolNet.attractors.completeness_with_counterexample(primes, "asynchronous")

    assert len(example) == len(primes)
    assert PyBoolNet.attractors.completeness(primes, "synchronous")

    bnet = "\n".join(["v1, !v1&v2&v3 | v1&!v2&!v3", "v2, !v1&!v2 | v1&v3", "v3, v2 | v3"])
    primes = PyBoolNet.file_exchange.bnet2primes(bnet)

    assert PyBoolNet.attractors.completeness(primes, "asynchronous")
    assert PyBoolNet.attractors.completeness(primes, "synchronous")

    bnet = "\n".join(["v1,   !v2", "v2,   v1", "v3,   v1", "v4,   v2", "v5,   v6", "v6,   v4&v5", "v7,   v2", "v8,   v5", "v9,   v6&v10", "v10,  v9&v7"])
    primes = PyBoolNet.file_exchange.bnet2primes(bnet)

    assert PyBoolNet.attractors.completeness(primes, "synchronous")


def test_completeness_maxoutput():
    primes = PyBoolNet.Repository.get_primes("davidich_yeast")

    assert PyBoolNet.attractors.completeness(primes, "asynchronous", max_output=10000)
    assert not PyBoolNet.attractors.completeness(primes, "asynchronous", max_output=2)


def test_compute_json():
    primes = PyBoolNet.Repository.get_primes("n5s3")
    fname_json = os.path.join(FILES_OUT, "n5s3_attrs.json")
    attrs = compute_json(primes=primes, update="asynchronous", fname_json=fname_json, max_output=2)

    assert attrs

