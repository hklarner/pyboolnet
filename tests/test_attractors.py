

import os


from pyboolnet.file_exchange import bnet2primes
from pyboolnet.state_transition_graphs import primes2stg
from pyboolnet.attractors import compute_attractors_tarjan
from pyboolnet.attractors import find_attractor_state_by_randomwalk_and_ctl
from pyboolnet.state_space import state_is_in_subspace, list_states_in_subspace, subspace2str, state2str
from pyboolnet.state_transition_graphs import list_reachable_states
from pyboolnet.attractors import univocality, univocality_with_counterexample
from pyboolnet.attractors import faithfulness, faithfulness_with_counterexample
from pyboolnet.attractors import completeness_naive, completeness, completeness_with_counterexample
from pyboolnet.attractors import compute_attractors
from pyboolnet.trap_spaces import trap_spaces
from pyboolnet.digraphs import has_path
from pyboolnet.repository import get_primes
from tests.helpers import get_tests_path_in, get_tests_path_out


def test_compute_attractors_tarjan():
    bnet = "\n".join(["x, !x&y | z", "y, !x | !z", "z, x&!y"])
    primes = bnet2primes(bnet)
    stg = primes2stg(primes, "asynchronous")
    steady_states, cyclic = compute_attractors_tarjan(stg)

    assert steady_states == ["101"]
    assert cyclic == [{"010", "110"}]


def test_find_attractor_state_by_randomwalk_and_ctl():
    fname_in = get_tests_path_in(fname="randomnet.bnet")
    fname_out = get_tests_path_out(fname="randomnet.primes")
    primes = bnet2primes(bnet=fname_in, fname_primes=fname_out)

    subspace = {"Gene1": 0, "Gene3": 0, "Gene5": 0, "Gene7": 0, "Gene9": 0}
    length = 200
    attempts = 10

    mints = {"Gene1": 1, "Gene11": 0, "Gene12": 1, "Gene13": 0, "Gene14": 1, "Gene15": 0, "Gene16": 1, "Gene17": 1, "Gene18": 1, "Gene19": 0, "Gene2": 1, "Gene20": 1, "Gene3": 0, "Gene4": 1, "Gene5": 0, "Gene6": 0, "Gene8": 0, "Gene9": 0}

    x = find_attractor_state_by_randomwalk_and_ctl(primes, "asynchronous", subspace, length, attempts)
    assert state_is_in_subspace(primes, x, mints)

    y = find_attractor_state_by_randomwalk_and_ctl(primes, "synchronous", subspace, length, attempts)
    reachable = list_reachable_states(primes, "synchronous", list(y), 100)

    assert state2str(y) in reachable

    z = find_attractor_state_by_randomwalk_and_ctl(primes, "mixed", subspace, length, attempts)
    assert state_is_in_subspace(primes, z, mints)
    

def test_univocality():
    bnet = "\n".join(["v1, !v1&!v2 | v2&!v3", "v2, v1&v2", "v3, v2 | v3", "v4, 1"])
    primes = bnet2primes(bnet)
    univocality(primes, "asynchronous", {"v4": 1})

    assert not univocality(primes, "asynchronous", {"v4": 1})

    answer, example = univocality_with_counterexample(primes, "asynchronous", {})

    assert (len(example[0]), len(example[1])) == (4, 4)

    primes = bnet2primes("""v1, 0 \n v2, v2""")
    tspace = {"v1": 0}
    answer, example = univocality_with_counterexample(primes, "asynchronous", tspace)
    expected = [{"v1": 0, "v2": 0}, {"v1": 0, "v2": 1}]

    assert example[0] in expected
    assert example[1] in expected
    assert len(example) == 2

    bnet = "\n".join(["v1, !v1&!v2 | !v3", "v2, v1&v2", "v3, v1&v3 | v2", "v4, 0"])
    primes = bnet2primes(bnet)

    answer, example = univocality_with_counterexample(primes, "asynchronous", {})

    assert example is None

    answer = univocality(primes, "asynchronous", tspace)

    assert answer


def test_faithfulness():
    bnet = "\n".join(["v1, !v1&!v2 | !v2&!v3", "v2, !v1&!v2&v3 | v1&!v3", "v3, !v1&v3 | !v2"])
    primes = bnet2primes(bnet)

    assert not faithfulness(primes, "asynchronous", {})
    assert faithfulness(primes, "asynchronous", {"v3": 1})

    primes = bnet2primes("""v1, 0 \n v2, v1 \n v3, v3""")
    answer, example = faithfulness_with_counterexample(primes, "asynchronous", {"v1": 0})
    
    assert not answer
    assert example in [{"v1": 0, "v2": 0, "v3": 0}, {"v1": 0, "v2": 0, "v3": 1}]


def test_completeness_naive():
    bnet = "\n".join(["v1, v1 | v2&!v3", "v2, !v1&v2&v3", "v3, !v2&!v3 | v2&v3"])
    primes = bnet2primes(bnet)

    answer = completeness_naive(primes, "asynchronous", ["00-", "10-"])

    assert not answer
    assert completeness_naive(primes, "asynchronous", ["00-", "10-", {"v1": 0, "v2": 1, "v3": 1}])


def test_completeness():
    bnet = "\n".join(["v0,   v0", "v1,   v2", "v2,   v1", "v3,   v1&v0", "v4,   v2", "v5,   v3&!v6", "v6,   v4&v5"])
    primes = bnet2primes(bnet)

    assert completeness(primes, "asynchronous")
    assert not completeness(primes, "synchronous")

    answer, example = completeness_with_counterexample(primes, "synchronous")
    example = state2str(example)
    stg = primes2stg(primes, "synchronous")

    for x in trap_spaces(primes, "min"):
        x = subspace2str(primes, x)

        states = list_states_in_subspace(primes, x)
        states = [state2str(x) for x in states]

        assert not has_path(stg, example, states)

    bnet = "\n".join(["v1, !v1&v2&v3 | v1&!v2&!v3", "v2, !v1&!v2 | v1&v3", "v3, !v1&v3 | v1&v2", "v4, 1", "v5, v4"])
    primes = bnet2primes(bnet)

    assert not completeness(primes, "asynchronous")

    answer, example = completeness_with_counterexample(primes, "asynchronous")

    assert len(example) == len(primes)
    assert completeness(primes, "synchronous")

    bnet = "\n".join(["v1, !v1&v2&v3 | v1&!v2&!v3", "v2, !v1&!v2 | v1&v3", "v3, v2 | v3"])
    primes = bnet2primes(bnet)

    assert completeness(primes, "asynchronous")
    assert completeness(primes, "synchronous")

    bnet = "\n".join(["v1,   !v2", "v2,   v1", "v3,   v1", "v4,   v2", "v5,   v6", "v6,   v4&v5", "v7,   v2", "v8,   v5", "v9,   v6&v10", "v10,  v9&v7"])
    primes = bnet2primes(bnet)

    assert completeness(primes, "synchronous")


def test_completeness_max_output():
    primes = get_primes("davidich_yeast")

    assert completeness(primes, "asynchronous", max_output=10000)
    assert not completeness(primes, "asynchronous", max_output=2)


def test_compute_json():
    primes = get_primes("n5s3")
    fname_json = os.path.join(FILES_OUT, "n5s3_attrs.json")
    attrs = compute_attractors(primes=primes, update="asynchronous", fname_json=fname_json, max_output=2)

    assert attrs

