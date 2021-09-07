

import pyboolnet.state_space
from pyboolnet.file_exchange import bnet2primes, read_primes
from pyboolnet.repository import get_primes
from pyboolnet.state_space import find_vanham_variables
from pyboolnet.state_space import random_state
from pyboolnet.state_transition_graphs import add_style_tendencies, stg2image, add_style_sccs
from pyboolnet.state_transition_graphs import condensationgraph2image, stg2condensationgraph
from pyboolnet.state_transition_graphs import energy, primes2stg, best_first_reachability, stg2dot
from pyboolnet.state_transition_graphs import htg2image, stg2htg
from pyboolnet.state_transition_graphs import random_successor_mixed, successor_synchronous, successors_mixed
from pyboolnet.state_transition_graphs import random_walk, add_style_path, stg2sccgraph
from pyboolnet.state_transition_graphs import sccgraph2image
from pyboolnet.state_transition_graphs import successors_asynchronous
from tests.helpers import get_tests_path_in, get_tests_path_out


def test_find_vanham_variables():
    primes = get_primes("multivalued")
    result = find_vanham_variables(primes)
    expected = {2: ["input", "x2", "x3", "x6_level2"], 3: ["x1"], 4: ["x4"], 5: ["x5"]}

    assert result == expected


def test_energy():
    primes = get_primes("raf")
    answer = energy(primes, "000")
    expected = 1
    
    assert answer == expected

    answer = energy(primes, "010")
    expected = 3
    
    assert answer == expected

    answer = energy(primes, "001")
    expected = 0
    
    assert answer == expected


def test_random_mixed_transition():
    primes = bnet2primes(bnet=get_tests_path_in(fname="randomnet.bnet"), fname_primes=get_tests_path_out(fname="randomnet.primes"))
    state = dict([("Gene%i" % (i+1), i % 2) for i in range(20)])
    random_successor_mixed(primes, state)


def test_successors_mixed():
    primes = bnet2primes(bnet=get_tests_path_in(fname="randomnet.bnet"), fname_primes=get_tests_path_out(fname="randomnet.primes"))
    state = dict([("Gene%i" % (i + 1), i % 2) for i in range(20)])
    successors_mixed(primes, state)


def test_successors_asynchronous():
    primes = bnet2primes(bnet=get_tests_path_in(fname="randomnet.bnet"), fname_primes=get_tests_path_out(fname="randomnet.primes"))
    state = dict([("Gene%i" % (i+1), i % 2) for i in range(20)])
    successors_asynchronous(primes, state)


def test_successor_synchronous():
    primes = bnet2primes(bnet=get_tests_path_in(fname="randomnet.bnet"), fname_primes=get_tests_path_out(fname="randomnet.primes"))
    state = dict([("Gene%i" % (i+1), i % 2) for i in range(20)])
    successor_synchronous(primes, state)


def test_best_first_reachability():
    primes = bnet2primes(bnet=get_tests_path_in(fname="randomnet.bnet"), fname_primes=get_tests_path_out(fname="randomnet.primes"))
    initial_space = dict([("Gene%i" % (i+1), i % 2) for i in range(20)])
    goal_space = {"Gene2": 0, "Gene4": 0, "Gene6": 0, "Gene8": 0}
    memory = 10000
    path = best_first_reachability(primes, initial_space, goal_space, memory)
    
    assert path is not None


def test_state2str():
    state = {"v2": 0, "v1": 1, "v3": 1}
    answer = pyboolnet.state_space.state2str(state)

    assert answer == "101"


def test_primes2stg():
    primes = read_primes(fname_json=get_tests_path_in(fname="irma.primes"))

    def init(x):
        return x["Cbf1"] + x["Ash1"] + x["Gal80"] == 1

    primes2stg(primes=primes, update="asynchronous")
    primes2stg(primes=primes, update="synchronous")
    primes2stg(primes=primes, update="mixed")
    primes2stg(primes=primes, update="asynchronous", initial_states=init)
    primes2stg(primes=primes, update="synchronous", initial_states=init)
    primes2stg(primes=primes, update="mixed", initial_states=init)

    init = []
    stg = primes2stg(primes=primes, update="synchronous", initial_states=init)
    answer = sorted(stg.nodes())
    expected = []
    
    assert answer == expected

    init = ["000010"]
    stg = primes2stg(primes=primes, update="synchronous", initial_states=init)
    answer = sorted(stg.nodes())

    assert answer == ["000010", "000110"]

    init = [{"Cbf1": 0, "Gal4": 1, "Gal80": 0, "gal": 1, "Swi5": 0, "Ash1": 1}]
    stg = primes2stg(primes=primes, update="synchronous", initial_states=init)
    answer = sorted(stg.nodes())

    assert answer == ["010001", "010011", "100011", "101001"]


def test_stg2dot():
    fname_in = get_tests_path_in(fname="irma.primes")
    fname_out = get_tests_path_out(fname="irma_stg.dot")
    primes = read_primes(fname_json=fname_in)
    stg = primes2stg(primes=primes, update="asynchronous")
    stg2dot(stg, fname_out)


def test_stg2image():
    fname_in = get_tests_path_in(fname="irma.primes")
    fname_out1 = get_tests_path_out(fname="irma_stg_async.pdf")
    fname_out2 = get_tests_path_out(fname="irma_stg_tendencies_async.pdf")
    fname_out3 = get_tests_path_out(fname="irma_stg_sccs_async.pdf")

    primes = read_primes(fname_json=fname_in)
    stg = primes2stg(primes=primes, update="asynchronous")
    stg2image(stg, fname_out1)

    add_style_tendencies(stg)
    stg2image(stg, fname_out2)

    stg = primes2stg(primes=primes, update="asynchronous")
    add_style_sccs(stg)
    stg2image(stg, fname_out3)

    fname_out1 = get_tests_path_out(fname="irma_stg_sync.pdf")
    fname_out2 = get_tests_path_out(fname="irma_stg_tendencies_sync.pdf")
    fname_out3 = get_tests_path_out(fname="irma_stg_sccs_sync.pdf")
    fname_out4 = get_tests_path_out(fname="irma_stg_path.pdf")

    primes = read_primes(fname_json=fname_in)
    stg = primes2stg(primes=primes, update="synchronous")
    stg2image(stg, fname_out1)

    stg = primes2stg(primes=primes, update="asynchronous")
    add_style_tendencies(stg)
    stg2image(stg, fname_out2)

    stg = primes2stg(primes=primes, update="synchronous")
    add_style_sccs(stg)
    stg2image(stg, fname_out3)

    init = random_state(primes=primes)
    walk = random_walk(primes=primes, update="asynchronous", initial_state=init, length=5)
    stg = primes2stg(primes=primes, update="asynchronous")
    add_style_path(stg, walk, "red")
    init = pyboolnet.state_space.random_state(primes=primes)
    walk = random_walk(primes=primes, update="asynchronous", initial_state=init, length=5)
    add_style_path(stg, walk, "blue")
    stg2image(stg, fname_out4)


def test_random_state():
    fname_in = get_tests_path_in(fname="irma.primes")
    primes = read_primes(fname_json=fname_in)
    pyboolnet.state_space.random_state(primes=primes)
    pyboolnet.state_space.random_state(primes=primes, subspace="111-0-")


def test_stg2sccgraph():
    fname_out = get_tests_path_out(fname="raf_sccgraph.pdf")
    primes = get_primes("raf")
    stg = primes2stg(primes, "asynchronous")
    scc_graph = stg2sccgraph(stg)
    sccgraph2image(scc_graph, fname_out)


def test_stg2condensationgraph():
    fname_out = get_tests_path_out(fname="raf_cgraph.pdf")
    primes = get_primes("raf")
    stg = primes2stg(primes, "asynchronous")
    cgraph = stg2condensationgraph(stg)
    condensationgraph2image(cgraph, fname_out)


def test_stg2htg():
    fname_out = get_tests_path_out(fname="raf_htg.pdf")
    primes = get_primes("raf")
    stg = primes2stg(primes, "asynchronous")
    htg = stg2htg(stg)
    htg2image(htg, fname_out)
