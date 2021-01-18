

import os

import PyBoolNet


FILES_IN = os.path.join(os.path.dirname(__file__), "files_input")
FILES_OUT = os.path.join(os.path.dirname(__file__), "files_output")


def test_find_vanham_variables():
    primes = PyBoolNet.Repository.get_primes("multivalued")
    result = PyBoolNet.StateTransitionGraphs.find_vanham_variables(primes)
    expected = {2: ["input", "x2", "x3", "x6_level2"], 3: ["x1"], 4: ["x4"], 5: ["x5"]}

    assert result == expected


def test_size_state_space():
    primes = PyBoolNet.Repository.get_primes("multivalued")
    result = PyBoolNet.StateTransitionGraphs.size_state_space(primes, VanHam=False, FixedInputs=False)
    expected = 2**13
    
    assert result == expected

    result = PyBoolNet.StateTransitionGraphs.size_state_space(primes, VanHam=False, FixedInputs=True)
    expected = 2**12
    
    assert result == expected

    result = PyBoolNet.StateTransitionGraphs.size_state_space(primes, VanHam=True, FixedInputs=False)
    expected = 2**4*3*4*5
    
    assert result == expected

    result = PyBoolNet.StateTransitionGraphs.size_state_space(primes, VanHam=True, FixedInputs=True)
    expected = 2**3*3*4*5
    
    assert result == expected


def test_energy():
    primes = PyBoolNet.Repository.get_primes("raf")

    answer = PyBoolNet.StateTransitionGraphs.energy(primes, "000")
    expected = 1
    
    assert answer == expected

    answer = PyBoolNet.StateTransitionGraphs.energy(primes, "010")
    expected = 3
    
    assert answer == expected

    answer = PyBoolNet.StateTransitionGraphs.energy(primes, "001")
    expected = 0
    
    assert answer == expected


def test_state_is_in_subspace():
    primes = ["a", "b", "c"]
    answer = PyBoolNet.StateTransitionGraphs.state_is_in_subspace(primes, {"a": 1, "b": 1, "c": 0}, {"a": 1})
    assert answer

    answer = PyBoolNet.StateTransitionGraphs.state_is_in_subspace(primes, "110", "1--")
    assert answer

    answer = PyBoolNet.StateTransitionGraphs.state_is_in_subspace(primes, {"a": 1, "b": 1, "c": 0}, {"a": 0})
    assert not answer

    answer = PyBoolNet.StateTransitionGraphs.state_is_in_subspace(primes, "110", "0--")
    assert not answer


def test_a_is_subspace_of_b():

    primes = ["a", "b", "c", "d"]
    answer = PyBoolNet.StateTransitionGraphs.A_is_subspace_of_B(primes, {"a": 1, "b": 1, "c": 0}, {"a": 1})
    assert answer

    answer = PyBoolNet.StateTransitionGraphs.A_is_subspace_of_B(primes, "110-", "1---")
    assert answer

    answer = PyBoolNet.StateTransitionGraphs.A_is_subspace_of_B(primes, {"a": 1, "b": 1, "c": 0}, {"a": 0})
    assert not answer

    answer = PyBoolNet.StateTransitionGraphs.A_is_subspace_of_B(primes, "110-", "0---")
    assert not answer


def test_enumerate_states():
    primes = PyBoolNet.Repository.get_primes("raf")
    prop = "!Erk | (Raf & Mek)"
    expected = {"010", "011", "001", "000", "111"}
    answer = set(PyBoolNet.StateTransitionGraphs.enumerate_states(primes, prop))
    
    assert answer == expected

    prop = "0"
    expected = set([])
    answer = set(PyBoolNet.StateTransitionGraphs.enumerate_states(primes, prop))
    
    assert answer == expected

    prop = "TRUE"
    expected = {"010", "011", "001", "000", "111", "110", "101", "100"}
    answer = set(PyBoolNet.StateTransitionGraphs.enumerate_states(primes, prop))
    
    assert answer == expected


def test_random_mixed_transition():
    fname_in = os.path.join(FILES_IN, "randomnet.bnet")
    fname_out = os.path.join(FILES_OUT, "randomnet.primes")
    primes = PyBoolNet.FileExchange.bnet2primes(BNET=fname_in, FnamePRIMES=fname_out)

    state = dict([("Gene%i" % (i+1), i % 2) for i in range(20)])
    PyBoolNet.StateTransitionGraphs.random_successor_mixed(primes, state)


def test_successors_mixed():
    fname_in = os.path.join(FILES_IN, "randomnet.bnet")
    fname_out = os.path.join(FILES_OUT, "randomnet.primes")
    primes = PyBoolNet.FileExchange.bnet2primes(BNET=fname_in, FnamePRIMES=fname_out)

    state = dict([("Gene%i" % (i + 1), i % 2) for i in range(20)])
    PyBoolNet.StateTransitionGraphs.successors_mixed(primes, state)


def test_successors_asynchronous():
    fname_in = os.path.join(FILES_IN, "randomnet.bnet")
    fname_out = os.path.join(FILES_OUT, "randomnet.primes")
    primes = PyBoolNet.FileExchange.bnet2primes(BNET=fname_in, FnamePRIMES=fname_out)

    state = dict([("Gene%i" % (i+1), i % 2) for i in range(20)])
    PyBoolNet.StateTransitionGraphs.successors_asynchronous(primes, state)


def test_successor_synchronous():
    fname_in = os.path.join(FILES_IN, "randomnet.bnet")
    fname_out = os.path.join(FILES_OUT, "randomnet.primes")
    primes = PyBoolNet.FileExchange.bnet2primes(BNET=fname_in, FnamePRIMES=fname_out)

    state = dict([("Gene%i" % (i+1), i % 2) for i in range(20)])
    PyBoolNet.StateTransitionGraphs.successor_synchronous(primes, state)


def test_best_first_reachability():
    fname_in = os.path.join(FILES_IN, "randomnet.bnet")
    fname_out = os.path.join(FILES_OUT, "randomnet.primes")
    primes = PyBoolNet.FileExchange.bnet2primes(BNET=fname_in, FnamePRIMES=fname_out)

    initial_space = dict([("Gene%i" % (i+1), i % 2) for i in range(20)])
    goal_space = {"Gene2": 0, "Gene4": 0, "Gene6": 0, "Gene8": 0}
    memory = 10000
    path = PyBoolNet.StateTransitionGraphs.best_first_reachability(primes, initial_space, goal_space, memory)
    
    assert path is not None


def test_state2str():
    state = {"v2": 0, "v1": 1, "v3": 1}
    answer = PyBoolNet.StateTransitionGraphs.state2str(state)

    assert answer == "101"


def test_primes2stg():
    fname_in = os.path.join(FILES_IN, "irma.primes")

    primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)

    def init(x):
        return x["Cbf1"] + x["Ash1"] + x["Gal80"] == 1

    PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="asynchronous")
    PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="synchronous")
    PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="mixed")
    PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="asynchronous", InitialStates=init)
    PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="synchronous", InitialStates=init)
    PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="mixed", InitialStates=init)

    init = []
    stg = PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="synchronous", InitialStates=init)
    answer = sorted(stg.nodes())
    expected = []
    
    assert answer == expected

    init = ["000010"]
    stg = PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="synchronous", InitialStates=init)
    answer = sorted(stg.nodes())

    assert answer == ["000010", "000110"]

    init = [{"Cbf1": 0, "Gal4": 1, "Gal80": 0, "gal": 1, "Swi5": 0, "Ash1": 1}]
    stg = PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="synchronous", InitialStates=init)
    answer = sorted(stg.nodes())

    assert answer == ["010001", "010011", "100011", "101001"]


def test_stg2dot():
    fname_in = os.path.join(FILES_IN, "irma.primes")
    fname_out = os.path.join(FILES_OUT, "irma_stg.dot")

    primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)
    stg = PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="asynchronous")
    PyBoolNet.StateTransitionGraphs.stg2dot(stg, fname_out)


def test_stg2image():
    fname_in = os.path.join(FILES_IN, "irma.primes")
    fname_out1 = os.path.join(FILES_OUT, "irma_stg_async.pdf")
    fname_out2 = os.path.join(FILES_OUT, "irma_stg_tendencies_async.pdf")
    fname_out3 = os.path.join(FILES_OUT, "irma_stg_sccs_async.pdf")

    primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)
    stg = PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="asynchronous")
    PyBoolNet.StateTransitionGraphs.stg2image(stg, fname_out1)

    PyBoolNet.StateTransitionGraphs.add_style_tendencies(stg)
    PyBoolNet.StateTransitionGraphs.stg2image(stg, fname_out2)

    stg = PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="asynchronous")
    PyBoolNet.StateTransitionGraphs.add_style_sccs(stg)
    PyBoolNet.StateTransitionGraphs.stg2image(stg, fname_out3)

    fname_out1 = os.path.join(FILES_OUT, "irma_stg_sync.pdf")
    fname_out2 = os.path.join(FILES_OUT, "irma_stg_tendencies_sync.pdf")
    fname_out3 = os.path.join(FILES_OUT, "irma_stg_sccs_sync.pdf")
    fname_out4 = os.path.join(FILES_OUT, "irma_stg_path.pdf")

    primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)
    stg = PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="synchronous")
    PyBoolNet.StateTransitionGraphs.stg2image(stg, fname_out1)

    stg = PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="asynchronous")
    PyBoolNet.StateTransitionGraphs.add_style_tendencies(stg)
    PyBoolNet.StateTransitionGraphs.stg2image(stg, fname_out2)

    stg = PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="synchronous")
    PyBoolNet.StateTransitionGraphs.add_style_sccs(stg)
    PyBoolNet.StateTransitionGraphs.stg2image(stg, fname_out3)

    init = PyBoolNet.StateTransitionGraphs.random_state(primes=primes)
    walk = PyBoolNet.StateTransitionGraphs.random_walk(Primes=primes, Update="asynchronous", InitialState=init, Length=5)
    stg = PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="asynchronous")
    PyBoolNet.StateTransitionGraphs.add_style_path(stg, walk, "red")
    init = PyBoolNet.StateTransitionGraphs.random_state(primes=primes)
    walk = PyBoolNet.StateTransitionGraphs.random_walk(Primes=primes, Update="asynchronous", InitialState=init, Length=5)
    PyBoolNet.StateTransitionGraphs.add_style_path(stg, walk, "blue")
    PyBoolNet.StateTransitionGraphs.stg2image(stg, fname_out4)


def test_random_state():
    fname_in = os.path.join(FILES_IN, "irma.primes")
    primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)
    PyBoolNet.StateTransitionGraphs.random_state(primes=primes)
    PyBoolNet.StateTransitionGraphs.random_state(primes=primes, subspace="111-0-")


def test_stg2sccgraph():
    fname_out = os.path.join(FILES_OUT, "raf_sccgraph.pdf")
    primes = PyBoolNet.Repository.get_primes("raf")
    stg = PyBoolNet.StateTransitionGraphs.primes2stg(primes, "asynchronous")
    sccg = PyBoolNet.StateTransitionGraphs.stg2sccgraph(stg)
    PyBoolNet.StateTransitionGraphs.sccgraph2image(sccg, fname_out)


def test_stg2condensationgraph():
    fname_out = os.path.join(FILES_OUT, "raf_cgraph.pdf")
    primes = PyBoolNet.Repository.get_primes("raf")
    stg = PyBoolNet.StateTransitionGraphs.primes2stg(primes, "asynchronous")
    cgraph = PyBoolNet.StateTransitionGraphs.stg2condensationgraph(stg)
    PyBoolNet.StateTransitionGraphs.condensationgraph2image(cgraph, fname_out)


def test_stg2htg():
    fname_out = os.path.join(FILES_OUT, "raf_htg.pdf")
    primes = PyBoolNet.Repository.get_primes("raf")
    stg = PyBoolNet.StateTransitionGraphs.primes2stg(primes, "asynchronous")
    htg = PyBoolNet.StateTransitionGraphs.stg2htg(stg)
    PyBoolNet.StateTransitionGraphs.htg2image(htg, fname_out)
