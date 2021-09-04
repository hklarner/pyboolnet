

import os

from pyboolnet.state_space import is_subspace, enumerate_states
from pyboolnet.state_space import size_state_space, state_is_in_subspace
from pyboolnet.state_transition_graphs import find_vanham_variables, random_successor_mixed
from pyboolnet.state_space import state2str, random_state
from pyboolnet.repository import get_primes

from tests.helpers import get_tests_path_in, get_tests_path_out


def test_find_vanham_variables():
    primes = get_primes("multivalued")
    result = find_vanham_variables(primes)
    expected = {2: ["input", "x2", "x3", "x6_level2"], 3: ["x1"], 4: ["x4"], 5: ["x5"]}

    assert result == expected


def test_size_state_space():
    primes = get_primes("multivalued")
    result = size_state_space(primes, van_ham=False, fixed_inputs=False)
    expected = 2**13
    
    assert result == expected

    result = size_state_space(primes, van_ham=False, fixed_inputs=True)
    expected = 2**12
    
    assert result == expected

    result = size_state_space(primes, van_ham=True, fixed_inputs=False)
    expected = 2**4*3*4*5
    
    assert result == expected

    result = size_state_space(primes, van_ham=True, fixed_inputs=True)
    expected = 2**3*3*4*5
    
    assert result == expected


def test_state_is_in_subspace():
    primes = {"a": None, "b": None, "c": None}
    answer = state_is_in_subspace(primes, {"a": 1, "b": 1, "c": 0}, {"a": 1})
    assert answer

    answer = state_is_in_subspace(primes, "110", "1--")
    assert answer

    answer = state_is_in_subspace(primes, {"a": 1, "b": 1, "c": 0}, {"a": 0})
    assert not answer

    answer = state_is_in_subspace(primes, "110", "0--")
    assert not answer


def test_is_subspace():
    primes = {"a": None, "b": None, "c": None, "d": None}
    answer = is_subspace(primes, {"a": 1, "b": 1, "c": 0}, {"a": 1})
    assert answer

    answer = is_subspace(primes, "110-", "1---")
    assert answer

    answer = is_subspace(primes, {"a": 1, "b": 1, "c": 0}, {"a": 0})
    assert not answer

    answer = is_subspace(primes, "110-", "0---")
    assert not answer


def test_enumerate_states():
    primes = get_primes("raf")
    prop = "!Erk | (Raf & Mek)"
    expected = {"010", "011", "001", "000", "111"}
    answer = set(enumerate_states(primes, prop))
    
    assert answer == expected

    prop = "0"
    expected = set([])
    answer = set(enumerate_states(primes, prop))
    
    assert answer == expected

    prop = "TRUE"
    expected = {"010", "011", "001", "000", "111", "110", "101", "100"}
    answer = set(enumerate_states(primes, prop))
    
    assert answer == expected


def test_state2str():
    state = {"v2": 0, "v1": 1, "v3": 1}
    answer = state2str(state)

    assert answer == "101"


def test_random_state():
    primes = get_primes(name="n6s1c2")
    random_state(primes=primes)
    random_state(primes=primes, subspace="111-0-")

