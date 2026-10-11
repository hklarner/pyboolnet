

from pyboolnet.repository import get_primes
from pyboolnet.state_space import is_subspace, enumerate_states
from pyboolnet.state_space import size_state_space, state_is_in_subspace
from pyboolnet.state_space import state2str, random_state
from pyboolnet.state_space import find_vanham_variables, bounding_box

import itertools
import pytest


@pytest.mark.parametrize("subspaces, expected", [
    ([{"a": 0}, {"b": 1}], {}),
    ([{"a": 0, "b": 1}, {"a": 0}], {"a": 0}),
    ([{"a": 0}, {"a": 0, "b": 1}], {"a": 0}),
    ([{}, {"a": 0}], {}),
    ([{"a": 0}, {}], {}),
    (["0-", "-1"], {}),
    (["01", {"a": 0}], {"a": 0}),
    (["01", "11"], {"b": 1}),
    (["01"], {"a": 0, "b": 1}),
    ([], {}),
])
def test_bounding_box_of_subspaces(subspaces, expected):
    primes = {"a": None, "b": None}
    assert bounding_box(primes, subspaces) == expected


def test_bounding_box_matches_enumerated_union():
    names = ["a", "b", "c"]
    primes = dict.fromkeys(names)
    states = [dict(zip(names, values)) for values in itertools.product([0, 1], repeat=3)]
    subspaces = [dict((name, value) for name, value in zip(names, values) if value is not None)
                 for values in itertools.product([None, 0, 1], repeat=3)]
    for first, second in itertools.product(subspaces, repeat=2):
        union = [state for state in states
                 if state_is_in_subspace(primes, state, first)
                 or state_is_in_subspace(primes, state, second)]
        expected = dict((name, union[0][name]) for name in names
                        if all(state[name] == union[0][name] for state in union))
        assert bounding_box(primes, [first, second]) == expected


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
    assert type(random_state(primes=primes)) is dict
    assert type(random_state(primes=primes, subspace="111-0-")) is dict

