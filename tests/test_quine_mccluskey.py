

import PyBoolNet


def test_functions2mindnf():
    functions = {"v1": lambda v1, v2: v1 or not v2, "v2": lambda v1: not v1, "v3": lambda: False, "v4": lambda v3: v3 or not v3}

    assert PyBoolNet.QuineMcCluskey.functions2mindnf(functions) == {"v1": "!v2 | v1", "v2": "!v1", "v3": "0", "v4": "1"}


def test_primes2mindnf():
    primes = {"A": [[{}], []], "B": [[], [{}]], "C": [[{"A": 1}, {"B": 0}], [{"A": 0, "B": 1}]]}

    assert PyBoolNet.QuineMcCluskey.primes2mindnf(primes) == {"A": "0", "C": "B&!A", "B": "1"}
