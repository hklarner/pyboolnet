

import PyBoolNet


def test_dicts_are_consistent():
    x = {1: 2}
    y = {}
    answer = PyBoolNet.Utility.Misc.dicts_are_consistent(x, y)

    assert answer

    x = {1: 2, 2: 3}
    y = {2: 3, 3: 4}
    answer = PyBoolNet.Utility.Misc.dicts_are_consistent(x, y)

    assert answer

    x = {1: 2}
    y = {1: 3}
    answer = PyBoolNet.Utility.Misc.dicts_are_consistent(x, y)

    assert not answer