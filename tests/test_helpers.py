

from pyboolnet.helpers import dicts_are_consistent


def test_dicts_are_consistent():
    x = {1: 2}
    y = {}
    are_consistent = dicts_are_consistent(x, y)

    assert are_consistent

    x = {1: 2, 2: 3}
    y = {2: 3, 3: 4}
    are_consistent = dicts_are_consistent(x, y)

    assert are_consistent

    x = {1: 2}
    y = {1: 3}
    are_consistent = dicts_are_consistent(x, y)

    assert not are_consistent
