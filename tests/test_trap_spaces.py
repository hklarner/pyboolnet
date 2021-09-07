

from pyboolnet.file_exchange import read_primes, bnet2primes
from pyboolnet.repository import get_primes
from pyboolnet.state_space import subspace2str
from pyboolnet.trap_spaces import percolate_trapspace, trapspaces_that_contain_state
from pyboolnet.trap_spaces import steady_states_projected
from pyboolnet.trap_spaces import trap_spaces, trapspaces_that_intersect_subspace
from pyboolnet.trap_spaces import trapspaces_within_subspace, trap_spaces_bounded
from tests.helpers import get_tests_path_in, get_tests_path_out


def test_percolated_trap_spaces():
    primes = get_primes("arellano_rootstem")
    all_trap_spaces = trap_spaces(primes, "all", max_output=200)
    expected = set(subspace2str(primes, percolate_trapspace(primes, x)) for x in all_trap_spaces)
    answer = set(trap_spaces(primes, "percolated", representation="str"))

    assert len(expected) == len(answer)
    assert expected == answer


def test_percolate_trapspace():
    primes = get_primes("raf")

    assert percolate_trapspace(primes, {"Mek": 0, "Erk": 0}) == {"Raf": 1, "Mek": 0, "Erk": 0}
    assert percolate_trapspace(primes, {}) == {}
    assert percolate_trapspace(primes, {u"Raf": 1, u"Mek": 0, u"Erk": 0}) == {u"Raf": 1, u"Mek": 0, u"Erk": 0}


def test_trapspaces_that_contain_state():
    primes = get_primes("raf")

    assert trapspaces_that_contain_state(primes, {"Raf": 1, "Mek": 0, "Erk": 0}, "min", fname_asp=None) == [{"Raf": 1, "Mek": 0, "Erk": 0}]
    assert trapspaces_that_contain_state(primes, {"Raf": 0, "Mek": 1, "Erk": 1}, "min", fname_asp=None) == [{"Mek": 1, "Erk": 1}]
    assert trapspaces_that_contain_state(primes, {"Raf": 1, "Mek": 1, "Erk": 0}, "min", fname_asp=None) == [{}]


def test_trapspaces_that_contain_state_maxoutput():
    primes = get_primes("raf")
    answer = trapspaces_that_contain_state(primes, {"Raf": 1, "Mek": 0, "Erk": 0}, "all", max_output=1)
    
    assert len(answer) == 1
    assert answer[0] in trapspaces_that_contain_state(primes, {"Raf": 1, "Mek": 0, "Erk": 0}, "all", max_output=1000)


def test_trapspaces_that_intersect_subspace():
    primes = get_primes("raf")

    assert trapspaces_that_intersect_subspace(primes, {"Raf": 1, "Mek": 0, "Erk": 0}, "min") == [{"Raf": 1, "Mek": 0, "Erk": 0}]
    assert trapspaces_that_intersect_subspace(primes, {"Erk": 0}, "min") == [{"Raf": 1, "Mek": 0, "Erk": 0}]
    assert trapspaces_that_intersect_subspace(primes, {"Erk": 0}, "all") == [{}, {'Erk': 0, 'Mek': 0}, {'Erk': 0, 'Mek': 0, 'Raf': 1}]
    assert trapspaces_that_intersect_subspace(primes, {"Erk": 0}, "max") == [{'Erk': 0, 'Mek': 0}]
    assert trapspaces_that_intersect_subspace(primes, {}, "all") == [{}, {'Erk': 1, 'Mek': 1}, {'Erk': 0, 'Mek': 0}, {'Erk': 0, 'Mek': 0, 'Raf': 1}]


def test_trapspaces_within_subspace():
    primes = get_primes("raf")

    assert trapspaces_that_intersect_subspace(primes, {"Raf": 0}, "all") == [{}, {'Erk': 1, 'Mek': 1}, {'Erk': 0, 'Mek': 0}]
    assert trapspaces_within_subspace(primes, {"Raf": 0}, "all") == []
    assert trapspaces_within_subspace(primes, {"Raf": 1}, "all") == [{'Erk': 0, 'Mek': 0, 'Raf': 1}]


def test_trap_spaces_piped1():
    fname_in = get_tests_path_in(fname="trapspaces_posfeedback.primes")
    primes = read_primes(fname_json=fname_in)
    tspaces = trap_spaces(primes=primes, option="min")
    tspaces.sort(key=lambda x: tuple(sorted(x.items())))
    expected = [{"v1": 0, "v2": 0, "v3": 0}, {"v1": 1, "v2": 1, "v3": 1}]

    assert tspaces == expected


def test_trap_spaces_piped2():
    fname_in = get_tests_path_in(fname="trapspaces_tsfree.primes")
    primes = read_primes(fname_json=fname_in)
    tspaces = trap_spaces(primes=primes, option="min")
    tspaces.sort(key=lambda x: tuple(sorted(x.items())))

    assert tspaces == [{}]


def test_trap_spaces_tsfree():
    fname_in = get_tests_path_in(fname="trapspaces_tsfree.primes")
    fname_out = get_tests_path_out(fname="trapspaces_tsfree_min.asp")
    primes = read_primes(fname_json=fname_in)
    tspaces = trap_spaces(primes=primes, option="min", fname_asp=fname_out)

    assert tspaces == [{}]

    fname_in = get_tests_path_in(fname="trapspaces_tsfree.primes")
    fname_out = get_tests_path_out(fname="trapspaces_tsfree_all.asp")
    primes = read_primes(fname_json=fname_in)
    tspaces = trap_spaces(primes=primes, option="all", fname_asp=fname_out)

    assert tspaces == [{}]

    fname_in = get_tests_path_in(fname="trapspaces_tsfree.primes")
    fname_out = get_tests_path_out(fname="trapspaces_tsfree_max.asp")
    primes = read_primes(fname_json=fname_in)
    tspaces = trap_spaces(primes=primes, option="max", fname_asp=fname_out)

    assert tspaces == []


def test_trap_spaces_positive_feedback_min():
    fname_in = get_tests_path_in(fname="trapspaces_posfeedback.primes")
    fname_out = get_tests_path_out(fname="trapspaces_posfeedback_min.asp")
    primes = read_primes(fname_json=fname_in)
    tspaces = trap_spaces(primes=primes, option="min", fname_asp=fname_out)
    tspaces.sort(key=lambda x: tuple(sorted(x.items())))
    expected = [{"v1": 0, "v2": 0, "v3": 0}, {"v1": 1, "v2": 1, "v3": 1}]

    assert tspaces == expected


def test_trap_spaces_positive_feedback_max():
    fname_in = get_tests_path_in(fname="trapspaces_posfeedback.primes")
    fname_out = get_tests_path_out(fname="trapspaces_posfeedback_max.asp")
    primes = read_primes(fname_json=fname_in)
    tspaces = trap_spaces(primes=primes, option="max", fname_asp=fname_out)
    tspaces.sort(key=lambda x: tuple(sorted(x.items())))
    expected = [{"v1": 0, "v2": 0, "v3": 0}, {"v1": 1, "v2": 1, "v3": 1}]

    assert tspaces == expected


def test_trap_spaces_positive_feedback_all():
    fname_in = get_tests_path_in(fname="trapspaces_posfeedback.primes")
    fname_out = get_tests_path_out(fname="trapspaces_posfeedback_all.asp")
    primes = read_primes(fname_json=fname_in)
    tspaces = trap_spaces(primes=primes, option="all", fname_asp=fname_out)
    tspaces.sort(key=lambda x: tuple(sorted(x.items())))

    assert tspaces == [{}, {"v1": 0, "v2": 0, "v3": 0}, {"v1": 1, "v2": 1, "v3": 1}]


def test_trap_spaces_positive_feedback_bounds1():
    fname_in = get_tests_path_in(fname="trapspaces_posfeedback.primes")
    fname_out = get_tests_path_out(fname="trapspaces_posfeedback_bounds1.asp")
    primes = read_primes(fname_json=fname_in)
    tspaces = trap_spaces_bounded(primes=primes, type_="all", bounds=(1, 2), fname_asp=fname_out)
    tspaces.sort(key=lambda x: tuple(sorted(x.items())))

    assert tspaces == []


def test_trap_spaces_positive_feedback_bounds2():
    fname_in = get_tests_path_in(fname="trapspaces_posfeedback.primes")
    fname_out = get_tests_path_out(fname="trapspaces_posfeedback_bounds2.asp")
    primes = read_primes(fname_json=fname_in)
    tspaces = trap_spaces_bounded(primes=primes, type_="max", bounds=(0, 100), fname_asp=fname_out)
    tspaces.sort(key=lambda x: tuple(sorted(x.items())))

    assert tspaces == [{}]


def test_trap_spaces_bounded():
    fname_in = get_tests_path_in(fname="trapspaces_bounded.bnet")
    fname_out = get_tests_path_out(fname="trapspaces_bounded.primes")
    primes = bnet2primes(fname_in, fname_out)
    tspaces_all = trap_spaces(primes, "all")
    tspaces_all.sort(key=lambda x: tuple(sorted(x.items())))
    expected = [{},
                {"v3": 1},
                {"v3": 0},
                {"v1": 1},
                {"v1": 1, "v2": 1},
                {"v1": 0, "v2": 0},
                {"v3": 1, "v4": 1},
                {"v1": 1, "v3": 0},
                {"v1": 1, "v3": 1},
                {"v1": 1, "v2": 1, "v3": 1},
                {"v1": 1, "v3": 1, "v4": 1},
                {"v1": 1, "v2": 1, "v3": 0},
                {"v1": 0, "v2": 0, "v3": 0},
                {"v1": 0, "v2": 0, "v3": 1},
                {"v1": 1, "v2": 1, "v4": 1},
                {"v1": 0, "v2": 0, "v3": 1, "v4": 1},
                {"v1": 1, "v2": 1, "v3": 0, "v4": 1},
                {"v1": 1, "v2": 1, "v3": 1, "v4": 1},
                {"v1": 0, "v2": 0, "v3": 0, "v4": 0}]

    expected.sort(key=lambda x: tuple(sorted(x.items())))
    
    assert tspaces_all == expected

    tspaces_min = trap_spaces(primes, "min")
    tspaces_min.sort(key=lambda x: tuple(sorted(x.items())))
    expected = [
        {"v1": 0, "v2": 0, "v3": 0, "v4": 0},
        {"v1": 1, "v2": 1, "v3": 1, "v4": 1},
        {"v1": 0, "v2": 0, "v3": 1, "v4": 1},
        {"v1": 1, "v2": 1, "v3": 0, "v4": 1}]

    expected.sort(key=lambda x: tuple(sorted(x.items())))
    
    assert tspaces_min == expected

    tspaces_max = trap_spaces(primes, "max")
    tspaces_max.sort(key=lambda x: tuple(sorted(x.items())))
    expected = [{"v3": 1}, {"v3": 0}, {"v1": 1}, {"v1": 0, "v2": 0}]
    expected.sort(key=lambda x: tuple(sorted(x.items())))

    assert tspaces_max == expected

    tspaces_bounded = trap_spaces_bounded(primes, "max", bounds=(1, 1))
    tspaces_bounded.sort(key=lambda x: tuple(sorted(x.items())))
    expected = [{"v3": 1}, {"v3": 0}, {"v1": 1}]
    expected.sort(key=lambda x: tuple(sorted(x.items())))

    assert tspaces_bounded == expected

    tspaces_bounded = trap_spaces_bounded(primes, "max", bounds=(2, 3))
    tspaces_bounded.sort(key=lambda x: tuple(sorted(x.items())))
    expected = [{"v1": 1, "v2": 1},
                {"v1": 0, "v2": 0},
                {"v3": 1, "v4": 1},
                {"v1": 1, "v3": 0},
                {"v1": 1, "v3": 1}]

    expected.sort(key=lambda x: tuple(sorted(x.items())))

    assert tspaces_bounded == expected

    tspaces_bounded = trap_spaces_bounded(primes, "all", bounds=(2, 3))
    tspaces_bounded.sort(key=lambda x: tuple(sorted(x.items())))
    expected = [
        {"v1": 1, "v2": 1},
        {"v1": 0, "v2": 0},
        {"v3": 1, "v4": 1},
        {"v1": 1, "v3": 0},
        {"v1": 1, "v3": 1},
        {"v1": 1, "v2": 1, "v3": 1},
        {"v1": 1, "v3": 1, "v4": 1},
        {"v1": 1, "v2": 1, "v3": 0},
        {"v1": 0, "v2": 0, "v3": 0},
        {"v1": 0, "v2": 0, "v3": 1},
        {"v1": 1, "v2": 1, "v4": 1}]

    expected.sort(key=lambda x: tuple(sorted(x.items())))

    assert tspaces_bounded == expected

    tspaces_bounded = trap_spaces_bounded(primes, "min", bounds=(2, 3))
    tspaces_bounded.sort(key=lambda x: tuple(sorted(x.items())))
    expected = [
        {"v1": 1, "v2": 1, "v3": 1},
        {"v1": 1, "v3": 1, "v4": 1},
        {"v1": 1, "v2": 1, "v3": 0},
        {"v1": 0, "v2": 0, "v3": 0},
        {"v1": 0, "v2": 0, "v3": 1},
        {"v1": 1, "v2": 1, "v4": 1}]

    expected.sort(key=lambda x: tuple(sorted(x.items())))

    assert tspaces_bounded == expected


def test_steady_states_projected():
    bnet = "\n".join(["x, !x&!y | x&y", "y, y", "z, z"])
    primes = bnet2primes(bnet)

    result = steady_states_projected(primes, ["y", "x"])
    result.sort(key=lambda x: tuple(sorted(x.items())))

    assert result == [{"x": 0, "y": 1}, {"x": 1, "y": 1}]


def test_encoding_bijection():
    """
    The mapping from stable and consistent prime implicant sets to trap spaces is surjective but not injective.
    Two different arc sets may lead to the same trap space.
    In the following example there are four trap stable+consistent arc sets but only two trap spaces.
    """

    bnet = "\n".join(["v1,v1|v2", "v2,v1"])
    primes = bnet2primes(bnet)

    result = trap_spaces(primes, "all")
    result.sort(key=lambda x: tuple(sorted(x.items())))

    assert result == [{}, {"v1": 0, "v2": 0}, {"v1": 1}, {"v1": 1, "v2": 1}]

    result = trap_spaces(primes, "min")
    result.sort(key=lambda x: tuple(sorted(x.items())))

    assert result == [{"v1": 0, "v2": 0}, {"v1": 1, "v2": 1}]

    result = trap_spaces(primes, "max")
    result.sort(key=lambda x: tuple(sorted(x.items())))

    assert result == [{"v1": 0, "v2": 0}, {"v1": 1}]