

import pytest

from pyboolnet.repository import get_primes
from pyboolnet.attractors import compute_attractors
from pyboolnet.basins_of_attraction import weak_basin, strong_basin, cycle_free_basin, compute_basins
from pyboolnet.basins_of_attraction import create_basins_of_attraction_barplot, create_basins_piechart
from tests.helpers import get_tests_path_out


@pytest.fixture(scope="session")
def primes():
    return get_primes("n5s3")


@pytest.fixture(scope="session")
def attractors(primes):
    return compute_attractors(primes, update="asynchronous")


def test_weak_basins():
    primes = get_primes("n5s3")
    weak_basin(primes, update="asynchronous")


def test_strong_basins():
    primes = get_primes("n5s3")
    strong_basin(primes, update="asynchronous")


def test_cycle_free_basins():
    primes = get_primes("n5s3")
    cycle_free_basin(primes, update="asynchronous")


def test_compute_basins():
    primes = get_primes("n5s3")
    attractors = compute_attractors(primes, update="asynchronous")
    compute_basins(attractors)


def test_create_basins_of_attraction_barplot():
    primes = get_primes("n5s3")
    attractors = compute_attractors(primes, update="asynchronous")
    fname_image = get_tests_path_out(fname="basins_of_attraction_barplot")
    create_basins_of_attraction_barplot(attractors, fname_image=fname_image)


def test_create_basins_piechart():
    primes = get_primes("n5s3")
    attractors = compute_attractors(primes, update="asynchronous")
    fname_image = get_tests_path_out(fname="basins_piechart")
    create_basins_piechart(attractors, fname_image=fname_image)

