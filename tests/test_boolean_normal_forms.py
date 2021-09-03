

from pyboolnet.boolean_normal_forms import primes2mindnf, functions2primes, functions2mindnf
from pyboolnet.repository import get_primes


def test_primes2mindnf():
    primes = get_primes("raf")
    primes2mindnf(primes)


def test_functions2primes():
    functions = {"x": lambda x, y: x or y, "y": lambda x, z: not x and z, "z": lambda x, y, z: sum([x, y, z]) == 1}
    functions2primes(functions)


def test_functions2mindnf():
    functions = {"x": lambda x, y: x or y, "y": lambda x, z: not x and z, "z": lambda x, y, z: sum([x, y, z]) == 1}
    functions2mindnf(functions)



