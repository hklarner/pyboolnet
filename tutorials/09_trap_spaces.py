

from pyboolnet.repository import get_primes
from pyboolnet.trap_spaces import trap_spaces, steady_states


if __name__ == "__main__":
    # compute minimal and maximal trap spaces

    primes = get_primes("remy_tumorigenesis")
    mints = trap_spaces(primes, "min")
    print(len(mints))

    max_trap_spaces = trap_spaces(primes, "max")
    print(len(max_trap_spaces))
    print(max_trap_spaces)

    # compute steady states using the ASP solver

    steady = steady_states(primes)
    print(len(steady))
    

