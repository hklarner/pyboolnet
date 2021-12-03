

from pyboolnet.repository import get_primes
from pyboolnet.trap_spaces import compute_trap_spaces, compute_steady_states


if __name__ == "__main__":
    # compute minimal and maximal trap spaces

    primes = get_primes("remy_tumorigenesis")
    mints = compute_trap_spaces(primes, "min")
    print(len(mints))

    max_trap_spaces = compute_trap_spaces(primes, "max")
    print(len(max_trap_spaces))
    print(max_trap_spaces)

    # compute steady states using the ASP solver

    steady = compute_steady_states(primes)
    print(len(steady))
    

