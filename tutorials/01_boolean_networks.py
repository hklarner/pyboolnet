

from pyboolnet.file_exchange import bnet2primes, primes2bnet
from pyboolnet.prime_implicants import find_constants, create_variables
from pyboolnet.repository import get_primes


if __name__ == "__main__":
    bnet = """
    v1,    !v1
    v2,    1
    v3,    v2 & (!v1 | v3)
    """

    primes = bnet2primes(bnet)

    # finding nodes

    const = find_constants(primes)
    print(const)

    # modifying networks

    create_variables(primes, {"v4": "v4 | v2"})
    create_variables(primes, {"v5": lambda v1, v2, v3: v1 + v2 + v3 == 1})

    print(primes2bnet(primes))

    # reading from the repository

    primes = get_primes("remy_tumorigenesis")
    print(primes2bnet(primes))




































# end of file
