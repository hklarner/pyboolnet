#!/usr/bin/env python3
# -*- coding: utf-8 -*-


import PyBoolNet


if __name__=="__main__":

    # reading bnet files

    bnet = """
    v1,    !v1
    v2,    1
    v3,    v2 & (!v1 | v3)
    """

    primes = PyBoolNet.file_exchange.bnet2primes(bnet)

    # finding nodes

    const = PyBoolNet.prime_implicants.find_constants(primes)
    print(const)

    # modifying networks

    PyBoolNet.prime_implicants.create_variables(primes, {"v4": "v4 | v2"})
    PyBoolNet.prime_implicants.create_variables(primes, {"v5": lambda v1, v2, v3: v1 + v2 + v3 == 1})

    print(PyBoolNet.file_exchange.primes2bnet(primes))

    # reading from the repository

    primes = PyBoolNet.Repository.get_primes("remy_tumorigenesis")
    print(PyBoolNet.file_exchange.primes2bnet(primes))




































# end of file
