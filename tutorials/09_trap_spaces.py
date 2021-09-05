

if __name__=="__main__":


    # compute minimal and maximal trap spaces

    primes = get_primes("remy_tumorigenesis")
    mints = trap_spaces(primes, "min")
    print(len(mints))

    maxts = trap_spaces(primes, "max")
    print(len(maxts))
    print(maxts)


    # compute steady states using the ASP solver

    steady = PyBoolNet.trap_spaces.steady_states(primes)
    print(len(steady))
    






























# end of file
