#!/usr/bin/env python3
# -*- coding: utf-8 -*-


import PyBoolNet


if __name__=="__main__":


    # compute minimal and maximal trap spaces

    primes = PyBoolNet.Repository.get_primes("remy_tumorigenesis")
    mints = PyBoolNet.AspSolver.trap_spaces(primes, "min")
    print(len(mints))

    maxts = PyBoolNet.AspSolver.trap_spaces(primes, "max")
    print(len(maxts))
    print(maxts)


    # compute steady states using the ASP solver

    steady = PyBoolNet.AspSolver.steady_states(primes)
    print(len(steady))
    






























# end of file
