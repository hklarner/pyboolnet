#!/usr/bin/env python3
# -*- coding: utf-8 -*-


import PyBoolNet


if __name__=="__main__":

    # basic model checking

    primes = PyBoolNet.Repository.get_primes("remy_tumorigenesis")
    init = "INIT TRUE"
    spec = "CTLSPEC DNA_damage -> AG(EF(Apoptosis_medium))"

    #tournier_apoptosis
    answer = PyBoolNet.ModelChecking.check_primes(primes, "asynchronous", init, spec)
    print(answer)


    # model checking with accepting states

    answer, accepting = PyBoolNet.ModelChecking.check_primes_with_acceptingstates(primes, "asynchronous", init, spec)
    for key, value in accepting.items():
        print("{} = {}".format(key, value))


    # model checking with counter examples

    spec = "CTLSPEC DNA_damage -> AG(EF(Proliferation))"
    answer, counterex = PyBoolNet.ModelChecking.check_primes_with_counterexample(primes, "asynchronous", init, spec)
    print(answer)
    if counterex:
        for state in counterex:
            print(state)

        path = PyBoolNet.StateTransitionGraphs.best_first_reachability(primes, InitialSpace=state, GoalSpace={"Proliferation":1})
        






























# end of file
