#!/usr/bin/env python3
# -*- coding: utf-8 -*-


import PyBoolNet


if __name__=="__main__":

    # basic drawing

    primes = PyBoolNet.Repository.get_primes("xiao_wnt5a")
    PyBoolNet.StateTransitionGraphs.create_image(primes, "asynchronous", "stg.pdf")

    PyBoolNet.StateTransitionGraphs.create_image(primes, "asynchronous", "stg2.pdf", InitialStates={"x4":0, "x5":0}, Styles=["anonymous", "tendencies", "mintrapspaces"])


    # drawing paths

    path = PyBoolNet.StateTransitionGraphs.random_walk(primes, "asynchronous", InitialState="--00---", Length=4)
    stg = PyBoolNet.StateTransitionGraphs.primes2stg(primes, "asynchronous", InitialStates={"x4":0, "x5":0})
    PyBoolNet.StateTransitionGraphs.add_style_path(stg, path, Color="red")
    PyBoolNet.StateTransitionGraphs.add_style_anonymous(stg)
    PyBoolNet.StateTransitionGraphs.stg2image(stg, "stg3.pdf")


    # drawing factor graphs

    primes = PyBoolNet.Repository.get_primes("randomnet_n7k3")
    stg = PyBoolNet.StateTransitionGraphs.primes2stg(primes, "asynchronous")
    scc_graph = PyBoolNet.StateTransitionGraphs.stg2sccgraph(stg)
    PyBoolNet.StateTransitionGraphs.sccgraph2image(scc_graph, "scc_graph.pdf")


    cograph = PyBoolNet.StateTransitionGraphs.stg2condensationgraph(stg)
    PyBoolNet.StateTransitionGraphs.sccgraph2image(cograph, "cograph.pdf")


    htg = PyBoolNet.StateTransitionGraphs.stg2condensationgraph(stg)
    PyBoolNet.StateTransitionGraphs.sccgraph2image(htg, "htg.pdf")


    # best first reachability

    X = "0--1-1-"
    Y = "1--0---"
    path = PyBoolNet.StateTransitionGraphs.best_first_reachability(primes, InitialSpace=X, GoalSpace=Y)
    if path:
        for x in path:
            print(x)



    # energy

    x = "0111010"
    e = PyBoolNet.StateTransitionGraphs.energy(primes, x)
    print(e)






























# end of file
