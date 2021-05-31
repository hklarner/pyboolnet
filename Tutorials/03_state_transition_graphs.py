#!/usr/bin/env python3
# -*- coding: utf-8 -*-


import PyBoolNet


if __name__=="__main__":

    # basic drawing

    primes = PyBoolNet.Repository.get_primes("xiao_wnt5a")
    PyBoolNet.state_transition_graphs.create_image(primes, "asynchronous", "stg.pdf")

    PyBoolNet.state_transition_graphs.create_image(primes, "asynchronous", "stg2.pdf", InitialStates={"x4":0, "x5":0}, Styles=["anonymous", "tendencies", "mintrapspaces"])


    # drawing paths

    path = PyBoolNet.state_transition_graphs.random_walk(primes, "asynchronous", InitialState="--00---", Length=4)
    stg = PyBoolNet.state_transition_graphs.primes2stg(primes, "asynchronous", InitialStates={"x4":0, "x5":0})
    PyBoolNet.state_transition_graphs.add_style_path(stg, path, Color="red")
    PyBoolNet.state_transition_graphs.add_style_anonymous(stg)
    PyBoolNet.state_transition_graphs.stg2image(stg, "stg3.pdf")


    # drawing factor graphs

    primes = PyBoolNet.Repository.get_primes("randomnet_n7k3")
    stg = PyBoolNet.state_transition_graphs.primes2stg(primes, "asynchronous")
    scc_graph = PyBoolNet.state_transition_graphs.stg2sccgraph(stg)
    PyBoolNet.state_transition_graphs.sccgraph2image(scc_graph, "scc_graph.pdf")


    cograph = PyBoolNet.state_transition_graphs.stg2condensationgraph(stg)
    PyBoolNet.state_transition_graphs.sccgraph2image(cograph, "cograph.pdf")


    htg = PyBoolNet.state_transition_graphs.stg2condensationgraph(stg)
    PyBoolNet.state_transition_graphs.sccgraph2image(htg, "htg.pdf")


    # best first reachability

    X = "0--1-1-"
    Y = "1--0---"
    path = PyBoolNet.state_transition_graphs.best_first_reachability(primes, InitialSpace=X, GoalSpace=Y)
    if path:
        for x in path:
            print(x)



    # energy

    x = "0111010"
    e = PyBoolNet.state_transition_graphs.energy(primes, x)
    print(e)






























# end of file
