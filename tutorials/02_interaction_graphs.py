#!/usr/bin/env python3
# -*- coding: utf-8 -*-


import PyBoolNet


if __name__=="__main__":

    # basic drawing

    primes = PyBoolNet.Repository.get_primes("remy_tumorigenesis")
    PyBoolNet.interaction_graphs.create_image(primes, "igraph.pdf")

    PyBoolNet.interaction_graphs.create_image(primes, "igraph2.pdf", styles=["anonymous", "sccs"])

    # advances drawing

    igraph = PyBoolNet.interaction_graphs.primes2igraph(primes)

    for x in igraph.nodes():
        if "GF" in x:
            igraph.node[x]["shape"] = "square"
            igraph.node[x]["fillcolor"] = "lightblue"

    PyBoolNet.interaction_graphs.igraph2image(igraph, "igraph3.pdf")

    # local interaction graphs

    state = PyBoolNet.state_transition_graphs.random_state(primes)
    local_igraph = PyBoolNet.interaction_graphs.local_igraph_of_state(primes, state)
    PyBoolNet.interaction_graphs.add_style_interactionsigns(local_igraph)
    PyBoolNet.interaction_graphs.igraph2image(local_igraph, "local_igraph.pdf")




































# end of file
