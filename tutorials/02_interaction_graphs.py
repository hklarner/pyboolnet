

import pyboolnet.state_space

if __name__ == "__main__":
    primes = PyBoolNet.Repository.get_primes("remy_tumorigenesis")
    PyBoolNet.interaction_graphs.create_stg_image(primes, "igraph.pdf")

    PyBoolNet.interaction_graphs.create_stg_image(primes, "igraph2.pdf", styles=["anonymous", "sccs"])

    # advances drawing

    igraph = PyBoolNet.interaction_graphs.primes2igraph(primes)

    for x in igraph.nodes():
        if "GF" in x:
            igraph.node[x]["shape"] = "square"
            igraph.node[x]["fillcolor"] = "lightblue"

    PyBoolNet.interaction_graphs.igraph2image(igraph, "igraph3.pdf")

    # local interaction graphs

    state = pyboolnet.state_space.random_state(primes)
    local_igraph = PyBoolNet.interaction_graphs.local_igraph_of_state(primes, state)
    PyBoolNet.interaction_graphs.add_style_interactionsigns(local_igraph)
    PyBoolNet.interaction_graphs.igraph2image(local_igraph, "local_igraph.pdf")




































# end of file
