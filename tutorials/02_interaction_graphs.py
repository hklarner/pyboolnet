

import pyboolnet.state_space
from pyboolnet.interaction_graphs import primes2igraph, igraph2image, local_igraph_of_state, add_style_interactionsigns
from pyboolnet.repository import get_primes
from pyboolnet.state_transition_graphs import create_stg_image

if __name__ == "__main__":
    primes = get_primes("remy_tumorigenesis")
    create_stg_image(primes, update="asynchronous", fname_image="igraph.pdf")
    create_stg_image(primes, update="asynchronous", fname_image="igraph2.pdf", styles=["anonymous", "sccs"])

    # advances drawing

    igraph = primes2igraph(primes)

    for x in igraph.nodes:
        if "GF" in x:
            igraph.nodes[x]["shape"] = "square"
            igraph.nodes[x]["fillcolor"] = "lightblue"

    igraph2image(igraph, "igraph3.pdf")

    # local interaction graphs

    state = pyboolnet.state_space.random_state(primes)
    local_igraph = local_igraph_of_state(primes, state)
    add_style_interactionsigns(local_igraph)
    igraph2image(local_igraph, "local_igraph.pdf")





































