

from pyboolnet.repository import get_primes
from pyboolnet.state_transition_graphs import create_stg_image
from pyboolnet.state_transition_graphs import energy, random_walk, add_style_path, add_style_anonymous, stg2image, \
    primes2stg
from pyboolnet.state_transition_graphs import sccgraph2image
from pyboolnet.state_transition_graphs import stg2sccgraph, stg2condensationgraph, best_first_reachability

if __name__ == "__main__":
    primes = get_primes("xiao_wnt5a")
    create_stg_image(primes, "asynchronous", "stg.pdf")
    create_stg_image(primes, "asynchronous", "stg2.pdf", initial_states={"x4":0, "x5":0}, styles=["anonymous", "tendencies", "mintrapspaces"])

    # drawing paths

    path = random_walk(primes, "asynchronous", initial_state="--00---", length=4)
    stg = primes2stg(primes, "asynchronous", initial_states={"x4":0, "x5":0})
    add_style_path(stg, path, color="red")
    add_style_anonymous(stg)
    stg2image(stg, "stg3.pdf")

    # drawing factor graphs

    primes = get_primes("randomnet_n7k3")
    stg = primes2stg(primes, "asynchronous")
    scc_graph = stg2sccgraph(stg)
    sccgraph2image(scc_graph, "scc_graph.pdf")

    cograph = stg2condensationgraph(stg)
    sccgraph2image(cograph, "cograph.pdf")

    htg = stg2condensationgraph(stg)
    sccgraph2image(htg, "htg.pdf")

    # best first reachability

    X = "0--1-1-"
    Y = "1--0---"
    path = best_first_reachability(primes, initial_space=X, goal_space=Y)
    if path:
        for x in path:
            print(x)

    # energy

    x = "0111010"
    e = energy(primes, x)
    print(e)































