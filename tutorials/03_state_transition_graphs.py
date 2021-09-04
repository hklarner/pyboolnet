

import PyBoolNet


if __name__ == "__main__":
    primes = PyBoolNet.Repository.get_primes("xiao_wnt5a")
    PyBoolNet.state_transition_graphs.create_stg_image(primes, "asynchronous", "stg.pdf")
    PyBoolNet.state_transition_graphs.create_stg_image(primes, "asynchronous", "stg2.pdf", initial_states={"x4":0, "x5":0}, styles=["anonymous", "tendencies", "mintrapspaces"])


    # drawing paths

    path = PyBoolNet.state_transition_graphs.random_walk(primes, "asynchronous", initial_state="--00---", length=4)
    stg = PyBoolNet.state_transition_graphs.primes2stg(primes, "asynchronous", initial_states={"x4":0, "x5":0})
    PyBoolNet.state_transition_graphs.add_style_path(stg, path, color="red")
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
    path = PyBoolNet.state_transition_graphs.best_first_reachability(primes, initial_space=X, goal_space=Y)
    if path:
        for x in path:
            print(x)



    # energy

    x = "0111010"
    e = PyBoolNet.state_transition_graphs.energy(primes, x)
    print(e)






























# end of file
