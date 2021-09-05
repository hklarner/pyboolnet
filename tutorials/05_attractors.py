

from pyboolnet.repository import get_primes
from pyboolnet.state_transition_graphs import primes2stg
from pyboolnet.attractors import compute_attractors_tarjan, compute_attractors, find_attractor_state_by_randomwalk_and_ctl


if __name__ == "__main__":
    # attractor computation with Tarjan

    primes = get_primes("tournier_apoptosis")

    stg = primes2stg(primes, "asynchronous")
    steady, cyclic = compute_attractors_tarjan(stg)
    print(steady)
    print(cyclic)

    # random walk attractor detection

    state = find_attractor_state_by_randomwalk_and_ctl(primes, "asynchronous")
    print(state)

    # model checking based attractor detection

    attrs = compute_attractors(primes, "asynchronous", fname_json="attrs.json")

    print(attrs["is_complete"])
    for x in attrs["attractors"]:
        print(x["is_steady"])
        print(x["state"]["str"])


