

from pyboolnet.model_checking import model_checking
from pyboolnet.repository import get_primes
from pyboolnet.state_transition_graphs import best_first_reachability


if __name__=="__main__":

    # basic model checking

    primes = get_primes("remy_tumorigenesis")
    init = "INIT TRUE"
    spec = "CTLSPEC DNA_damage -> AG(EF(Apoptosis_medium))"

    #tournier_apoptosis

    answer = model_checking(primes, "asynchronous", init, spec)
    print(answer)

    # model checking with accepting states

    answer, accepting_states = model_checking(primes, "asynchronous", init, spec, enable_accepting_states=True)
    for key, value in accepting_states.items():
        print(f"{key} = {value}")

    # model checking with counter examples

    spec = "CTLSPEC DNA_damage -> AG(EF(Proliferation))"
    answer, counterexample = model_checking(primes, "asynchronous", init, spec, enable_counterexample=True)
    print(answer)
    if counterexample:
        for state in counterexample:
            print(state)
            path = best_first_reachability(primes, initial_space=state, goal_space={"Proliferation": 1})
        































