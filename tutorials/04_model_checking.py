

from pyboolnet.model_checking import model_checking
from pyboolnet.model_checking import model_checking_with_counterexample, model_checking_with_acceptingstates
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

    answer, accepting = model_checking_with_acceptingstates(primes, "asynchronous", init, spec)
    for key, value in accepting.items():
        print(f"{key} = {value}")

    # model checking with counter examples

    spec = "CTLSPEC DNA_damage -> AG(EF(Proliferation))"
    answer, counterexample = model_checking_with_counterexample(primes, "asynchronous", init, spec)
    print(answer)
    if counterexample:
        for state in counterexample:
            print(state)
            path = best_first_reachability(primes, initial_space=state, goal_space={"Proliferation": 1})
        






























# end of file
