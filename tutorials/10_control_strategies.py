
from pyboolnet.control_strategies import compute_control_strategies_with_model_checking, compute_control_strategies_with_completeness
from pyboolnet.repository import get_primes


if __name__ == "__main__":

    # Defining control problem
    network = "calzone_cellfate"  # "grieco_mapk" # "selvaggio_emt"
    target = [{"Apoptosis": 1, "Survival": 0, "NonACD": 0}]  # [{"Apoptosis":1, "Proliferation":0, "Growth_Arrest":1}] #[{"AJ_b1":0, "AJ_b2":0, "FA_b1":1, "FA_b2":1, "FA_b3":1}]
    update = "asynchronous"
    limit = 2

    primes = get_primes(network)

    cs = compute_control_strategies_with_model_checking(
        primes=primes,
        target=target,
        update=update,
        limit=limit,
        silent=True,
        starting_length=0,
        previous_cs=[],
        known_cs=[],
        avoid_nodes=[])

    print("Number of control strategies:", len(cs))
    print("Control strategies:", cs)
