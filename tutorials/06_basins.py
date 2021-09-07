

from pyboolnet.attractors import compute_attractors
from pyboolnet.attractors import write_attractors_json
from pyboolnet.basins_of_attraction import create_basins_of_attraction_barplot
from pyboolnet.basins_of_attraction import weak_basin, strong_basin, cycle_free_basin
from pyboolnet.basins_of_attraction import compute_basins, create_basins_piechart
from pyboolnet.repository import get_primes


if __name__ == "__main__":
    # compute weak, strong and cycle-free basins

    primes = get_primes("tournier_apoptosis")
    attractors = compute_attractors(primes, "asynchronous")
    state = attractors["attractors"][0]["state"]["str"]
    print(state)

    weak = weak_basin(primes, "asynchronous", state)
    for key, value in weak.items():
        print(f"{key} = {value}")

    strong = strong_basin(primes, "asynchronous", state)
    for key, value in strong.items():
        print(f"{key} = {value}")

    cycle_free = cycle_free_basin(primes, "asynchronous", state)
    for key, value in cycle_free.items():
        print(f"{key} = {value}")

    # to save the results and plot basins extend the attrs data

    compute_basins(attractors)
    write_attractors_json(attractors, "attrs_basin.json")
    create_basins_of_attraction_barplot(attractors, "basin_barplot.pdf")
    create_basins_piechart(attractors, "basin_piechart.pdf")







