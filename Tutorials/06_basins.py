#!/usr/bin/env python3
# -*- coding: utf-8 -*-


import PyBoolNet


if __name__=="__main__":


    # compute weak, strong and cycle-free basins

    primes = PyBoolNet.Repository.get_primes("tournier_apoptosis")
    attrs = PyBoolNet.attractors.compute_json(primes, "asynchronous")
    state = attrs["attractors"][0]["state"]["str"]
    print(state)

    weak = PyBoolNet.basins_of_attraction.weak_basin(primes, "asynchronous", state)
    for key, value in weak.items():
        print("{} = {}".format(key, value))

    strong = PyBoolNet.basins_of_attraction.strong_basin(primes, "asynchronous", state)
    for key, value in strong.items():
        print("{} = {}".format(key, value))

    cycfree = PyBoolNet.basins_of_attraction.cyclefree_basin(primes, "asynchronous", state)
    for key, value in cycfree.items():
        print("{} = {}".format(key, value))



    # to save the results and plot basins extend the attrs data

    PyBoolNet.basins_of_attraction.compute_basins(attrs)
    PyBoolNet.attractors.save_json(attrs, "attrs_basin.json")
    PyBoolNet.basins_of_attraction.create_barplot(attrs, "basin_barplot.pdf")
    PyBoolNet.basins_of_attraction.create_piechart(attrs, "basin_piechart.pdf")


































# end of file
