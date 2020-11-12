
# -*- coding: utf-8 -*-

import PyBoolNet

bnet = """
# created using http://page.mi.fu-berlin.de/klarner/iBoolNet/iBoolNet.html
v1, !v1&v2 | v1&!v2&!v3
v2, v1&v3
v3, v2
"""

PRIMES = PyBoolNet.FileExchange.bnet2primes(bnet)
UPDATE = "asynchronous"
ATTRS = PyBoolNet.Attractors.compute_json(PRIMES, UPDATE)
PyBoolNet.Basins.compute_basins(ATTRS)


def style_stg_basin(stg, basin, color):
    for x in PyBoolNet.StateTransitionGraphs.enumerate_states(PRIMES, basin["formula"]):
        stg.node[x]["fillcolor"] = color
    stg.graph["node"]["shape"] = "circle"
    stg.graph["node"]["color"] = "black"

    stg.node["000"]["shape"] = "doublecircle"
    stg.node["100"]["shape"] = "doublecircle"


    #stg.node["000"]["penwidth"] = "3"
    #stg.node["100"]["penwidth"] = "3"


def create_figure_01():


    engine = "neato"

    stg = PyBoolNet.StateTransitionGraphs.primes2stg(PRIMES, UPDATE)
    basin = PyBoolNet.Basins.weak_basin(PRIMES, UPDATE, Subspace="000")
    style_stg_basin(stg, basin, PyBoolNet.Basins.BASIN_COLORS[0])
    PyBoolNet.StateTransitionGraphs.stg2image(stg, FnameIMAGE="figure01a.pdf", LayoutEngine=engine)
    PyBoolNet.StateTransitionGraphs.stg2dot(stg, "junk.dot")

    stg = PyBoolNet.StateTransitionGraphs.primes2stg(PRIMES, UPDATE)
    basin = PyBoolNet.Basins.strong_basin(PRIMES, UPDATE, Subspace="000")
    style_stg_basin(stg, basin, PyBoolNet.Basins.BASIN_COLORS[1])
    PyBoolNet.StateTransitionGraphs.stg2image(stg, FnameIMAGE="figure01b.pdf", LayoutEngine=engine)

    stg = PyBoolNet.StateTransitionGraphs.primes2stg(PRIMES, UPDATE)
    basin = PyBoolNet.Basins.cyclefree_basin(PRIMES, UPDATE, Subspace="000")
    style_stg_basin(stg, basin, PyBoolNet.Basins.BASIN_COLORS[2])
    PyBoolNet.StateTransitionGraphs.stg2image(stg, FnameIMAGE="figure01c.pdf", LayoutEngine=engine)


if __name__=="__main__":


    create_figure_01()














# end of file
