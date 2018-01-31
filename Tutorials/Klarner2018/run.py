
# -*- coding: utf-8 -*-

import sys
sys.path.insert(0,"/home/hannes/github/PyBoolNet")

import os

import PyBoolNet


bnet = """
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
	stg.node["000"]["penwidth"] = "3"
	stg.node["100"]["penwidth"] = "3"


def style_stg_commitment(stg, diagram):
	for i,node in enumerate(diagram):
		for x in PyBoolNet.StateTransitionGraphs.enumerate_states(PRIMES, diagram.node[node]["formula"]):
			stg.node[x]["fillcolor"] = PyBoolNet.Commitment.COMMITMENT_COLORS[i]
			diagram.node[node]["fillcolor"] = PyBoolNet.Commitment.COMMITMENT_COLORS[i]

	stg.graph["node"]["shape"] = "circle"
	stg.graph["node"]["color"] = "black"


def create_figure_01():

	stg = PyBoolNet.StateTransitionGraphs.primes2stg(PRIMES, UPDATE)
	basin = PyBoolNet.Basins.weak_basin(PRIMES, UPDATE, Subspace="000")
	style_stg_basin(stg, basin, PyBoolNet.Basins.BASIN_COLORS[0])
	PyBoolNet.StateTransitionGraphs.stg2image(stg, FnameIMAGE="figure01a.pdf")

	stg = PyBoolNet.StateTransitionGraphs.primes2stg(PRIMES, UPDATE)
	basin = PyBoolNet.Basins.strong_basin(PRIMES, UPDATE, Subspace="000")
	style_stg_basin(stg, basin, PyBoolNet.Basins.BASIN_COLORS[1])
	PyBoolNet.StateTransitionGraphs.stg2image(stg, FnameIMAGE="figure01b.pdf")

	stg = PyBoolNet.StateTransitionGraphs.primes2stg(PRIMES, UPDATE)
	basin = PyBoolNet.Basins.cyclefree_basin(PRIMES, UPDATE, Subspace="000")
	style_stg_basin(stg, basin, PyBoolNet.Basins.BASIN_COLORS[2])
	PyBoolNet.StateTransitionGraphs.stg2image(stg, FnameIMAGE="figure01c.pdf")


def create_figure_02():

	PyBoolNet.Basins.create_barplot(ATTRS, FnameImage="figure02a.pdf", Title="")
	PyBoolNet.Basins.create_piechart(ATTRS, FnameImage="figure02b.pdf", Title="")

def create_figure_03():

	diagram = PyBoolNet.Commitment.compute_diagram(ATTRS)
	stg = PyBoolNet.StateTransitionGraphs.primes2stg(PRIMES, UPDATE)
	style_stg_commitment(stg, diagram)
	PyBoolNet.StateTransitionGraphs.stg2image(stg, FnameIMAGE="figure03a.pdf")
	PyBoolNet.Commitment.diagram2image(diagram, FnameImage="figure03b.pdf")
	PyBoolNet.Commitment.create_piechart(diagram, FnameImage="figure03c.pdf", Title="")

if __name__=="__main__":
	create_figure_01()
	create_figure_02()
	create_figure_03()

















# end of file
