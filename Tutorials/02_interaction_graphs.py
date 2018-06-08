#!/usr/bin/env python3
# -*- coding: utf-8 -*-


import PyBoolNet


if __name__=="__main__":

	# basic drawing

	primes = PyBoolNet.Repository.get_primes("remy_tumorigenesis")
	PyBoolNet.InteractionGraphs.create_image(primes, "igraph.pdf")

	PyBoolNet.InteractionGraphs.create_image(primes, "igraph2.pdf", Styles=["anonymous", "sccs"])

	# advances drawing

	igraph = PyBoolNet.InteractionGraphs.primes2igraph(primes)

	for x in igraph.nodes():
		if "GF" in x:
			igraph.node[x]["shape"] = "square"
			igraph.node[x]["fillcolor"] = "lightblue"

	PyBoolNet.InteractionGraphs.igraph2image(igraph, "igraph3.pdf")

	# local interaction graphs

	state = PyBoolNet.StateTransitionGraphs.random_state(primes)
	local_igraph = PyBoolNet.InteractionGraphs.local_igraph_of_state(primes, state)
	PyBoolNet.InteractionGraphs.add_style_interactionsigns(local_igraph)
	PyBoolNet.InteractionGraphs.igraph2image(local_igraph, "local_igraph.pdf")




































# end of file
