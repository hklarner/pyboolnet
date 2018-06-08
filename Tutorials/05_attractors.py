#!/usr/bin/env python3
# -*- coding: utf-8 -*-


import PyBoolNet


if __name__=="__main__":


	# attractor computation with Tarjan

	primes = PyBoolNet.Repository.get_primes("tournier_apoptosis")

	stg = PyBoolNet.StateTransitionGraphs.primes2stg(primes, "asynchronous")
	steady, cyclic = PyBoolNet.Attractors.compute_attractors_tarjan(stg)
	print(steady)
	print(cyclic)


	# random walk attractor detection

	state = PyBoolNet.Attractors.find_attractor_state_by_randomwalk_and_ctl(primes, "asynchronous")
	print(state)


	# model checking based attractor detection

	attrs = PyBoolNet.Attractors.compute_json(primes, "asynchronous", FnameJson="attrs.json")

	print(attrs["is_complete"])
	for x in attrs["attractors"]:
		print(x["is_steady"])
		print(x["state"]["str"])

































# end of file
