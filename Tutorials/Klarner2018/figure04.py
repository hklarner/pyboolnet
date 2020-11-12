
# -*- coding: utf-8 -*-

import random
import os
import sys
sys.path.insert(0,"/home/hannes/github/PyBoolNet")

import PyBoolNet



def run_simulations():
    primes = PyBoolNet.Repository.get_primes("remy_tumorigenesis")
    print("fixing inputs to 0110")
    PyBoolNet.PrimeImplicants.create_constants(primes, {"EGFR_stimulus":0, "FGFR3_stimulus":1, "DNA_damage":1, "Growth_inhibitors":0})

    if os.path.isfile("remy_0110_attrs.json"):
        print(" opening {x}.".format(x="remy_0110_attrs.json"))
        attrs = PyBoolNet.Attractors.open_json("remy_0110_attrs.json")
        PyBoolNet.Basins.create_barplot(attrs, FnameImage="remy_0110_basins.pdf")
    else:
        print(" creating {x}.".format(x="remy_0110_attrs.json"))
        attrs = PyBoolNet.Attractors.compute_json(primes, "asynchronous", FnameJson="remy_0110_attrs.json")
        PyBoolNet.Basins.compute_basins(attrs, FnameBarplot="remy_0110_basins.pdf")
        PyBoolNet.Attractors.save_json(attrs, "remy_0110_attrs.json")

    goal = {x:0 for x in PyBoolNet.AspSolver.trap_spaces(primes, "min", Representation="str")}

    for i in range(10):
        x = PyBoolNet.StateTransitionGraphs.random_state(primes)
        x_str = PyBoolNet.StateTransitionGraphs.state2str(x)

        while x_str not in goal:
            x = random.choice(PyBoolNet.StateTransitionGraphs.successors_asynchronous(primes,x))
            x_str = PyBoolNet.StateTransitionGraphs.state2str(x)

        goal[x_str] += 1

    for x_str in goal:
        x = PyBoolNet.StateTransitionGraphs.state2dict(primes, x_str)
        pheno = "".join(str(x[i]) for i in ["Proliferation", "Apoptosis_medium", "Apoptosis_high", "Growth_arrest"])
        print(" pheno: {p} likelihood: {l}%".format(p=pheno, l=goal[x_str]/10000.*100))




def create_table2():
    Primes = PyBoolNet.Repository.get_primes("remy_tumorigenesis")
    Mints  = PyBoolNet.AspSolver.trap_spaces(Primes, "min")
    inputs = PyBoolNet.PrimeImplicants.find_inputs(Primes)

    bins = {}
    for x in Mints:
        pattern = "".join(str(x[y]) for y in ["EGFR_stimulus", "FGFR3_stimulus", "DNA_damage", "Growth_inhibitors"])
        if pattern in bins:
            bins[pattern].append(x)
        else:
            bins[pattern] = [x]

    phenos = {}
    for x in sorted(bins):
        cyclic = [y for y in bins[x] if len(y)<len(Primes)]
        steady = [z for z in bins[x] if len(z)==len(Primes)]
        print(" {x}: steady: {y} cyclic: {z}".format(x=x, y=len(steady), z=len(cyclic)))
        for mints in bins[x]:
            pheno  = "".join(str(mints[i]) if i in mints else "*" for i in ["Proliferation", "Apoptosis_medium", "Apoptosis_high", "Growth_arrest"])
            print(" pheno: " + pheno)
            if pheno not in phenos:
                phenos[pheno] = {"steady":0, "cyclic":0}

            if len(mints)==len(Primes):
                phenos[pheno]["steady"] += 1
            else:
                phenos[pheno]["cyclic"] += 1

    print("===============================")
    for x in phenos:
        print(" pheno: {p}. cyclic: {c}. steady: {s}".format(p=x, c=phenos[x]["cyclic"], s=phenos[x]["steady"]))



def create_figure_04():

    primes = PyBoolNet.Repository.get_primes("remy_tumorigenesis")
    if os.path.isfile("remy_wildtype_attrs.json"):
        print(" opening {x}.".format(x="remy_wildtype_attrs.json"))
        attrs = PyBoolNet.Attractors.open_json("remy_wildtype_attrs.json")
        PyBoolNet.Basins.create_barplot(attrs, FnameImage="wildtype_basins.pdf")
    else:
        print(" creating {x}.".format(x="remy_wildtype_attrs.json"))
        attrs = PyBoolNet.Attractors.compute_json(primes, "asynchronous", FnameJson="remy_wildtype_attrs.json")
        PyBoolNet.Basins.compute_basins(attrs, FnameBarplot="wildtype_basins.pdf")
        PyBoolNet.Attractors.save_json(attrs, "remy_wildtype_attrs.json")




if __name__=="__main__":
    #create_figure_04()
    create_table2()
    #run_simulations()



















# end of file
