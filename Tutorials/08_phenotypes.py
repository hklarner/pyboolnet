#!/usr/bin/env python3
# -*- coding: utf-8 -*-


import PyBoolNet


if __name__=="__main__":


    # compute the commitment diagram

    primes = PyBoolNet.Repository.get_primes("arellano_rootstem")
    print(sorted(primes))
    attrs = PyBoolNet.Attractors.compute_json(primes, "asynchronous")
    markers = ["WOX", "MGP"]
    phenos = PyBoolNet.Phenotypes.compute_json(attrs, markers, FnameJson="phenos.json")


    # inspect marker patterns

    for pheno in phenos["phenotypes"]:
        print(pheno["name"])
        print(pheno["pattern"])


    # draw diagram

    diag = PyBoolNet.Phenotypes.compute_diagram(phenos, FnameImage="phenos_diagram.pdf")


    # draw pie chart

    PyBoolNet.Phenotypes.create_piechart(diag, FnameImage="phenos_piechart.pdf")
































# end of file
