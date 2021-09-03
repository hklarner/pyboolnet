#!/usr/bin/env python3
# -*- coding: utf-8 -*-


import PyBoolNet


if __name__=="__main__":


    # compute the commitment diagram

    primes = PyBoolNet.Repository.get_primes("tournier_apoptosis")
    attrs = PyBoolNet.attractors.compute_attractor_json(primes, "asynchronous")
    diag = PyBoolNet.commitment_diagrams.compute_diagram(attrs)
    PyBoolNet.commitment_diagrams.diagram2image(diag, "commitment_diag.pdf")


    # compute commitment pie chart

    PyBoolNet.commitment_diagrams.create_piechart(diag, "commitment_pie.pdf")

































# end of file
