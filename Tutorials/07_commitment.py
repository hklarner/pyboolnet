#!/usr/bin/env python3
# -*- coding: utf-8 -*-


import PyBoolNet


if __name__=="__main__":


    # compute the commitment diagram

    primes = PyBoolNet.Repository.get_primes("tournier_apoptosis")
    attrs = PyBoolNet.Attractors.compute_json(primes, "asynchronous")
    diag = PyBoolNet.Commitment.compute_diagram(attrs)
    PyBoolNet.Commitment.diagram2image(diag, "commitment_diag.pdf")


    # compute commitment pie chart

    PyBoolNet.Commitment.create_piechart(diag, "commitment_pie.pdf")

































# end of file
