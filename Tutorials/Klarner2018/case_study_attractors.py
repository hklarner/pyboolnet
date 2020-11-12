
# -*- coding: utf-8 -*-

from __future__ import print_function

import os
import sys
sys.path.insert(0,"/home/hannes/github/PyBoolNet")
import PyBoolNet


if __name__=="__main__":

    primes = PyBoolNet.Repository.get_primes("remy_tumorigenesis")

    fname = "remy_tumorigenesis_attrs.json"
    if os.path.isfile(fname):
        attrs = PyBoolNet.Attractors.open_json(fname)
    else:
        attrs = PyBoolNet.Attractors.compute_json(primes, "asynchronous")
        PyBoolNet.Basins.compute_basins(attrs)
        PyBoolNet.Attractors.save_json(attrs, FnameJson=fname)


    markers = ["Proliferation", "Apoptosis_medium", "Apoptosis_high", "Growth_arrest"]
    def PhenoMap(Dict):
        pattern = "".join(str(Dict[x]) if x in Dict else "*" for x in markers)

        if pattern=="0001":
            res = "GA"
        elif pattern=="1000":
            res = "P"
        elif pattern=="0101":
            res = "A"
        elif pattern=="*00*":
            res = "OscP/GA"
        else:
            res = "unknown"

        if len(Dict)<len(primes):
            res+= " cyclic"

        return res

    fname = "remy_tumorigenesis_basins_barplot.pdf"
    PyBoolNet.Basins.create_barplot(attrs, fname, Ymax=9, LabelsMap=PhenoMap)

    inputs = PyBoolNet.PrimeImplicants.find_inputs(attrs["primes"])
    if inputs and 0:
        combinations = set()
        for A in attrs["attractors"]:
            A["input_combination"] = "".join(str(A["mintrapspace"]["dict"][x]) for x in inputs)
            combinations.add(A["input_combination"])

        for input_combination in sorted(combinations):
            fname = "remy_tumorigenesis_basins_barplot_{}.pdf".format(input_combination)

            attrs_copy = PyBoolNet.Utility.Misc.copy_json_data(attrs)
            attrs_copy["attractors"] = [x for x in attrs_copy["attractors"] if x["input_combination"] == input_combination]

            PyBoolNet.Basins.create_barplot(attrs_copy, fname, Ymax=9, LabelsMap=PhenoMap)

    fname = "remy_tumorigenesis_basins_piechart.pdf"
    PyBoolNet.Basins.create_piechart(attrs, fname, LabelsMap=PhenoMap)

    fname = "remy_tumorigenesis_commitment.json"
    if os.path.isfile(fname):
        diagram = PyBoolNet.Commitment.open_diagram(fname)
    else:
        diagram = PyBoolNet.Commitment.compute_diagram(attrs, FnameJson=fname)

    fname = "remy_tumorigenesis_commitment.pdf"
    PyBoolNet.Commitment.diagram2image(diagram, fname)

    fname = "remy_tumorigenesis_commitmentpie.pdf"
    PyBoolNet.Commitment.create_piechart(diagram, fname)














# end of file
