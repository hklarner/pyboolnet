
# -*- coding: utf-8 -*-

import sys
sys.path.insert(0,"/home/hannes/github/PyBoolNet")

import os

import PyBoolNet




def run():

    name = "remy_tumorigenesis"
    primes = PyBoolNet.Repository.get_primes(name)

    update = "asynchronous"
    markers = ["Proliferation", "Growth_arrest", "Apoptosis_medium", "Apoptosis_high"]


    fname_attrs = "{n}_{u}_attrs.json".format(n=name, u=update)
    fname_phenos = "{n}_{u}_phenos.json".format(n=name, u=update)
    fname_diag = "{n}_{u}_phenodiagram.pdf".format(n=name, u=update)

    if os.path.isfile(fname_attrs):
        print("Using existing attractors file {x}.".format(x=fname_attrs))
        attrs = PyBoolNet.attractors.read_attractors_json(fname_attrs)
    else:
        print("Computing attractors, this takes about 25 minutes. Results will be saved as {x}.".format(x=fname_attrs))
        attrs = PyBoolNet.attractors.compute_attractors(primes, update="asynchronous", fname_json=fname_attrs)
        # real    24m0.954s
        # user    23m54.158s
        # sys    0m7.109s



    phenos = PyBoolNet.phenotypes.compute_attractors(attrs, markers, FnameJson=fname_phenos)

    print("Computing phenotype diagram, this takes about xxx minutes.")
    PyBoolNet.phenotypes.compute_phenotype_diagram(phenos, fname_diag)


if __name__=="__main__":
    run()

















# end of file
