

import sys
import os

BASE = os.path.normpath(os.path.abspath(os.path.join(os.path.dirname(__file__), "../..")))
sys.path.insert(0,BASE)

import PyBoolNet



def run():

    for name in ["tournier_apoptosis", "grieco_mapk", "remy_tumorigenesis", "dahlhaus_neuroplastoma"]:
        primes = PyBoolNet.Repository.get_primes(name)
        fname = os.path.join(name,name+"_attrs_sync.json")
        PyBoolNet.Attractors.compute_json(primes, Update="synchronous", FnameJson=fname)

        fname = os.path.join(name,name+"_attrs_mixed.json")
        PyBoolNet.Attractors.compute_json(primes, Update="mixed", FnameJson=fname)


    return

    names = PyBoolNet.Repository.get_all_names()

    for name in names:

        if name=="n12c5": continue # takes forever to compute prime implicants

        primes = PyBoolNet.FileExchange.bnet2primes(os.path.join(name,name+".bnet"))
        fname = os.path.join(name,name+"_igraph.pdf")
        PyBoolNet.InteractionGraphs.create_image(primes,fname)


    names = PyBoolNet.Repository.names_with_fast_analysis()

    for name in names:

        primes = PyBoolNet.FileExchange.bnet2primes(os.path.join(name,name+".bnet"))

        fname = os.path.join(name,name+"_attrs.json")
        attrs = PyBoolNet.Attractors.compute_json(primes, Update="asynchronous", FnameJson=fname)

        markers = PyBoolNet.PrimeImplicants.find_outputs(primes)
        if markers:
            fname = os.path.join(name,name+"_phenos.json")
            phenos = PyBoolNet.Phenotypes.compute_json(attrs, markers)

            fname = os.path.join(name,name+"_phenos.pdf")
            diagram = PyBoolNet.Phenotypes.compute_diagram(phenos, FnameImage=fname)

            fname = os.path.join(name,name+"_phenos_pie.pdf")
            PyBoolNet.Phenotypes.create_piechart(diagram, FnameImage=fname)

        #fname = os.path.join(name,name+"_attractors.md")
        #PyBoolNet.Attractors.create_attractor_report(primes, fname)

        fname = os.path.join(name,name+"_commitment.pdf")
        diagram = PyBoolNet.Commitment.compute_diagram(attrs, FnameImage=fname, FnameJson=None, EdgeData=False, Silent=False)

        fname = os.path.join(name,name+"_commitment_pie.pdf")
        PyBoolNet.Commitment.create_piechart(diagram, FnameImage=fname, ColorMap=None, Silent=False, Title=None)

        fname = os.path.join(name,name+"_basins.pdf")
        PyBoolNet.Basins.create_barplot(primes, "asynchronous", FnameImage=fname, Title="All Basins - %s"%name)

        fname = os.path.join(name,name+"_basins_pie.pdf")
        PyBoolNet.Basins.create_piechart(primes, "asynchronous", FnameImage=fname, Title="Strong Basins - %s"%name)


if __name__=="__main__":
    run()
