

import sys
import os

import PyBoolNet

BASE = os.path.normpath(os.path.abspath(os.path.join(os.path.dirname(__file__), "../..")))
sys.path.insert(0, BASE)


def run():

    for name in ["tournier_apoptosis", "grieco_mapk", "remy_tumorigenesis", "dahlhaus_neuroplastoma"]:
        primes = PyBoolNet.Repository.get_primes(name)
        fname = os.path.join(name, name+"_attrs_sync.json")
        PyBoolNet.attractors.compute_attractors(primes, update="synchronous", fname_json=fname)

        fname = os.path.join(name, name+"_attrs_mixed.json")
        PyBoolNet.attractors.compute_attractors(primes, update="mixed", fname_json=fname)

    return

    names = PyBoolNet.Repository.get_all_names()

    for name in names:

        if name == "n12c5":
            continue  # takes forever to compute prime implicants

        primes = PyBoolNet.file_exchange.bnet2primes(os.path.join(name, name + ".bnet"))
        fname = os.path.join(name, name+"_igraph.pdf")
        PyBoolNet.interaction_graphs.create_stg_image(primes, fname)

    names = PyBoolNet.Repository.names_with_fast_analysis()

    for name in names:

        primes = PyBoolNet.file_exchange.bnet2primes(os.path.join(name, name + ".bnet"))

        fname = os.path.join(name, name+"_attrs.json")
        attrs = PyBoolNet.attractors.compute_attractors(primes, update="asynchronous", fname_json=fname)

        markers = PyBoolNet.prime_implicants.find_outputs(primes)
        if markers:
            fname = os.path.join(name, name+"_phenos.json")
            phenos = PyBoolNet.phenotypes.compute_attractors(attrs, markers)

            fname = os.path.join(name, name+"_phenos.pdf")
            diagram = PyBoolNet.phenotypes.compute_phenotype_diagram(phenos, fname_image=fname)

            fname = os.path.join(name, name+"_phenos_pie.pdf")
            PyBoolNet.phenotypes.create_phenotypes_piechart(diagram, fname_image=fname)

        #fname = os.path.join(name,name+"_attractors.md")
        #PyBoolNet.Attractors.create_attractor_report(primes, fname)

        fname = os.path.join(name, name+"_commitment.pdf")
        diagram = PyBoolNet.commitment_diagrams.compute_phenotype_diagram(attrs, fname_image=fname, fname_json=None, EdgeData=False, Silent=False)

        fname = os.path.join(name, name+"_commitment_pie.pdf")
        PyBoolNet.commitment_diagrams.create_phenotypes_piechart(diagram, fname_image=fname, color_map=None, Silent=False, title=None)

        fname = os.path.join(name, name+"_basins.pdf")
        PyBoolNet.basins_of_attraction.create_barplot(primes, "asynchronous", FnameImage=fname, Title="All Basins - %s" % name)

        fname = os.path.join(name, name+"_basins_pie.pdf")
        PyBoolNet.basins_of_attraction.create_phenotypes_piechart(primes, "asynchronous", fname_image=fname, title="Strong Basins - %s" % name)


if __name__ == "__main__":
    run()
