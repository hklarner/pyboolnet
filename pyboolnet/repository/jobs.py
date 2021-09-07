from pyboolnet.file_exchange import bnet2primes
from pyboolnet.repository import get_primes

if __name__ == "__main__":

    for name in ["tournier_apoptosis", "grieco_mapk", "remy_tumorigenesis", "dahlhaus_neuroplastoma"]:
        primes = get_primes(name)
        fname = os.path.join(name, name+"_attractors_sync.json")
        compute_attractors(primes, update="synchronous", fname_json=fname)
        fname = os.path.join(name, name+"_attractors_mixed.json")
        compute_attractors(primes, update="mixed", fname_json=fname)


    names = get_all_names()

    for name in names:

        if name == "n12c5":
            continue  # takes forever to compute prime implicants

        primes = bnet2primes(os.path.join(name, name + ".bnet"))
        fname = os.path.join(name, name+"_igraph.pdf")
        create_stg_image(primes, fname)

    names = PyBoolNet.Repository.names_with_fast_analysis()

    for name in names:

        primes = bnet2primes(os.path.join(name, name + ".bnet"))

        fname = os.path.join(name, name+"_attractors.json")
        attractors = compute_attractors(primes, update="asynchronous", fname_json=fname)

        markers = find_outputs(primes)
        if markers:
            fname = os.path.join(name, name+"_phenos.json")
            phenos = compute_attractors(attractors, markers)

            fname = os.path.join(name, name+"_phenos.pdf")
            diagram = compute_phenotype_diagram(phenos, fname_image=fname)

            fname = os.path.join(name, name+"_phenos_pie.pdf")
            create_phenotypes_piechart(diagram, fname_image=fname)

        fname = os.path.join(name, name+"_commitment.pdf")
        diagram = PyBoolNet.commitment_diagrams.compute_phenotype_diagram(attractors, fname_image=fname, fname_json=None, EdgeData=False, Silent=False)

        fname = os.path.join(name, name+"_commitment_pie.pdf")
        PyBoolNet.commitment_diagrams.create_phenotypes_piechart(diagram, fname_image=fname, color_map=None, Silent=False, title=None)

        fname = os.path.join(name, name+"_basins.pdf")
        PyBoolNet.basins_of_attraction.create_basins_of_attraction_barplot(primes, "asynchronous", fname_image=fname, title="All Basins - %s" % name)

        fname = os.path.join(name, name+"_basins_pie.pdf")
        PyBoolNet.basins_of_attraction.create_phenotypes_piechart(primes, "asynchronous", fname_image=fname, title="Strong Basins - %s" % name)


