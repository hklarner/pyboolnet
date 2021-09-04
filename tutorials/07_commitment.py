

if __name__=="__main__":


    # compute the commitment diagram

    primes = PyBoolNet.Repository.get_primes("tournier_apoptosis")
    attrs = PyBoolNet.attractors.compute_attractors(primes, "asynchronous")
    diag = PyBoolNet.commitment_diagrams.compute_phenotype_diagram(attrs)
    PyBoolNet.commitment_diagrams.phenotype_diagram2image(diag, "commitment_diag.pdf")


    # compute commitment pie chart

    PyBoolNet.commitment_diagrams.create_phenotypes_piechart(diag, "commitment_pie.pdf")

































# end of file
