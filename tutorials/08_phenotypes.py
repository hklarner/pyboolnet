

if __name__=="__main__":


    # compute the commitment diagram

    primes = get_primes("arellano_rootstem")
    print(sorted(primes))
    attrs = PyBoolNet.attractors.compute_attractors(primes, "asynchronous")
    markers = ["WOX", "MGP"]
    phenos = PyBoolNet.phenotypes.compute_attractors(attrs, markers, FnameJson="phenos.json")


    # inspect marker patterns

    for pheno in phenos["phenotypes"]:
        print(pheno["name"])
        print(pheno["pattern"])


    # draw diagram

    diag = PyBoolNet.phenotypes.compute_phenotype_diagram(phenos, fname_image="phenos_diagram.pdf")


    # draw pie chart

    PyBoolNet.phenotypes.create_phenotypes_piechart(diag, fname_image="phenos_piechart.pdf")
































# end of file
