

from pyboolnet.phenotypes import compute_phenotypes, compute_phenotype_diagram, create_phenotypes_piechart
from pyboolnet.attractors import compute_attractors
from pyboolnet.repository import get_primes


if __name__ == "__main__":
    # compute the commitment diagram

    primes = get_primes("arellano_rootstem")
    print(sorted(primes))

    attractors = compute_attractors(primes, "asynchronous")
    markers = ["WOX", "MGP"]
    phenotypes = compute_phenotypes(attractors, markers, fname_json="phenos.json")

    # inspect marker patterns

    for pheno in phenotypes["phenotypes"]:
        print(pheno["name"])
        print(pheno["pattern"])

    # draw diagram

    diagram = compute_phenotype_diagram(phenotypes, fname_image="phenos_diagram.pdf")

    # draw pie chart

    create_phenotypes_piechart(diagram, fname_image="phenos_piechart.pdf")





