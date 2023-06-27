

from pyboolnet.phenotypes import compute_phenotypes, compute_phenotype_diagram, create_phenotypes_piechart
from pyboolnet.attractors import compute_attractors
from pyboolnet.repository import get_primes


if __name__ == "__main__":
    primes = get_primes("arellano_rootstem")
    attractors = compute_attractors(primes, "asynchronous")
    markers = ["WOX", "MGP"]
    phenotypes = compute_phenotypes(attractors=attractors, markers=markers, fname_json="phenos.json")

    diagram = compute_phenotype_diagram(phenotypes=phenotypes, fname_image="phenos_diagram.pdf")
    create_phenotypes_piechart(diagram=diagram, fname_image="phenos_piechart.pdf")





