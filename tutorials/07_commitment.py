

from pyboolnet.phenotypes import phenotype_diagram2image, compute_phenotype_diagram, create_phenotypes_piechart
from pyboolnet.attractors import compute_attractors
from pyboolnet.repository import get_primes


if __name__ == "__main__":
    # compute the commitment diagram

    primes = get_primes("tournier_apoptosis")
    attractors = compute_attractors(primes, "asynchronous")
    diagram = compute_phenotype_diagram(attractors)
    phenotype_diagram2image(diagram, "commitment_diagram.pdf")

    # compute commitment pie chart

    create_phenotypes_piechart(diagram, "commitment_piechart.pdf")

































# end of file
