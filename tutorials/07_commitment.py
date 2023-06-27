

from pyboolnet.attractors import compute_attractors
from pyboolnet.commitment_diagrams import compute_commitment_diagram, create_commitment_piechart
from pyboolnet.repository import get_primes


if __name__ == "__main__":
    primes = get_primes("tournier_apoptosis")
    attractors = compute_attractors(primes=primes, update="asynchronous")

    diagram = compute_commitment_diagram(attractors=attractors, fname_image="commitment_diagram.pdf")
    create_commitment_piechart(diagram=diagram, fname_image="commitment_piechart.pdf")



































