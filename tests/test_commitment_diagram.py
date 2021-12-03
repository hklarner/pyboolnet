

import pytest

from pyboolnet.commitment_diagrams import compute_commitment_diagram, create_commitment_piechart
from pyboolnet.commitment_diagrams import open_commitment_diagram
from pyboolnet.attractors import compute_attractors
from pyboolnet.repository import get_primes
from tests.helpers import get_tests_path_out


@pytest.fixture(scope="session")
def attractors():
    return compute_attractors(primes=get_primes("raf"), update="asynchronous")


@pytest.mark.parametrize("edge_data", [True, False])
def test_compute_commitment_diagram(attractors, edge_data):
    fname_image = get_tests_path_out(fname="compute_commitment_diagram.pdf")
    fname_json = get_tests_path_out(fname="compute_commitment_diagram.json")

    diagram = compute_commitment_diagram(attractors, fname_image=fname_image, fname_json=fname_json, edge_data=edge_data)
    diagram_from_file = open_commitment_diagram(fname_json=fname_json)

    assert sorted(diagram.edges(data=True)) == sorted(diagram_from_file.edges(data=True))
    assert sorted(diagram.nodes(data=True)) == sorted(diagram_from_file.nodes(data=True))


def test_create_piechart(attractors):
    try:
        diagram = compute_commitment_diagram(attractors)
        fname_image = get_tests_path_out(fname="compute_commitment_diagram.pdf")
        create_commitment_piechart(diagram=diagram, fname_image=fname_image, title="A commitment pie chart")
    except NameError:
        pass

