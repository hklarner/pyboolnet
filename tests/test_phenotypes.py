

from typing import List

import pytest

from pyboolnet.attractors import compute_attractors
from pyboolnet.phenotypes import compute_phenotype_diagram
from pyboolnet.phenotypes import create_phenotypes_piechart
from pyboolnet.phenotypes import phenotype_diagram2image, compute_phenotypes
from pyboolnet.phenotypes import save_phenotype_diagram, open_phenotype_diagram
from pyboolnet.repository import get_primes
from tests.helpers import get_tests_path_out


@pytest.fixture()
def markers() -> List[str]:
    return ["v2", "v3"]


@pytest.fixture()
def attractors() -> dict:
    fname_json = get_tests_path_out(fname="attractors.json")
    return compute_attractors(primes=get_primes(name="n5s3"), update="asynchronous", fname_json=fname_json)


@pytest.fixture()
def phenotypes(attractors, markers) -> dict:
    fname_json = get_tests_path_out(fname="phenotypes.json")
    return compute_phenotypes(attractors=attractors, markers=markers, fname_json=fname_json)


def test_compute_phenotypes(attractors, markers):
    fname_json = get_tests_path_out(fname="phenotypes.json")
    compute_phenotypes(attractors=attractors, markers=markers, fname_json=fname_json)


def test_compute_phenotype_diagram(phenotypes):
    fname_json = get_tests_path_out(fname="phenotype_diagram.json")
    fname_image = get_tests_path_out(fname="phenotype_diagram.pdf")
    compute_phenotype_diagram(phenotypes=phenotypes, fname_json=fname_json, fname_image=fname_image)


def test_save_and_open_phenotype_diagram(phenotypes):
    diagram = compute_phenotype_diagram(phenotypes=phenotypes)
    fname_json = get_tests_path_out(fname="attractors.json")
    save_phenotype_diagram(diagram=diagram, fname_json=fname_json)
    open_phenotype_diagram(fname_json=fname_json)


def test_diagram2image(phenotypes):
    diagram = compute_phenotype_diagram(phenotypes=phenotypes)
    fname_image = get_tests_path_out(fname="phenotype_diagram.pdf")
    phenotype_diagram2image(diagram=diagram, fname_image=fname_image)


def test_create_phenotypes_piechart(phenotypes):
    try:
        diagram = compute_phenotype_diagram(phenotypes=phenotypes)
        fname_image = get_tests_path_out(fname="phenotype_piechart.pdf")
        create_phenotypes_piechart(diagram=diagram, fname_image=fname_image)
    except NameError:
        pass

