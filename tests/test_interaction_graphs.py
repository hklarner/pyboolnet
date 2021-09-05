

import os
import networkx

from pyboolnet.repository import get_primes
from pyboolnet.interaction_graphs import primes2igraph
from pyboolnet.file_exchange import read_primes
from pyboolnet.interaction_graphs import create_image, igraph2dot, igraph2image
from pyboolnet.interaction_graphs import activities2animation
from pyboolnet.interaction_graphs import find_minimal_autonomous_nodes
from pyboolnet.interaction_graphs import add_style_interactionsigns, add_style_activities
from pyboolnet.interaction_graphs import add_style_constants, add_style_inputs, add_style_outputs
from pyboolnet.interaction_graphs import add_style_sccs, add_style_subgraphs
from pyboolnet.digraphs import dot2image, find_outdag
from tests.helpers import get_tests_path_in, get_tests_path_out


def test_find_minimal_autonomous_nodes():
    primes = get_primes("randomnet_n15k3")
    igraph = primes2igraph(primes)
    nodes = find_minimal_autonomous_nodes(igraph, core=set())
    expected = [{"Gene8", "Gene9", "Gene1", "Gene2", "Gene3", "Gene4", "Gene5", "Gene6", "Gene7", "Gene12", "Gene13", "Gene10", "Gene11", "Gene14"}]

    assert expected == nodes


def test_create_image():
    fname = get_tests_path_out(fname="interactiongraphs_create_image.pdf")
    primes = get_primes("raf")
    create_image(primes, fname)


def test_outdag():
    igraph = networkx.DiGraph()
    igraph.add_edges_from([(1, 1), (2, 1), (2, 3), (3, 2), (2, 4), (4, 1), (4, 5), (5, 6), (6, 6), (5, 7)])
    outdag = find_outdag(igraph)

    assert outdag == [7]


def test_activities2animation():
    fname_in = get_tests_path_in(fname="irma.primes")
    fname_out1 = get_tests_path_out(fname="irma*.png")
    fname_out2 = get_tests_path_out(fname="irma.gif")
    primes = read_primes(fname_json=fname_in)
    igraph = primes2igraph(primes)

    activities = [{"gal": 0, "Cbf1": 1, "Gal80": 1, "Ash1": 0, "Gal4": 0, "Swi5": 1},
                  {"gal": 1, "Cbf1": 1, "Gal80": 1, "Ash1": 0, "Gal4": 0, "Swi5": 1},
                  {"gal": 1, "Cbf1": 0, "Gal80": 1, "Ash1": 0, "Gal4": 0, "Swi5": 1},
                  {"gal": 1, "Cbf1": 0, "Gal80": 0, "Ash1": 0, "Gal4": 0, "Swi5": 1},
                  {"gal": 1, "Cbf1": 0, "Gal80": 0, "Ash1": 1, "Gal4": 0, "Swi5": 1},
                  {"gal": 1, "Cbf1": 0, "Gal80": 0, "Ash1": 1, "Gal4": 1, "Swi5": 1},
                  {"gal": 1, "Cbf1": 0, "Gal80": 0, "Ash1": 1, "Gal4": 1, "Swi5": 0},
                  ]

    activities2animation(igraph=igraph, activities=activities, fname_tmp=fname_out1, fname_gif=fname_out2)


def test_primes2igraph1():
    fname_in = get_tests_path_in(fname="interactiongraphs_irma.primes")
    primes = read_primes(fname_json=fname_in)
    igraph = primes2igraph(primes=primes)
    nodes_edges = sorted(igraph.nodes()) + sorted(igraph.edges())
    expected = ["Ash1", "Cbf1", "Gal4", "Gal80", "Swi5", "gal", ("Ash1", "Cbf1"), ("Cbf1", "Ash1"), ("Gal4", "Swi5"),
                ("Gal80", "Gal4"), ("Swi5", "Gal4"), ("gal", "Ash1"), ("gal", "Gal80"), ("gal", "gal")]

    assert nodes_edges == expected


def test_primes2igraph2():
    fname_in = get_tests_path_in(fname="interactiongraphs_irma.primes")
    primes = read_primes(fname_json=fname_in)
    igraph = primes2igraph(primes=primes)
    nodes_edges = sorted(igraph.nodes(data=True)) + sorted(igraph.edges(data=True))
    expected = [("Ash1", {}), ("Cbf1", {}), ("Gal4", {}), ("Gal80", {}), ("Swi5", {}), ("gal", {}),
                ("Ash1", "Cbf1", {"sign": {1}}), ("Cbf1", "Ash1", {"sign": {1}}), ("Gal4", "Swi5", {"sign": {-1}}),
                ("Gal80", "Gal4", {"sign": {1}}), ("Swi5", "Gal4", {"sign": {-1}}), ("gal", "Ash1", {"sign": {1}}),
                ("gal", "Gal80", {"sign": {-1}}), ("gal", "gal", {"sign": {1}})]

    assert nodes_edges == expected


def test_primes2igraph3():
    primes = {"A": [[{"A": 0}], [{"A": 1}]], "B": [[{}], []], "C": [[{"B": 0}], [{"B": 1}]]}
    igraph = primes2igraph(primes=primes)
    nodes_edges = sorted(igraph.nodes(data=True)) + sorted(igraph.edges(data=True))
    expected = [("A", {}), ("B", {}), ("C", {}),
                ("A", "A", {"sign": {1}}), ("B", "C", {"sign": {1}})]

    assert nodes_edges == expected, sorted(igraph.nodes(data=True))+sorted(igraph.edges(data=True))


def test_primes2igraph4():
    primes = {"A": [[{}], []], "B": [[{"B": 0}], [{"B": 1}]], "C": [[{"C": 1}], [{"C": 0}]],
              "D": [[{"B": 0, "C": 0}, {"B": 1, "C": 1}], [{"B": 1, "C": 0}, {"B": 0, "C": 1}]]}
    igraph = primes2igraph(primes=primes)
    nodes_edges = sorted(igraph.nodes(data=True)) + sorted(igraph.edges(data=True))
    expected = [("A", {}), ("B", {}), ("C", {}), ("D", {}), ("B", "B", {"sign": {1}}),
                ("B", "D", {"sign": {1, -1}}), ("C", "C", {"sign": {-1}}), ("C", "D", {"sign": {1, -1}})]

    assert nodes_edges == expected, sorted(igraph.nodes(data=True))+sorted(igraph.edges(data=True))


def test_igraph2dot():
    fname_in = get_tests_path_in(fname="interactiongraphs_irma.primes")
    fname_out = get_tests_path_out(fname="interactiongraphs_igraph2dot.dot")
    primes = read_primes(fname_json=fname_in)
    igraph = primes2igraph(primes=primes)
    igraph2dot(igraph=igraph, fname_dot=fname_out)


def test_igraph2dot_string():
    fname_in = get_tests_path_in(fname="interactiongraphs_irma.primes")
    primes = read_primes(fname_json=fname_in)
    igraph = primes2igraph(primes=primes)
    igraph2dot(igraph=igraph, fname_dot=None)


def test_igraph2image():
    fname_in = get_tests_path_in(fname="interactiongraphs_irma.primes")
    primes = read_primes(fname_json=fname_in)
    igraph = primes2igraph(primes=primes)
    fname_out = get_tests_path_out(fname="interactiongraphs_igraph2image.png")
    igraph2image(igraph=igraph, fname_image=fname_out)


def test_dot2image():
    fname_in = get_tests_path_in(fname="interactiongraphs_topology.dot")
    fname_out1 = get_tests_path_out(fname="interactiongraphs_dot2image1.png")
    fname_out2 = get_tests_path_out(fname="interactiongraphs_dot2image2.svg")
    fname_out3 = get_tests_path_out(fname="interactiongraphs_dot2image3.eps")
    dot2image(fname_dot=fname_in, fname_image=fname_out1)
    dot2image(fname_dot=fname_in, fname_image=fname_out2)
    dot2image(fname_dot=fname_in, fname_image=fname_out3)


def test_styles():
    fname_in = get_tests_path_in(fname="interactiongraphs_topology.primes")
    fname_out_dot = get_tests_path_out(fname="interactiongraphs_style_interactionsigns.dot")
    fname_out_pdf = get_tests_path_out(fname="interactiongraphs_style_interactionsigns.pdf")
    primes = read_primes(fname_json=fname_in)
    igraph = primes2igraph(primes=primes)
    add_style_interactionsigns(igraph=igraph)
    igraph2dot(igraph=igraph, fname_dot=fname_out_dot)
    dot2image(fname_dot=fname_out_dot, fname_image=fname_out_pdf)
    igraph2image(igraph=igraph, fname_image=fname_out_pdf)

    fname_out_dot = get_tests_path_out(fname="interactiongraphs_style_activities.dot")
    fname_out_pdf = get_tests_path_out(fname="interactiongraphs_style_activities.pdf")

    add_style_interactionsigns(igraph=igraph)
    igraph2dot(igraph=igraph, fname_dot=fname_out_dot)
    dot2image(fname_dot=fname_out_dot, fname_image=fname_out_pdf)
    igraph2image(igraph=igraph, fname_image=fname_out_pdf)

    igraph = primes2igraph(primes=primes)
    activities = {"v1": 1, "v2": 0, "v3": 1, "v4": 1, "v5": 1, "v6": 0}
    add_style_activities(igraph=igraph, activities=activities)
    igraph2dot(igraph=igraph, fname_dot=fname_out_dot)
    dot2image(fname_dot=fname_out_dot, fname_image=fname_out_pdf)

    fname_in = get_tests_path_in(fname="interactiongraphs_topology.primes")
    fname_out_dot = get_tests_path_out(fname="interactiongraphs_style_sccs.dot")
    fname_out_pdf = get_tests_path_out(fname="interactiongraphs_style_sccs.pdf")
    primes = read_primes(fname_json=fname_in)

    igraph = primes2igraph(primes=primes)
    add_style_sccs(igraph=igraph)
    igraph2dot(igraph=igraph, fname_dot=fname_out_dot)
    dot2image(fname_dot=fname_out_dot, fname_image=fname_out_pdf)

    fname_in = get_tests_path_in(fname="interactiongraphs_topology.primes")
    fname_out_pdf = get_tests_path_out(fname="interactiongraphs_style_ioc.pdf")
    primes = read_primes(fname_json=fname_in)

    igraph = primes2igraph(primes=primes)
    add_style_inputs(igraph=igraph)
    add_style_constants(igraph=igraph)
    add_style_outputs(igraph=igraph)
    igraph2image(igraph=igraph, fname_image=fname_out_pdf)

    fname_in = get_tests_path_in(fname="interactiongraphs_topology.primes")
    fname_out_pdf = get_tests_path_out(fname="interactiongraphs_style_subgrapghs.pdf")
    fname_out_dot = get_tests_path_out(fname="interactiongraphs_style_subgrapghs.dot")
    primes = read_primes(fname_json=fname_in)

    igraph = primes2igraph(primes=primes)
    subgraphs = [(["v1", "v2"], {}), (["v3", "v4"], {"label": "jo"})]
    add_style_subgraphs(igraph=igraph, subgraphs=subgraphs)
    igraph2dot(igraph=igraph, fname_dot=fname_out_dot)
    dot2image(fname_dot=fname_out_dot, fname_image=fname_out_pdf)
