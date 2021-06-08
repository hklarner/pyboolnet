

import os
import networkx

import PyBoolNet


FILES_IN = os.path.join(os.path.dirname(__file__), "files_input")
FILES_OUT = os.path.join(os.path.dirname(__file__), "files_output")


def test_find_minimal_autonomous_nodes():
    primes = PyBoolNet.Repository.get_primes("randomnet_n15k3")
    igraph = PyBoolNet.interaction_graphs.primes2igraph(primes)
    nodes = PyBoolNet.interaction_graphs.find_minimal_autonomous_nodes(igraph)
    expected = [{"Gene8", "Gene9", "Gene1", "Gene2", "Gene3", "Gene4", "Gene5", "Gene6", "Gene7", "Gene12", "Gene13", "Gene10", "Gene11", "Gene14"}]

    assert expected == nodes


def test_create_image():
    fname = os.path.join(FILES_OUT, "interactiongraphs_create_image.pdf")
    primes = PyBoolNet.Repository.get_primes("raf")
    PyBoolNet.interaction_graphs.create_image(primes, fname)


def test_outdag():
    igraph = networkx.DiGraph()
    igraph.add_edges_from([(1, 1), (2, 1), (2, 3), (3, 2), (2, 4), (4, 1), (4, 5), (5, 6), (6, 6), (5, 7)])
    outdag = PyBoolNet.interaction_graphs.find_outdag(igraph)

    assert outdag == [7]


def test_activities2animation():
    fname_in = os.path.join(FILES_IN,  "irma.primes")
    fname_out1 = os.path.join(FILES_OUT, "irma*.png")
    fname_out2 = os.path.join(FILES_OUT, "irma.gif")
    primes = PyBoolNet.file_exchange.read_primes(FnamePRIMES=fname_in)
    igraph = PyBoolNet.interaction_graphs.primes2igraph(primes)

    activities = [{"gal": 0, "Cbf1": 1, "Gal80": 1, "Ash1": 0, "Gal4": 0, "Swi5": 1},
                  {"gal": 1, "Cbf1": 1, "Gal80": 1, "Ash1": 0, "Gal4": 0, "Swi5": 1},
                  {"gal": 1, "Cbf1": 0, "Gal80": 1, "Ash1": 0, "Gal4": 0, "Swi5": 1},
                  {"gal": 1, "Cbf1": 0, "Gal80": 0, "Ash1": 0, "Gal4": 0, "Swi5": 1},
                  {"gal": 1, "Cbf1": 0, "Gal80": 0, "Ash1": 1, "Gal4": 0, "Swi5": 1},
                  {"gal": 1, "Cbf1": 0, "Gal80": 0, "Ash1": 1, "Gal4": 1, "Swi5": 1},
                  {"gal": 1, "Cbf1": 0, "Gal80": 0, "Ash1": 1, "Gal4": 1, "Swi5": 0},
                  ]

    PyBoolNet.interaction_graphs.activities2animation(IGraph=igraph, Activities=activities, FnameTMP=fname_out1, FnameGIF=fname_out2)


def test_primes2igraph1():
    fname_in = os.path.join(FILES_IN, "interactiongraphs_irma.primes")
    primes = PyBoolNet.file_exchange.read_primes(FnamePRIMES=fname_in)

    igraph = PyBoolNet.interaction_graphs.primes2igraph(primes=primes)
    nodes_edges = sorted(igraph.nodes()) + sorted(igraph.edges())
    expected = ["Ash1", "Cbf1", "Gal4", "Gal80", "Swi5", "gal", ("Ash1", "Cbf1"), ("Cbf1", "Ash1"), ("Gal4", "Swi5"),
                ("Gal80", "Gal4"), ("Swi5", "Gal4"), ("gal", "Ash1"), ("gal", "Gal80"), ("gal", "gal")]

    assert nodes_edges == expected


def test_primes2igraph2():
    fname_in = os.path.join(FILES_IN, "interactiongraphs_irma.primes")
    primes = PyBoolNet.file_exchange.read_primes(FnamePRIMES=fname_in)

    igraph = PyBoolNet.interaction_graphs.primes2igraph(primes=primes)
    nodes_edges = sorted(igraph.nodes(data=True)) + sorted(igraph.edges(data=True))
    expected = [("Ash1", {}), ("Cbf1", {}), ("Gal4", {}), ("Gal80", {}), ("Swi5", {}), ("gal", {}),
                ("Ash1", "Cbf1", {"sign": {1}}), ("Cbf1", "Ash1", {"sign": {1}}), ("Gal4", "Swi5", {"sign": {-1}}),
                ("Gal80", "Gal4", {"sign": {1}}), ("Swi5", "Gal4", {"sign": {-1}}), ("gal", "Ash1", {"sign": {1}}),
                ("gal", "Gal80", {"sign": {-1}}), ("gal", "gal", {"sign": {1}})]

    assert nodes_edges == expected


def test_primes2igraph3():
    primes = {"A": [[{"A": 0}], [{"A": 1}]], "B": [[{}], []], "C": [[{"B": 0}], [{"B": 1}]]}

    igraph = PyBoolNet.interaction_graphs.primes2igraph(primes=primes)
    nodes_edges = sorted(igraph.nodes(data=True)) + sorted(igraph.edges(data=True))
    expected = [("A", {}), ("B", {}), ("C", {}),
                ("A", "A", {"sign": {1}}), ("B", "C", {"sign": {1}})]

    assert nodes_edges == expected, sorted(igraph.nodes(data=True))+sorted(igraph.edges(data=True))


def test_primes2igraph4():
    primes = {"A": [[{}], []], "B": [[{"B": 0}], [{"B": 1}]], "C": [[{"C": 1}], [{"C": 0}]],
              "D": [[{"B": 0, "C": 0}, {"B": 1, "C": 1}], [{"B": 1, "C": 0}, {"B": 0, "C": 1}]]}

    igraph = PyBoolNet.interaction_graphs.primes2igraph(primes=primes)
    nodes_edges = sorted(igraph.nodes(data=True)) + sorted(igraph.edges(data=True))
    expected = [("A", {}), ("B", {}), ("C", {}), ("D", {}), ("B", "B", {"sign": {1}}),
                ("B", "D", {"sign": {1, -1}}), ("C", "C", {"sign": {-1}}), ("C", "D", {"sign": {1, -1}})]

    assert nodes_edges == expected, sorted(igraph.nodes(data=True))+sorted(igraph.edges(data=True))


def test_igraph2dot():
    fname_in = os.path.join(FILES_IN, "interactiongraphs_irma.primes")
    fname_out = os.path.join(FILES_OUT, "interactiongraphs_igraph2dot.dot")
    primes = PyBoolNet.file_exchange.read_primes(FnamePRIMES=fname_in)

    igraph = PyBoolNet.interaction_graphs.primes2igraph(primes=primes)
    PyBoolNet.interaction_graphs.igraph2dot(IGraph=igraph, FnameDOT=fname_out)


def test_igraph2dot_string():
    fname_in = os.path.join(FILES_IN, "interactiongraphs_irma.primes")
    primes = PyBoolNet.file_exchange.read_primes(FnamePRIMES=fname_in)

    igraph = PyBoolNet.interaction_graphs.primes2igraph(primes=primes)
    PyBoolNet.interaction_graphs.igraph2dot(IGraph=igraph, FnameDOT=None)


def test_igraph2image():
    fname_in = os.path.join(FILES_IN, "interactiongraphs_irma.primes")
    primes = PyBoolNet.file_exchange.read_primes(FnamePRIMES=fname_in)

    igraph = PyBoolNet.interaction_graphs.primes2igraph(primes=primes)
    fname_out = os.path.join(FILES_OUT, "interactiongraphs_igraph2image.png")
    PyBoolNet.interaction_graphs.igraph2image(IGraph=igraph, FnameIMAGE=fname_out)


def test_dot2image():
    fname_in = os.path.join(FILES_IN, "interactiongraphs_topology.dot")
    fname_out1 = os.path.join(FILES_OUT, "interactiongraphs_dot2image1.png")
    fname_out2 = os.path.join(FILES_OUT, "interactiongraphs_dot2image2.svg")
    fname_out3 = os.path.join(FILES_OUT, "interactiongraphs_dot2image3.eps")

    PyBoolNet.interaction_graphs.dot2image(FnameDOT=fname_in, FnameIMAGE=fname_out1)
    PyBoolNet.interaction_graphs.dot2image(FnameDOT=fname_in, FnameIMAGE=fname_out2)
    PyBoolNet.interaction_graphs.dot2image(FnameDOT=fname_in, FnameIMAGE=fname_out3)


def test_styles():
    fname_in = os.path.join(FILES_IN, "interactiongraphs_topology.primes")
    fname_out_dot = os.path.join(FILES_OUT, "interactiongraphs_style_interactionsigns.dot")
    fname_out_pdf = os.path.join(FILES_OUT, "interactiongraphs_style_interactionsigns.pdf")
    primes = PyBoolNet.file_exchange.read_primes(FnamePRIMES=fname_in)

    igraph = PyBoolNet.interaction_graphs.primes2igraph(primes=primes)
    PyBoolNet.interaction_graphs.add_style_interactionsigns(IGraph=igraph)
    PyBoolNet.interaction_graphs.igraph2dot(IGraph=igraph, FnameDOT=fname_out_dot)
    PyBoolNet.interaction_graphs.dot2image(FnameDOT=fname_out_dot, FnameIMAGE=fname_out_pdf)
    PyBoolNet.interaction_graphs.igraph2image(IGraph=igraph, FnameIMAGE=fname_out_pdf)

    fname_out_dot = os.path.join(FILES_OUT, "interactiongraphs_style_activities.dot")
    fname_out_pdf = os.path.join(FILES_OUT, "interactiongraphs_style_activities.pdf")

    PyBoolNet.interaction_graphs.add_style_interactionsigns(IGraph=igraph)
    PyBoolNet.interaction_graphs.igraph2dot(IGraph=igraph, FnameDOT=fname_out_dot)
    PyBoolNet.interaction_graphs.dot2image(FnameDOT=fname_out_dot, FnameIMAGE=fname_out_pdf)
    PyBoolNet.interaction_graphs.igraph2image(IGraph=igraph, FnameIMAGE=fname_out_pdf)

    igraph = PyBoolNet.interaction_graphs.primes2igraph(primes=primes)
    activities = {"v1": 1, "v2": 0, "v3": 1, "v4": 1, "v5": 1, "v6": 0}
    PyBoolNet.interaction_graphs.add_style_activities(IGraph=igraph, Activities=activities)
    PyBoolNet.interaction_graphs.igraph2dot(IGraph=igraph, FnameDOT=fname_out_dot)
    PyBoolNet.interaction_graphs.dot2image(FnameDOT=fname_out_dot, FnameIMAGE=fname_out_pdf)

    fname_in = os.path.join(FILES_IN, "interactiongraphs_topology.primes")
    fname_out_dot = os.path.join(FILES_OUT, "interactiongraphs_style_sccs.dot")
    fname_out_pdf = os.path.join(FILES_OUT, "interactiongraphs_style_sccs.pdf")
    primes = PyBoolNet.file_exchange.read_primes(FnamePRIMES=fname_in)

    igraph = PyBoolNet.interaction_graphs.primes2igraph(primes=primes)
    PyBoolNet.interaction_graphs.add_style_sccs(IGraph=igraph)
    PyBoolNet.interaction_graphs.igraph2dot(IGraph=igraph, FnameDOT=fname_out_dot)
    PyBoolNet.interaction_graphs.dot2image(FnameDOT=fname_out_dot, FnameIMAGE=fname_out_pdf)

    fname_in = os.path.join(FILES_IN, "interactiongraphs_topology.primes")
    fname_out_pdf = os.path.join(FILES_OUT, "interactiongraphs_style_ioc.pdf")
    primes = PyBoolNet.file_exchange.read_primes(FnamePRIMES=fname_in)

    igraph = PyBoolNet.interaction_graphs.primes2igraph(primes=primes)
    PyBoolNet.interaction_graphs.add_style_inputs(IGraph=igraph)
    PyBoolNet.interaction_graphs.add_style_constants(IGraph=igraph)
    PyBoolNet.interaction_graphs.add_style_outputs(IGraph=igraph)
    PyBoolNet.interaction_graphs.igraph2image(IGraph=igraph, FnameIMAGE=fname_out_pdf)

    fname_in = os.path.join(FILES_IN, "interactiongraphs_topology.primes")
    fname_out_pdf = os.path.join(FILES_OUT, "interactiongraphs_style_subgrapghs.pdf")
    fname_out_dot = os.path.join(FILES_OUT, "interactiongraphs_style_subgrapghs.dot")
    primes = PyBoolNet.file_exchange.read_primes(FnamePRIMES=fname_in)

    igraph = PyBoolNet.interaction_graphs.primes2igraph(primes=primes)
    subgraphs = [(["v1", "v2"], {}), (["v3", "v4"], {"label": "jo"})]
    PyBoolNet.interaction_graphs.add_style_subgraphs(IGraph=igraph, Subgraphs=subgraphs)
    PyBoolNet.interaction_graphs.igraph2dot(IGraph=igraph, FnameDOT=fname_out_dot)
    PyBoolNet.interaction_graphs.dot2image(FnameDOT=fname_out_dot, FnameIMAGE=fname_out_pdf)
