

import itertools
import logging
from typing import Optional, List

import networkx
import networkx.readwrite.json_graph

from pyboolnet.digraphs import digraph2image
from pyboolnet.helpers import divide_list_into_similar_length_lists
from pyboolnet.helpers import perc2str
from pyboolnet.helpers import save_json_data, copy_json_data, open_json_data
from pyboolnet.model_checking import model_checking_with_acceptingstates
from pyboolnet.prime_implicants import copy_primes
from pyboolnet.state_space import size_state_space
from pyboolnet.state_transition_graphs import UPDATE_STRATEGIES

LETTERS = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

log = logging.getLogger(__name__)


def compute_phenotypes(attractors: dict, markers: List[str], fname_json: Optional[str] = None) -> dict:
    """
    Computes the phenotypes object for given *markers*.

    structure:
        primes: dict
        update: str
        markers: tuple
        phenotypes: (tuple)
            name: str
            pattern: str
            activated_markers: list of markers
            inhibited_markers: list of markers
            stateformula: disjunction over all state props

            states: (tuple)
                str: state string
                dict: state dict
                prop: state proposition
                is_steady: bool
                is_cyclic: bool

                mintrapspace:
                    str: subspace string
                    dict: subspace dict
                    prop: subspace proposition


    **arguments**:
        * *attractors*: json attractor data, see :ref:`attractors_compute_json`
        * *markers*: list of names
        * *fname_json*: save phenotypes as json

    **returns**::
        * *phenotypes*: the phenotypes data

    **example**::

        >>> attractors = compute_attractors(primes, update, "attractors.json")
        >>> markers = ["raf", "mek"]
        >>> compute_phenotypes(attractors, markers, "phenotypes.json")
    """

    assert attractors["is_complete"] == "yes"
    assert all(x["mintrapspace"]["is_univocal"] for x in attractors["attractors"])
    assert all(x["mintrapspace"]["is_faithful"] for x in attractors["attractors"])

    primes = copy_primes(attractors["primes"])

    ignored = [x for x in markers if x not in primes]
    markers = [x for x in markers if x in primes]

    if ignored:
        log.info(f"ignored markers (they are not in primes): {', '.join(ignored)}")

    phenos = {"primes": primes, "update": attractors["update"], "markers": list(markers), "phenotypes": []}

    seen_patterns = []

    i = 0
    for attr in attractors["attractors"]:
        state = {
            "str": str(attr["state"]["str"]),
            "dict": dict(attr["state"]["dict"]),
            "prop": str(attr["state"]["prop"]),
            "is_steady": bool(attr["is_steady"]),
            "is_cyclic": bool(attr["is_cyclic"]),
            "mintrapspace": {
                "str": str(attr["mintrapspace"]["str"]),
                "dict": dict(attr["mintrapspace"]["dict"]),
                "prop": str(attr["mintrapspace"]["prop"])
            }}

        pattern = "".join(str(attr["mintrapspace"]["dict"][x]) if x in attr["mintrapspace"]["dict"] else "-" for x in markers)

        if pattern in seen_patterns:
            for pheno in phenos["phenotypes"]:
                if pheno["pattern"] == pattern:
                    pheno["states"].append(state)
                    break

        else:
            seen_patterns.append(pattern)
            pheno = {}
            if i <= 26:
                pheno["name"] = f"Pheno {LETTERS[i]}"
            else:
                pheno["name"] = f"Pheno {i}"

            i += 1
            pheno["pattern"] = pattern
            pheno["activated_markers"] = sorted(x for x in markers if (x, 1) in attr["mintrapspace"]["dict"].items())
            pheno["inhibited_markers"] = sorted(x for x in markers if (x, 0) in attr["mintrapspace"]["dict"].items())
            pheno["oscillating_markers"] = sorted(x for x in markers if x not in attr["mintrapspace"]["dict"])
            pheno["states"] = [state]
            phenos["phenotypes"].append(pheno)

    for pheno in phenos["phenotypes"]:
        pheno["states"] = tuple(sorted(pheno["states"], key=lambda x: x["mintrapspace"]["str"]))
        pheno["stateformula"] = f"({' | '.join(x['prop'] for x in pheno['states'])})"

    if fname_json:
        save_json_data(data=phenos, fname=fname_json)
        log.info(f"created {fname_json}")

    return phenos


def compute_phenotype_diagram(phenotypes: dict, fname_json: Optional[str] = None, fname_image: Optional[str] = None):
    """
    Computes the phenotype diagram from the phenotypes object obtained from :ref:`phenotypes_compute_json`.
    save the diagram as json data with *fname_json*. useful for e.g. manually renaming nodes.

    **arguments**:
        * *phenotypes*: result of compute_json(..)
        * *fname_json*: save diagram as json
        * *fname_image*: generate image for diagram

    **returns**::
        * *diagram*: the phenotype diagram

    **example**::

        >>> phenos = compute_phenotypes(attrobj, markers)
        >>> compute_phenotype_diagram(phenos, fname_image="phenos.pdf")
        created phenos.pdf
    """

    primes = phenotypes["primes"]
    update = phenotypes["update"]

    assert update in UPDATE_STRATEGIES
    assert primes

    diagram = networkx.DiGraph()
    for key in phenotypes:
        diagram.graph[key] = copy_json_data(phenotypes[key])

    node_id = 0
    flags = [[0, 1]] * len(phenotypes["phenotypes"])
    for i, flags in enumerate(itertools.product(*flags)):

        state_formulas, names = [], []
        for j, flag in enumerate(flags):
            if flag:
                state_formulas.append(phenotypes["phenotypes"][j]["stateformula"])
                names.append(phenotypes["phenotypes"][j]["name"])

        state_formulas.sort()
        names = tuple(sorted(names))

        if not state_formulas:
            unreachable = " & ".join(f"!EF({x['stateformula']})" for x in phenotypes["phenotypes"])
            spec = f"CTLSPEC {unreachable}"

        else:
            reach = [f"EF({x})" for x in state_formulas]
            reach_all = " & ".join(reach)
            reach_some = " | ".join(reach)
            spec = f"CTLSPEC {reach_all} & AG({reach_some})"

        init = "INIT TRUE"
        answer, accepting = model_checking_with_acceptingstates(primes, update, init, spec)

        data = {"names": names,
                "init": init,
                "spec": spec,
                "initaccepting_size": accepting["INITACCEPTING_SIZE"],
                "initaccepting": accepting["INITACCEPTING"]}

        if data["initaccepting_size"] > 0:
            log.info(f"[{', '.join(names)}] = {data['initaccepting_size']}")
            diagram.add_node(node_id)

            for key, value in data.items():
                diagram.nodes[node_id][key] = value

            node_id += 1

    for source in diagram:
        for target in diagram:
            if source == target:
                continue

            source_set = set(diagram.nodes[source]["names"])
            target_set = set(diagram.nodes[target]["names"])

            if target_set.issubset(source_set):
                init = f"INIT {diagram.nodes[source]['initaccepting']}"
                spec = f"CTLSPEC EX({diagram.nodes[target]['initaccepting']})"
                answer, accepting = model_checking_with_acceptingstates(primes, update, init, spec)

                if accepting["INITACCEPTING_SIZE"] > 0:

                    data = {"init": init,
                            "spec": spec,
                            "initaccepting_size": accepting["INITACCEPTING_SIZE"],
                            "initaccepting": accepting["INITACCEPTING"]}

                    diagram.add_edge(source, target)
                    for key, value in data.items():
                        diagram.edges[source, target][key] = value

                    log.info(f"[{', '.join(diagram.nodes[source]['names'])}] --{data['initaccepting_size']}--> [{', '.join(diagram.nodes[target]['names'])}]")

    if fname_image:
        phenotype_diagram2image(diagram, fname_image)

    if fname_json:
        save_phenotype_diagram(diagram=diagram, fname_json=fname_json)
        log.info(f"created {fname_json}")

    return diagram


def save_phenotype_diagram(diagram: networkx.DiGraph, fname_json: str):
    """
    Save the diagram as a json file.

      **arguments**:
        * *diagram*: prime implicants
        * *fname_json*: json file name

      **example**::

        >>> save_phenotype_diagram(diagram, "diagram.json")
    """

    data = networkx.readwrite.json_graph.adjacency_data(diagram)
    save_json_data(data, fname_json)


def open_phenotype_diagram(fname_json: str) -> networkx.DiGraph:
    """
    Opens a phenotype diagram.

    **arguments**:
        * *fname_json*: json file name

    **returns**:
        * *phenotype_diagram*: the phenotype diagram

    **example**::

        >>> open_phenotype_diagram("diagram.json")
    """

    data = open_json_data(fname_json)
    diagram = networkx.readwrite.json_graph.adjacency_graph(data)

    for x in diagram:
        diagram.nodes[x]["names"] = tuple(diagram.nodes[x]["names"])

    return diagram


def phenotype_diagram2image(diagram: networkx.DiGraph, fname_image: Optional[str] = None):
    """
    Creates an image of the abstract commitment diagram.

    **arguments**:
        * *diagram*: a phenotype diagram
        * *fname_image*: name of the diagram image

    **returns**::
        * *styled_diagram*: the styled abstract commitment diagram

    **example**::

        >>> phenotype_diagram2image(primes, diagram, "diagram.pdf")
    """

    assert type(diagram) == type(networkx.DiGraph())

    primes = diagram.graph["primes"]
    size_total = size_state_space(primes)

    image = networkx.DiGraph()
    image.graph["node"] = {
        "shape": "rect",
        "style": "filled",
        "color": "none",
        "fillcolor": "lightgray"}

    image.graph["edge"] = {}
    labels = {}

    for node, data in diagram.nodes(data=True):
        labels[node] = {}
        image.add_node(node)
        head = divide_list_into_similar_length_lists(data["names"])
        head = [",".join(x) for x in head]
        labels[node]["head"] = "<br/>".join(head)

        if "fillcolor" in data:
            image.nodes[node]["fillcolor"] = data["fillcolor"]
        elif len(data["names"]) == 1:
            image.nodes[node]["fillcolor"] = "cornflowerblue"

        if "color" in data:
            image.nodes[node]["color"] = data["color"]

        if "penwidth" in data:
            image.nodes[node]["penwidth"] = data["penwidth"]

    for source, target, data in diagram.edges(data=True):
        image.add_edge(source, target)

    for x in diagram.nodes():
        perc = 100. * diagram.nodes[x]["initaccepting_size"] / size_total
        labels[x]["initaccepting_size"] = f"states: {perc2str(perc)}%"

    for x in diagram.nodes():
        image.nodes[x]['label'] = f"<{'<br/>'.join(labels[x].values())}>"

    ranks = {}
    for node, data in diagram.nodes(data=True):
        x = len(data["names"])
        if x not in ranks:
            ranks[x] = []

        ranks[x].append(node)

    ranks = sorted(ranks.items(), key=lambda x: x[0])

    for _, names in ranks:
        names = [f'"{x}"' for x in names]
        names = "; ".join(names)
        image.graph["{rank = same; %s;}" % names] = ""

    if fname_image:
        digraph2image(image, fname_image, layout_engine="dot")

    return image


def create_phenotypes_piechart(diagram: networkx.DiGraph, fname_image: str, title: Optional[str] = None, color_map: Optional[dict] = None):
    """
    creates the abstract commitment pie.

    **arguments**:
        * *diagram*: a phenotype diagram
        * *fname_image*: name of the output image
        * *title*: optional title of plot
        * *color_map*: assignment of diagram nodes to colors for custom colors

    **example**::

        >>> attractors = compute_attractors(primes, update)
        >>> phenos = compute_phenotypes(attractors, markers)
        >>> diagram = compute_phenotype_diagram(phenos)
        >>> create_phenotypes_piechart(diagram, "piechart.pdf")
    """

    import matplotlib.pyplot

    matplotlib.rcParams['hatch.linewidth'] = 4.0
    matplotlib.rcParams['hatch.color'] = "#ff7c00"

    indices = sorted(diagram, key=lambda x: diagram.nodes[x]["initaccepting_size"])

    labels = [", ".join(diagram.nodes[x]["names"]) for x in indices]
    sizes = [diagram.nodes[x]["initaccepting_size"] for x in indices]

    total = sum(sizes)
    is_small_network = total <= 1024

    figure = matplotlib.pyplot.figure()
    if color_map:
        colors = [color_map[x] for x in indices]
    else:
        colors = [matplotlib.pyplot.cm.rainbow(1. * x / (len(diagram) + 1)) for x in range(len(diagram) + 2)][1:-1]

    for i, x in enumerate(indices):
        if "fillcolor" in diagram.nodes[x]:
            colors[i] = diagram.nodes[x]["fillcolor"]

    auto_percent = (lambda p: f"{p * total / 100:.0f}") if is_small_network else "%.1f%%"
    stuff = matplotlib.pyplot.pie(sizes, explode=None, labels=labels, colors=colors, autopct=auto_percent, shadow=True, startangle=45)
    patches = stuff[0]

    for i, patch in enumerate(patches):
        if "hatch" in diagram.nodes[indices[i]]:
            patch.set_hatch(diagram.nodes[indices[i]]["hatch"])

        elif "fillcolor" in diagram.nodes[indices[i]]:
            patch.set_ec("black")

    matplotlib.pyplot.axis("equal")

    if title is None:
        title = "Phenotype Commitment Sets"

    matplotlib.pyplot.title(title, y=1.08)
    matplotlib.pyplot.tight_layout()
    figure.savefig(fname_image, bbox_inches="tight")
    matplotlib.pyplot.close(figure)
    log.info(f"created {fname_image}")


if __name__=="__main__":

    diagram = networkx.DiGraph()
    diagram.add_node(0, initaccepting_size=2900, names=["GA"], fillcolor="#ff7c00")
    diagram.add_node(1, initaccepting_size=5000, names=["A"], fillcolor="#919191")
    diagram.add_node(2, initaccepting_size=600, names=["OscP/GA"], fillcolor="#c8fbc0", hatch="//", penwidth=3, color="#ff7c00")
    diagram.add_node(3, initaccepting_size=1500, names=["P"], fillcolor="#c8fbc0")

    create_phenotypes_piechart(diagram, fname_image="remy_pie.svg", title="", color_map=None, Silent=False)
























# end of file
