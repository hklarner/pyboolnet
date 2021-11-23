

import functools
import itertools
import logging
import operator
import random
from typing import Optional

import networkx

import pyboolnet.state_space
from pyboolnet import find_command
from pyboolnet.digraphs import add_style_subgraphs, digraph2image
from pyboolnet.digraphs import find_ancestors, find_outdag
from pyboolnet.helpers import copy_json_data, save_json_data, open_json_data
from pyboolnet.helpers import dicts_are_consistent, merge_dicts
from pyboolnet.helpers import perc2str, divide_list_into_similar_length_lists
from pyboolnet.interaction_graphs import primes2igraph
from pyboolnet.model_checking import model_checking
from pyboolnet.prime_implicants import copy_primes, remove_all_variables_except
from pyboolnet.prime_implicants import list_input_combinations, find_inputs
from pyboolnet.state_space import size_state_space, subspace2str
from pyboolnet.state_transition_graphs import UPDATE_STRATEGIES
from pyboolnet.temporal_logic import subspace2proposition

CMD_DOT = find_command("dot")
COMMITMENT_COLORS = ["#8dd3c7", "#ffffb3", "#bebada", "#fb8072", "#80b1d3", "#fdb462", "#b3de69", "#fccde5", "#d9d9d9", "#bc80bd", "#ccebc5"]

log = logging.getLogger(__name__)

try:
    import matplotlib.pyplot
except ImportError:
    log.warning(f"failed to import matplotlib: try to run 'pip3 install matplotlib>=3.3.3'.")


def compute_commitment_diagram(attractors: dict, fname_image: Optional[str] = None, fname_json=None, edge_data=False) -> networkx.DiGraph:
    """
    Computes the commitment diagram for the AttrJson and STG defined in *attractors*, a json object computed by :ref:`AttrJson_compute_json`
    The nodes of the diagram represent states that can reach the exact same subset of *attractors*.
    Edges indicate the existence of a transition between two nodes in the respective commitment sets.
    Edges are labeled by the number of states of the source set that can reach the target set and,
    if *EdgeData* is true, additionally by the size of the border.

    **arguments**:
        * *attractors*: json attractor data, see :ref:`compute_attractors`
        * *fname_image*: generate image for diagram
        * *fname_json*: save diagram as json
        * *edge_data*: toggles computation of additional edge data

    **returns**::
        * *diagram*: the commitment diagram

    **example**::

        >>> attractors = compute_attractors(primes, update)
        >>> diagram = compute_phenotype_diagram(attractors)
    """

    primes = attractors["primes"]
    update = attractors["update"]

    subspaces = []
    for x in attractors["attractors"]:
        if x["min_trap_space"]["is_univocal"] and x["min_trap_space"]["is_faithful"]:
            subspaces.append(x["min_trap_space"]["dict"])
        else:
            subspaces.append(x["state"]["dict"])

    log.info("Commitment.compute_diagram(..)")

    size_total = size_state_space(primes)

    if len(subspaces) == 1:
        log.info(" single attractor, trivial case.")
        diagram = networkx.DiGraph()
        counter_mc = 0

        diagram.add_node("0")
        diagram.nodes["0"]["attractors"] = subspaces
        diagram.nodes["0"]["size"] = size_total
        diagram.nodes["0"]["formula"] = "TRUE"

    else:
        igraph = primes2igraph(primes)
        outdag = find_outdag(igraph)

        attractor_nodes = [x for A in subspaces for x in A]
        critical_nodes = find_ancestors(igraph, attractor_nodes)
        outdag = [x for x in outdag if x not in critical_nodes]

        igraph.remove_nodes_from(outdag)
        log.info(f"excluding the non-critical out-dag nodes {outdag}")

        components = networkx.connected_components(igraph.to_undirected())
        components = [list(x) for x in components]
        log.info(f"working on {len(components)} connected component(s)")

        counter_mc = 0
        diagrams = []
        for component in components:
            sub_primes = copy_primes(primes)
            remove_all_variables_except(sub_primes, component)
            attractors_projected = _project_attractors(subspaces, component)
            diagram, count = _compute_diagram_component(sub_primes, update, attractors_projected, edge_data)
            counter_mc += count
            diagrams.append(diagram)

        factor = 2**len(outdag)
        diagram = _cartesian_product_of_diagrams(diagrams, factor, edge_data)

        for x in attractors:
            diagram.graph[x] = copy_json_data(attractors[x])

        nodes_sum = 0
        for x in diagram.nodes():
            projection = diagram.nodes[x]["attractors"]
            diagram.nodes[x]["attractors"] = _lift_attractors(subspaces, projection)
            nodes_sum += diagram.nodes[x]["size"]

        if not nodes_sum == size_total:
            log.warning("commitment diagram does not partition the state space, this may be due to rounding of large numbers.")

        sorted_ids = sorted(diagram, key=lambda x: diagram.nodes[x]["formula"])
        mapping = {x: str(sorted_ids.index(x)) for x in diagram}
        networkx.relabel_nodes(diagram, mapping, copy=False)

    log.info(f"total executions of NuSMV: {counter_mc}")

    if fname_image:
        commitment_diagram2image(diagram, fname_image=fname_image, style_inputs=True, style_edges=edge_data, style_ranks=True, first_index=1)

    if fname_json:
        save_commitment_diagram(diagram, fname_json)

    return diagram


def save_commitment_diagram(diagram: networkx.DiGraph, fname_json: str):
    """
    Saves a commitment diagram as a json file.

    **arguments**:
        * *diagram*: a commitment diagram
        * *fname_json*: json file name

    **example**::

        >>> save_commitment_diagram(diagram, "commitment_diagram.json")
    """

    data = networkx.readwrite.json_graph.adjacency_data(diagram)
    save_json_data(data, fname_json)


def open_commitment_diagram(fname_json: str) -> networkx.DiGraph:
    """
    Opens a commitment diagram json file.
    See also :ref:`commitment_compute_diagram`, :ref:`commitment_save_diagram`.

    **arguments**:
        * *fname_json*: a json file name

    **returns**:
        * *diagram*: the commitment diagram

    **example**::

        >>> diagram = open_commitment_diagram("commitment_diagram.json")
    """

    data = open_json_data(fname_json)
    diagram = networkx.readwrite.json_graph.adjacency_graph(data)
    for edge in diagram.edges:
        if "id" in diagram.edges[edge]:
            diagram.edges[edge].pop("id")

    return diagram


def _compute_diagram_component(primes: dict, update: str, subspaces, edge_data: bool):
    """
    Computes the commitment diagram but without removing out-DAGs or considering connected components separately.
    """

    assert update in UPDATE_STRATEGIES
    assert primes

    counter_mc = 0
    node_id = 0
    worst_case_nodes = 0
    inputs = find_inputs(primes)
    states_per_case = pyboolnet.state_space.size_state_space(primes, fixed_inputs=True)
    diagram = networkx.DiGraph()
    log.info("_compute_diagram_component(..)")
    log.info(f"inputs: {len(inputs)} ({', '.join(inputs)})")
    log.info(f"combinations:  {2**len(inputs)}")

    for i, combination in enumerate(list_input_combinations(primes)):
        attr = [x for x in subspaces if pyboolnet.state_space.is_subspace(primes, this=x, other=combination)]
        worst_case_nodes += 2 ** len(attr) - 1
        states_covered = 0
        specs = [subspace2proposition(primes, x) for x in attr]
        vectors = len(attr) * [[0, 1]]
        vectors = list(itertools.product(*vectors))
        random.shuffle(vectors)
        combination_formula = subspace2proposition(primes, combination)

        log.info(f"input combination {i}, worst case #nodes: {2 ** len(attr) - 1}")

        for vector in vectors:
            if sum(vector) == 0: continue
            if states_covered == states_per_case:
                log.info("avoided executions of NuSMV due to state counting")
                break

            if len(vector) == 1:
                data = {"attractors": attr, "size": states_per_case, "formula": combination_formula}

            else:
                init = f"INIT {combination_formula}"
                reach = [f"EF({x})" for flag, x in zip(vector, specs) if flag]
                reach_all = " & ".join(reach)
                reach_some = " | ".join(reach)
                spec = f"CTLSPEC {reach_all} & AG({reach_some})"

                answer, accepting_states = model_checking(primes, update, init, spec, enable_accepting_states=True)
                counter_mc += 1

                data = {
                    "attractors": [x for flag,x in zip(vector, attr) if flag],
                    "size": accepting_states["INITACCEPTING_SIZE"],
                    "formula": accepting_states["INITACCEPTING"]}

            if data["size"] > 0:
                diagram.add_node(node_id)
                for key, value in data.items():
                    diagram.nodes[node_id][key] = value

                node_id += 1
                states_covered += data["size"]

    perc = f"= {(100 * diagram.order() / worst_case_nodes)}" if worst_case_nodes else ""
    log.info(f"worst case #nodes: {worst_case_nodes}")
    log.info(f"actual nodes: {diagram.order()} {perc}")

    potential_targets = {}
    for source, source_data in diagram.nodes(data=True):
        successors = []

        for target, target_data in diagram.nodes(data=True):
            if source == target:
                continue

            if all(x in source_data["attractors"] for x in target_data["attractors"]):
                successors.append((target, target_data))

        potential_targets[source] = successors

    worst_case_edges = sum(len(x) for x in potential_targets.values())
    log.info(f"worst case #edges: {worst_case_edges}")

    for source, source_data in diagram.nodes(data=True):
        for target, target_data in potential_targets[source]:
            init = f"INIT {source_data['formula']}"
            spec = f"CTLSPEC EX({target_data['formula']})"
            answer, accepting_states = model_checking(primes, update, init, spec, enable_accepting_states=True)
            counter_mc += 1
            data = {"EX_size": accepting_states["INITACCEPTING_SIZE"], "EX_formula": accepting_states["INITACCEPTING"]}

            if data["EX_size"] > 0:

                if edge_data:
                    if len(potential_targets[source]) == 1:
                        data["EF_size"] = source_data["size"]
                        data["EF_formula"] = source_data["formula"]

                    else:
                        spec = f"CTLSPEC E[{source_data['formula']} U {target_data['formula']}]"
                        answer, accepting_states = model_checking(primes, update, init, spec, enable_accepting_states=True)
                        counter_mc += 1

                        data["EF_size"] = accepting_states["INITACCEPTING_SIZE"]
                        data["EF_formula"] = accepting_states["INITACCEPTING"]

                diagram.add_edge(source, target)
                for key, value in data.items():
                    diagram.edges[source, target][key] = value

    perc = f"= {100 * diagram.size() / worst_case_edges:.2f}%" if worst_case_edges else ""
    log.info(f"actual edges: {diagram.size()} {perc}")
    log.info(f"total executions of NuSMV: {counter_mc}")

    return diagram, counter_mc


def commitment_diagram2image(
        diagram: networkx.DiGraph,
        fname_image: str,
        style_inputs: bool = True,
        style_edges: bool = False,
        style_ranks: bool = True,
        first_index: int = 1) -> networkx.DiGraph:
    """
    Creates the image file *fname_image* for the basin diagram given by *diagram*.
    The flag *StyleInputs* can be used to highlight which basins belong to which input combination.
    *style_edges* adds edge labels that indicate the size of the "border" (if *compute_border* was enabled in :ref:`commitment_compute_diagram`)
    and the size of the states of the source basin that can reach the target basin.

    **arguments**:
        * *diagram*: a commitment diagram
        * *fname_image*: file name of image
        * *style_inputs*: whether basins should be grouped by input combinations
        * *style_edges*: whether edges should be size of border / reachable states
        * *style_ranks*: style that places nodes with the same number of reachable attractors on the same rank (level)
        * *first_index*: first index of attractor names

    **returns**::
        * *styled_diagram*: the styled commitment diagram

    **example**::

        >>> attractors = compute_attractors(primes, update)
        >>> compute_phenotype_diagram(attractors)
        >>> commitment_diagram2image(diagram, "diagram.pdf")
    """

    primes = diagram.graph["primes"]
    size_total = pyboolnet.state_space.size_state_space(primes)
    size_per_input_combination = pyboolnet.state_space.size_state_space(primes, fixed_inputs=True)
    is_small_network = size_total <= 1024

    digraph = networkx.DiGraph()
    digraph.graph["node"] = {"shape": "rect", "style": "filled", "color": "none"}
    digraph.graph["edge"] = {}

    if style_inputs:
        digraph.graph["node"]["fillcolor"] = "grey95"
    else:
        digraph.graph["node"]["fillcolor"] = "lightgray"

    attractors = [x["attractors"] for _, x in diagram.nodes(data=True)]
    attractors = [x for x in attractors if len(x) == 1]
    attractors = set(subspace2str(primes, x[0]) for x in attractors)
    attractors = sorted(attractors)

    labels = {}
    # "labels" is used for node labels
    # keys:
    # head = reachable attractors
    # size = number of states in % (depends on StyleInputs)

    for node, data in diagram.nodes(data=True):
        labels[node] = {}
        digraph.add_node(node)

        if len(data["attractors"]) == 1:
            digraph.nodes[node]["fillcolor"] = "cornflowerblue"

            attr = subspace2str(primes, data["attractors"][0])
            index = attractors.index(attr) + first_index
            labels[node]["head"] = f'A{index} = <font face="Courier New">{attr}</font>'

        else:
            head = sorted(f"A{attractors.index(subspace2str(primes, x)) + first_index}" for x in data["attractors"])
            head = divide_list_into_similar_length_lists(head)
            head = [",".join(x) for x in head]
            labels[node]["head"] = "<br/>".join(head)

        if "fillcolor" in data:
            digraph.nodes[node]["fillcolor"] = data["fillcolor"]

    for source, target, data in diagram.edges(data=True):
        digraph.add_edge(source, target)

        if style_edges:
            edge_label = []

            #perc = 100.* data["EX_size"] / Diagram.nodes[source]["size"]
            #edge_label.append("EX: %s%%"%perc2str(perc))

            if "EF_size" in data:
                #perc = 100.* data["EF_size"] / Diagram.nodes[source]["size"]
                #edge_label.append("EF: %s%%"%perc2str(perc))

                if data["EF_size"] < diagram.nodes[source]["size"]:
                    digraph.adj[source][target]["color"] = "lightgray"

            #result.adj[source][target]["label"] = "<%s>"%("<br/>".join(edge_label))

    for x in diagram.nodes():
        if is_small_network:
            labels[x]["size"] = f"states: {diagram.nodes[x]['size']}"
        else:
            perc = 100. * diagram.nodes[x]["size"] / size_total
            labels[x]["size"] = f"states: {perc2str(perc)}%"

    subgraphs = []
    if style_inputs:
        for inputs in list_input_combinations(primes):
            if not inputs:
                continue

            nodes = [x for x in diagram.nodes() if dicts_are_consistent(inputs, diagram.nodes[x]["attractors"][0])]
            label = subspace2str(primes, inputs)
            subgraphs.append((nodes, {"label": f"inputs: {label}", "color": "none", "fillcolor": "lightgray"}))

            for x in nodes:
                perc = 100. * diagram.nodes[x]["size"] / size_per_input_combination
                labels[x]["size"] = f"states: {perc2str(perc)}%"

        if subgraphs:
            digraph.graph["subgraphs"] = []
            add_style_subgraphs(digraph, subgraphs)

    for x in diagram.nodes():
        digraph.nodes[x]['label'] = f"<{'<br/>'.join(labels[x].values())}>"

    if style_ranks:
        if subgraphs:
            to_rank = digraph.graph["subgraphs"]
        else:
            to_rank = [digraph]

        for graph in to_rank:
            ranks = {}
            for node, data in diagram.nodes(data=True):
                if node not in graph:
                    continue

                size = len(data["attractors"])
                if size not in ranks:
                    ranks[size] = []

                ranks[size].append(node)

            ranks = list(ranks.items())
            ranks.sort(key=lambda x: x[0])

            for _, names in ranks:
                names = [f'"{x}"' for x in names]
                graph.graph[f"{{rank = same; {'; '.join(names)};}}"] = ""

    if fname_image:
        digraph2image(digraph, fname_image, layout_engine="dot")

    return digraph


def create_commitment_piechart(diagram: networkx.DiGraph, fname_image: str, color_map: Optional[dict] = None, title: Optional[str] = None):
    """
    Creates the commitment pie chart for the commitment diagram using matplotlib.
    The pieces of the chart represent states that can reach the exact same subset of *Attractors*.

    **arguments**:
        * *diagram*: commitment diagram, see :ref:`commitment_compute_diagram`
        * *fname_image*: name of the output image
        * *color_map*: assignment of diagram nodes to colors for custom colors
        * *title*: optional title of plot

    **example**::

        >>> primes = get_primes("xiao_wnt5a")
        >>> attractors = compute_attractors(primes, update)
        >>> diagram = compute_commitment_diagram(attractors)
        >>> create_commitment_piechart(diagram, "commitment_piechart.pdf")
    """

    primes = diagram.graph["primes"]
    total = pyboolnet.state_space.size_state_space(primes)
    is_small_network = total <= 1024
    indices = sorted(diagram, key=lambda x: len(diagram.nodes[x]["attractors"]))

    labels = []
    for x in indices:
        label = sorted(subspace2str(primes, y) for y in diagram.nodes[x]["attractors"])
        labels.append("\n".join(label))

    sizes = [diagram.nodes[x]["size"] for x in indices]
    figure = matplotlib.pyplot.figure()

    if color_map:
        colors = [color_map[x] for x in indices]
    else:
        colors = [matplotlib.pyplot.cm.rainbow(1. * x / (len(diagram) + 1)) for x in range(len(diagram) + 2)][1:-1]

    for i, x in enumerate(indices):
        if "fillcolor" in diagram.nodes[x]:
            colors[i] = diagram.nodes[x]["fillcolor"]

    if is_small_network:
        auto_percent = lambda p: f"{{{p * total / 100:.0f}}}"
    else:
        auto_percent = lambda p: f"{{{p:1.1f}}}%"

    stuff = matplotlib.pyplot.pie(sizes, explode=None, labels=labels, colors=colors, autopct=auto_percent, shadow=True, startangle=140)
    patches = stuff[0]

    for i, patch in enumerate(patches):
        patch.set_ec("black")

    matplotlib.pyplot.axis("equal")

    if not title:
        title = "Commitment Sets"

    matplotlib.pyplot.title(title, y=1.08)
    matplotlib.pyplot.tight_layout()

    figure.savefig(fname_image, bbox_inches='tight')
    log.info(f"created {fname_image}")
    matplotlib.pyplot.close(figure)


def _project_attractors(attractors, names):
    result = set()
    for space in attractors:
        projection = tuple((k, v) for k, v in sorted(space.items()) if k in names)
        result.add(projection)

    result = [dict(x) for x in result]

    return result


def _lift_attractors(attractors, projection):
    return [x for x in attractors for y in projection if dicts_are_consistent(x, y)]


def _cartesian_product_of_diagrams(diagrams, factor, edge_data):
    result = networkx.DiGraph()
    nodes = [x.nodes(data=True) for x in diagrams]

    for product in itertools.product(*nodes):
        data = {
            "size": functools.reduce(operator.mul, [x["size"] for _, x in product]) * factor,
            "formula": " & ".join(f"({x['formula']})" for _, x in product)}

        attractors = [x["attractors"] for _, x in product]
        attractors = list(itertools.product(*attractors))
        attractors = [merge_dicts(x) for x in attractors]
        data["attractors"] = attractors

        node = tuple(x for x, _ in product)

        result.add_node(node)
        for key, value in data.items():
            result.nodes[node][key] = value

    for source in result.nodes():
        for s, diagram in zip(source, diagrams):
            factor = result.nodes[source]["size"] / diagram.nodes[s]["size"]
            for _, t, data in diagram.out_edges(s, data=True):

                data = {}
                basic_formula = ["(%s)" % g.nodes[x]["formula"] for x,g in zip(source, diagrams) if not g == diagram]
                data["EX_size"] = factor * diagram.adj[s][t]["EX_size"]
                formula = basic_formula + [f"({diagram.adj[s][t]['EX_formula']})"]
                data["EX_formula"] = " & ".join(formula)

                if edge_data:
                    data["EF_size"] = factor * diagram.adj[s][t]["EF_size"]
                    formula = basic_formula + [f"({diagram.adj[s][t]['EF_formula']})"]
                    data["EF_formula"] = " & ".join(formula)

                target = tuple(x if g != diagram else t for x, g in zip(source, diagrams))

                result.add_edge(source, target)
                for key, value in data.items():
                    result.edges[source, target][key] = value

    result = networkx.convert_node_labels_to_integers(result)

    return result


def commitment_diagrams_are_equivalent(this: networkx.DiGraph, other: networkx.DiGraph) -> bool:
    """
    Checks whether diagrams *this* and *other* are equivalent.
    """

    g1 = this.copy()
    g2 = other.copy()

    for g in [g1, g2]:
        for x in g.nodes():
            g.nodes[x].pop("formula")

        for x, y in g.edges():
            if "border_formula" in g.adj[x][y]:
                g.adj[x][y].pop("border_formula")
                g.adj[x][y].pop("finally_formula")

    return networkx.is_isomorphic(g1, g2, edge_match=lambda x, y: x == y)
