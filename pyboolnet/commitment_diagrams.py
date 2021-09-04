

import os
import logging
import itertools
import random
import operator
import functools
import networkx
from typing import Optional

import pyboolnet.state_space
from pyboolnet import find_command
from pyboolnet.helpers import perc2str
from pyboolnet.prime_implicants import input_combinations
from pyboolnet.state_space import size_state_space
from pyboolnet.interaction_graphs import primes2igraph
from pyboolnet.digraphs import ancestors, find_outdag
from pyboolnet.prime_implicants import copy_primes, remove_all_variables_except
from pyboolnet.helpers import copy_json_data, save_json_data, open_json_data

CMD_DOT = find_command("dot")
COMMITMENT_COLORS = ["#8dd3c7", "#ffffb3", "#bebada", "#fb8072", "#80b1d3", "#fdb462", "#b3de69", "#fccde5", "#d9d9d9", "#bc80bd", "#ccebc5"]

log = logging.getLogger(__name__)


def compute_commitment_diagram(attractors: dict, fname_image: Optional[str] = None, fname_json=None, edge_data=False) -> networkx.DiGraph:
    """
     Computes the commitment diagram for the AttrJson and STG defined in *attractors*, a json object computed by :ref:`AttrJson_compute_json`
    The nodes of the diagram represent states that can reach the exact same subset of *attractors*.
    Edges indicate the existence of a transition between two nodes in the respective commitment sets.
    Edges are labeled by the number of states of the source set that can reach the target set and,
    if *EdgeData* is true, additionally by the size of the border.

    **arguments**:
        * *attractors*: json attractor data, see :ref:`AttrJson_compute_json`
        * *fname_image*: generate image for diagram
        * *fname_json*: save diagram as json
        * *edge_data*: toggles computation of additional edge data

    **returns**::
        * *diagram*: the commitment diagram

    **example**::

        >>> attrs = attractors.compute_attractors(primes, update)
        >>> diagram = Commitment.compute_phenotype_diagram(attrs)
    """

    primes = attractors["primes"]
    update = attractors["update"]

    subspaces = []
    for x in attractors["attractors"]:
        if x["mintrapspace"]["is_univocal"] and x["mintrapspace"]["is_faithful"]:
            subspaces.append(x["mintrapspace"]["dict"])
        else:
            subspaces.append(x["state"]["dict"])

    log.info("Commitment.compute_diagram(..)")

    size_total = size_state_space(primes)

    if len(subspaces)==1:
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
        critical_nodes = ancestors(igraph, attractor_nodes)
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
            attrs_projected = project_attractors(subspaces, component)
            diagram, count = _compute_diagram_component(sub_primes, update, attrs_projected, edge_data)
            counter_mc += count
            diagrams.append(diagram)

        factor = 2**len(outdag)
        diagram = cartesian_product(diagrams, factor, edge_data)

        for x in attractors:
            diagram.graph[x] = copy_json_data(attractors[x])

        nodes_sum = 0
        for x in diagram.nodes():
            projection = diagram.nodes[x]["attractors"]
            diagram.nodes[x]["attractors"] = lift_attractors(subspaces, projection)
            nodes_sum += diagram.nodes[x]["size"]

        if not nodes_sum == size_total:
            log.warning("commitment diagram does not partition the state space, this may be due to rounding of large numbers.")

        sorted_ids = sorted(diagram, key=lambda x: diagram.nodes[x]["formula"])
        mapping = {x: str(sorted_ids.index(x)) for x in diagram}
        networkx.relabel_nodes(diagram, mapping, copy=False)

    log.info(f"total executions of NuSMV: {counter_mc}")

    if fname_image:
        diagram2image(diagram, FnameImage=fname_image, StyleInputs=True, StyleSplines="curved", StyleEdges=edge_data, StyleRanks=True, FirstIndex=1)

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

    return diagram


def _compute_diagram_component(primes: dict, Update, Subspaces, EdgeData, Silent):
    """
    Also computes the commitment diagram but without removing out-DAGs or considering connected components separately.
    Not meant for general use. Use compute_diagram(..) instead.
    """

    assert(Update in PyBoolNet.state_transition_graphs.UPDATE_STRATEGIES)
    assert(primes)

    # create nodes
    counter_mc = 0
    node_id = 0
    worst_case_nodes = 0
    inputs = PyBoolNet.prime_implicants.find_inputs(primes)

    states_per_case = pyboolnet.state_space.size_state_space(primes, fixed_inputs=True)

    diagram = networkx.DiGraph()

    if not Silent:
        print(" _compute_diagram_component(..)")
        print("  inputs: {x} ({y})".format(x=len(inputs), y=", ".join(inputs)))
        print("  combinations:  %i"%2**len(inputs))

    for i, combination in enumerate(input_combinations(primes)):

        attr = [x for x in Subspaces if pyboolnet.state_space.is_subspace(primes, this=x, other=combination)]

        worst_case_nodes+= 2**len(attr)-1
        states_covered = 0
        specs = [PyBoolNet.temporal_logic.subspace2proposition(primes, x) for x in attr]
        vectors = len(attr)*[[0,1]]
        vectors = list(itertools.product(*vectors))
        random.shuffle(vectors)

        combination_formula = PyBoolNet.temporal_logic.subspace2proposition(primes, combination)

        if not Silent:
            print("  input combination %i, worst case #nodes: %i"%(i,2**len(attr)-1))

        for vector in vectors:
            if sum(vector)==0: continue
            if states_covered==states_per_case:
                if not Silent:
                    print("  avoided executions of NuSMV due to state counting")
                break

            if len(vector)==1:
                data = {"attractors":   attr,
                        "size":             states_per_case,
                        "formula":          combination_formula}

            else:

                init = "INIT %s"%combination_formula

                reach = ["EF(%s)"%x for flag, x in zip(vector, specs) if flag]
                reach_all  = " & ".join(reach)
                reach_some = " | ".join(reach)
                spec = "CTLSPEC %s & AG(%s)"%(reach_all,reach_some)

                answer, accepting = PyBoolNet.model_checking.check_primes_with_acceptingstates(primes, Update, init, spec)
                counter_mc+=1

                data = {"attractors":   [x for flag,x in zip(vector, attr) if flag],
                        "size":             accepting["INITACCEPTING_SIZE"],
                        "formula":          accepting["INITACCEPTING"]}

            if data["size"]>0:
                diagram.add_node(node_id)
                for key, value in data.items():
                    diagram.nodes[node_id][key] = value
                node_id+=1
                states_covered+= data["size"]

    if not Silent:
        perc = "= %.2f%%"%(100.*diagram.order()/worst_case_nodes) if worst_case_nodes else ""
        print("  worst case #nodes: %i"%worst_case_nodes)
        print("  actual nodes: %i %s"%(diagram.order(),perc))

    # list potential targets
    potential_targets = {}
    for source, source_data in diagram.nodes(data=True):
        succs = []
        for target, target_data in diagram.nodes(data=True):
            if source==target: continue
            if all(x in source_data["attractors"] for x in target_data["attractors"]):
                succs.append((target,target_data))

        potential_targets[source] = succs

    if not Silent:
        worst_case_edges = sum(len(x) for x in potential_targets.values())
        print("  worst case #edges: %i"%worst_case_edges)

    # create edges
    for source, source_data in diagram.nodes(data=True):
        for target, target_data in potential_targets[source]:

            init = "INIT %s"%source_data["formula"]
            spec = "CTLSPEC EX(%s)"%target_data["formula"]
            answer, accepting = PyBoolNet.model_checking.check_primes_with_acceptingstates(primes, Update, init, spec)
            counter_mc+=1

            data = {}
            data["EX_size"] = accepting["INITACCEPTING_SIZE"]
            data["EX_formula"] = accepting["INITACCEPTING"]

            if data["EX_size"]>0:

                if EdgeData:
                    if len(potential_targets[source])==1:
                        data["EF_size"] = source_data["size"]
                        data["EF_formula"] = source_data["formula"]

                    else:
                        spec = "CTLSPEC E[%s U %s]"%(source_data["formula"],target_data["formula"])
                        answer, accepting = PyBoolNet.model_checking.check_primes_with_acceptingstates(primes, Update, init, spec)
                        counter_mc+=1

                        data["EF_size"] = accepting["INITACCEPTING_SIZE"]
                        data["EF_formula"] = accepting["INITACCEPTING"]

                diagram.add_edge(source, target)
                for key, value in data.items():
                    diagram.edges[source, target][key] = value

    if not Silent:
        perc = "= %.2f%%"%(100.*diagram.size()/worst_case_edges) if worst_case_edges else ""
        print("  actual edges: %i %s"%(diagram.size(),perc))
        print("  total executions of NuSMV: %i"%counter_mc)

    return diagram, counter_mc


def diagram2image(Diagram, FnameImage, StyleInputs=True, StyleSplines="curved", StyleEdges=False, StyleRanks=True, FirstIndex=1, Silent=True):
    """
    Creates the image file *fname_image* for the basin diagram given by *diagram*.
    The flag *StyleInputs* can be used to highlight which basins belong to which input combination.
    *StyleEdges* adds edge labels that indicate the size of the "border" (if *ComputeBorder* was enabled in :ref:`commitment_compute_diagram`)
    and the size of the states of the source basin that can reach the target basin.

    **arguments**:
        * *diagram*: a commitment diagram
        * *fname_image*: file name of image
        * *StyleInputs*: whether basins should be grouped by input combinations
        * *StyleSplines*: dot style for edges, e.g. "curved", "line" or "ortho" for orthogonal edges
        * *StyleEdges*: whether edges should be size of border / reachable states
        * *StyleRanks*: style that places nodes with the same number of reachable attractors on the same rank (level)
        * *FirstIndex*: first index of attractor names

    **returns**::
        * *styled_diagram* (networkx.DiGraph)

    **example**::

        >>> attrs = Attractors.compute_attractors(primes, update)
        >>> Commitment.compute_phenotype_diagram(attrs)
        >>> diagram2image(diagram, "diagram.pdf")
        >>> diagram2image(diagram, "basins.pdf", "attractors.pdf")
    """

    Primes = Diagram.graph["primes"]

    size_total = pyboolnet.state_space.size_state_space(Primes)
    size_per_input_combination = pyboolnet.state_space.size_state_space(Primes, fixed_inputs=True)
    is_small_network = size_total <= 1024

    result = networkx.DiGraph()
    result.graph["node"]  = {"shape":"rect","style":"filled","color":"none"}
    result.graph["edge"]  = {}

    if StyleInputs:
        result.graph["node"]["fillcolor"] = "grey95"
    else:
        result.graph["node"]["fillcolor"] = "lightgray"

    attractors = [x["attractors"] for _,x in Diagram.nodes(data=True)]
    attractors = [x for x in attractors if len(x)==1]
    attractors = set(pyboolnet.state_space.subspace2str(Primes, x[0]) for x in attractors)
    attractors = sorted(attractors)

    labels = {}
    # "labels" is used for node labels
    # keys:
    # head = reachable attractors
    # size = number of states in % (depends on StyleInputs)


    for node, data in Diagram.nodes(data=True):

        labels[node] = {}
        result.add_node(node)

        if len(data["attractors"])==1:
            result.nodes[node]["fillcolor"] = "cornflowerblue"

            attr  = pyboolnet.state_space.subspace2str(Primes, data["attractors"][0])
            index = attractors.index(attr)+FirstIndex
            labels[node]["head"] = 'A%i = <font face="Courier New">%s</font>'%(index,attr)

        else:
            head = sorted("A%i" % (attractors.index(pyboolnet.state_space.subspace2str(Primes, x)) + FirstIndex) for x in data["attractors"])
            head = PyBoolNet.Utility.Misc.divide_list_into_similar_length_lists(head)
            head = [",".join(x) for x in head]
            labels[node]["head"] = "<br/>".join(head)


        if "fillcolor" in data:
            result.nodes[node]["fillcolor"] = data["fillcolor"]



    for source, target, data in Diagram.edges(data=True):
        result.add_edge(source, target)

        if StyleEdges:
            edge_label = []


            #perc = 100.* data["EX_size"] / Diagram.nodes[source]["size"]
            #edge_label.append("EX: %s%%"%perc2str(perc))

            if "EF_size" in data:
                #perc = 100.* data["EF_size"] / Diagram.nodes[source]["size"]
                #edge_label.append("EF: %s%%"%perc2str(perc))

                if data["EF_size"] < Diagram.nodes[source]["size"]:
                    result.adj[source][target]["color"]="lightgray"

            #result.adj[source][target]["label"] = "<%s>"%("<br/>".join(edge_label))


    for x in Diagram.nodes():
        if is_small_network:
            labels[x]["size"] = "states: {x}".format(x=Diagram.nodes[x]["size"])
        else:
            perc = 100.* Diagram.nodes[x]["size"] / size_total
            labels[x]["size"] = "states: {x}%".format(x=perc2str(perc))

    subgraphs = []
    if StyleInputs:
        for inputs in PyBoolNet.prime_implicants.input_combinations(Primes):
            if not inputs: continue
            nodes = [x for x in Diagram.nodes() if PyBoolNet.Utility.Misc.dicts_are_consistent(inputs,Diagram.nodes[x]["attractors"][0])]
            label = pyboolnet.state_space.subspace2str(Primes, inputs)
            subgraphs.append((nodes,{"label":"inputs: %s"%label, "color":"none", "fillcolor":"lightgray"}))


            for x in nodes:
                perc = 100.* Diagram.nodes[x]["size"] / size_per_input_combination
                labels[x]["size"] = "states: %s%%"%perc2str(perc)


        if subgraphs:
            result.graph["subgraphs"] = []
            PyBoolNet.Utility.DiGraphs.add_style_subgraphs(result, subgraphs)


    for x in Diagram.nodes():
        result.nodes[x]['label'] = "<%s>"%"<br/>".join(labels[x].values())

    if StyleRanks:
        if subgraphs:
            to_rank = result.graph["subgraphs"]
        else:
            to_rank = [result]

        for graph in to_rank:
            ranks = {}
            for node, data in Diagram.nodes(data=True):
                if not node in graph:continue

                size = len(data["attractors"])
                if not size in ranks:
                    ranks[size]=[]
                ranks[size].append(node)
            ranks=list(ranks.items())
            ranks.sort(key=lambda x: x[0])

            for _,names in ranks:
                names = ['"%s"'%x for x in names]
                names = "; ".join(names)
                graph.graph["{rank = same; %s;}"%names]=""


    if FnameImage:
        PyBoolNet.Utility.DiGraphs.digraph2image(result, FnameImage, layout_engine="dot")

    return result


def create_piechart(Diagram, FnameImage, ColorMap=None, Silent=False, Title=None):
    """
    Creates the commitment pie chart for the commitment diagram using matplotlib.
    The pieces of the chart represent states that can reach the exact same subset of *Attractors*.

    **arguments**:
        * *diagram*: commitment diagram, see :ref:`commitment_compute_diagram`
        * *fname_image*: name of the output image
        * *color_map*: assignment of diagram nodes to colors for custom colors
        * *title*: optional title of plot

    **returns**::
        * *None*

    **example**::

        >>> primes = Repository.get_primes("xiao_wnt5a")
        >>> attrs = Attractors.compute_attractors(primes, update)
        >>> diagram = compute_commitment_diagram(attrs)
        >>> create_piechart(diagram, "pie.pdf")
        created pie.pdf
    """

    import matplotlib.pyplot

    Primes = Diagram.graph["primes"]

    total = pyboolnet.state_space.size_state_space(Primes)
    is_small_network = total <= 1024

    indeces = sorted(Diagram, key=lambda x: len(Diagram.nodes[x]["attractors"]))

    labels = []
    for x in indeces:
        label = sorted(pyboolnet.state_space.subspace2str(Primes, y) for y in Diagram.nodes[x]["attractors"])
        labels.append("\n".join(label))

    sizes  = [Diagram.nodes[x]["size"] for x in indeces]

    figure = matplotlib.pyplot.figure()

    if ColorMap:
        colors = [ColorMap[x] for x in indeces]
    else:
        colors = [matplotlib.pyplot.cm.rainbow(1.*x/(len(Diagram)+1)) for x in range(len(Diagram)+2)][1:-1]

    for i,x in enumerate(indeces):
        if "fillcolor" in Diagram.nodes[x]:
            colors[i] = Diagram.nodes[x]["fillcolor"]

    if is_small_network:
        autopct = lambda p: '{:.0f}'.format(p * total / 100)
    else:
        autopct = lambda p: '{:1.1f}%'.format(p)

    stuff = matplotlib.pyplot.pie(sizes, explode=None, labels=labels, colors=colors, autopct=autopct, shadow=True, startangle=140)
    patches = stuff[0] # required because matplotlib.pyplot.pie returns variable number of things depending on autopct!!
    for i, patch in enumerate(patches):
        patch.set_ec("black")
    matplotlib.pyplot.axis('equal')

    if Title is None:
        Title = "Commitment Sets"
    matplotlib.pyplot.title(Title, y=1.08)

    matplotlib.pyplot.tight_layout()

    figure.savefig(FnameImage, bbox_inches='tight')
    print("created %s"%FnameImage)
    matplotlib.pyplot.close(figure)


#################################
###### Auxillary Functions ######
#################################

def project_attractors(Attractors, Names):
    result = set()
    for space in Attractors:
        projection = tuple((k,v) for k,v in sorted(space.items()) if k in Names)
        result.add(projection)

    result = [dict(x) for x in result]

    return result


def lift_attractors(Attractors, Projection):
    return [x for x in Attractors for y in Projection if PyBoolNet.Utility.Misc.dicts_are_consistent(x,y)]


def cartesian_product(Diagrams, Factor, EdgeData):
    """
    creates the cartesian product of *Diagrams*.
    """

    result = networkx.DiGraph()

    # create nodes
    nodes = [x.nodes(data=True) for x in Diagrams]

    for product in itertools.product(*nodes):
        data = {}
        data["size"] = functools.reduce(operator.mul,[x["size"] for _,x in product]) * Factor
        data["formula"] = " & ".join("(%s)"%x["formula"] for _,x in product)

        attrs = [x["attractors"] for _,x in product]
        attrs = list(itertools.product(*attrs))
        attrs = [PyBoolNet.Utility.Misc.merge_dicts(x) for x in attrs]
        data["attractors"] = attrs

        node = tuple(x for x,_ in product)

        result.add_node(node)
        for key, value in data.items():
            result.nodes[node][key] = value

    # create edges
    for source in result.nodes():
        for s, diagram in zip(source, Diagrams):
            factor = result.nodes[source]["size"] / diagram.nodes[s]["size"]
            for _, t, data in diagram.out_edges(s,data=True):

                data = {}
                basic_formula = ["(%s)"%g.nodes[x]["formula"] for x,g in zip(source,Diagrams) if not g==diagram]
                data["EX_size"]    = factor * diagram.adj[s][t]["EX_size"]
                formula = basic_formula + ["(%s)"%diagram.adj[s][t]["EX_formula"]]
                data["EX_formula"]  = " & ".join(formula)

                if EdgeData:
                    data["EF_size"]     = factor * diagram.adj[s][t]["EF_size"]
                    formula = basic_formula + ["(%s)"%diagram.adj[s][t]["EF_formula"]]
                    data["EF_formula"]  = " & ".join(formula)

                target = tuple(x if not g==diagram else t for x,g in zip(source,Diagrams))

                result.add_edge(source, target)
                for key, value in data.items():
                    result.edges[source, target][key] = value

    # relabel nodes
    result = networkx.convert_node_labels_to_integers(result)

    return result


def diagrams_are_equal(Diagram1, Diagram2):
    """
    removes for formulas, which are different for naive / product diagrams.
    """

    g1 = Diagram1.copy_primes()
    g2 = Diagram2.copy_primes()

    for g in [g1,g2]:
        for x in g.nodes():
            g.nodes[x].pop("formula")
        for x,y in g.edges():
            if "border_formula" in g.adj[x][y]:
                g.adj[x][y].pop("border_formula")
                g.adj[x][y].pop("finally_formula")

    em = lambda x,y:x==y

    return networkx.is_isomorphic(g1,g2,edge_match=em)
