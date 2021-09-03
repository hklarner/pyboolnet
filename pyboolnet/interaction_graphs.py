import subprocess
from typing import Union, List, Optional, Dict, Set
import os
import sys
import networkx
import logging

from pyboolnet.misc import find_command
from pyboolnet.state_transition_graphs import states2dict
from pyboolnet.digraphs import digraph2dot, digraph2image, digraph2condensationgraph
from pyboolnet.digraphs import add_style_subgraphs as digraphs_add_style_subgraphs
from pyboolnet.state_transition_graphs import subspace2dict, successor_synchronous, state2dict

CMD_DOT = find_command("dot")
CMD_CONVERT = find_command("convert")
STYLES_SET = {"interactionsigns", "inputs", "outputs", "constants", "sccs", "anonymous"}

log = logging.getLogger(__name__)


def create_empty_igraph(primes: dict) -> networkx.DiGraph:
    """
    creates an empty igraph with default attributes
    """

    igraph = networkx.DiGraph()

    factor = 0.2
    width = factor * sum(len(x) for x in primes) / len(primes)

    igraph.graph["node"] = {"style": "filled", "shape": "circle", "fixedsize": "true", "width": str(width),
                            "color": "none", "fillcolor": "gray95"}
    igraph.graph["edge"] = {}
    igraph.graph["subgraphs"] = []

    return igraph


def primes2igraph(primes: dict) -> networkx.DiGraph:
    """
    Creates the interaction graph from the prime implicants of a network.
    Interaction graphs are implemented as :ref:`installation_networkx` digraph objects.
    Edges are given the attribute *sign* whose value is a Python set containing 1 or -1 or both, depending on
    whether the interaction is activating or inhibiting or both.

    **arguments**:
        * *primes*: prime implicants

    **returns**:
        * *igraph*: interaction graph

    **example**::

        >>> bnet = "\\n".join(["v1, v1","v2, 1", "v3, v1&!v2 | !v1&v2"])
        >>> primes = bnet2primes(bnet)
        >>> igraph = primes2igraph(primes)
        >>> igraph.nodes()
        ["v1", "v2", "v3"]
        >>> igraph.edges()
        [("v1", "v1"), ("v1", "v3"), ("v2", "v3"), ("v3", "v1")]
        >>> igraph.adj["v1"]["v3"]["sign"]
        set([1, -1])
    """

    igraph = create_empty_igraph(primes)

    edges = {}
    for name in primes:
        igraph.add_node(name)
        for term in primes[name][1]:
            for k, v in term.items():
                if v == 0:
                    sign = -1
                else:
                    sign = +1
                if not (k, name) in edges:
                    edges[(k, name)] = set([])
                edges[(k, name)].add(sign)

    for k, name in edges:
        igraph.add_edge(k, name, sign=edges[(k, name)])

    return igraph


def local_igraph_of_state(primes: dict, state: Union[dict, str]) -> networkx.DiGraph:
    """
    Computes the local interaction graph dF/dx of a state x.

    **arguments**:
        * *primes*: prime implicants
        * *State*: a state

    **returns**:
        * *local_igraph*: the local interaction graph

    **example**::

        >>> primes = get_primes("remy_tumorigenesis")
        >>> state = random_state(primes)
        >>> local_igraph = local_igraph_of_state(primes, state)
        >>> add_style_interactionsigns(local_igraph)
        >>> igraph2image(local_igraph, "local_igraph.pdf")
        created local_igraph.pdf
    """

    if type(state) is str:
        state = state2dict(primes, state)

    local_igraph = create_empty_igraph(primes)

    def func(x):
        return successor_synchronous(primes, x)

    x = state

    for i in primes:
        for j in primes:

            y = dict(state)
            y[i] = 1 - x[i]

            dx = x[i] - y[i]
            df = func(x)[j] - func(y)[j]
            sign = int(df / dx)

            if sign:
                local_igraph.add_edge(i, j, sign={sign})

    return local_igraph


def local_igraph_of_states(primes: dict, states: List[Union[str, dict]]):
    """
    computes the local interaction graph of a states.
    """

    states = states2dict(primes, states)
    local_igraph = create_empty_igraph(primes)

    for state in states:
        g = local_igraph_of_state(primes, state)

        for i, j in g.edges():
            signs = g[i][j]["sign"]

            if local_igraph.has_edge(i, j):
                local_igraph[i][j]["sign"].update(signs)
            else:
                local_igraph.add_edge(i, j, sign=signs)

    return local_igraph


def copy(igraph: networkx.DiGraph) -> networkx.DiGraph:
    """
    Creates a copy of *igraph* including all *dot* attributes.

    **arguments**:
        * *igraph*: interaction graph

    **returns**:
        * *new_igraph*: new interaction graph

    **example**::

        >>> igraph2 = copy(igraph)
    """

    new_igraph = igraph.copy()
    if new_igraph.graph["subgraphs"]:
        new_igraph.graph["subgraphs"] = [x.copy() for x in new_igraph.graph["subgraphs"]]

    return new_igraph


def igraph2dot(igraph: networkx.DiGraph, fname_dot: Optional[str] = None) -> str:
    """
    Generates a *dot* file from *igraph* and saves it as *FnameDOT* or returns it as a string.

    **arguments**:
        * *igraph*: interaction graph
        * *fname_dot*: name of *dot* file

    **returns**:
        * *dot*: contents of dot file as text

    **example**::

          >>> igraph2dot(igraph, "irma.dot")
          >>> dotfile = igraph2dot(igraph)
    """

    return digraph2dot(igraph, fname_dot)


def igraph2image(igraph: networkx.DiGraph, fname_image: str, layout_engine="fdp"):
    """
    Creates an image file from *igraph* using :ref:`installation_graphviz` and the force directed layout engine *fdp*.
    To find out which file formats are supported call ``$ dot -T?``.

    **arguments**:
        * *igraph*: interaction graph
        * *fname_image*: name of image
        * *layout_engine*: one of "dot", "neato", "fdp", "sfdp", "circo", "twopi"

    **example**::

          >>> igraph2image(igraph, "mapk_igraph.pdf")
          >>> igraph2image(igraph, "mapk_igraph.jpg")
          >>> igraph2image(igraph, "mapk_igraph.svg")
    """

    digraph2image(igraph, fname_image, LayoutEngine=layout_engine)


def create_image(primes: dict, fname_image: str, styles: List[str] = ["interactionsigns"], layout_engine: str = "fdp"):
    """
    A convenience function for drawing interaction graphs directly from the prime implicants.
    *Styles* must be a sublist of ["interactionsigns", "inputs", "outputs", "constants", "sccs", "anonymous"].

    **arguments**:
        * *primes*: prime implicants
        * *fname_image*: name of image
        * *styles* the styles to be applied
        * *layout_engine*: one of "dot", "neato", "fdp", "sfdp", "circo", "twopi"

    **example**::

          >>> create_image(primes, "mapk_igraph.pdf", styles=["interactionsigns", "anonymous"])
    """

    unknown_styles = set(styles).difference(STYLES_SET)
    if unknown_styles:
        log.error(f"cannot apply styles: unknown_styles={unknown_styles}")
        sys.exit()

    igraph = primes2igraph(primes)

    if "interactionsigns" in styles:
        add_style_interactionsigns(igraph)
    if "inputs" in styles:
        add_style_inputs(igraph)
    if "outputs" in styles:
        add_style_outputs(igraph)
    if "constants" in styles:
        add_style_constants(igraph)
    if "sccs" in styles:
        add_style_sccs(igraph)
    if "anonymous" in styles:
        add_style_anonymous(igraph)

    igraph2image(igraph, fname_image, layout_engine=layout_engine)


def find_outdag(igraph: networkx.DiGraph) -> List[str]:
    """
    Finds the maximal directed acyclic subgraph that is closed under the successors operation.
    Essentially, these components are the "output cascades" which can be exploited by various algorithms, e.g.
    the computation of basins of attraction.

    **arguments**:
        * *igraph*: interaction graph

    **returns**:
        * *names*: the outdag

    **example**::

        >>> find_outdag(igraph)
        ["v7", "v8", "v9"]
    """

    graph = igraph.copy()
    sccs = networkx.strongly_connected_components(graph)
    sccs = [list(x) for x in sccs]
    candidates = [scc[0] for scc in sccs if len(scc) == 1]
    candidates = [x for x in candidates if not graph.has_edge(x, x)]
    sccs = [scc for scc in sccs if len(scc) > 1 or graph.has_edge(scc[0], scc[0])]

    graph.add_node("!")
    for scc in sccs:
        graph.add_edge(scc[0], "!")

    outdag = [x for x in candidates if not networkx.has_path(graph, x, "!")]

    return outdag


def find_minimal_autonomous_nodes(igraph: networkx.DiGraph, core: Set[str]) -> List[Set[str]]:
    """
    Returns the minimal autonomous node sets of *igraph*.
    See :ref:`Klarner2015(b) <klarner2015approx>` Sec. 5.2 for a formal definition and details.
    Minimal autonomous sets generalize inputs, which are autonomous sets of size 1.
    If *Superset* is specified then all autonomous sets that are not supersets of it are ignored.

    **arguments**:
        * *igraph*: interaction graph
        * *core*: all autonomous sets must be supersets of these components

    **returns**:
        * *autonomous_nodes* (list of sets): the minimal autonomous node sets of *igraph*

    **example**::

          >>> find_minimal_autonomous_nodes(igraph)
          [set(["raf"]), set(["v1","v8","v9"])]
    """

    cgraph = digraph2condensationgraph(igraph)
    for x in cgraph.nodes():
        if set(x).issubset(core):
            cgraph.remove_node(x)

    return [set(x) for x in cgraph.nodes() if cgraph.in_degree(x) == 0]


def add_style_anonymous(igraph: networkx.DiGraph):
    """
    Creates an anonymous interaction graph with circular nodes without labels.

    **arguments**:
        * *igraph*: interaction graph

    **example**::

          >>> add_style_anonymous(igraph)
    """

    igraph.graph["node"]["shape"] = "circle"
    igraph.graph["node"]["style"] = "filled"
    igraph.graph["node"]["fillcolor"] = "lightgray"
    igraph.graph["node"]["color"] = "black"

    for x in igraph.nodes():
        igraph.nodes[x]["label"] = ""


def add_style_interactionsigns(igraph: networkx.DiGraph):
    """
    Sets attributes for the arrow head and edge color of interactions to indicate the interaction sign.
    Activating interactions get the attributes *"arrowhead"="normal"* and *"color"="black"*,
    inhibiting interactions get the attributes *"arrowhead"="tee"* and *"color"="red"*, and
    ambivalent interaction get the attributes *"arrowhead"="dot"* and *"color"="blue"*.

    **arguments**:
        * *igraph*: interaction graph

    **example**::

          >>> add_style_interactionsigns(igraph)
    """

    for source, target, attr in sorted(igraph.edges(data=True)):
        if attr["sign"] == {1, -1}:
            igraph.adj[source][target]["arrowhead"] = "dot"
            igraph.adj[source][target]["color"] = "dodgerblue"

        elif attr["sign"] == {-1}:
            igraph.adj[source][target]["arrowhead"] = "tee"
            igraph.adj[source][target]["color"] = "red"

        elif attr["sign"] == {1}:
            igraph.adj[source][target]["arrowhead"] = "normal"
            igraph.adj[source][target]["color"] = "black"


def add_style_activities(igraph: networkx.DiGraph, activities: Union[str, dict], color_active: str = "/paired10/5",
                         color_inactive: str = "/paired10/1"):
    """
    Sets attributes for the color and fillcolor of nodes to indicate which variables are activated and which are inhibited in *Activities*.
    All activated or inhibited components get the attribute *"color"="black"*.
    Activated components get the attribute *"fillcolor"="red"* and
    inactivated components get the attribute *"fillcolor"="blue"*.
    Interactions involving activated or inhibited nodes get the attribute *"color"="gray"* to reflect that they are ineffective.

    **arguments**:
        * *igraph*: interaction graph
        * *activities*: activated and inhibited nodes
        * *color_active*: color in dot format for active components
        * *color_inactive*: color in dot format for inactive components

    **example**::

          >>> activities = {"ERK":1, "MAPK":0}
          >>> add_style_activities(igraph, activities)
    """

    names = sorted(igraph.nodes())
    if type(activities) is str:
        activities = subspace2dict(names, activities)

    for name in igraph.nodes():
        if name in activities:
            igraph.nodes[name]["color"] = "black"
            igraph.nodes[name]["fillcolor"] = color_active if activities[name] == 1 else color_inactive

    for x, y in igraph.edges():
        if x in activities or y in activities:
            igraph.adj[x][y]["color"] = "gray"


def add_style_inputs(igraph: networkx.DiGraph):
    """
    Adds a subgraph to the *dot* representation of *igraph* that contains all inputs.
    Nodes that belong to the same *dot* subgraph are contained in a rectangle and treated separately during layout computations.
    In addition, the subgraph is labeled by a "Inputs" in bold font.

    **arguments**:
        * *igraph*: interaction graph

    **example**::

          >>> add_style_inputs(igraph)
    """

    inputs = [x for x in igraph.nodes() if igraph.in_degree(x) == 1 and x in igraph.successors(x)]

    if inputs:
        subgraph = networkx.DiGraph()
        subgraph.add_nodes_from(inputs)
        subgraph.graph["label"] = "Inputs"

        for x in list(igraph.graph["subgraphs"]):
            y = x.nodes()
            if len(y) == 1 and y[0] in inputs:
                igraph.graph["subgraphs"].remove(x)

        igraph.graph["subgraphs"].append(subgraph)


def add_style_outputs(igraph: networkx.DiGraph):
    """
    Adds a subgraph to the *dot* representation of *igraph* that contains all outputs.
    Nodes that belong to the same *dot* subgraph are contained in a rectangle and treated separately during layout computations.
    In addition, the subgraph is labeled by a *"Outputs"* in bold font.

    **arguments**:
        * *igraph*: interaction graph

    **example**::

          >>> add_style_outputs(igraph)
    """

    outputs = [x for x in igraph.nodes() if not list(igraph.successors(x))]

    if outputs:
        subgraph = networkx.DiGraph()
        subgraph.add_nodes_from(outputs)
        subgraph.graph["label"] = "Outputs"
        igraph.graph["subgraphs"].append(subgraph)


def add_style_constants(igraph: networkx.DiGraph):
    """
    Sets the attribute *"style"="plaintext"* with *"fillcolor"="none"* and *"fontname"="Times-Italic"* for all constants.

    **arguments**:
        * *igraph*: interaction graph

    **example**::

          >>> add_style_constants(igraph)
    """

    for x in igraph.nodes():
        if not igraph.predecessors(x):
            igraph.nodes[x]["shape"] = "plaintext"
            igraph.nodes[x]["fillcolor"] = "none"
            igraph.nodes[x]["fontname"] = "Times-Italic"

            for y in igraph.successors(x):
                igraph.adj[x][y]["color"] = "gray"


def add_style_sccs(igraph: networkx.DiGraph):
    """
    Adds a subgraph for every non-trivial strongly connected component (SCC) to the *dot* representation of *igraph*.
    Nodes that belong to the same *dot* subgraph are contained in a rectangle and treated separately during layout computations.
    Each subgraph is filled by a shade of gray that gets darker with an increasing number of SCCs that are above it in the condensation graph.
    Shadings repeat after a depth of 9.

    **arguments**:
        * *igraph*: interaction graph

    **example**::

          >>> add_style_sccs(igraph)
    """

    condensation_graph = digraph2condensationgraph(igraph)

    for scc in condensation_graph.nodes():
        depth = condensation_graph.nodes[scc]["depth"]
        col = 2 + (depth % 8)

        subgraph = networkx.DiGraph()
        subgraph.add_nodes_from(scc)
        subgraph.graph["style"] = "filled"
        subgraph.graph["color"] = "none"
        subgraph.graph["fillcolor"] = f"/greys9/{col}"

        igraph.graph["subgraphs"].append(subgraph)


def add_style_path(igraph: networkx.DiGraph, path: List[str], color: str):
    """
    Sets the color of all nodes and edges involved in the given *Path* to *Color*.

    **arguments**:
        * *igraph*: interaction graph
        * *Path*: sequence of component names
        * *Color*: color of the path

    **example**::

        >>> path = ["Raf", "Ras", "Mek"]
        >>> add_style_path(igraph, path, "red")
    """

    unknown_names = [x for x in path if x not in igraph]
    if unknown_names:
        log.error(f"cannot draw path: unknown_names={unknown_names}")
        sys.exit()

    for x in path:
        igraph.nodes[x]["color"] = color

    if len(path) > 1:
        for x, y in zip(path[:-1], path[1:]):
            igraph.adj[x][y]["color"] = color
            igraph.adj[x][y]["penwidth"] = "2"


def add_style_subgraphs(igraph: networkx.DiGraph, subgraphs):
    """
    Adds the subgraphs given in *Subgraphs* to *igraph* - or overwrites them if they already exist.
    Nodes that belong to the same *dot* subgraph are contained in a rectangle and treated separately during layout computations.
    *Subgraphs* must consist of tuples of the form *NodeList*, *Attributs* where *NodeList* is a list of graph nodes and *Attributes*
    is a dictionary of subgraph attributes in *dot* format.

    .. note::

        *Subgraphs* must satisfy the following property:
        Any two subgraphs have either empty intersection or one is a subset of the other.
        The reason for this requirement is that *dot* can not draw intersecting subgraphs.

    **arguments**:
        * *igraph*: interaction graph
        * *subgraphs*: pairs of lists and subgraph attributes

    **example**:

        >>> sub1 = (["v1","v2"], {"label":"Genes"})
        >>> sub2 = (["v3","v4"], {})
        >>> subgraphs = [sub1,sub2]
        >>> add_style_subgraphs(igraph, subgraphs)
    """

    digraphs_add_style_subgraphs(igraph, subgraphs)


def add_style_default(igraph: networkx.DiGraph):
    """
    A convenience function that adds styles for interaction signs, SCCs, inputs, outputs and constants.

    **arguments**:
        * *igraph*: interaction graph

    **example**::

        >>> add_style_default(igraph, path)

    """

    # careful, the order matters
    add_style_interactionsigns(igraph)
    add_style_sccs(igraph)
    add_style_inputs(igraph)
    add_style_outputs(igraph)
    add_style_constants(igraph)


def activities2animation(igraph: networkx.DiGraph, activities, fname_gif: str, fname_tmp: str = "tmp*.jpg",
                         delay: int = 50, loop: int = 0):
    """
    Generates an animated *gif* from the sequence of *Activities* by mapping the activities on
    the respective components of the interaction graph using :ref:`add_style_activities`.
    The activities may be given in *dict* or *str* format, see :ref:`states_subspaces_paths` for details.
    Requires the program *convert* from the :ref:`installation_imagemagick` software suite.
    The argument *FnameTMP* is the string that is used for generating the individual frames.
    Use "*" to indicate the position of the frame counter.
    The default *"tmp\*.jpg"* will result in the creation of the files::

        tmp01.jpg, tmp02.jpg, ...

    The files will be deleted after the *gif* is generated.
    The *Delay* parameter sets the frame rate and *Loop* the number of repititions,
    both are parameters that are directly passed to *convert*.

    **arguments**:
        * *igraph*: interaction graph
        * *Activities*: sequence of activities
        * *Delay* (int): number of 1/100s between each frame
        * *Loop* (int): number of repetitions, use 0 for infinite
        * *FnameTMP*: name for temporary image files, use "*" to indicate counter
        * *FnameGIF*: name of the output *gif* file

    **example**::

        >>> activities = ["11--1-0", "111-1-0", "11111-0", "1111100"]
        >>> activities2animation(igraph, activities, "animation.gif")
    """

    assert "." in fname_tmp
    assert "*" in fname_tmp
    assert fname_gif[-4:].lower() == ".gif"
    assert activities is not None

    width = len(str(len(activities))) + 1
    for i, x in enumerate(activities):
        dummy = copy(igraph)
        add_style_activities(dummy, x)
        dummy.graph["label"] = "%i of %i" % (i + 1, len(activities))
        igraph2image(igraph=dummy, fname_image=fname_tmp.replace("*", '{i:0{w}d}'.format(i=i, w=width)))

    cmd = [CMD_CONVERT, "-delay", str(delay), "-loop", str(loop), fname_tmp, fname_gif]
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    output, error = proc.communicate()

    if not (proc.returncode == 0):
        log.error(f"could not create animation: error={error}, output={output}, return_code={proc.returncode}, cmd={' '.join(cmd)}")
        sys.exit()

    for i in range(len(activities)):
        fname = fname_tmp.replace("*", "{i:0{w}d}".format(i=i, w=width))
        os.remove(fname)

    log.info(f"created {fname_gif}")
