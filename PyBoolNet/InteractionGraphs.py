

import itertools
import subprocess
import math
import os
import networkx

import PyBoolNet.StateTransitionGraphs
import PyBoolNet.Utility.Misc
import PyBoolNet.Utility.DiGraphs

CMD_DOT = PyBoolNet.Utility.Misc.find_command("dot")
CMD_CONVERT = PyBoolNet.Utility.Misc.find_command("convert")


def dot2image(FnameDOT, FnameIMAGE):
    PyBoolNet.Utility.DiGraphs.dot2image(FnameDOT, FnameIMAGE, LayoutEngine="dot")


def create_empty_igraph(Primes):
    """
    creates an empty igraph with default attributes
    """

    igraph = networkx.DiGraph()

    factor = 0.2
    width = factor * sum(len(x) for x in Primes) / len(Primes)

    igraph.graph["node"]  = {"style":"filled","shape":"circle", "fixedsize":"true", "width":str(width),"color":"none","fillcolor":"gray95"}
    igraph.graph["edge"]  = {}
    igraph.graph["subgraphs"]  = []

    return igraph


def primes2igraph(Primes):
    """
    Creates the interaction graph from the prime implicants of a network.
    Interaction graphs are implemented as :ref:`installation_networkx` digraph objects.
    Edges are given the attribute *sign* whose value is a Python set containing 1 or -1 or both, depending on
    whether the interaction is activating or inhibiting or both.

    **arguments**:
        * *Primes*: prime implicants

    **returns**:
        * *IGraph* (networkx.DiGraph): interaction graph

    **example**::

            >>> bnet = "\\n".join(["v1, v1","v2, 1", "v3, v1&!v2 | !v1&v2"])
            >>> primes = bnet2primes(bnet)
            >>> igraph = primes2igraph(primes)
            >>> igraph.nodes()
            ['v1', 'v2', 'v3']
            >>> igraph.edges()
            [('v1', 'v1'), ('v1', 'v3'), ('v2', 'v3'), ('v3', 'v1')]
            >>> igraph.adj["v1"]["v3"]["sign"]
            set([1, -1])
    """

    igraph = create_empty_igraph(Primes)

    edges = {}
    for name in Primes:
        igraph.add_node(name)
        for term in Primes[name][1]:
            for k,v in term.items():
                if v==0:
                    sign = -1
                else:
                    sign = +1
                if not (k,name) in edges:
                    edges[(k,name)]=set([])
                edges[(k,name)].add(sign)

    for k,name in edges:
        igraph.add_edge(k, name, sign=edges[(k,name)])

    return igraph


def local_igraph_of_state(Primes, State):
    """
    Computes the local interaction graph dF/dx of a state x.

    **arguments**:
        * *Primes*: prime implicants
        * *State* (dict or str)

    **returns**:
        * *LocalIGraph* (networkx.DiGraph): the local interaction graph

    **example**::

            >>> primes = PyBoolNet.Repository.get_primes("remy_tumorigenesis")
            >>> state = PyBoolNet.StateTransitionGraphs.random_state(primes)
            >>> local_igraph = PyBoolNet.InteractionGraphs.local_igraph_of_state(primes, state)
            >>> PyBoolNet.InteractionGraphs.add_style_interactionsigns(local_igraph)
            >>> PyBoolNet.InteractionGraphs.igraph2image(local_igraph, "local_igraph.pdf")
            created local_igraph.pdf
    """

    if type(State)==str:
        State = PyBoolNet.StateTransitionGraphs.state2dict(Primes, State)

    local_igraph = create_empty_igraph(Primes)

    F = lambda x: PyBoolNet.StateTransitionGraphs.successor_synchronous(Primes, x)
    x = State

    for i in Primes:
        for j in Primes:

            y = dict(State)
            y[i] = 1-x[i]

            dx = x[i] - y[i]
            dF = F(x)[j] - F(y)[j]

            sign = int( dF/dx )

            if sign:
                local_igraph.add_edge(i,j,sign=set([sign]))

    return local_igraph


def local_igraph_of_states(Primes, States):
    """
    computes the local interaction graph of a states.
    """

    States = PyBoolNet.StateTransitionGraphs.states2dict(Primes, States)

    local_igraph = create_empty_igraph(Primes)

    for state in States:
        g = local_igraph_of_state(Primes, state)

        for i, j in g.edges():
            signs = g[i][j]["sign"]

            if local_igraph.has_edge(i,j):
                local_igraph[i][j]["sign"].update(signs)
            else:
                local_igraph.add_edge(i,j,sign=signs)

    return local_igraph


def copy(IGraph):
    """
    Creates a copy of *IGraph* including all *dot* attributes.

    **arguments**:
        * *IGraph*: interaction graph

    **returns**:
        * *IGraph2*: new interaction graph

    **example**::

        >>> igraph2 = copy(igraph)
    """

    newgraph = IGraph.copy()
    if newgraph.graph["subgraphs"]:
        newgraph.graph["subgraphs"] = [x.copy() for x in newgraph.graph["subgraphs"]]

    return newgraph


def igraph2dot(IGraph, FnameDOT=None):
    """
    Generates a *dot* file from *IGraph* and saves it as *FnameDOT* or returns it as a string.

    **arguments**:
        * *IGraph*: interaction graph
        * *FnameDOT* (str): name of *dot* file or *None*

    **returns**:
        * *FileDOT* (str): file as string if not *FnameDOT is None*, otherwise it returns *None*

    **example**::

          >>> igraph2dot(igraph, "irma.dot")
          >>> dotfile = igraph2dot(igraph)
    """

    return PyBoolNet.Utility.DiGraphs.digraph2dot(IGraph, FnameDOT)


def igraph2image(IGraph, FnameIMAGE, LayoutEngine="fdp", Silent=False):
    """
    Creates an image file from *IGraph* using :ref:`installation_graphviz` and the force directed layout engine *fdp*.
    To find out which file formats are supported call ``$ dot -T?``.

    **arguments**:
        * *IGraph*: interaction graph
        * *FnameIMAGE* (str): name of image
        * *LayoutEngine*: one of "dot", "neato", "fdp", "sfdp", "circo", "twopi"
        * *Silent* (bool): print infos to screen

    **example**::

          >>> igraph2image(igraph, "mapk_igraph.pdf")
          >>> igraph2image(igraph, "mapk_igraph.jpg")
          >>> igraph2image(igraph, "mapk_igraph.svg")
    """

    PyBoolNet.Utility.DiGraphs.digraph2image(IGraph, FnameIMAGE, LayoutEngine=LayoutEngine, Silent=Silent)


def create_image(Primes, FnameIMAGE, Styles=["interactionsigns"], LayoutEngine="fdp"):
    """
    A convenience function for drawing interaction graphs directly from the prime implicants.
    *Styles* must be a sublist of ["interactionsigns", "inputs", "outputs", "constants", "sccs", "anonymous"].

    **arguments**:
        * *Primes*: prime implicants
        * *FnameIMAGE* (str): name of image
        * *Styles* (list): the styles to be applied
        * *LayoutEngine* (str): one of "dot", "neato", "fdp", "sfdp", "circo", "twopi"

    **example**::

          >>> create_image(primes, "mapk_igraph.pdf", Styles=["interactionsigns", "anonymous"])
    """

    assert(set(Styles).issubset(set(["interactionsigns", "inputs", "outputs", "constants", "sccs", "anonymous"])))

    igraph = primes2igraph(Primes)

    if "interactionsigns" in Styles:
        add_style_interactionsigns(igraph)
    if "inputs" in Styles:
        add_style_inputs(igraph)
    if "outputs" in Styles:
        add_style_outputs(igraph)
    if "constants" in Styles:
        add_style_constants(igraph)
    if "sccs" in Styles:
        add_style_sccs(igraph)
    if "anonymous" in Styles:
        add_style_anonymous(igraph)

    igraph2image(igraph, FnameIMAGE, LayoutEngine=LayoutEngine)


def find_outdag(IGraph):
    """
    Finds the maximal directed acyclic subgraph that is closed under the successors operation.
    Essentially, these components are the "output cascades" which can be exploited by various algorithms, e.g.
    the computation of basins of attraction.

    **arguments**:
        * *IGraph*: interaction graph

    **returns**:
        * *Names* (list): the outdag

    **example**::

        >>> find_outdag(igraph)
        ['v7', 'v8', 'v9']
    """

    graph = IGraph.copy()

    sccs = networkx.strongly_connected_components(graph)
    sccs = [list(x) for x in sccs]
    candidates = [scc[0] for scc in sccs if len(scc)==1]
    candidates = [x for x in candidates if not graph.has_edge(x,x)]
    sccs = [scc for scc in sccs if len(scc)>1 or graph.has_edge(scc[0],scc[0])]

    graph.add_node("!")
    for scc in sccs:
        graph.add_edge(scc[0],"!")

    outdags = [x for x in candidates if not networkx.has_path(graph,x,"!")]

    return outdags


def find_minimal_autonomous_nodes(IGraph, Superset=set([])):
    """
    Returns the minimal autonomous node sets of *IGraph*.
    See :ref:`Klarner2015(b) <klarner2015approx>` Sec. 5.2 for a formal definition and details.
    Minimal autonomous sets generalize inputs, which are autonomous sets of size 1.
    If *Superset* is specified then all autonomous sets that are not supersets of it are ignored.

    **arguments**:
        * *IGraph*: interaction graph
        * *Superset* (set): all autonomous sets must be supersets of this is

    **returns**:
        * *Nodes* (list of sets): the minimal autonomous node sets of *IGraph*

    **example**::

          >>> find_minimal_autonomous_nodes(IGraph)
          [set(['raf']), set(['v1','v8','v9'])]
    """

    cgraph = PyBoolNet.Utility.DiGraphs.digraph2condensationgraph(IGraph)
    for x in cgraph.nodes():
        if set(x).issubset(Superset):
            cgraph.remove_node(x)

    return [set(x) for x in cgraph.nodes() if cgraph.in_degree(x)==0]


def add_style_anonymous(IGraph):
    """
    Creates an anonymous interaction graph with circular nodes without labels.

    **arguments**:
        * *IGraph*: interaction graph

    **example**::

          >>> add_style_anonymous(igraph)
    """

    IGraph.graph["node"]["shape"] = "circle"
    IGraph.graph["node"]["style"] = "filled"
    IGraph.graph["node"]["fillcolor"] = "lightgray"
    IGraph.graph["node"]["color"] = "black"

    for x in IGraph.nodes():
        IGraph.nodes[x]["label"]=""


def add_style_interactionsigns(IGraph):
    """
    Sets attributes for the arrow head and edge color of interactions to indicate the interaction sign.
    Activating interactions get the attributes *"arrowhead"="normal"* and *"color"="black"*,
    inhibiting interactions get the attributes *"arrowhead"="tee"* and *"color"="red"*, and
    ambivalent interaction get the attributes *"arrowhead"="dot"* and *"color"="blue"*.

    **arguments**:
        * *IGraph*: interaction graph

    **example**::

          >>> add_style_interactionsigns(igraph)
    """

    for source, target, attr in sorted(IGraph.edges(data=True)):
        if attr["sign"]==set([1,-1]):
            IGraph.adj[source][target]["arrowhead"] = "dot"
            IGraph.adj[source][target]["color"] = "dodgerblue"
        elif attr["sign"]==set([-1]):
            IGraph.adj[source][target]["arrowhead"] = "tee"
            IGraph.adj[source][target]["color"] = "red"
        elif attr["sign"]==set([1]):
            IGraph.adj[source][target]["arrowhead"] = "normal"
            IGraph.adj[source][target]["color"] = "black"


def add_style_activities(IGraph, Activities, ColorActive="/paired10/5", ColorInactive="/paired10/1"):
    """
    Sets attributes for the color and fillcolor of nodes to indicate which variables are activated and which are inhibited in *Activities*.
    All activated or inhibited components get the attribute *"color"="black"*.
    Activated components get the attribute *"fillcolor"="red"* and
    inactivated components get the attribute *"fillcolor"="blue"*.
    Interactions involving activated or inhibited nodes get the attribute *"color"="gray"* to reflect that they are ineffective.

    **arguments**:
        * *IGraph*: interaction graph
        * *Activities* (dict): activated and inhibited nodes
        * *ColorActive* (str): color in dot format for active components
        * *ColorInactive* (str): color in dot format for inactive components

    **example**::

          >>> activities = {"ERK":1, "MAPK":0}
          >>> add_style_activities(igraph, activities)
    """

    names = sorted(IGraph.nodes())
    if type(Activities)==str:
        Activities = PyBoolNet.StateTransitionGraphs.subspace2dict(names, Activities)

    for name in IGraph.nodes():

        # steady variables
        if name in Activities:
            value = Activities[name]

            IGraph.nodes[name]["color"] = "black"

            if value == 0:
                IGraph.nodes[name]["fillcolor"] = ColorInactive

            else:
                IGraph.nodes[name]["fillcolor"] = ColorActive

    for x,y in IGraph.edges():
        if x in Activities or y in Activities:
            IGraph.adj[x][y]["color"] = "gray"


def add_style_inputs(IGraph):
    """
    Adds a subgraph to the *dot* representation of *IGraph* that contains all inputs.
    Nodes that belong to the same *dot* subgraph are contained in a rectangle and treated separately during layout computations.
    In addition, the subgraph is labeled by a *"Inputs"* in bold font.

    **arguments**:
        * *IGraph*: interaction graph

    **example**::

          >>> add_style_inputs(igraph)
    """

    inputs = [x for x in IGraph.nodes() if IGraph.in_degree(x)==1 and x in IGraph.successors(x)]

    if inputs:
        subgraph = networkx.DiGraph()
        subgraph.add_nodes_from(inputs)
        subgraph.graph["label"] = "Inputs"

        # remove subgraphs for inputs added by add_style_sccs
        for x in list(IGraph.graph["subgraphs"]):
            y = x.nodes()
            if len(y)==1 and y[0] in inputs:
                IGraph.graph["subgraphs"].remove(x)

        IGraph.graph["subgraphs"].append(subgraph)


def add_style_outputs(IGraph):
    """
    Adds a subgraph to the *dot* representation of *IGraph* that contains all outputs.
    Nodes that belong to the same *dot* subgraph are contained in a rectangle and treated separately during layout computations.
    In addition, the subgraph is labeled by a *"Outputs"* in bold font.

    **arguments**:
        * *IGraph*: interaction graph

    **example**::

          >>> add_style_outputs(igraph)
    """

    outputs = [x for x in IGraph if not list(IGraph.successors(x))]

    if outputs:
        subgraph = networkx.DiGraph()
        subgraph.add_nodes_from(outputs)
        subgraph.graph["label"] = "Outputs"
        IGraph.graph["subgraphs"].append(subgraph)


def add_style_constants(IGraph):
    """
    Sets the attribute *"style"="plaintext"* with *"fillcolor"="none"* and *"fontname"="Times-Italic"* for all constants.

    **arguments**:
        * *IGraph*: interaction graph

    **example**::

          >>> add_style_constants(igraph)
    """

    for x in IGraph.nodes():
        if not IGraph.predecessors(x):
            IGraph.nodes[x]["shape"] = "plaintext"
            IGraph.nodes[x]["fillcolor"] = "none"
            IGraph.nodes[x]["fontname"] = "Times-Italic"

            for y in IGraph.successors(x):
                IGraph.adj[x][y]["color"] = "gray"


def add_style_sccs(IGraph):
    """
    Adds a subgraph for every non-trivial strongly connected component (SCC) to the *dot* representation of *IGraph*.
    Nodes that belong to the same *dot* subgraph are contained in a rectangle and treated separately during layout computations.
    Each subgraph is filled by a shade of gray that gets darker with an increasing number of SCCs that are above it in the condensation graph.
    Shadings repeat after a depth of 9.

    **arguments**:
        * *IGraph*: interaction graph

    **example**::

          >>> add_style_sccs(igraph)
    """

    subgraphs = networkx.DiGraph()
    condensation_graph = PyBoolNet.Utility.DiGraphs.digraph2condensationgraph(IGraph)

    for scc in condensation_graph.nodes():
        depth = condensation_graph.nodes[scc]["depth"]
        col   = 2+(depth % 8)

        subgraph = networkx.DiGraph()
        subgraph.add_nodes_from(scc)
        subgraph.graph["style"] = "filled"
        subgraph.graph["color"] = "none"
        subgraph.graph["fillcolor"] = "/greys9/%i"%col

        IGraph.graph["subgraphs"].append(subgraph)


def add_style_path(IGraph, Path, Color):
    """
    Sets the color of all nodes and edges involved in the given *Path* to *Color*.

    **arguments**:
        * *IGraph*: interaction graph
        * *Path* (list): sequence of component names
        * *Color* (str): color of the path

    **example**::

        >>> path = ["Raf", "Ras", "Mek"]
        >>> add_style_path(igraph, path, "red")
    """

    if not Path: return

    names = IGraph.nodes()
    assert(all([x in names for x in Path]))

    for x in Path:
        IGraph.nodes[x]["color"] = Color

    if len(Path)>1:
        for x,y in zip(Path[:-1],Path[1:]):
            IGraph.adj[x][y]["color"]     = Color
            IGraph.adj[x][y]["penwidth"]  = "2"


def add_style_subgraphs(IGraph, Subgraphs):
    """
    Adds the subgraphs given in *Subgraphs* to *IGraph* - or overwrites them if they already exist.
    Nodes that belong to the same *dot* subgraph are contained in a rectangle and treated separately during layout computations.
    *Subgraphs* must consist of tuples of the form *NodeList*, *Attributs* where *NodeList* is a list of graph nodes and *Attributes*
    is a dictionary of subgraph attributes in *dot* format.

    .. note::

        *Subgraphs* must satisfy the following property:
        Any two subgraphs have either empty intersection or one is a subset of the other.
        The reason for this requirement is that *dot* can not draw intersecting subgraphs.

    **arguments**:
        * *IGraph*: interaction graph
        * *Subgraphs* (list): pairs of lists and subgraph attributes

    **example**:

        >>> sub1 = (["v1","v2"], {"label":"Genes"})
        >>> sub2 = (["v3","v4"], {})
        >>> subgraphs = [sub1,sub2]
        >>> add_style_subgraphs(igraph, subgraphs)
    """

    PyBoolNet.Utility.DiGraphs.add_style_subgraphs(IGraph, Subgraphs)


def add_style_default(IGraph):
    """
    A convenience function that adds styles for interaction signs, SCCs, inputs, outputs and constants.

    **arguments**:
        * *IGraph*: interaction graph

    **example**::

        >>> add_style_default(igraph, path)

    """

    # careful, the order matters
    add_style_interactionsigns(IGraph)
    add_style_sccs(IGraph)
    add_style_inputs(IGraph)
    add_style_outputs(IGraph)
    add_style_constants(IGraph)


def activities2animation(IGraph, Activities, FnameGIF, FnameTMP="tmp*.jpg", Delay=50, Loop=0):
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
        * *IGraph*: interaction graph
        * *Activities* (list): sequence of activities
        * *Delay* (int): number of 1/100s between each frame
        * *Loop* (int): number of repetitions, use 0 for infinite
        * *FnameTMP* (str): name for temporary image files, use "*" to indicate counter
        * *FnameGIF* (str): name of the output *gif* file

    **example**::

        >>> activities = ["11--1-0", "111-1-0", "11111-0", "1111100"]
        >>> activities2animation(igraph, activities, "animation.gif")
    """

    assert("." in FnameTMP)
    assert("*" in FnameTMP)
    assert(FnameGIF[-4:].lower()=='.gif')
    assert(Activities != None)

    width = len(str(len(Activities)))+1
    for i,x in enumerate(Activities):
        dummy = copy(IGraph)
        add_style_activities(dummy, x)
        dummy.graph["label"] = "%i of %i"%(i+1,len(Activities))
        igraph2image(IGraph = dummy,
                     FnameIMAGE = FnameTMP.replace("*",'{i:0{w}d}'.format(i=i,w=width)),
                     Silent = True)

    filetype = FnameTMP.split(".")[-1]
    cmd = [CMD_CONVERT, "-delay", str(Delay), "-loop", str(Loop), FnameTMP, FnameGIF]
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    output, error = proc.communicate()

    if not (proc.returncode ==0):
        print(output)
        print(error)
        print('"convert" finished with return code %i'%proc.returncode)
        print("cmd: %s"%' '.join(cmd))
        raise Exception

    for i in range(len(Activities)):
        fname = FnameTMP.replace("*",'{i:0{w}d}'.format(i=i,w=width))
        os.remove(fname)

    print("created %s"%FnameGIF)
