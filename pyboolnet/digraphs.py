

import itertools
import logging
import os
import subprocess
from typing import Optional, List, Union, Iterable

import networkx

from pyboolnet import find_command

LAYOUT_ENGINES = {name: find_command(name) for name in ["dot", "neato", "fdp", "sfdp", "circo", "twopi"]}

log = logging.getLogger(__name__)


def _primes2signed_digraph(primes: dict) -> networkx.DiGraph:
    """
    Creates a signed interaction graph for primes.
    The method is in this module to avoid circular imports between the modules prime_implicants and interaction_graphs.
    """

    digraph = networkx.DiGraph()

    edges = {}
    for name in primes:
        digraph.add_node(name)
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
        digraph.add_edge(k, name, sign=edges[(k, name)])

    return digraph


def digraph2dot_lines(digraph: networkx.DiGraph, indent: int = 1):
    """
    Basic function to create *dot* lines from a *networkx.DiGraph*.

    **arguments**:
        * *digraph* (*networkx.DiGraph* or *networkx.MultiDiGraph*)

    **returns**:
        * list of *dot* lines
    """

    space = indent * "  "
    lines = []

    # fix cluster_ids for subgraphs
    if "subgraphs" in digraph.graph:
        for ID, subgraph in enumerate(digraph.graph["subgraphs"]):
            subgraph.graph["cluster_id"] = ID

            if not "label" in subgraph.graph:
                subgraph.graph["label"] = ""
                # bugfix for inherited labels
                # see: http://www.graphviz.org/content/cluster-and-graph-labels-bug

    hit = False
    # node and edge defaults first
    for key in ["node", "edge"]:
        if key in digraph.graph:
            value = digraph.graph[key]
            attr = ', '.join(['%s="%s"'%(str(x),str(y)) for x,y in value.items()])
            if attr:
                lines+= [space+'%s [%s];'%(key,attr)]
            hit = False

    # general graph attributes
    for key, value in sorted(digraph.graph.items()):
        # ignore because treated elsewhere
        key = key.strip()
        if key.lower() in ["subgraphs","cluster_id","node","edge"]:
            continue

        # handle for keys that contain "{"
        # used for graph attributes of the from {rank = same; B; D; Y;}
        if "{" in key:
            lines += [space+key]

        # handle for labels, i.e., the quotation mark problem
        elif key == "label":
            value = value.strip()
            if value.startswith("<"):
                lines += [space+'label = %s;'%value]
            elif value == "":
                lines += [space+'label = "";']
                # bugfix for inherited labels
                # see: http://www.graphviz.org/content/cluster-and-graph-labels-bug

            elif value:
                lines += [space + 'label = "%s"'%value.strip()]
                #lines+= [space+'label=<<B>%s</B>>;'%value.replace("&","&amp;")]

        # everything else is just passed on:
        else:
            lines += [space + '%s = "%s";'%(key, value)]

        hit = True

    if hit:
        lines += ['']

    # handle for subgraphs
    if "subgraphs" in digraph.graph:
        value = digraph.graph["subgraphs"]
        if value:
            tree = subgraphs2tree(value)
            roots = [x for x in tree.nodes() if not list(tree.predecessors(x))]
            for root in roots:
                subnodes = list(networkx.descendants(tree,root))+[root]
                subtree = tree.subgraph(subnodes)
                lines += tree2dot_lines(subtree, indent)

            lines += ['']

    # node attributes
    for node, attr in sorted(digraph.nodes(data=True)):
        if attr:
            values = []
            for k,v in attr.items():

                # html style label attribute
                if str(v).startswith("<"):
                    values += ['%s=%s' % (k, v)]

                # normal attribute
                else:
                    values += ['%s="%s"' % (k,v)]

            values = ', '.join(values)
            lines += [space+'"%s" [%s];' % (node, values)]
        else:
            lines += [space+'"%s";' % node]

    if digraph.order() > 0 and digraph.size() > 0:
        lines += ['']

    # edge attributes
    for source, target, attr in digraph.edges(data=True):

        # sign is reserved for interaction signs
        attr = dict([x for x in attr.items() if not x[0] == "sign"])

        if attr:
            values = []
            for k,v in attr.items():

                # html style label attribute
                if str(v).startswith("<"):
                    values += ['%s=%s' % (k, v)]

                # normal attribute
                else:
                    values += ['%s="%s"' % (k, v)]

            values = ', '.join(values)
            lines += [space+'"%s" -> "%s" [%s];' % (source, target, values)]

        else:

            # for edges without attributes
            lines += [space+'"%s" -> "%s";' % (source, target)]

    if digraph.size() > 0:
        lines += ['']

    return lines


def digraph2dot(digraph: networkx.DiGraph, fname_dot: Optional[str] = None) -> Optional[str]:
    """
    Generates a *dot* file from *digraph* and saves it as *fname_dot* or returns dot file as a string.

    **arguments**:
        * *digraph*: a digraph
        * *fname_dot*: name of *dot* file or *None*

    **returns**:
        * *text_dot*: file as string if not *fname_dot is None*, otherwise it returns *None*

    **example**::

          >>> digraph2dot(digraph, "digraph.dot")
          >>> digraph2dot(digraph)
    """

    if digraph.order() == 0:
        log.warning("digraph has no nodes.")
        return

    if not type(list(digraph.nodes())[0]) == str:
        digraph = networkx.relabel_nodes(digraph, mapping=lambda x: str(x))

    lines = ["digraph {"]
    lines += digraph2dot_lines(digraph)
    lines += ["}"]

    dot_text = "\n".join(lines)

    if fname_dot:
        with open(fname_dot, "w") as f:
            f.writelines(dot_text)

        log.info(f"created {fname_dot}")

    return dot_text


def dot2image(fname_dot: str, fname_image: str, layout_engine: str = "dot"):
    """
    Creates an image file from a *dot* file using the Graphviz layout *layout_engine*.
    The output format is detected automatically.
    Use e.g. ``dot -T?`` to find out which output formats are supported on your installation.

    **arguments**:
        * *fname_dot*: name of input *dot* file
        * *fname_image*: name of output file
        * *layout_engine*: one of "dot", "neato", "fdp", "sfdp", "circo", "twopi"

    **example**::

          >>> dot2image("mapk.dot", "mapk.pdf")
    """

    filetype = fname_image.split('.')[-1]

    cmd = [LAYOUT_ENGINES[layout_engine], "-T" + filetype, fname_dot, "-o", fname_image]
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    output, error = proc.communicate()

    if not (proc.returncode == 0) or not os.path.exists(fname_image):
        log.error(output)
        log.error(error)
        log.error(f'"{layout_engine}" finished with return code {proc.returncode}')
        raise Exception

    print("created %s" % fname_image)


def digraph2image(digraph: networkx.DiGraph, fname_image: str, layout_engine: str):
    """
    Creates an image file from a *digraph* file using the Graphviz layout *layout_engine*.
    The output format is detected automatically.
    Use e.g. ``dot -T?`` to find out which output formats are supported on your installation.

    **arguments**:
        * *digraph* (*networkx.DiGraph* or *networkx.MultiDiGraph*)
        * *fname_dot*: name of input *dot* file
        * *layout_engine*: one of "dot", "neato", "fdp", "sfdp", "circo", "twopi"
        * *fname_image*: name of output file

    **example**::

          >>> dot2image("mapk.dot", "mapk.pdf")
    """

    filetype = fname_image.split('.')[-1]

    cmd = [LAYOUT_ENGINES[layout_engine], "-T" + filetype, "-o", fname_image]
    dotfile = digraph2dot(digraph)

    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = proc.communicate(input=dotfile.encode())
    proc.stdin.close()

    if not (proc.returncode == 0) or not os.path.exists(fname_image):
        log.error(dotfile)
        log.error(out)
        log.error(err)
        log.error('dot did not respond with return code 0')
        log.error(f"command: {' '.join(cmd)}")
        raise Exception

    log.info(f"created {fname_image}")


def subgraphs2tree(subgraphs) -> networkx.DiGraph:
    """
    Creates a tree (*networkx.DiGraph*) *G* from the list *subgraphs* such that each node of *G* is a subgraph
    and there is an edge from *x* to *y* if *x* is the smallest superset of *y*.
    It is required that the node sets of any *x,y* of *subgraphs* are either disjoint or one is a subset of the other.
    The function throws an exception if there are *x,y* of *subgraphs* that violate this condition.

    This function is used to draw Graphviz_ subgraphs.

    It is recommended that the digraphs in *subgraphs* contain only unstyled nodes and no edges.
    Use the original graph to style edges and nodes of the subgraph.
    Use the digraphs in *subgraphs* only to style the color and label of the subgraph.

    If you do node styles or edges to a subgraph, styles may be overwritten and duplicate edges may be introduced.

    **arguments**:
        * *subgraphs*: list of *networkx.DiGraphs*

    **returns**:
        * *tree*: a tree that captures the "strictest inclusion" property

    **example**::

        >>> nodes1 = igraph.nodes()[:10]
        >>> nodes2 = igraph.nodes()[3:8]
        >>> sub1 = networkx.DiGraph()
        >>> sub1.add_nodes_from(nodes1)
        >>> sub1.graph["label"] = "subgraph1"
        >>> sub2 = networkx.DiGraph()
        >>> sub2.add_nodes_from(nodes2)
        >>> sub2.graph["label"] = "subgraph2"
        >>> subgraph2tree([sub1,sub2])
    """

    tree = networkx.DiGraph()
    tree.add_nodes_from(subgraphs)

    for x in subgraphs:
        for y in subgraphs:
            if x == y:
                continue

            if set(x.nodes()).issuperset(set(y.nodes())):
                tree.add_edge(x, y)

    for x, y in tree.edges():
        for path in networkx.all_simple_paths(tree, x, y):
            if len(path) > 2:
                tree.remove_edge(x, y)
                break

    for node in tree.nodes():
        if "fillcolor" in node.graph and not "style" in node.graph:
            node.graph["style"] = "filled"

        if "fillcolor" not in node.graph and "style" not in node.graph:
            node.graph["color"] = "black"
            node.graph["fillcolor"] = "/prgn10/6"
            node.graph["style"] = "filled"

        if "label" not in node.graph:
            node.graph["label"] = ""

    return tree


def tree2dot_lines(tree: networkx.DiGraph, indent: int = 1):
    """
    Creates a list of *dot* lines from *tree* which is obtained from the function *subgraphs2tree*.
    Handles the nesting and *dot* properties.

    **arguments**:
        * *tree*: graph of subgraph obtained from *subgraphs2tree*

    **returns**:
        * list of *dot* lines
    """

    roots = [x for x in tree.nodes() if not list(tree.predecessors(x))]
    
    assert len(roots) == 1
    
    root = roots[0]
    
    assert "subgraphs" not in root.graph
    
    cluster_id = root.graph["cluster_id"]
    space = indent * "  "

    lines = []
    lines += [space + "subgraph cluster_%i {" % cluster_id]
    lines += [x for x in digraph2dot_lines(digraph=root, indent=indent + 1)]

    for successor in tree.successors(root):
        subnodes = list(networkx.descendants(tree, successor)) + [successor]
        subtree = tree.subgraph(subnodes)
        lines += tree2dot_lines(subtree, indent=indent + 1)

    lines += [space+"}"]

    return lines


def digraph2sccgraph(digraph: networkx.DiGraph) -> networkx.DiGraph:
    """
    Creates the strongly connected component graph from the interaction graph.
    Each node consists of a tuple of names the make up that nodes SCC.
    Note that the SCC graph is cycle-free and can therefore not distinguish
    between constants and inputs.
    The graph has no additional data.

    **arguments**:
        * *digraph*: a directed graph

    **returns**:
        * *scc_graph*: the scc graph

    **example**::

        >>> sccgraph = digraph2sccgraph(igraph)
        >>> sccgraph.nodes()
        [('Ash1', 'Cbf1'), ('gal',), ('Gal80',), ('Gal4','Swi5)]
        >>> sccgraph.edges()
        [(('gal',), ('Ash1', 'Cbf1')), (('gal',), ('Gal80',)),
         (('Gal80',),('Gal4','Swi5))]
    """

    sccs = sorted([tuple(sorted(c)) for c in networkx.strongly_connected_components(digraph)])

    sccgraph = networkx.DiGraph()
    sccgraph.add_nodes_from(sccs)

    for U, W in itertools.product(sccs, sccs):
        if U == W:
            continue  # no self-loops in SCC graph

        for u, w in itertools.product(U, W):
            if digraph.has_edge(u, w):
                sccgraph.add_edge(U, W)
                break

    return sccgraph


def digraph2condensationgraph(digraph: networkx.DiGraph) -> networkx.DiGraph:
    """
    Creates the condensation graph from *digraph*.
    The condensation graph is similar to the SCC graph but it replaces
    cascades between SCCs by single edges.
    Its nodes are therefore non-trivial SCCs or inputs.
    As for the SCC graph, nodes are tuples of names that belong to the SCC.
    The condensation graph is cycle-free and does distinguish between inputs
    and constants.
    The graph has no additional data.

    **arguments**:
        * *digraph*: directed graph

    **returns**:
        * *condensation_graph*: the condensation graph

    **example**::

        >>> cgraph = digraph2condensationgraph(igraph)
        >>> cgraph.nodes()
        [('Ash1', 'Cbf1'), ('Gal4',), ('Gal80',), ('Cbf1','Swi5)]
        >>> cgraph.edges()
        [(('Gal4',), ('Ash1', 'Cbf1')), (('Gal4',), ('Gal80',)),
         (('Gal80',),('Cbf1','Swi5))]
    """

    sccs = sorted([tuple(sorted(scc)) for scc in networkx.strongly_connected_components(digraph)])
    cascades = [scc for scc in sccs if (len(scc) == 1) and not digraph.has_edge(scc[0], scc[0])]
    noncascades = [scc for scc in sccs if scc not in cascades]

    cgraph = networkx.DiGraph()
    cgraph.add_nodes_from(noncascades)

    # rgraph is a copy of Digraph with edges leaving noncascade components removed.
    # will use rgraph to decide if there is a cascade path between U and W (i.e. edge in cgraph)
    rgraph = networkx.DiGraph(digraph.edges())

    for U, W in itertools.product(noncascades,noncascades):
        if U == W:
            continue

        rgraph = digraph.copy()
        for X in noncascades:
            if not X == U and not X == W:
                rgraph.remove_nodes_from(X)

        if has_path(rgraph, U, W):
            cgraph.add_edge(U, W)

    # annotate each node with its depth in the hierarchy and an integer ID
    for ID, target in enumerate(cgraph.nodes()):
        depth = 1

        for source in networkx.ancestors(cgraph, target):
            for p in networkx.all_simple_paths(cgraph, source, target):
                depth = max(depth, len(p))

        cgraph.nodes[target]["depth"] = depth
        cgraph.nodes[target]["id"] = ID

    return cgraph


def add_style_subgraphs(digraph: networkx.DiGraph, subgraphs):
    """
    Adds the subgraphs given in *subgraphs* to *digraph* or overwrites them if they already exist.
    Nodes that belong to the same *dot* subgraph are contained in a rectangle and treated separately during layout computations.
    *subgraphs* must consist of tuples of the form *NodeList*, *Attributs* where *NodeList* is a list of graph nodes and *Attributes*
    is a dictionary of subgraph attributes in *dot* format.

    .. note::

        *subgraphs* must satisfy the following property:
        Any two subgraphs have either empty intersection or one is a subset of the other.
        The reason for this requirement is that *dot* can not draw intersecting subgraphs.

    **arguments**:
        * *digraph*: directed graph
        * *subgraphs*: pairs of lists and subgraph attributes

    **example**:

        >>> sub1 = (["v1","v2"], {"label":"Genes"})
        >>> sub2 = (["v3","v4"], {})
        >>> subgraphs = [sub1,sub2]
        >>> add_style_subgraphs(graph, subgraphs)
    """

    if "subgraphs" not in digraph.graph:
        digraph.graph["subgraphs"] = []

    for nodes, attr in subgraphs:
        if not nodes: continue
        for x in nodes:
            if x not in digraph:
                log.error(" error: subgraph nodes must belong to the digraph")
                log.error(" this node does not exist: %s" % x)
                raise Exception

        subgraph = networkx.DiGraph()
        subgraph.graph["color"] = "none"
        subgraph.add_nodes_from(nodes)
        if attr:
            subgraph.graph.update(attr)

        for x in list(digraph.graph["subgraphs"]):
            if sorted(x.nodes()) == sorted(subgraph.nodes()):
                digraph.graph["subgraphs"].remove(x)

        digraph.graph["subgraphs"].append(subgraph)


def convert_nodes_to_anonymous_strings(digraph: networkx.DiGraph):
    """
    used to convert meaningful nodes into strings for drawing.
    """

    mapping = {x: str(i) for i, x in enumerate(digraph.nodes())}
    networkx.relabel_nodes(digraph, mapping, copy=False)


def find_ancestors(digraph: networkx.DiGraph, node_or_nodes):
    """
    Return all nodes having a path to one of the nodes in *node_or_nodes*.
    """

    if node_or_nodes in digraph:
        return networkx.ancestors(digraph, node_or_nodes)
    else:
        # bugfix for networkx.ancestors (it doesn't recognize self-loops)
        ancestors = set([x for x in node_or_nodes if x in networkx.nodes_with_selfloops(digraph)])
        for x in node_or_nodes:
            ancestors.add(x)
            ancestors.update(networkx.ancestors(digraph, x))
        return ancestors


def find_successors(digraph: networkx.DiGraph, node_or_nodes: Union[str, Iterable[str]]) -> List[str]:
    """
    returns successors of a node or list of nodes
    """

    if node_or_nodes in digraph:
        return digraph.successors(node_or_nodes)

    else:
        successors = set([])
        for x in node_or_nodes:
            successors.update(set(digraph.successors(x)))

        return sorted(successors)


def find_predecessors(digraph: networkx.DiGraph, node_or_nodes):
    """
    returns successors of a node or the union of several nodes
    """

    if node_or_nodes in digraph:
        return digraph.predecessors(node_or_nodes)
    else:
        predecessors = set([])
        for x in node_or_nodes:
            predecessors.update(set(digraph.predecessors(x)))
        return sorted(predecessors)


def has_path(digraph, from_node_or_nodes, to_node_or_nodes):
    assert "!s" not in digraph
    assert "!t" not in digraph

    if from_node_or_nodes in digraph:
        source = from_node_or_nodes
    else:
        source = "!s"
        digraph.add_node("!s")
        digraph.add_edges_from([("!s", x) for x in from_node_or_nodes])

    if to_node_or_nodes in digraph:
        target = to_node_or_nodes
    else:
        target = "!t"
        digraph.add_node("!t")
        digraph.add_edges_from([(y, "!t") for y in to_node_or_nodes])

    answer = networkx.has_path(digraph, source, target)
    for x in ["!s", "!t"]:
        if x in digraph:
            digraph.remove_node(x)

    return answer


def has_edge(digraph, from_node_or_nodes, to_node_or_nodes):

    if from_node_or_nodes in digraph:
        from_node_or_nodes = [from_node_or_nodes]
    if to_node_or_nodes in digraph:
        to_node_or_nodes = [to_node_or_nodes]

    for x in from_node_or_nodes:
        for y in to_node_or_nodes:
            if digraph.has_edge(x, y):
                return True

    return False


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
