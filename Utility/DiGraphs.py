

import os
import subprocess
import networkx
import itertools

import PyBoolNet.Utility.Misc
    
BASE = os.path.abspath(os.path.join(os.path.dirname(__file__),".."))
BASE = os.path.normpath(BASE)
config = PyBoolNet.Utility.Misc.myconfigparser.SafeConfigParser()
config.read(os.path.join(BASE, "Dependencies", "settings.cfg"))
LAYOUT_ENGINES = {name:os.path.join(BASE, "Dependencies", config.get("Executables", name)) for name in ["dot","neato","fdp","sfdp","circo","twopi"]}



def digraph2dotlines(DiGraph, Indent=1):
    """
    Basic function to create *dot* lines from a *networkx.DiGraph*.

    **arguments**:
        * *DiGraph* (*networkx.DiGraph*)

    **returns**:
        * list of *dot* lines
    """

    space = Indent*"  "
    lines = []

    # fix cluster_ids for subgraphs
    if "subgraphs" in DiGraph.graph:
        for ID, subgraph in enumerate(DiGraph.graph["subgraphs"]):
            subgraph.graph["cluster_id"] = ID
            
            if not "label" in subgraph.graph:
                subgraph.graph["label"] = ""
                # bugfix for inherited labels
                # see: http://www.graphviz.org/content/cluster-and-graph-labels-bug

    hit = False
    # node and edge defaults first
    for key in ["node", "edge"]:
        if key in DiGraph.graph:
            value = DiGraph.graph[key]
            attr = ', '.join(['%s="%s"'%(str(x),str(y)) for x,y in value.items()])
            if attr:
                lines+= [space+'%s [%s];'%(key,attr)]
            hit = False
    
    # general graph attributes
    for key, value in sorted(DiGraph.graph.items()):
        # ignore because treated elsewhere
        key = key.strip()
        if key.lower() in ["subgraphs","cluster_id","node","edge"]:
            continue

        # handle for keys that contain "{"
        # used for graph attributes of the from {rank = same; B; D; Y;}
        if "{" in key:
            lines+= [space+key]

        # handle for labels, i.e., the quotation mark problem
        elif key=="label":
            value = value.strip()
            if value.startswith("<"):
                lines+= [space+'label = %s;'%value]
            elif value=="":
                lines+= [space+'label = "";']
                # bugfix for inherited labels
                # see: http://www.graphviz.org/content/cluster-and-graph-labels-bug
                
            elif value:
                lines+= [space+'label = "%s"'%value.strip()]
                #lines+= [space+'label=<<B>%s</B>>;'%value.replace("&","&amp;")]

        # everything else is just passed on:
        else:
            lines+= [space+'%s = "%s";'%(key,value)]
            
        hit = True
        
    if hit: lines+= ['']

    # handle for subgraphs
    if "subgraphs" in DiGraph.graph:
        value = DiGraph.graph["subgraphs"]
        if value:
            tree = subgraphs2tree(value)
            roots = [x for x in tree.nodes() if not tree.predecessors(x)]
            for root in roots:
                subnodes = list(networkx.descendants(tree,root))+[root]
                subtree  = tree.subgraph(subnodes)
                lines+= tree2dotlines(subtree, Indent) 
            
            lines+= ['']

    # node attributes
    for node, attr in sorted(DiGraph.nodes(data=True)):
        if attr:
            values = []
            for k,v in attr.items():

                # html style label attribute
                if str(v).startswith("<"):
                    values+=['%s=%s'%(k,v)]

                # normal attribute
                else:
                    values+=['%s="%s"'%(k,v)]
                    
            values = ', '.join(values)
            lines += [space+'"%s" [%s];'%(node, values)]
        else:
            lines += [space+'"%s";'%node]

    if DiGraph.order()>0 and DiGraph.size()>0:
        lines+= ['']

    # edge attributes
    for source, target, attr in sorted(DiGraph.edges(data=True)):
        
        # sign is reserved for interaction signs
        attr = dict([x for x in attr.items() if not x[0]=="sign"])

        if attr:
            values = []
            for k,v in attr.items():

                # html style label attribute
                if str(v).startswith("<"):
                    values+=['%s=%s'%(k,v)]

                # normal attribute
                else:
                    values+=['%s="%s"'%(k,v)]

            values = ', '.join(values)
            lines += [space+'"%s" -> "%s" [%s];'%(source,target,values)]

        else:
            
            # for edges without attributes
            lines += [space+'"%s" -> "%s";'%(source,target)]

    if DiGraph.size()>0:
        lines+= ['']
            
    return lines


def digraph2dot(DiGraph, FnameDOT=None):
    """
    Generates a *dot* file from *DiGraph* and saves it as *FnameDOT* or returns dot file as a string.
    
    **arguments**:
        * *DiGraph*: networkx.DiGraph
        * *FnameDOT* (str): name of *dot* file or *None*

    **returns**:
        * *FileDOT* (str): file as string if not *FnameDOT==None*, otherwise it returns *None*

    **example**::

          >>> digraph2dot(digraph, "digraph.dot")
          >>> digraph2dot(digraph)
    """
    
    if DiGraph.order()==0:
        print("DiGrap has no nodes.")
        if FnameDOT!=None:
            print("%s was not created."%FnameDot)
        return

    assert(type(DiGraph.nodes()[0])==str)
    
    lines = ['digraph {']
    lines+= digraph2dotlines(DiGraph)
    lines += ['}']

    if FnameDOT==None:
        return '\n'.join(lines)
    
    with open(FnameDOT, 'w') as f:
        f.writelines('\n'.join(lines))
    print("created %s"%FnameDOT)
    

def dot2image(FnameDOT, FnameIMAGE, LayoutEngine):
    """
    Creates an image file from a *dot* file using the Graphviz layout *LayoutEngine*.
    The output format is detected automatically.
    Use e.g. ``dot -T?`` to find out which output formats are supported on your installation.
    
    **arguments**:
        * *FnameDOT*: name of input *dot* file
        * *FnameIMAGE*: name of output file
        * *LayoutEngine*: one of "dot", "neato", "fdp", "sfdp", "circo", "twopi"

    **returns**:
        * *None*
        
    **example**::

          >>> dot2image("mapk.dot", "mapk.pdf")
    """

    filetype = FnameIMAGE.split('.')[-1]
    
    
    cmd = [LAYOUT_ENGINES[LayoutEngine], "-T"+filetype, FnameDOT, "-o", FnameIMAGE]
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    output, error = proc.communicate()

    if not (proc.returncode ==0) or not os.path.exists(FnameIMAGE):
        print(output)
        print(error)
        print('"%s" finished with return code %i'%(LayoutEngine,proc.returncode))
        raise Exception
    
    print("created %s"%FnameIMAGE)


def digraph2image(DiGraph, FnameIMAGE, LayoutEngine, Silent=False):
    """
    Creates an image file from a *DiGraph* file using the Graphviz layout *LayoutEngine*.
    The output format is detected automatically.
    Use e.g. ``dot -T?`` to find out which output formats are supported on your installation.
    
    **arguments**:
        * *FnameDOT*: name of input *dot* file
        * *LayoutEngine*: one of "dot", "neato", "fdp", "sfdp", "circo", "twopi"
        * *FnameIMAGE*: name of output file

    **returns**:
        * *None*
        
    **example**::

          >>> dot2image("mapk.dot", "mapk.pdf")
    """
    
    filetype = FnameIMAGE.split('.')[-1]

    cmd = [LAYOUT_ENGINES[LayoutEngine], "-T"+filetype, "-o", FnameIMAGE]
    dotfile = digraph2dot(DiGraph, FnameDOT=None)
    
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = proc.communicate(input=dotfile.encode())
    proc.stdin.close()

    if not (proc.returncode == 0) or not os.path.exists(FnameIMAGE):
        print(out)
        print('dot did not respond with return code 0')
        raise Exception
    
    if not Silent:
        print("created %s"%FnameIMAGE)
    

def subgraphs2tree(Subgraphs):
    """
    Creates a tree (*networkx.DiGraph*) *G* from the list *Subgraphs* such that each node of *G* is a subgraph
    and there is an edge from *x* to *y* if *x* is the smallest superset of *y*.
    It is required that the node sets of any *x,y* of *Subgraphs* are either disjoint or one is a subset of the other.
    The function throws an exception if there are *x,y* of *Subgraphs* that violate this condition.

    This function is used to draw Graphviz_ subgraphs.

    It is recommended that the digraphs in *Subgraphs* contain only unstyled nodes and no edges.
    Use the original graph to style edges and nodes of the subgraph.
    Use the digraphs in *Subgraphs* only to style the color and label of the subgraph.

    If you do node styles or edges to a subgraph, styles may be overwritten and duplicate edges may be introduced.

    **arguments**:
        * *Subgraphs*: list of *networkx.DiGraphs*

    **returns**:
        * (*networkx.DiGraph*): a tree that captures the "strictest inclusion" property

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
    tree.add_nodes_from(Subgraphs)
    
    for source in Subgraphs:
        for target in Subgraphs:
            if source==target:
                continue

            if set(source.nodes()).issuperset(set(target.nodes())):

                p = tree.predecessors(target)

                if not p:
                    # source is the first graph to contain target: add source->target
                    tree.add_edge(source,target)
                    
                else:
                    # p already contains target
                    assert(len(p)==1)
                    p=p[0]

                    if networkx.has_path(tree, p, source):
                        # source is subset of p, replace p->target by source->target
                        tree.remove_edge(p,target)
                        tree.add_edge(source,target)

                    elif networkx.has_path(tree, source, p):
                        # p is subset of source, nothing to do
                        pass

                    else:
                        # source and p have non-empty intersection but neither is included in the other.
                        print("cannot build inclusion tree")
                        print(" source: %s"%source.nodes())
                        print(" target: %s"%target.nodes())
                        print(" p (predecessor of target): %s"%p.nodes())
                        print(" intersection source and p: %s"%','.join(set(source.nodes()).intersection(set(p.nodes()))))
                        raise Exception


    for node in tree.nodes():

        if "fillcolor" in node.graph and not "style" in node.graph:
            node.graph["style"] = "filled"
        
        if not "fillcolor" in node.graph and not "style" in node.graph:
            node.graph["color"] = "black"
            node.graph["fillcolor"] = "/prgn10/6"
            node.graph["style"] = "filled"

        if not "label" in node.graph:
            node.graph["label"] = ""
        
    return tree


def tree2dotlines(Tree, Indent=1):
    """
    Creates a list of *dot* lines from *Tree* which is obtained from the function *subgraphs2tree*.
    Handles the nesting and *dot* properties.

    **arguments**:
        * *Tree* (*networkx.DiGraph*): graph of subgraph obtained from *subgraphs2tree*

    **returns**:
        * list of *dot* lines
    """


    roots = [x for x in Tree.nodes() if not Tree.predecessors(x)]
    assert(len(roots)==1)
    root = roots[0]
    assert(not "subgraphs" in root.graph)
    cluster_id = root.graph["cluster_id"]
    space = Indent*"  "

    lines = []
    lines+= [space+"subgraph cluster_%i {"%cluster_id]
    lines+= [x for x in digraph2dotlines(DiGraph=root, Indent=Indent+1)]
    
    for successor in Tree.successors(root):
        subnodes = list(networkx.descendants(Tree,successor))+[successor]
        subtree  = Tree.subgraph(subnodes)
        lines+= tree2dotlines(subtree, Indent=Indent+1)
        
    lines+= [space+"}"]


    return lines


def digraph2sccgraph(Digraph):
    """
    Creates the strongly connected component graph from the interaction graph.
    Each node consists of a tuple of names the make up that nodes SCC.
    Note that the SCC graph is cycle-free and can therefore not distinguish
    between constants and inputs.
    The graph has no additional data.

    **arguments**:
        * *Digraph* (networkx.DiGraph): directed graph

    **returns**:
        * *(networkx.DiGraph)*: the SCC graph

    **example**::

            >>> sccgraph = digraph2sccgraph(igraph)
            >>> sccgraph.nodes()
            [('Ash1', 'Cbf1'), ('gal',), ('Gal80',), ('Gal4','Swi5)]
            >>> sccgraph.edges()
            [(('gal',), ('Ash1', 'Cbf1')), (('gal',), ('Gal80',)),
             (('Gal80',),('Gal4','Swi5))]
    """
    
    sccs = sorted([tuple(sorted(c)) for c in networkx.strongly_connected_components(Digraph)])

    sccgraph = networkx.DiGraph()
    sccgraph.add_nodes_from(sccs)

    for U,W in itertools.product(sccs, sccs):
        if U==W: continue # no self-loops in SCC graph

        for u,w in itertools.product(U,W):
            if Digraph.has_edge(u,w):
                sccgraph.add_edge(U,W)
                break    
    
    return sccgraph


def digraph2condensationgraph(Digraph):
    """
    Creates the condensation graph from *Digraph*.
    The condensation graph is similar to the SCC graph but it replaces
    cascades between SCCs by single edges.
    Its nodes are therefore non-trivial SCCs or inputs.
    As for the SCC graph, nodes are tuples of names that belong to the SCC.
    The condensation graph is cycle-free and does distinguish between inputs
    and constants.
    The graph has no additional data.

    **arguments**:
        * *Digraph* (networkx.DiGraph): directed graph

    **returns**:
        * *(networkx.DiGraph)*: the condensation graph

    **example**::

            >>> cgraph = digraph2condensationgraph(igraph)
            >>> cgraph.nodes()
            [('Ash1', 'Cbf1'), ('Gal4',), ('Gal80',), ('Cbf1','Swi5)]
            >>> cgraph.edges()
            [(('Gal4',), ('Ash1', 'Cbf1')), (('Gal4',), ('Gal80',)),
             (('Gal80',),('Cbf1','Swi5))]
    """
    
    sccs = sorted([tuple(sorted(c)) for c in networkx.strongly_connected_components(Digraph)])
    cascades = [c for c in sccs if (len(c)==1) and not Digraph.has_edge(c[0],c[0])]
    noncascades = [c for c in sccs if c not in cascades]

    cgraph = networkx.DiGraph()
    cgraph.add_nodes_from(noncascades)
    
    # rgraph is a copy of Digraph with edges leaving noncascade components removed.
    # will use rgraph to decide if there is a cascade path between U and W (i.e. edge in cgraph)
    rgraph = networkx.DiGraph(Digraph.edges())

    for U,W in itertools.product(noncascades,noncascades):
        if U==W: continue

        rgraph = Digraph.copy()
        for X in noncascades:
            if not X==U and not X==W:
                rgraph.remove_nodes_from(X)
                
        if has_path(rgraph, U, W):
            cgraph.add_edge(U,W)

    # annotate each node with its depth in the hierarchy and an integer ID
    for ID, target in enumerate(cgraph.nodes()):
        depth = 1
        for source in networkx.ancestors(cgraph, target):
            for p in networkx.all_simple_paths(cgraph, source, target):
                depth = max(depth, len(p))
        cgraph.node[target]["depth"] = depth
        cgraph.node[target]["id"]    = ID

    return cgraph


def add_style_subgraphs(DiGraph, Subgraphs):
    """
    Adds the subgraphs given in *Subgraphs* to *DiGraph* or overwrites them if they already exist.
    Nodes that belong to the same *dot* subgraph are contained in a rectangle and treated separately during layout computations.
    *Subgraphs* must consist of tuples of the form *NodeList*, *Attributs* where *NodeList* is a list of graph nodes and *Attributes*
    is a dictionary of subgraph attributes in *dot* format.

    .. note::
    
        *Subgraphs* must satisfy the following property:
        Any two subgraphs have either empty intersection or one is a subset of the other.
        The reason for this requirement is that *dot* can not draw intersecting subgraphs.

    **arguments**:
        * *DiGraph*: directed graph
        * *Subgraphs* (list): pairs of lists and subgraph attributes

    **example**:

        >>> sub1 = (["v1","v2"], {"label":"Genes"})
        >>> sub2 = (["v3","v4"], {})
        >>> subgraphs = [sub1,sub2]
        >>> add_style_subgraphs(graph, subgraphs)
    """


    if not "subgraphs" in DiGraph.graph:
        DiGraph.graph["subgraphs"] = []

    for nodes, attr in Subgraphs:
        if not nodes: continue
        for x in nodes:
            if not x in DiGraph:
                print(" error: subgraph nodes must belong to the digraph")
                print(" this node does not exist: %s"%x)
                raise Exception
            
        subgraph = networkx.DiGraph()
        subgraph.graph["color"] = "black"
        subgraph.add_nodes_from(nodes)
        if attr:
            subgraph.graph.update(attr)

        # overwrite existing subgraphs
        for x in list(DiGraph.graph["subgraphs"]):
            if sorted(x.nodes()) == sorted(subgraph.nodes()):
                DiGraph.graph["subgraphs"].remove(x)
                
        DiGraph.graph["subgraphs"].append(subgraph)
    

def convert_nodes_to_anonymous_strings(DiGraph):
    """
    used to convert meaningful nodes into anonymous stringified integers for drawing.
    """

    mapping = {x:str(i) for i,x in enumerate(DiGraph.nodes())}
    networkx.relabel_nodes(DiGraph, mapping, copy=False)


## graph traversal and analysis ##

def ancestors(DiGraph, X):
    """
    Return all nodes having a path to one of the nodes in X.
    """
    
    if X in DiGraph:
        return networkx.ancestors(DiGraph,X)
    else:
        # bugfix for networkx.ancestors (it doesn't recognize self-loops)
        ancs = set([x for x in X if x in DiGraph.nodes_with_selfloops()])
        for x in X:
            ancs.add(x)
            ancs.update(networkx.ancestors(DiGraph,x))
        return ancs
                                

def successors(DiGraph, X):
    """
    returns successors of a node or the union of several nodes
    """
    
    if X in DiGraph:
        return DiGraph.successors(X)
    else:
        sucs = set([])
        for x in X: sucs.update(set(DiGraph.successors(x)))
        return sorted(sucs)


def predecessors(DiGraph, X):
    """
    returns successors of a node or the union of several nodes
    """
    
    if X in DiGraph:
        return DiGraph.predecessors(X)
    else:
        preds = set([])
        for x in X: preds.update(set(DiGraph.predecessors(x)))
        return sorted(preds)


def has_path(DiGraph, X, Y):
    assert("!s" not in DiGraph)
    assert("!t" not in DiGraph)
    
    if X in DiGraph:
        source = X
    else:
        source = "!s"
        DiGraph.add_node("!s")
        DiGraph.add_edges_from([("!s",x) for x in X])

    if Y in DiGraph:
        target = Y
    else:
        target = "!t"
        DiGraph.add_node("!t")
        DiGraph.add_edges_from([(y,"!t") for y in Y])

    answer = networkx.has_path(DiGraph, source, target)
    for x in ["!s","!t"]:
        if x in DiGraph: DiGraph.remove_node(x)

    return answer


def has_edge(DiGraph, X, Y):
    
    if X in DiGraph: X = [X]
    if Y in DiGraph: Y = [Y]

    for x in X:
        for y in Y:
            if DiGraph.has_edge(x,y):
                return True

    return False



        
    
