

import os
import subprocess

try:
    # Python 2.x
    import ConfigParser as configparser
except ImportError:
    # Python 3.x
    import configparser

myconfigparser = configparser
    
BASE = os.path.abspath(os.path.join(os.path.dirname(__file__)))
BASE = os.path.normpath(BASE)
config = myconfigparser.SafeConfigParser()
config.read( os.path.join(BASE, "Dependencies", "settings.cfg") )
CMD_DOT = os.path.join( BASE, "Dependencies", config.get("Executables", "dot") )

import networkx
import itertools





def digraph2dot( DiGraph, Indent=1 ):
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
        if key.lower() in ["subgraphs","cluster_id","node","edge"]:
            continue
        if key.strip()=="label":
            if value.strip().startswith("<"):
                lines+= [space+'label = %s;'%value]
            elif value=="":
                lines+= [space+'label = "";']
                # bugfix for inherited labels
                # see: http://www.graphviz.org/content/cluster-and-graph-labels-bug
                
            elif value.strip():
                lines+= [space+'label=<<B>%s</B>>;'%value.replace("&","&amp;")]
        else:
            lines+= [space+'%s = "%s";'%(key,value)]
        hit = True
        
    if hit: lines+= ['']

    # special handle for subgraphs
    if "subgraphs" in DiGraph.graph:
        value = DiGraph.graph["subgraphs"]
        if value:
            tree = subgraphs2tree( value )
            roots = [x for x in tree.nodes() if not tree.predecessors(x)]
            for root in roots:
                subnodes = list(networkx.descendants(tree,root))+[root]
                subtree  = tree.subgraph(subnodes)
                lines+= tree2dotlines( subtree, Indent ) 
            
            lines+= ['']

    # node attributes
    for node, attr in sorted(DiGraph.nodes(data=True)):
        if attr:
            values = []
            for k,v in attr.items():

                # html style label attribute
                if v.startswith("<"):
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
            
            # for edges with attributes
            values = ', '.join(['%s="%s"'%(str(x),str(y)) for x,y in sorted(attr.items())])
            lines += [space+'"%s" -> "%s" [%s];'%(source,target,values)]

        else:
            
            # for edges without attributes
            lines += [space+'"%s" -> "%s";'%(source,target)]

    if DiGraph.size()>0:
        lines+= ['']

    # condensation graph
    if "condensation" in DiGraph.graph:
        lines+= ['']
        condensation_graph = DiGraph.graph["condensation"]

        if condensation_graph.order()>0:

            lines+= [space+"subgraph cluster_condensation {"]
            lines+= [space+"\t"+'label=<<B>Condensation Graph</B>>;']
            lines+= [space+"\t"+'color="none";']
            scc_ids = {}
            for i, scc in enumerate(condensation_graph.nodes()):
                scc_ids[scc] = "$scc%i"%i
                
            for scc in condensation_graph.nodes():
                if len(scc)==1:
                    line = '"%s" [label="%s"];'%(scc_ids[scc], scc[0])
                else:    
                    line = '"%s" [shape="circle", color="black", label="%i"];'%(scc_ids[scc], len(scc))
                line = line
                lines+= [space+"\t"+line]
            lines+= ['']
            
            for scc1, scc2 in condensation_graph.edges():
                line = '"%s" -> "%s"'%(scc_ids[scc1], scc_ids[scc2])
                lines+= [space+"\t"+line]
            lines+= [space+"}"]
            
    return lines


def dot2image( FnameDOT, FnameIMAGE ):
    """
    Creates an image file from a *dot* file using ``dot -T? FnameDOT -o FnamePDF`` where ``?`` is one of the output formats supported by *dot*.
    Use ``dot -T?`` to find out which output formats are supported on your installation.
    
    **arguments**:
    
        * *FnameDOT*: name of input *dot* file
        
        * *FnameIMAGE*: name of output file

    **returns**: *None*
        
    **example**::

          dot2image( "mapk.dot", "mapk.pdf" )
    """

    assert( FnameIMAGE.count('.')>=1 and FnameIMAGE.split('.')[-1].isalnum() )

    filetype = FnameIMAGE.split('.')[-1]
    
    
    cmd = [CMD_DOT, "-T"+filetype, FnameDOT, "-o", FnameIMAGE]
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    output, error = proc.communicate()

    if not (proc.returncode ==0) or not os.path.exists(FnameIMAGE):
        print(output)
        print(error)
        print('"dot" finished with return code %i'%proc.returncode)
        raise Exception
    
    print("created %s"%FnameIMAGE)


def subgraphs2tree( Subgraphs ):
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
            node.graph["fillcolor"] = "/prgn10/6"
            node.graph["style"] = "filled"

        if not "label" in node.graph:
            node.graph["label"] = ""
        
    return tree


def tree2dotlines( Tree, Indent=1 ):
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
    lines+= [x for x in digraph2dot( DiGraph=root, Indent=Indent+1 )]
    
    for successor in Tree.successors(root):
        subnodes = list(networkx.descendants(Tree,successor))+[successor]
        subtree  = Tree.subgraph(subnodes)
        lines+= tree2dotlines( subtree, Indent=Indent+1 )
        
    lines+= [space+"}"]


    return lines
                        









def digraph2sccgraph( Digraph ):
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

            >>> sccgraph = digraph2sccgraph( igraph )
            >>> sccgraph.nodes()
            [('Ash1', 'Cbf1'), ('gal',), ('Gal80',), ('Gal4','Swi5)]
            >>> sccgraph.edges()
            [(('gal',), ('Ash1', 'Cbf1')), (('gal',), ('Gal80',)),
             (('Gal80',),('Gal4','Swi5))]
    """
    
    sccs = sorted([tuple(sorted(c)) for c in networkx.strongly_connected_components( Digraph )])

    sccgraph = networkx.DiGraph()
    sccgraph.add_nodes_from( sccs )

    for U,W in itertools.product( sccs, sccs ):
        if U==W: continue # no self-loops in SCC graph

        for u,w in itertools.product(U,W):
            if Digraph.has_edge(u,w):
                sccgraph.add_edge(U,W)
                break    
    
    return sccgraph



def digraph2condensationgraph( Digraph ):
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

            >>> cgraph = digraph2condensationgraph( igraph )
            >>> cgraph.nodes()
            [('Ash1', 'Cbf1'), ('Gal4',), ('Gal80',), ('Cbf1','Swi5)]
            >>> cgraph.edges()
            [(('Gal4',), ('Ash1', 'Cbf1')), (('Gal4',), ('Gal80',)),
             (('Gal80',),('Cbf1','Swi5))]
    """
    
    sccs = sorted([tuple(sorted(c)) for c in networkx.strongly_connected_components( Digraph )])
    cascades = [c for c in sccs if (len(c)==1) and not Digraph.has_edge(c[0],c[0])]
    noncascades = [c for c in sccs if c not in cascades]

    cgraph = networkx.DiGraph()
    cgraph.add_nodes_from( noncascades )
    
    # rgraph is a copy of IGraph with edges leaving noncascade components removed.
    # will use rgraph to decide if their is a cascade path between U and W (i.e. edge in cgraph)
    rgraph = networkx.DiGraph(Digraph.edges())
    
    for scc in noncascades:
        for s in scc:
            for t in rgraph.successors(s):
                if not tuple([t]) in cascades:
                    rgraph.remove_edge(s,t)

    for U,W in itertools.product(noncascades,noncascades):
        if U==W: continue

        # special case: direct edge between U and W
        for u,w in itertools.product(U,W):
            if Digraph.has_edge(u,w):
                cgraph.add_edge(U,W)
                break
        if cgraph.has_edge(U,W): continue
                
        # general case: cascade path from U to W
        rgraph.add_nodes_from(['x','y'])
        rgraph.add_edges_from([('x',u) for u in U]+[(w,'y') for w in W])

        if networkx.has_path(rgraph, 'x','y'):
            cgraph.add_edge(U,W)

        rgraph.remove_nodes_from(['x','y'])

    # annotate each node with its depth in the hierarchy and an integer ID
    for ID, target in enumerate(cgraph.nodes()):
        depth = 1
        for source in networkx.ancestors(cgraph, target):
            for p in networkx.all_simple_paths(cgraph, source, target):
                depth = max(depth, len(p))
        cgraph.node[target]["depth"] = depth
        cgraph.node[target]["id"]    = ID

    return cgraph


def ancestors( DiGraph, Nodes ):
    """
    returns all ancestors of *Nodes*.
    """

    # single node
    if type(Nodes)==str:
        return networkx.ancestors(DiGraph, Nodes)

    # several nodes
    else:
        result = set([])
        for x in Nodes:
            result.update( networkx.ancestors(DiGraph,x) )
            
        return sorted(result)





    
