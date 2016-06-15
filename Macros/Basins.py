

import os
import sys
import itertools
import networkx
import math
from operator import mul

BASE = os.path.normpath(os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))
sys.path.append(BASE)

import ModelChecking
import TemporalQueries
import TrapSpaces
import AttractorDetection
import StateTransitionGraphs
import InteractionGraphs
import ExampleNetworks
import PrimeImplicants
import Utility

config = Utility.myconfigparser.SafeConfigParser()
config.read( os.path.join(BASE, "Dependencies", "settings.cfg") )
CMD_DOT = os.path.join( BASE, "Dependencies", config.get("Executables", "dot") )




## auxillary functions
def consistent( X, Y):
    return all(X[k]==Y[k] for k in set(X).intersection(set(Y)))


def project( Subspace, Names ):
    return {k:v for k,v in Subspace.items() if k in Names}


def flatten( ListOfLists ):
    return [x for sublist in ListOfLists for x in sublist]


def find_outdags( DiGraph ):
    """
    Finds the largest directed acyclic subgraph that is closed under the successors operation.
    => add to InteractionGraphs?

    **arguments**:
        * *Primes*: primes implicants
        * *Update* (str): either *"asynchronous"* or *"synchronous"*
        * *FnameIMAGE* (str): name of output file

    **returns**::
        * *Names* (list): names of components that belong to outdags

    **example**::

        >>> igraph = IGs.primes2igraph(primes)
        >>> outdags = remove_outdags( igraph )
    """

    cgraph = Utility.digraph2condensationgraph(DiGraph)
    dummy = DiGraph.to_undirected()
    for U in cgraph.nodes():
        dummy.remove_nodes_from(U)

    outdags = []
    for component in networkx.connected_components(dummy):
        if all(y in component for x in component for y in DiGraph.successors(x)):
            outdags+= list(component)

    return outdags


## main functions
def basins_diagram_naive( Primes, Update, Attractors ):
    """
    computes the basins diagram.
    performs case by case for inputs.
    nodes are integers starting from *FirstNode*.
    
    node attributes:
        - size:
        - formula:
        - attractors:

    edge attributes:
        - size:
        - border:

    **returns**::
        * *BasinsDiagram* (netowrkx.DiGraph): the basins diagram
    """
    
    assert(Update in ["synchronous", "mixed", "asynchronous"])
    
    if not Primes:
        print("what are the basins of an empty Boolean network?")
        raise Exception


    # case by case for inputs
    inputs = PrimeImplicants.find_inputs(Primes)
    if inputs:
        cases = []
        for combination in PrimeImplicants.input_combinations(Primes):
            init = "INIT %s"%TemporalQueries.subspace2proposition(combination)
            attr = [x for x in Attractors if consistent(x,combination)]
            cases.append( (init,attr) )
    else:
        cases = [("INIT TRUE",Attractors)]


    # create nodes
    node = 0
    basins = networkx.DiGraph()
    for init, attr in cases:        
        specs = [TemporalQueries.subspace2proposition(Primes,x) for x in attr]
        vectors = len(attr)*[[0,1]]
        for vector in itertools.product( *vectors ):
            if sum(vector)==0: continue

            if len(vector)==1:
                data = {"attractors":   attr,
                        "size":         2**(len(Primes)-len(inputs)),
                        "formula":,     ""}
                
            else:
                spec = " & ".join("EF(%s)"%x if flag else "!EF(%s)"%x for flag, x in zip(vector, specs))
                spec = "CTLSPEC %s"%spec

                answer, accepting = ModelChecking.check_primes(Primes, Update, init, spec)

                data = {"attractors":   [x for flag,x in zip(vector,Attractors) if flag],
                        "size":         accepting["INITACCEPTING_SIZE"],
                        "formula":,     accepting["INITACCEPTING"]}

            if data["size"]>0:
                basins.add_node(node, data)
                node+=1


    # find potential edges
    potential_edges = {}
    for source, source_data in basins.nodes(data=True):
        succs = []
        for target, target_data in basins.nodes(data=True):
            if source==target: continue
            if all(x in source_data["attractors"] for x in target_data["attractors"]):
                succs.append((target,target_data))
        potential_edges[source] = succs


    # create edges
    for source, source_data in basins.nodes(data=True):
        phi1 = source_data["formula"]
        phi2 = target_data["formula"]
        
        if len(potential_edges[source])==1:
            data = {"size": source_data["size"]}
        else:    
            init = "INIT %s"%phi1
            spec = "CTLSPEC E[%s U %s]"%(phi1,phi2)
            answer, accepting = ModelChecking.check_primes(Primes, Update, init, spec)
            
            data = {"size": accepting["INITACCEPTING_SIZE"]}

        init = "INIT %s"phi1
        spec = "CTLSPEC EX(%s)"%phi2
        data["border"] = accepting["INITACCEPTING_SIZE"]

        if data["size"]>0:
            basins.add_edge(source, target, data)

    return basins


def basins_diagram( Primes, Update, Attractors ):
    """
    copy from basins_diagram_naive.
    removes out-dags.
    divides remaining network into connected components.

    **returns**::
        * *BasinsDiagram* (netowrkx.DiGraph): the basins diagram
    """
    
    assert(Update in ["synchronous", "mixed", "asynchronous"])
    
    if not Primes:
        print("what are the basins of an empty Boolean network?")
        raise Exception

    igraph = InteractionGraphs.primes2igraph(Primes)
    outdags = find_outdags(igraph)
    igraph.remove_nodes_from(outdags)
    components = networkx.connected_components(igraph.to_undirected())
    components = [list(x) for x in components]

    diagrams = []
    for component in components:
        subprimes = PrimeImplicants.copy(Primes)
        PrimeImplicants.remove_variables(subprimes, [x for x in Primes if not x in component])
        attrs = []
        for x in Attractors:
            x = project(x,component)
            if not x in attrs: attrs.append(x)

        diagram = basins_diagram_naive(subprimes,Update,attrs)
        diagrams.append(diagram)

    factor = 2**len(outdags)
    
    return cartesian_product(diagrams, factor)


def cartesian_product( Diagrams, Factor ):
    """
    creates the cartesian product of 
    """

    diagram = networkx.DiGraph()
    nodes = [x.nodes(data=True) for x in Diagrams]

    for product in itertools.product(*nodes):

        node = (x for x,_ in product)
        data = {}
        data["size"] = reduce(mul,[x["size"] for _,x in product])
        data["formula"] = " & ".join("(%s)"%x["formula"] for _,x in product)

        attrs = [x["attractors"].items() for _,x in product]
        data["attractors"]  = [dict(flatten(x)) for x in itertools.product(*attrs)
        
        # continue here


        zip(Diagrams,node)

    

def diagram2image(Diagram):
    pass





def dict_product( Dicts ):
    keys  = set.union(*[set(d) for d in Dicts])
    items = [(k, tuple(d.get(k) for d in Dicts)) for k in keys]
    
    return dict(items)


def dict_union( *Dicts ):
    items = [y for x in Dicts for y in x.items()]
    return dict(items)


def add_edge_attributes( DiGraph ):
    
    for source, target, data in DiGraph.edges(data=True):

        size1 = data["size"]
        size2 = DiGraph.node[source]["size"]
        
        if 0 < size1 < size2:
            DiGraph.edge[source][target]["style"] = "dashed"
            
        elif size1 == size2:
            DiGraph.edge[source][target]["style"] = "solid"


def add_node_attributes( DiGraph, NodeWidth ):

    subprimes = DiGraph.graph["subprimes"]
    mints_subprimes = DiGraph.graph["mints_subprimes"]
    size_total = float(2**len(subprimes))

    for node, data in DiGraph.nodes(data=True):

        vector = data["vector"]

        size = data["size"]
        size_percent = size / size_total
        
        indices = [mints_subprimes.index(x) for x in data["mints_reachable"]]
        label = ",".join("A%i"%i for i in indices)
        DiGraph.node[node]["label"] = "<%s<br/>%i>"%(label, size)
            
        DiGraph.node[node]["fillcolor"] = "0.0 0.0 %.2f"%(1-size_percent)
        if size_percent>0.5: DiGraph.node[node]["fontcolor"] = "0.0 0.0 0.8"
        DiGraph.node[node]["width"] = NodeWidth*math.sqrt(size_percent/math.pi)

        if all(d["style"]=="solid" for x,y,d in DiGraph.out_edges(node,data=True)):
            if DiGraph.out_degree(node)>0:
                DiGraph.node[node]["color"] = "cornflowerblue"
                DiGraph.node[node]["penwidth"] = "5"


def add_graph_attributes( DiGraph, Subgraphs=None ):

    DiGraph.graph["subgraphs"] = []
    DiGraph.graph["node"]  = {"shape":"rect","style":"filled","fixedsize":"false","color":"none"}
    DiGraph.graph["edge"]  = {}
    if Subgraphs: InteractionGraphs.add_style_subgraphs(DiGraph, Subgraphs)


def compute_subgraphs( DiGraph ):
    
    nodes = DiGraph.nodes()
    subprimes = DiGraph.graph["subprimes"]
    label = ",".join(DiGraph.graph["component"])
    subgraphs = [ (nodes,{"label":"component= %s"%label, "style":"none"}) ]

    input_combinations = {}
    for node, data in DiGraph.nodes(data=True):
        x = data["inputs"]
        if not x: continue
        key = TemporalQueries.subspace2proposition(subprimes, x)
        if not key in input_combinations:
            input_combinations[key] = []
        input_combinations[key].append(node)

    for label, nodes in input_combinations.items():
        
        subgraphs.append( (nodes, {"label":"input= %s"%label, "style":"none"}) )

    return subgraphs


def remove_auxillary_attributes( DiGraph ):

    DiGraph.graph.pop("component", None)
    DiGraph.graph.pop("subprimes", None)
    DiGraph.graph.pop("mints_subprimes", None)
    
    for x in DiGraph.nodes():
        DiGraph.node[x].pop("vector")
        DiGraph.node[x].pop("mints_reachable")
        DiGraph.node[x].pop("inputs")
        DiGraph.node[x].pop("size")
        DiGraph.node[x].pop("formula")
        
    for x,y in DiGraph.edges():
        DiGraph.edge[x][y].pop("size")

    
def disjoint_union( DiGraphs, NodeWidth, Subgraphs ):
    graphs = iter(DiGraphs)
    union = networkx.DiGraph()
    subgraphs = []
    
    for graph in graphs:

        # unique ids
        graph = networkx.convert_node_labels_to_integers(graph, first_label=len(union))
        mapping = {x:str(x) for x in graph.nodes()}
        networkx.relabel_nodes(graph, mapping, copy=False)

        # styles
        add_edge_attributes(graph)
        add_node_attributes(graph, NodeWidth)
        if Subgraphs: subgraphs+= compute_subgraphs(graph)
        
        # add to union
        union.add_nodes_from(graph.nodes(data=True))
        union.add_edges_from(graph.edges(data=True))


    add_graph_attributes( union, subgraphs )
    remove_auxillary_attributes(union)

    return union
    

def cartesian_product( DiGraphs, NodeWidth, Subgraphs ):
    graphs = iter(DiGraphs)
    product = next(graphs)

    # create product graph
    for graph in graphs:
        newproduct = networkx.DiGraph()

        # graph data
        component = product.graph["component"] + graph.graph["component"]
        subprimes = dict_union(product.graph["subprimes"],graph.graph["subprimes"])
        mints_subprimes = itertools.product(product.graph["mints_subprimes"],graph.graph["mints_subprimes"])
        mints_subprimes = [dict_union(x,y) for x,y in mints_subprimes]
        
        newproduct.graph["component"] = component
        newproduct.graph["subprimes"] = subprimes
        newproduct.graph["mints_subprimes"] = mints_subprimes
            
        # nodes
        for node_current, data_current in product.nodes(data=True):            
            for node_next, data_next in graph.nodes(data=True):

                node = node_current + node_next
                mints_reachable = itertools.product(data_current["mints_reachable"],data_next["mints_reachable"])
                mints_reachable = [dict_union(x,y) for x,y in mints_reachable]
                size = data_current["size"] * data_next["size"]
                formula = "(%s) & (%s)"%(data_current["formula"],data_next["formula"])
                inputs = dict_union(data_current["inputs"],data_next["inputs"])

                newproduct.add_node(node, vector=node, mints_reachable=mints_reachable, size=size, formula=formula, inputs=inputs)


        # edges (old)
        for source_current, target_current, data_current in product.edges(data=True):
            for node_next, data_next in graph.nodes(data=True):
                
                source = source_current + node_next
                target = target_current + node_next
                size = data_current["size"] * data_next["size"]

                newproduct.add_edge(source, target, size=size)

        # edges (new)
        for node_current, data_current in product.nodes(data=True):
            for source_next,target_next, data_next in graph.edges(data=True):

                source = node_current + source_next
                target = node_current + target_next
                size = data_current["size"] * data_next["size"]

                newproduct.add_edge(source, target, size=size)



        product = newproduct
        
        
    # styles
    add_edge_attributes(product)
    add_node_attributes(product, NodeWidth)
    subgraphs = compute_subgraphs(product) if Subgraphs else None
    add_graph_attributes(product, subgraphs)

    x = 0
    for node, data in product.nodes(data=True):
        print node, data["size"]
        x+= data["size"]
    print "total size:", x
    print "2**13=",2**13
        
    remove_auxillary_attributes(product)

    return product

    
def primes2basins( Primes, Update, FnameIMAGE=None, Subgraphs=False, FactoredForm=False, NodeWidth=5 ):
    """
    Creates the basins of attraction graph for the STG of the network defined by *Primes* and *Update*.
    *FactoredForm* determines whether the basins of independent sub-networks should be combined.
    A trivial example of network that has independent sub-networks is::

        v1, v1
        v2, v2

    The optional argument *FnameIMAGE* can be used to create an image using :ref:`installation_graphviz` and the layout engine *dot*.

    revise this text: uses the function :ref:`ModelChecking.check_primes <check_primes>`
    
    **arguments**:
        * *Primes*: primes implicants
        * *Update* (str): either *"asynchronous"* or *"synchronous"*
        * *FactoredForm* (bool): whether the basins of independent sub-networks should be combined
        * *NodeSize* (int): factor for node sizes
        * *FnameIMAGE* (str): name of output file

    **example**::

        >>> primes = FEX.read_primes("mapk.primes")
        >>> update = "asynchronous"
        >>> primes2basins(primes, update, "basins.pdf")
        created basins.pdf
    """

    assert(Update in ["synchronous", "mixed", "asynchronous"])
    
    if not Primes:
        print("what are the basins of an empty Boolean network?")
        raise Exception

    igraph = InteractionGraphs.primes2igraph(Primes)
    if networkx.is_directed_acyclic_graph(igraph):
        outdags = remove_outdages(igraph)
        igraph.remove_nodes_from(outdags)
    else:
        outdags = None
        
    connected_components = networkx.connected_components(igraph.to_undirected())
    connected_components = [list(x) for x in connected_components]
    graphs = []

    for component in connected_components:

        subprimes = PrimeImplicants.copy(Primes)
        toremove = [x for x in Primes if not x in component]
        PrimeImplicants.remove_variables(subprimes, toremove)

        mints_subprimes = TrapSpaces.trap_spaces(subprimes, "min")
        vectors = []
        
        inputs = PrimeImplicants.find_inputs(subprimes)
        
        if inputs:
            for combination in PrimeImplicants.input_combinations(subprimes):
                mints_selected = [x for x in mints_subprimes if all(x[key]==combination[key] for key in combination)]


                newvectors = [[0,1] if x in mints_selected else [0] for x in mints_subprimes]
                newvectors = itertools.product(*newvectors)
                vectors+= [(combination,x) for x in newvectors]

        else:

            newvectors = [[0,1] for x in mints_subprimes]
            newvectors = itertools.product(*newvectors)
            vectors+= [({},x) for x in newvectors]
        
        
        props = [TemporalQueries.subspace2proposition(subprimes,x) for x in mints_subprimes]
        graph = networkx.DiGraph(component=component, subprimes=subprimes, mints_subprimes=mints_subprimes)

        # nodes
        nodes_data = {}
        for combination, vector in vectors:
            
            spec = ["EF(%s)"%p if v else "!EF(%s)"%p for v,p in zip(vector,props)]
            spec = " & ".join(spec)
            spec = "CTLSPEC %s"%spec
            
            if combination:
                init = "INIT %s"%TemporalQueries.subspace2proposition(subprimes, combination)
            else:
                init = "INIT TRUE"
                
            answer, accepting = ModelChecking.check_primes(subprimes, Update, init, spec, AcceptingStates=True)

            
            size = accepting["INITACCEPTING_SIZE"]
            formula = accepting["INITACCEPTING"]
            if size>0:
                node = "".join(str(x) for x in vector)
                mints_reachable = [x for v,x in zip(vector,mints_subprimes) if v]
                graph.add_node(node, formula=formula, size=size, vector=node, inputs=combination, mints_reachable=mints_reachable)


        # edges
        for source in graph.nodes():
                    
            subvectors = [[0,1] if x=="1" else [0] for x in source]
            subvectors = itertools.product(*subvectors)

            for subvector in subvectors:
                
                target = "".join([str(v) for v in subvector])

                if target in graph.nodes():
                    if source==target: continue
                    
                    phi1 = graph.node[source]["formula"]
                    phi2 = graph.node[target]["formula"]
                    init = "INIT %s"%phi1
                    spec = "CTLSPEC  E[%s U %s]"%(phi1,phi2)

                    answer, accepting = ModelChecking.check_primes(subprimes, Update, init, spec, AcceptingStates=True)
                    size = accepting["INITACCEPTING_SIZE"]
                    if size>0:
                        graph.add_edge(source, target, size=size)


        graphs.append(graph)


    if FactoredForm:
        graph = disjoint_union(graphs, NodeWidth, Subgraphs)
    else:
        graph = cartesian_product(graphs, NodeWidth, Subgraphs)

    if outdags and not FactoredForm:
        for x in graph.nodes():
            graph.node[x]["size"]*=2**len(outdags)

        if Subgraphs:
            for names, data in graph.graph["subgraphs"]:
                if "component" in data["label"]:
                    graph.graph["subgraphs"].remove((names, data))
                    graph.graph["subgraphs"].append((",".join(Primes),data))
        
        

    StateTransitionGraphs.stg2dot(graph, FnameIMAGE.replace("pdf","dot"))
    StateTransitionGraphs.stg2image(graph, FnameIMAGE)
    
    return    
    

    
    

         

if __name__=="__main__":
    import FileExchange
    test = 1

    if test==1:
        bnet = ExampleNetworks.raf
        primes = FileExchange.bnet2primes(bnet)
        update = "asynchronous"
        specs = [TemporalQueries.subspace2proposition(primes,x) for x in TrapSpaces.trap_spaces(primes, "min")]
        
        basins_naive(primes, update, specs)



