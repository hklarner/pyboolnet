

import os
import sys
import itertools
import networkx
import math

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



def find_outdags( DiGraph ):
    """
    Finds the largest directed acyclic subgraph that is closed under the successors operation.

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
        if size_percent>0.5: DiGraph.node[node]["fontcolor"] = "0.0 0.0 0.2"
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

    
def factored_form2disjoint_union( DiGraphs, NodeWidth, Subgraphs ):
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
    

def factored_form2cartesian_product( DiGraphs, NodeWidth, Subgraphs ):
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
                    graph.add_edge(source, target, size=size)


        graphs.append(graph)


    if FactoredForm:
        graph = factored_form2disjoint_union(graphs, NodeWidth, Subgraphs)
    else:
        graph = factored_form2cartesian_product(graphs, NodeWidth, Subgraphs)

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
    test = 5

    if test==1:
        bnet = ExampleNetworks.raf
        primes = FileExchange.bnet2primes(bnet)
        update = "asynchronous"
        primes2basins( primes, update, "test%i.pdf"%test, FactoredForm=True )
        
    elif test==2:
        bnet = ExampleNetworks.isolated_circuit(3, "negative")
        primes = FileExchange.bnet2primes(bnet)
        update = "asynchronous"
        primes2basins( primes, update, "test%i.pdf"%test )
        
    elif test==3:
        bnet = """
        v1, 1
        v2, v2
        v3, v4
        v4, !v3 | v2
        """
        primes = FileExchange.bnet2primes(bnet)
        update = "asynchronous"
        primes2basins( primes, update, "test%i.pdf"%test )
        
    elif test==4:
        bnet = """
        v1, 1
        v2, 0
        """
        primes = FileExchange.bnet2primes(bnet)
        update = "asynchronous"
        primes2basins( primes, update, FnameIMAGE="test%i.pdf"%test, FactoredForm=False )
        
    elif test==5:
        bnet = """
        v1, v2
        v2, v1
        v3, v3
        v4, !v1 | v3
        """
        primes = FileExchange.bnet2primes(bnet)
        update = "asynchronous"
        primes2basins( primes, update, "test%i.pdf"%test, FactoredForm=False, Subgraphs=True, NodeWidth=5 )
        
    elif test==6:
        bnet = """
        v1, v1
        v2, v1
        v3, v2 & v3
        """
        primes = FileExchange.bnet2primes(bnet)
        update = "asynchronous"
        primes2basins( primes, update, "test%i.pdf"%test )
        
    elif test==7:
        bnet = ExampleNetworks.davidich_yeast
        primes = FileExchange.bnet2primes(bnet)
        update = "asynchronous"
        primes2basins( primes, update, "test%i.pdf"%test )
        
    elif test==8:
        bnet = """
        v1, v1
        v2, v2
        """
        primes = FileExchange.bnet2primes(bnet)
        update = "asynchronous"
        primes2basins( primes, update, "test%i.pdf"%test )

    elif test==9:
        bnet = ExampleNetworks.xiao_wnt5a
        primes = FileExchange.bnet2primes(bnet)
        update = "synchronous"
        primes2basins( primes, update, "test%i.pdf"%test )
        igraph = InteractionGraphs.primes2igraph(primes)
        InteractionGraphs.add_style_interactionsigns(igraph)
        InteractionGraphs.igraph2image(igraph, "igraph.pdf")
        stg = StateTransitionGraphs.primes2stg(primes, update)
        StateTransitionGraphs.stg2image(stg, "stg.pdf")

    
    elif test==10:
        g1 = networkx.DiGraph()
        g1.add_edges_from([(1,2),(2,3)])
        for x in g1.nodes(): g1.node[x]["label"] = str(x)

        g2 = networkx.DiGraph()
        g2.add_edges_from([(10,20),(20,30)])
        for x in g2.nodes(): g2.node[x]["label"] = str(x)
        
        g3 = networkx.DiGraph()
        g3.add_edges_from([("a",2),(2,"c")])
        for x in g3.nodes(): g3.node[x]["label"] = str(x)
        
        g = networkx.disjoint_union_all([g1,g2,g3])

        print g.edges(data=True)
        print g.nodes(data=True)



