

import os
import sys
import itertools
import networkx

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


def remove_outdags( DiGraph ):
    """
    Removes the largest directed acyclic subgraph that is closed under the successors operation.

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
            outdag+= component

    DiGraph.remove_nodes_from(outdags)

    return outdags

    
def tensor_product_all( DiGraphs ):
    graph = networkx.DiGraph()
    for x in itertools.product(*DiGraphs):
        data = [g.node[x[i]] for i,g in enumerate(DiGraphs)]
        data = [(k,tuple(d.get(k) for d in data)) for k in set.union(*[set(d) for d in data])]
        data = dict(data)
        graph.add_node(x, data)

    return graph    

    
def primes2basins( Primes, Update, FactoredForm=True, FnameIMAGE=None ):
    """
    Creates the basins of attraction graph for the STG of the network defined by *Primes* and *Update*.
    *FactoredForm* determines whether the basins of independent sub-networks should be combined.
    A trivial example of network that has independent sub-networks is::

        v1, v1
        v2, v2

    The optional argument *FnameIMAGE* can be used to create an image using :ref:`installation_graphviz` and the layout engine *dot*.

    .. note::
        This function assumes that the minimal trap spaces are *univocal*, *faithful* and *complete*, i.e., that each attractor can be
        approximated by a minimal trap space. For details on approximating attractors by minimal trap spaces, see :ref:`Klarner2015(a) <klarner2015trap>`.
        Use :ref:`AttractorDetection.univocal <univocal>`, :ref:`AttractorDetection.completeness_iterative <faithful>` and
        :ref:`AttractorDetection.completeness_iterative <completeness_iterative>` to decide whether the attractors of your network can be approximated.

    revise this text: uses the function :ref:`ModelChecking.check_primes <check_primes>`
    
    **arguments**:
        * *Primes*: primes implicants
        * *Update* (str): either *"asynchronous"* or *"synchronous"*
        * *FactoredForm* (bool): whether the basins of independent sub-networks should be combined
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
    if not networkx.is_directed_acyclic_graph(igraph):
        outdags = remove_outdags(igraph)
        print "len(outdags)", len(outdags)
        
    connected_components = networkx.connected_components(igraph.to_undirected())
    graphs = []

    for component in connected_components:

        subprimes = PrimeImplicants.copy(Primes)
        toremove = [x for x in Primes.keys() if not x in component]
        PrimeImplicants.remove_variables(subprimes, toremove)

        mints = TrapSpaces.trap_spaces(subprimes, "min")
        print "len(mints)", len(mints)
        vectors = []
        
        inputs = PrimeImplicants.find_inputs(subprimes)
        
        if inputs:
            for combination in PrimeImplicants.input_combinations(subprimes):
                mints_projected = [x for x in mints if all(x[key]==combination[key] for key in combination.keys())]


                newvectors = [[0,1] if x in mints_projected else [0] for x in mints]
                newvectors = itertools.product(*newvectors)
                newvectors = [x for x in newvectors if sum(x)>0]
                vectors+= [(TemporalQueries.subspace2proposition(subprimes, combination),x) for x in newvectors]

        else:

            newvectors = [[0,1] for x in mints]
            newvectors = itertools.product(*newvectors)
            newvectors = [x for x in newvectors if sum(x)>0]
            vectors+= [(None,x) for x in newvectors]

        print "len(subprimes): %i"%len(subprimes)
        print "len(vectors): %i"%len(vectors)
        
        
        props = [TemporalQueries.subspace2proposition(subprimes,x) for x in mints]
        graph = networkx.DiGraph(component=component, primes=subprimes, mints=mints)
        graph.graph["node"]  = {"shape":"rect","color":"black","style":"filled"}
        graph.graph["edge"]  = {}

        # nodes
        nodes_data = {}
        for init, vector in vectors:
            
            spec = ["EF(%s)"%p if v else "!EF(%s)"%p for v,p in zip(vector,props)]
            spec = " & ".join(spec)
            spec = "CTLSPEC %s"%spec
            if not init: init = "TRUE"
            init = "INIT %s"%init

            answer, accepting = ModelChecking.check_primes(subprimes, Update, init, spec, AcceptingStates=True)

            
            size = accepting["INITACCEPTING_SIZE"]
            if size>0:
                node = "".join(str(x) for x in vector)
                graph.add_node(node, accepting=accepting)


        # edges
        for source in graph.nodes():
                    
            subvectors = [[0,1] if x=="1" else [0] for x in source]
            subvectors = itertools.product(*subvectors)
            subvectors = [x for x in subvectors if sum(x)>0]

            for subvector in subvectors:
                
                target = "".join([str(v) for v in subvector])

                if target in graph.nodes():
                    if source==target: continue
                    
                    init = "INIT %s"%accepting_map[source]["INITACCEPTING"]
                    phi1 = graph.node[source]["INITACCEPTING"]
                    phi2 = graph.node[target]["INITACCEPTING"]
                    spec = "CTLSPEC  E[%s U %s]"%(phi1,phi2)

                    answer, accepting = ModelChecking.check_primes(subprimes, Update, init, spec, AcceptingStates=True)
                    graph.add_edge(source, target, accepting=accepting)


        graphs.append(graph)

    if 0:
        # styles
        size_total = float(2**len(Primes))
        for node, accepting in accepting_map.items():
        
            value = 1 - accepting["INITACCEPTING_SIZE"] / size_total
                
            graph.node[node]["fillcolor"] = "0.0 0.0 %.2f"%value
            if value<.5:
                graph.node[node]["fontcolor"] = "white"

            if graph.out_degree(node)==0: continue
            if all(graph.edge[node][x]["style"]=="solid" for x in graph.successors(node)):
                graph.node[node]["color"] = "cornflowerblue"
                graph.node[node]["penwidth"] = "5"

        # node
        label = "<%s<br/>%i>"%(node, size)

        # edge
        size1 = accepting["INITACCEPTING_SIZE"]
        size2 = graph.node[source]["INITACCEPTING_SIZE"]
        
        if 0 < size1 < size2:
            graph.add_edge(source, target, style="dashed")
            
        elif size1 == size2:
            graph.add_edge(source, target, style="solid")
    


    if FactoredForm:
        graph = networkx.disjoint_union_all(graphs)
        mapping = {x:str(x) for x in graph.nodes()}
        networkx.relabel_nodes(graph, mapping, copy=False)

    else:
        print ">>", graphs
        graph = tensor_product_all(graphs)
        mapping = {x:".".join(x) for x in graph.nodes()}
        networkx.relabel_nodes(graph, mapping, copy=False)

    if 0:
        #size_total = 
        for node, data in graph.nodes(data=True):
            
            graph.node[node]["fillcolor"] = 1

    #igraph = InteractionGraphs.primes2igraph(Primes)
    
    #if networkx.has_path(igraph, source, target): pass
    
    

    

    print graph.edges(data=True)
    for v, d in graph.nodes(data=True):
        print repr(v)
        print repr(d)
        print

    StateTransitionGraphs.stg2dot(graph, FnameIMAGE.replace("pdf","dot"))
    StateTransitionGraphs.stg2image(graph, FnameIMAGE)
    

         

if __name__=="__main__":
    import FileExchange
    test = 4
    
    if test==1:
        bnet = ExampleNetworks.grieco_mapk
        primes = FileExchange.bnet2primes(bnet)
        update = "asynchronous"
        primes2basins( primes, update, "test%i.pdf"%test )
        
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
        primes2basins( primes, update, False, "test%i.pdf"%test )
        
    elif test==5:
        bnet = """
        v1, v1
        v2, v2
        """
        primes = FileExchange.bnet2primes(bnet)
        update = "asynchronous"
        primes2basins( primes, update, "test%i.pdf"%test )
        
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



