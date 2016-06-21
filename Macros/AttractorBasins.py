

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
            init = "INIT %s"%TemporalQueries.subspace2proposition(Primes,combination)
            attr = [x for x in Attractors if consistent(x,combination)]
            cases.append( (init,attr) )
    else:
        cases = [("INIT TRUE",Attractors)]


    # create nodes
    node = 0
    diagram = networkx.DiGraph()
    for init, attr in cases:        
        specs = [TemporalQueries.subspace2proposition(Primes,x) for x in attr]
        vectors = len(attr)*[[0,1]]
        for vector in itertools.product( *vectors ):
            if sum(vector)==0: continue

            if len(vector)==1:
                data = {"attractors":   attr,
                        "size":         2**(len(Primes)-len(inputs)),
                        "formula":      "TRUE"}
                
            else:
                spec = " & ".join("EF(%s)"%x if flag else "!EF(%s)"%x for flag, x in zip(vector, specs))
                spec = "CTLSPEC %s"%spec

                answer, accepting = ModelChecking.check_primes(Primes, Update, init, spec, AcceptingStates=True)

                data = {"attractors":   [x for flag,x in zip(vector,Attractors) if flag],
                        "size":         accepting["INITACCEPTING_SIZE"],
                        "formula":      accepting["INITACCEPTING"]}

            if data["size"]>0:
                diagram.add_node(node, data)
                node+=1


    # list potential edges
    potential_edges = {}
    for source, source_data in diagram.nodes(data=True):
        succs = []
        for target, target_data in diagram.nodes(data=True):
            if source==target: continue
            if all(x in source_data["attractors"] for x in target_data["attractors"]):
                succs.append((target,target_data))
                
        potential_edges[source] = succs


    # create edges
    for source, source_data in diagram.nodes(data=True):
        for target, target_data in potential_edges[source]:

            init = "INIT %s"%source_data["formula"]
            spec = "CTLSPEC EX(%s)"%target_data["formula"]
            answer, accepting = ModelChecking.check_primes(Primes, Update, init, spec, AcceptingStates=True)
            
            data = {}
            data["border_size"] = accepting["INITACCEPTING_SIZE"]
            data["border_formula"] = accepting["INITACCEPTING"]
            
            if data["border_size"]>0:

                if len(potential_edges[source])==1:
                    data["finally_size"] = source_data["size"]
                    data["finally_formula"] = source_data["formula"]

                else:                
                    spec = "CTLSPEC EF(%s)"%data["border_formula"]
                    answer, accepting = ModelChecking.check_primes(Primes, Update, init, spec, AcceptingStates=True)
                    
                    data["finally_size"] = accepting["INITACCEPTING_SIZE"]
                    data["finally_formula"] = accepting["INITACCEPTING"]
                
                diagram.add_edge(source, target, data)

    return diagram


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
        remove = [x for x in Primes if not x in component]
        PrimeImplicants.remove_variables(subprimes, remove)
        
        attrs_projected = []
        for x in Attractors:
            x = project(x,component)
            if not x in attrs_projected:
                attrs_projected.append(x)

        diagram = basins_diagram_naive(subprimes,Update,attrs_projected)
        diagrams.append(diagram)
        

    factor = 2**len(outdags)
    diagram = cartesian_product(diagrams, factor)
    # add subspaces for input combinations?
    
    return diagram

def merge_dicts(Dicts):
    '''
    Given any number of dicts, shallow copy and merge into a new dict,
    precedence goes to key value pairs in latter dicts.
    '''
    result = {}
    for dictionary in Dicts:
        result.update(dictionary)
    return result

def cartesian_product( Diagrams, Factor ):
    """
    creates the cartesian product of *Diagrams*.
    """

    diagram = networkx.DiGraph()


    # create nodes
    nodes = [x.nodes(data=True) for x in Diagrams]
    for product in itertools.product(*nodes):

        data = {}
        data["size"] = reduce(mul,[x["size"] for _,x in product]) * Factor
        data["formula"] = " & ".join("(%s)"%x["formula"] for _,x in product)
            
        attrs = [x["attractors"] for _,x in product]
        attrs = list(itertools.product(*attrs))
        attrs = [merge_dicts(x) for x in attrs]
        data["attractors"] = attrs

        node = tuple(x for x,_ in product)

        diagram.add_node(node, data)


    
    # create edges
    for source in diagram.nodes():
        for s, graph in zip(source, Diagrams):
            factor = diagram.node[source]["size"] / graph.node[s]["size"]
            for _, t, data in graph.out_edges(s,data=True):
                
                data = {}
                data["border_size"]     = factor * graph.edge[s][t]["border_size"]
                basic_formula = [g.node[x]["formula"] for x,g in zip(source,Diagrams) if not g==graph]
                formula = basic_formula + [graph.edge[s][t]["border_formula"]]
                data["border_formula"]  = " & ".join(formula)
                data["finally_size"]    = factor * graph.edge[s][t]["finally_size"]
                formula = basic_formula + [graph.edge[s][t]["finally_formula"]]
                data["finally_formula"]  = " & ".join(formula)

                target = tuple(x if not g==graph else t for x,g in zip(source,Diagrams))
                
                diagram.add_edge(source, target, data)



    # relabel nodes
    mapping = {x:",".join(map(str,x)) for x in diagram.nodes()}
    networkx.relabel_nodes(diagram,mapping)
        
    return diagram
    

def diagram2image(Diagram, FnameIMAGE):
    """
    creates an image of diagram
    """

    size = 0
    
    graph = networkx.DiGraph()
    graph.graph["node"] = {"shape":"rect"}
    graph.graph["splines"] = "ortho"

    for node, data in Diagram.nodes(data=True):
        size = size + data["size"]
        label = ["formula=%s"%data["formula"],
                 "size=%s"%data["size"],
                 "attractors=%s"%data["attractors"]]
        label = "<br/>".join(label)
        label = "<%s>"%label
        label = label.replace("&","&amp;")
        graph.add_node(str(node), label=label)

    for source, target, data in Diagram.edges(data=True):
        
        label = ["finally_size=%s"%data["finally_size"],
                 "finally_formula=%s"%data["finally_formula"],
                 "border_formula=%s"%data["border_formula"],
                 "border_size=%s"%data["border_size"]]
        label = "<br/>".join(label)
        label = "<%s>"%label
        label = label.replace("&","&amp;")
        graph.add_edge(str(source), str(target), label=label)

    print "size:",size
    InteractionGraphs.igraph2image(graph, FnameIMAGE)






tnet1 = """
raf, mek
mek, raf
v1, v1 | raf
v2, v2 & mek
v3, v2
v5, v5
"""

tnet2 = """
raf, mek
mek, raf
v1, v1 | raf
v2, v2 & mek
v3, v2
v5, v5
v6, v5
"""
    

TestNetworks = [tnet1,tnet2]    

         

if __name__=="__main__":
    import FileExchange
    test = 1

    if test==1:
        bnet = ExampleNetworks.raf
        bnet = tnet1
        primes = FileExchange.bnet2primes(bnet)
        update = "asynchronous"

        attractors = TrapSpaces.trap_spaces(primes, "min")
        diagram1 = basins_diagram_naive( primes, update, attractors )
        diagram2image(diagram1, FnameIMAGE="diagram_naive.pdf")
        
        diagram2 = basins_diagram( primes, update, attractors )
        diagram2image(diagram2, FnameIMAGE="diagram.pdf")

        print "is_isomorphic(basins_diagram_naive,basins_diagram)=", networkx.is_isomorphic(diagram1,diagram2)
                               


                            



