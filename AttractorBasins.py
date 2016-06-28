

import os
import sys
import itertools
import math
from operator import mul
import networkx

BASE = os.path.normpath(os.path.abspath(os.path.join(os.path.dirname(__file__))))
sys.path.append(BASE)

import FileExchange
import ModelChecking
import TemporalQueries
import TrapSpaces
import AttractorDetection
import StateTransitionGraphs
import InteractionGraphs
import Examples
import PrimeImplicants
import Utility

config = Utility.Miscellaneous.myconfigparser.SafeConfigParser()
config.read( os.path.join(BASE, "Dependencies", "settings.cfg") )
CMD_DOT = os.path.join( BASE, "Dependencies", config.get("Executables", "dot") )



def basins_diagram( Primes, Update, Attractors, ComputeBorders=False, Silent=True ):
    """
    copy from basins_diagram_naive.
    removes out-dags.
    divides remaining network into connected component(s).

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
    if not Silent:
        print("excluding the out-dag %s"%outdags)

    components = networkx.connected_components(igraph.to_undirected())
    components = [list(x) for x in components]
    if not Silent:
        print("working on %i connected component(s)"%len(components))
        
    counter = 0
    diagrams = []
    for component in components:
        subprimes = PrimeImplicants.copy(Primes)
        remove = [x for x in Primes if not x in component]
        PrimeImplicants.remove_variables(subprimes, remove)
        
        attrs_projected = project_attractors(Attractors, component)

        diagram, count = basins_diagram_naive(subprimes, Update, attrs_projected, ComputeBorders, Silent)
        counter+=count
        
        diagrams.append(diagram)
        

    factor = 2**len(outdags)
    diagram = cartesian_product(diagrams, factor, ComputeBorders)


    for x in diagram.nodes():
        projection = diagram.node[x]["attractors"]
        diagram.node[x]["attractors"] = lift_attractors(Attractors, projection)
        

    if not Silent:
        print("basin diagram required %i executions of NuSMV"%counter)
    
    return diagram


def basins_diagram_naive( Primes, Update, Attractors, ComputeBorders, Silent ):
    """
    computes the basins diagram.
    performs case by case for inputs.
    nodes are integers starting from *FirstNode*.
    
    node attributes:
        - size:
        - formula:
        - attractors:

    edge attributes:
        - finally_size:
        - finally_formula:
        - if ComputeBorders:
            - border_size
            - border_formula

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

    counter = 0

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
                        "formula":      init.split()[1]}
                
            else:
                spec = " & ".join("EF(%s)"%x if flag else "!EF(%s)"%x for flag, x in zip(vector, specs))
                spec = "CTLSPEC %s"%spec

                answer, accepting = ModelChecking.check_primes(Primes, Update, init, spec, AcceptingStates=True)
                counter+=1
                
                data = {"attractors":   [x for flag,x in zip(vector,attr) if flag],
                        "size":         accepting["INITACCEPTING_SIZE"],
                        "formula":      accepting["INITACCEPTING"]}

                
                

            if data["size"]>0:
                diagram.add_node(node, data)
                node+=1


    # list potential targets
    potential_targets = {}
    for source, source_data in diagram.nodes(data=True):
        succs = []
        for target, target_data in diagram.nodes(data=True):
            if source==target: continue
            if all(x in source_data["attractors"] for x in target_data["attractors"]):
                succs.append((target,target_data))
                
        potential_targets[source] = succs


    # create edges
    for source, source_data in diagram.nodes(data=True):
        for target, target_data in potential_targets[source]:

            # computation of edges with borders ...
            if ComputeBorders:
                init = "INIT %s"%source_data["formula"]
                spec = "CTLSPEC EX(%s)"%target_data["formula"]
                answer, accepting = ModelChecking.check_primes(Primes, Update, init, spec, AcceptingStates=True)
                counter+=1
                
                data = {}
                data["border_size"] = accepting["INITACCEPTING_SIZE"]
                data["border_formula"] = accepting["INITACCEPTING"]
                
                if data["border_size"]>0:

                    if len(potential_targets[source])==1:
                        data["finally_size"] = source_data["size"]
                        data["finally_formula"] = source_data["formula"]

                    else:
                        spec = "CTLSPEC EF(%s)"%data["border_formula"]
                        answer, accepting = ModelChecking.check_primes(Primes, Update, init, spec, AcceptingStates=True)
                        counter+=1
                        
                        data["finally_size"] = accepting["INITACCEPTING_SIZE"]
                        data["finally_formula"] = accepting["INITACCEPTING"]
                    
                    diagram.add_edge(source, target, data)

            # .. is very different from the computation without
            else:
                phi1 = source_data["formula"]
                phi2 = target_data["formula"]
                init = "INIT %s"%phi1
                spec = "CTLSPEC E[%s U %s]"%(phi1,phi2)
                answer, accepting = ModelChecking.check_primes(Primes, Update, init, spec, AcceptingStates=True)
                counter+=1

                data = {}
                data["finally_size"] = accepting["INITACCEPTING_SIZE"]
                data["finally_formula"] = accepting["INITACCEPTING"]

                if data["finally_size"]>0:
                    diagram.add_edge(source, target, data)
                    
    if not Silent:
        print("basin diagram (naive) required %i executions of NuSMV"%counter)

    return diagram, counter


def diagram2image(Diagram, Primes, FnameIMAGE, StyleInputs=True, StyleDetails=False):
    """
    creates an image of diagram
    """
    

    size_total = float(2**len(Primes))
    
    graph = networkx.DiGraph()
    graph.graph["node"]  = {"shape":"rect","style":"filled","color":"none"}
    graph.graph["edge"]  = {}
    #graph.graph["splines"] = "ortho"
    

    for node, data in Diagram.nodes(data=True):
        attr = data["attractors"]
        attr = sorted(StateTransitionGraphs.subspace2str(Primes,x) for x in attr)
        
        label = attr+["states: %s"%data["size"]]
        label = "<br/>".join(label)
        label = "<%s>"%label

        graph.add_node(node, label=label)

        if len(attr)==1:
            graph.node[node]["color"] = "cornflowerblue"
            graph.node[node]["penwidth"] = "4"

        size_percent = data["size"] / size_total
        
        graph.node[node]["fillcolor"] = "0.0 0.0 %.2f"%(1-size_percent)
        if size_percent>0.5: graph.node[node]["fontcolor"] = "0.0 0.0 0.8"            

        if StyleDetails:
            if all(d["finally_size"]==data["size"] for _,_,d in Diagram.out_edges(node,data=True)):
                graph.node[node]["fontcolor"] = "cornflowerblue"
        

    for source, target, data in Diagram.edges(data=True):
        graph.add_edge(source, target)
        if StyleDetails:
            if data["finally_size"] < Diagram.node[source]["size"]:
                graph.edge[source][target]["style"]="dashed"
        

    if StyleInputs:
        subgraphs = []
        for inputs in PrimeImplicants.input_combinations(Primes):
            nodes = [x for x in Diagram.nodes() if consistent(inputs,Diagram.node[x]["attractors"][0])]
            label = StateTransitionGraphs.subspace2str(Primes,inputs)
            subgraphs.append((nodes,{"label":"inputs: %s"%label, "color":"none"}))
            
        if subgraphs:
            graph.graph["subgraphs"] = []

        InteractionGraphs.add_style_subgraphs(graph, subgraphs)


    mapping = {x:str(x) for x in graph.nodes()}
    networkx.relabel_nodes(graph,mapping,copy=False)
        
    InteractionGraphs.igraph2image(graph, FnameIMAGE)


def diagram2abstract_image( Diagram, FnameIMAGE ):
    graph = networkx.DiGraph()

    for node, data in Diagram.nodes(data=True):
        x = len(data["attractors"])
        if not x in Diagram:
            graph.add_nodes(x, size=data["size"])
        else:
            graph.node[x]["size"]+= data["size"]

    for source, target in Diagram.edges():
        x = len(Diagram.node[source]["attractors"])
        y = len(Diagram.node[source]["attractors"])
        graph.add_edge(x,y)

        
    mapping = {x:str(x) for x in graph.nodes()}
    networkx.relabel_nodes(graph,mapping,copy=False)
        
    InteractionGraphs.igraph2image(graph, FnameIMAGE)


## auxillary functions
def consistent( X, Y):
    return all(X[k]==Y[k] for k in set(X).intersection(set(Y)))

def merge_dicts(Dicts):
    '''
    merges any number of dicts (shallow copies),
    precedence goes to key value pairs in latter dicts.
    '''
    
    result = {}
    for dictionary in Dicts:
        result.update(dictionary)
    return result

def project_attractors( Attractors, Names ):
    result = set()
    for space in Attractors:
        projection = tuple((k,v) for k,v in sorted(space.items()) if k in Names)
        result.add(projection)

    result = [dict(x) for x in result]

    return result


def lift_attractors( Attractors, Projection ):
    return [x for x in Attractors for y in Projection if consistent(x,y)]


def find_outdags( DiGraph ):
    """
    finds the largest directed acyclic subgraph that is closed under the successors operation.
    """

    graph = DiGraph.copy()
    
    sccs = networkx.strongly_connected_components(graph)
    sccs = [list(x) for x in sccs]
    candidates = [scc[0] for scc in sccs if len(scc)==1]
    candidates = [x for x in candidates if not graph.has_edge(x,x)]
    sccs = [scc for scc in sccs if len(scc)>1]

    graph.add_node("!")
    for scc in sccs:
        graph.add_edge(scc[0],"!")

    outdags = [x for x in candidates if not networkx.has_path(graph,x,"!")]

    return outdags


def cartesian_product( Diagrams, Factor, ComputeBorders ):
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
                basic_formula = ["(%s)"%g.node[x]["formula"] for x,g in zip(source,Diagrams) if not g==graph]
                data["finally_size"]    = factor * graph.edge[s][t]["finally_size"]
                formula = basic_formula + ["(%s)"%graph.edge[s][t]["finally_formula"]]
                data["finally_formula"]  = " & ".join(formula)

                if ComputeBorders:
                    data["border_size"]     = factor * graph.edge[s][t]["border_size"]
                    formula = basic_formula + ["(%s)"%graph.edge[s][t]["border_formula"]]
                    data["border_formula"]  = " & ".join(formula)                    

                target = tuple(x if not g==graph else t for x,g in zip(source,Diagrams))
                
                diagram.add_edge(source, target, data)



    # relabel nodes
    diagram = networkx.convert_node_labels_to_integers(diagram)
        
    return diagram


def diagrams_are_equal(Diagram1, Diagram2):
    """
    removes for formulas, which are different for naive / product diagrams.
    """
    g1 = Diagram1.copy()
    g2 = Diagram2.copy()

    for g in [g1,g2]:
        for x in g.nodes():
            g.node[x].pop("formula")
        for x,y in g.edges():
            if "border_formula" in g.edge[x][y]:
                g.edge[x][y].pop("border_formula")
                g.edge[x][y].pop("finally_formula")

    em = lambda x,y:x==y
    
    return networkx.is_isomorphic(g1,g2,edge_match=em)

         
def tests():
    import json
    from networkx.readwrite import json_graph

    if 0:
        # raf 
        primes = Examples.get_primes("raf")
        update = "asynchronous"
        attractors = TrapSpaces.trap_spaces(primes, "min")
        diagram = basins_diagram( primes, update, attractors, Silent=True )
        data = {'directed': True, 'graph': {'name': '()_with_int_labels'}, 'nodes': [{'formula': '(!(Erk & (Mek) | !Erk & ((Raf) | !Mek)))', 'attractors': [{u'Raf': 1, u'Mek': 0, u'Erk': 0}, {u'Mek': 1, u'Erk': 1}], 'id': 0, 'size': 3}, {'formula': '(Erk & (Mek) | !Erk & (Mek & (Raf)))', 'attractors': [{u'Mek': 1, u'Erk': 1}], 'id': 1, 'size': 3}, {'formula': '(!(Erk | (Mek)))', 'attractors': [{u'Raf': 1, u'Mek': 0, u'Erk': 0}], 'id': 2, 'size': 2}], 'links': [{'target': 1, 'finally_formula': '(!(Erk & (Mek) | !Erk & ((Raf) | !Mek)))', 'border_size': 3, 'source': 0, 'finally_size': 3, 'border_formula': '(!(Erk & (Mek) | !Erk & ((Raf) | !Mek)))'}, {'target': 2, 'finally_formula': '(!(Erk & (Mek) | !Erk & ((Raf) | !Mek)))', 'border_size': 3, 'source': 0, 'finally_size': 3, 'border_formula': '(!(Erk & (Mek) | !Erk & ((Raf) | !Mek)))'}], 'multigraph': False}
        expected = json_graph.node_link_graph(data)
        print diagrams_are_equal(diagram, expected)
    
    if 0:
        # positive feedback
        bnet = """
        v1,v2
        v2,v3
        v3,v1"""
        primes = FileExchange.bnet2primes(bnet)
        update = "asynchronous"
        attractors = TrapSpaces.trap_spaces(primes, "min")
        diagram = basins_diagram( primes, update, attractors, Silent=False )
        data = {'directed': True, 'graph': {'name': '()_with_int_labels'}, 'nodes': [{'formula': '(!(v1 & (v2 & (v3)) | !v1 & !(v2 | (v3))))', 'attractors': [{u'v1': 0, u'v2': 0, u'v3': 0}, {u'v1': 1, u'v2': 1, u'v3': 1}], 'id': 0, 'size': 6}, {'formula': '(v1 & (v2 & (v3)))', 'attractors': [{u'v1': 1, u'v2': 1, u'v3': 1}], 'id': 1, 'size': 1}, {'formula': '(!(v1 | (v2 | (v3))))', 'attractors': [{u'v1': 0, u'v2': 0, u'v3': 0}], 'id': 2, 'size': 1}], 'links': [{'target': 1, 'finally_formula': '(!(v1 & (v2 & (v3)) | !v1 & !(v2 | (v3))))', 'border_size': 3, 'source': 0, 'finally_size': 6, 'border_formula': '(!(v1 & (v2 & (v3) | !v2 & !(v3)) | !v1 & !(v2 & (v3))))'}, {'target': 2, 'finally_formula': '(!(v1 & (v2 & (v3)) | !v1 & !(v2 | (v3))))', 'border_size': 3, 'source': 0, 'finally_size': 6, 'border_formula': '(!(v1 & (v2 | (v3)) | !v1 & (v2 & (v3) | !v2 & !(v3))))'}], 'multigraph': False}
        expected = json_graph.node_link_graph(data)
        print diagrams_are_equal(diagram, expected)
        diagram2image(diagram, primes, FnameIMAGE="Junk/diagram.pdf", StyleInputs=False)

    if 0:
        # negative feedback
        bnet = """
        v1,!v2
        v2,v3
        v3,v1"""
        primes = FileExchange.bnet2primes(bnet)
        update = "asynchronous"
        attractors = TrapSpaces.trap_spaces(primes, "min")
        diagram = basins_diagram( primes, update, attractors, Silent=False )
        print json_graph.node_link_data(diagram)
        data = {'directed': True, 'graph': {'name': '()_with_int_labels'}, 'nodes': [{'formula': '(TRUE)', 'attractors': [{}], 'id': 0, 'size': 8}], 'links': [], 'multigraph': False}
        expected = json_graph.node_link_graph(data)
        print diagrams_are_equal(diagram, expected)
        diagram2image(diagram, primes, FnameIMAGE="Junk/diagram.pdf", StyleInputs=False)

    if 0:
        # arellano_antelope
        primes = Examples.get_primes("arellano_rootstem")
        update = "asynchronous"
        attractors = TrapSpaces.trap_spaces(primes, "min")
        diagram = basins_diagram( primes, update, attractors, Silent=False )
        #print json_graph.node_link_data(diagram)
        data = {'directed': True, 'graph': {'name': '()_with_int_labels'}, 'nodes': [{'formula': '(!AUXINS&!SHR)', 'attractors': [{u'SHR': 0, u'PLT': 0, u'AUXINS': 0, u'WOX': 0, u'IAA': 1, u'MGP': 0, u'ARF': 0, u'JKD': 0, u'SCR': 0}], 'id': 0, 'size': 128}, {'formula': '(!(AUXINS | (SCR | !(SHR))))', 'attractors': [{u'SHR': 1, u'PLT': 0, u'AUXINS': 0, u'WOX': 0, u'IAA': 1, u'MGP': 0, u'ARF': 0, u'JKD': 0, u'SCR': 0}], 'id': 1, 'size': 64}, {'formula': '(!(AUXINS | !(JKD & (SCR & (SHR)))))', 'attractors': [{u'SHR': 1, u'PLT': 0, u'AUXINS': 0, u'WOX': 0, u'IAA': 1, u'MGP': 1, u'ARF': 0, u'JKD': 1, u'SCR': 1}], 'id': 2, 'size': 32}, {'formula': '(!((SCR | !(SHR)) | !AUXINS))', 'attractors': [{u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 0, u'IAA': 0, u'MGP': 0, u'ARF': 1, u'JKD': 0, u'SCR': 0}], 'id': 3, 'size': 64}, {'formula': '(!(AUXINS | (JKD | !(SCR & (SHR)))))', 'attractors': [{u'SHR': 1, u'PLT': 0, u'AUXINS': 0, u'WOX': 0, u'IAA': 1, u'MGP': 1, u'ARF': 0, u'JKD': 1, u'SCR': 1}, {u'SHR': 1, u'PLT': 0, u'AUXINS': 0, u'WOX': 0, u'IAA': 1, u'MGP': 0, u'ARF': 0, u'JKD': 0, u'SCR': 0}], 'id': 4, 'size': 32}, {'formula': '(!(((IAA | (JKD | !(MGP & (SCR & (SHR & (WOX)))))) | !AUXINS) | !ARF))', 'attractors': [{u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 0, u'IAA': 0, u'MGP': 0, u'ARF': 1, u'JKD': 0, u'SCR': 0}, {u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 1, u'IAA': 0, u'MGP': 0, u'ARF': 1, u'JKD': 1, u'SCR': 1}], 'id': 5, 'size': 2}, {'formula': '(AUXINS&!SHR)', 'attractors': [{u'SHR': 0, u'PLT': 1, u'AUXINS': 1, u'WOX': 0, u'IAA': 0, u'MGP': 0, u'ARF': 1, u'JKD': 0, u'SCR': 0}], 'id': 6, 'size': 128}, {'formula': '(!((JKD | ((((WOX) | !SHR) | !SCR) | !MGP)) | !AUXINS))', 'attractors': [{u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 0, u'IAA': 0, u'MGP': 1, u'ARF': 1, u'JKD': 1, u'SCR': 1}, {u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 0, u'IAA': 0, u'MGP': 0, u'ARF': 1, u'JKD': 0, u'SCR': 0}], 'id': 7, 'size': 8}, {'formula': '(!(((IAA | !(JKD & (SCR & (SHR & (WOX))) | !JKD & !(MGP | !(SCR & (SHR & (WOX)))))) | !AUXINS) | !ARF))', 'attractors': [{u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 1, u'IAA': 0, u'MGP': 0, u'ARF': 1, u'JKD': 1, u'SCR': 1}], 'id': 8, 'size': 6}, {'formula': '(!(ARF & ((IAA & (JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !IAA & (JKD | (MGP | (((WOX) | !SHR) | !SCR)))) | !AUXINS) | !ARF & ((JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !AUXINS)))', 'attractors': [{u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 0, u'IAA': 0, u'MGP': 1, u'ARF': 1, u'JKD': 1, u'SCR': 1}, {u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 0, u'IAA': 0, u'MGP': 0, u'ARF': 1, u'JKD': 0, u'SCR': 0}, {u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 1, u'IAA': 0, u'MGP': 0, u'ARF': 1, u'JKD': 1, u'SCR': 1}], 'id': 9, 'size': 20}, {'formula': '(!((((((WOX) | !SHR) | !SCR) | !MGP) | !JKD) | !AUXINS))', 'attractors': [{u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 0, u'IAA': 0, u'MGP': 1, u'ARF': 1, u'JKD': 1, u'SCR': 1}], 'id': 10, 'size': 8}, {'formula': '(ARF & (AUXINS & (IAA & (JKD & (MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !IAA & !((MGP | (((WOX) | !SHR) | !SCR)) | !JKD))) | !ARF & (AUXINS & (JKD & (MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR))))))', 'attractors': [{u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 0, u'IAA': 0, u'MGP': 1, u'ARF': 1, u'JKD': 1, u'SCR': 1}, {u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 1, u'IAA': 0, u'MGP': 0, u'ARF': 1, u'JKD': 1, u'SCR': 1}], 'id': 11, 'size': 20}], 'links': [{'target': 1, 'finally_formula': '(!(AUXINS | (JKD | !(SCR & (SHR)))))', 'border_size': 16, 'source': 4, 'finally_size': 32, 'border_formula': '(!(AUXINS | (JKD | !(MGP & (SCR & (SHR))))))'}, {'target': 2, 'finally_formula': '(!(AUXINS | (JKD | !(SCR & (SHR)))))', 'border_size': 32, 'source': 4, 'finally_size': 32, 'border_formula': '(!(AUXINS | (JKD | !(SCR & (SHR)))))'}, {'target': 8, 'finally_formula': '(!(((IAA | (JKD | !(MGP & (SCR & (SHR & (WOX)))))) | !AUXINS) | !ARF))', 'border_size': 2, 'source': 5, 'finally_size': 2, 'border_formula': '(!(((IAA | (JKD | !(MGP & (SCR & (SHR & (WOX)))))) | !AUXINS) | !ARF))'}, {'target': 3, 'finally_formula': '(!(((IAA | (JKD | !(MGP & (SCR & (SHR & (WOX)))))) | !AUXINS) | !ARF))', 'border_size': 2, 'source': 5, 'finally_size': 2, 'border_formula': '(!(((IAA | (JKD | !(MGP & (SCR & (SHR & (WOX)))))) | !AUXINS) | !ARF))'}, {'target': 10, 'finally_formula': '(!((JKD | ((((WOX) | !SHR) | !SCR) | !MGP)) | !AUXINS))', 'border_size': 8, 'source': 7, 'finally_size': 8, 'border_formula': '(!((JKD | ((((WOX) | !SHR) | !SCR) | !MGP)) | !AUXINS))'}, {'target': 3, 'finally_formula': '(!((JKD | ((((WOX) | !SHR) | !SCR) | !MGP)) | !AUXINS))', 'border_size': 8, 'source': 7, 'finally_size': 8, 'border_formula': '(!((JKD | ((((WOX) | !SHR) | !SCR) | !MGP)) | !AUXINS))'}, {'target': 8, 'finally_formula': '(!(ARF & ((IAA & (JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !IAA & (JKD | (MGP | (((WOX) | !SHR) | !SCR)))) | !AUXINS) | !ARF & ((JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !AUXINS)))', 'border_size': 6, 'source': 9, 'finally_size': 20, 'border_formula': '(!(ARF & ((IAA & (JKD | (MGP | !(SCR & (SHR & (WOX))))) | !IAA & (JKD | (MGP | (((WOX) | !SHR) | !SCR)))) | !AUXINS) | !ARF & ((IAA | (JKD | (MGP | !(SCR & (SHR & (WOX)))))) | !AUXINS)))'}, {'target': 3, 'finally_formula': '(!(ARF & (((JKD | !(MGP & (SCR & (SHR & (WOX))))) | !IAA) | !AUXINS) | !ARF & ((JKD | !(MGP & (SCR & (SHR & (WOX))))) | !AUXINS)))', 'border_size': 6, 'source': 9, 'finally_size': 6, 'border_formula': '(!(ARF & (((JKD | !(MGP & (SCR & (SHR & (WOX))))) | !IAA) | !AUXINS) | !ARF & ((JKD | !(MGP & (SCR & (SHR & (WOX))))) | !AUXINS)))'}, {'target': 11, 'finally_formula': '(!(ARF & ((IAA & (JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !IAA & (JKD | (MGP | (((WOX) | !SHR) | !SCR)))) | !AUXINS) | !ARF & ((JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !AUXINS)))', 'border_size': 20, 'source': 9, 'finally_size': 20, 'border_formula': '(!(ARF & ((IAA & (JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !IAA & (JKD | (MGP | (((WOX) | !SHR) | !SCR)))) | !AUXINS) | !ARF & ((JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !AUXINS)))'}, {'target': 5, 'finally_formula': '(!(ARF & (((JKD | !(MGP & (SCR & (SHR & (WOX))))) | !IAA) | !AUXINS) | !ARF & ((JKD | !(MGP & (SCR & (SHR & (WOX))))) | !AUXINS)))', 'border_size': 4, 'source': 9, 'finally_size': 6, 'border_formula': '(!(ARF & (((JKD | !(MGP & (SCR & (SHR & (WOX))))) | !IAA) | !AUXINS) | !ARF & ((IAA | (JKD | !(MGP & (SCR & (SHR & (WOX)))))) | !AUXINS)))'}, {'target': 7, 'finally_formula': '(!(ARF & ((IAA & (JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !IAA & (JKD | (MGP | (((WOX) | !SHR) | !SCR)))) | !AUXINS) | !ARF & ((JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !AUXINS)))', 'border_size': 12, 'source': 9, 'finally_size': 20, 'border_formula': '(!(ARF & ((JKD | (MGP | (((WOX) | !SHR) | !SCR))) | !AUXINS) | !ARF & ((JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & !(((WOX) | !SHR) | !SCR))) | !AUXINS)))'}, {'target': 8, 'finally_formula': '(ARF & (AUXINS & (IAA & (JKD & (MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !IAA & !((MGP | (((WOX) | !SHR) | !SCR)) | !JKD))) | !ARF & (AUXINS & (JKD & (MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR))))))', 'border_size': 10, 'source': 11, 'finally_size': 20, 'border_formula': '(ARF & (AUXINS & (IAA & (JKD & (SCR & (SHR & (WOX)))) | !IAA & !((MGP | (((WOX) | !SHR) | !SCR)) | !JKD))) | !ARF & !((IAA | !(JKD & (SCR & (SHR & (WOX))))) | !AUXINS))'}, {'target': 10, 'finally_formula': '(ARF & (AUXINS & (IAA & (JKD & (MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !IAA & !((MGP | (((WOX) | !SHR) | !SCR)) | !JKD))) | !ARF & (AUXINS & (JKD & (MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR))))))', 'border_size': 12, 'source': 11, 'finally_size': 20, 'border_formula': '(!(ARF & (((MGP | (((WOX) | !SHR) | !SCR)) | !JKD) | !AUXINS) | !ARF & !(AUXINS & (JKD & (MGP & (SCR & (SHR & (WOX))) | !MGP & !(((WOX) | !SHR) | !SCR))))))'}], 'multigraph': False}
        expected = json_graph.node_link_graph(data)
        print diagrams_are_equal(diagram, expected)
        diagram2image(diagram, primes, FnameIMAGE="Junk/diagram.pdf", StyleInputs=True)

        igraph = InteractionGraphs.primes2igraph(primes)
        InteractionGraphs.igraph2image(igraph,"Junk/igraph.pdf")
    

    if 1:
        # 
        primes = Examples.get_primes("tournier_apoptosis")
        update = "asynchronous"
        attractors = TrapSpaces.trap_spaces(primes, "min")
        diagram = basins_diagram( primes, update, attractors )
        #print json_graph.node_link_data(diagram)
        data = {'directed': True, 'graph': {'name': '()_with_int_labels'}, 'nodes': [{'formula': '(!AUXINS&!SHR)', 'attractors': [{u'SHR': 0, u'PLT': 0, u'AUXINS': 0, u'WOX': 0, u'IAA': 1, u'MGP': 0, u'ARF': 0, u'JKD': 0, u'SCR': 0}], 'id': 0, 'size': 128}, {'formula': '(!(AUXINS | (SCR | !(SHR))))', 'attractors': [{u'SHR': 1, u'PLT': 0, u'AUXINS': 0, u'WOX': 0, u'IAA': 1, u'MGP': 0, u'ARF': 0, u'JKD': 0, u'SCR': 0}], 'id': 1, 'size': 64}, {'formula': '(!(AUXINS | !(JKD & (SCR & (SHR)))))', 'attractors': [{u'SHR': 1, u'PLT': 0, u'AUXINS': 0, u'WOX': 0, u'IAA': 1, u'MGP': 1, u'ARF': 0, u'JKD': 1, u'SCR': 1}], 'id': 2, 'size': 32}, {'formula': '(!((SCR | !(SHR)) | !AUXINS))', 'attractors': [{u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 0, u'IAA': 0, u'MGP': 0, u'ARF': 1, u'JKD': 0, u'SCR': 0}], 'id': 3, 'size': 64}, {'formula': '(!(AUXINS | (JKD | !(SCR & (SHR)))))', 'attractors': [{u'SHR': 1, u'PLT': 0, u'AUXINS': 0, u'WOX': 0, u'IAA': 1, u'MGP': 1, u'ARF': 0, u'JKD': 1, u'SCR': 1}, {u'SHR': 1, u'PLT': 0, u'AUXINS': 0, u'WOX': 0, u'IAA': 1, u'MGP': 0, u'ARF': 0, u'JKD': 0, u'SCR': 0}], 'id': 4, 'size': 32}, {'formula': '(!(((IAA | (JKD | !(MGP & (SCR & (SHR & (WOX)))))) | !AUXINS) | !ARF))', 'attractors': [{u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 0, u'IAA': 0, u'MGP': 0, u'ARF': 1, u'JKD': 0, u'SCR': 0}, {u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 1, u'IAA': 0, u'MGP': 0, u'ARF': 1, u'JKD': 1, u'SCR': 1}], 'id': 5, 'size': 2}, {'formula': '(AUXINS&!SHR)', 'attractors': [{u'SHR': 0, u'PLT': 1, u'AUXINS': 1, u'WOX': 0, u'IAA': 0, u'MGP': 0, u'ARF': 1, u'JKD': 0, u'SCR': 0}], 'id': 6, 'size': 128}, {'formula': '(!((JKD | ((((WOX) | !SHR) | !SCR) | !MGP)) | !AUXINS))', 'attractors': [{u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 0, u'IAA': 0, u'MGP': 1, u'ARF': 1, u'JKD': 1, u'SCR': 1}, {u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 0, u'IAA': 0, u'MGP': 0, u'ARF': 1, u'JKD': 0, u'SCR': 0}], 'id': 7, 'size': 8}, {'formula': '(!(((IAA | !(JKD & (SCR & (SHR & (WOX))) | !JKD & !(MGP | !(SCR & (SHR & (WOX)))))) | !AUXINS) | !ARF))', 'attractors': [{u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 1, u'IAA': 0, u'MGP': 0, u'ARF': 1, u'JKD': 1, u'SCR': 1}], 'id': 8, 'size': 6}, {'formula': '(!(ARF & ((IAA & (JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !IAA & (JKD | (MGP | (((WOX) | !SHR) | !SCR)))) | !AUXINS) | !ARF & ((JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !AUXINS)))', 'attractors': [{u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 0, u'IAA': 0, u'MGP': 1, u'ARF': 1, u'JKD': 1, u'SCR': 1}, {u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 0, u'IAA': 0, u'MGP': 0, u'ARF': 1, u'JKD': 0, u'SCR': 0}, {u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 1, u'IAA': 0, u'MGP': 0, u'ARF': 1, u'JKD': 1, u'SCR': 1}], 'id': 9, 'size': 20}, {'formula': '(!((((((WOX) | !SHR) | !SCR) | !MGP) | !JKD) | !AUXINS))', 'attractors': [{u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 0, u'IAA': 0, u'MGP': 1, u'ARF': 1, u'JKD': 1, u'SCR': 1}], 'id': 10, 'size': 8}, {'formula': '(ARF & (AUXINS & (IAA & (JKD & (MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !IAA & !((MGP | (((WOX) | !SHR) | !SCR)) | !JKD))) | !ARF & (AUXINS & (JKD & (MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR))))))', 'attractors': [{u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 0, u'IAA': 0, u'MGP': 1, u'ARF': 1, u'JKD': 1, u'SCR': 1}, {u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 1, u'IAA': 0, u'MGP': 0, u'ARF': 1, u'JKD': 1, u'SCR': 1}], 'id': 11, 'size': 20}], 'links': [{'target': 1, 'finally_formula': '(!(AUXINS | (JKD | !(SCR & (SHR)))))', 'border_size': 16, 'source': 4, 'finally_size': 32, 'border_formula': '(!(AUXINS | (JKD | !(MGP & (SCR & (SHR))))))'}, {'target': 2, 'finally_formula': '(!(AUXINS | (JKD | !(SCR & (SHR)))))', 'border_size': 32, 'source': 4, 'finally_size': 32, 'border_formula': '(!(AUXINS | (JKD | !(SCR & (SHR)))))'}, {'target': 8, 'finally_formula': '(!(((IAA | (JKD | !(MGP & (SCR & (SHR & (WOX)))))) | !AUXINS) | !ARF))', 'border_size': 2, 'source': 5, 'finally_size': 2, 'border_formula': '(!(((IAA | (JKD | !(MGP & (SCR & (SHR & (WOX)))))) | !AUXINS) | !ARF))'}, {'target': 3, 'finally_formula': '(!(((IAA | (JKD | !(MGP & (SCR & (SHR & (WOX)))))) | !AUXINS) | !ARF))', 'border_size': 2, 'source': 5, 'finally_size': 2, 'border_formula': '(!(((IAA | (JKD | !(MGP & (SCR & (SHR & (WOX)))))) | !AUXINS) | !ARF))'}, {'target': 10, 'finally_formula': '(!((JKD | ((((WOX) | !SHR) | !SCR) | !MGP)) | !AUXINS))', 'border_size': 8, 'source': 7, 'finally_size': 8, 'border_formula': '(!((JKD | ((((WOX) | !SHR) | !SCR) | !MGP)) | !AUXINS))'}, {'target': 3, 'finally_formula': '(!((JKD | ((((WOX) | !SHR) | !SCR) | !MGP)) | !AUXINS))', 'border_size': 8, 'source': 7, 'finally_size': 8, 'border_formula': '(!((JKD | ((((WOX) | !SHR) | !SCR) | !MGP)) | !AUXINS))'}, {'target': 8, 'finally_formula': '(!(ARF & ((IAA & (JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !IAA & (JKD | (MGP | (((WOX) | !SHR) | !SCR)))) | !AUXINS) | !ARF & ((JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !AUXINS)))', 'border_size': 6, 'source': 9, 'finally_size': 20, 'border_formula': '(!(ARF & ((IAA & (JKD | (MGP | !(SCR & (SHR & (WOX))))) | !IAA & (JKD | (MGP | (((WOX) | !SHR) | !SCR)))) | !AUXINS) | !ARF & ((IAA | (JKD | (MGP | !(SCR & (SHR & (WOX)))))) | !AUXINS)))'}, {'target': 3, 'finally_formula': '(!(ARF & (((JKD | !(MGP & (SCR & (SHR & (WOX))))) | !IAA) | !AUXINS) | !ARF & ((JKD | !(MGP & (SCR & (SHR & (WOX))))) | !AUXINS)))', 'border_size': 6, 'source': 9, 'finally_size': 6, 'border_formula': '(!(ARF & (((JKD | !(MGP & (SCR & (SHR & (WOX))))) | !IAA) | !AUXINS) | !ARF & ((JKD | !(MGP & (SCR & (SHR & (WOX))))) | !AUXINS)))'}, {'target': 11, 'finally_formula': '(!(ARF & ((IAA & (JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !IAA & (JKD | (MGP | (((WOX) | !SHR) | !SCR)))) | !AUXINS) | !ARF & ((JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !AUXINS)))', 'border_size': 20, 'source': 9, 'finally_size': 20, 'border_formula': '(!(ARF & ((IAA & (JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !IAA & (JKD | (MGP | (((WOX) | !SHR) | !SCR)))) | !AUXINS) | !ARF & ((JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !AUXINS)))'}, {'target': 5, 'finally_formula': '(!(ARF & (((JKD | !(MGP & (SCR & (SHR & (WOX))))) | !IAA) | !AUXINS) | !ARF & ((JKD | !(MGP & (SCR & (SHR & (WOX))))) | !AUXINS)))', 'border_size': 4, 'source': 9, 'finally_size': 6, 'border_formula': '(!(ARF & (((JKD | !(MGP & (SCR & (SHR & (WOX))))) | !IAA) | !AUXINS) | !ARF & ((IAA | (JKD | !(MGP & (SCR & (SHR & (WOX)))))) | !AUXINS)))'}, {'target': 7, 'finally_formula': '(!(ARF & ((IAA & (JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !IAA & (JKD | (MGP | (((WOX) | !SHR) | !SCR)))) | !AUXINS) | !ARF & ((JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !AUXINS)))', 'border_size': 12, 'source': 9, 'finally_size': 20, 'border_formula': '(!(ARF & ((JKD | (MGP | (((WOX) | !SHR) | !SCR))) | !AUXINS) | !ARF & ((JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & !(((WOX) | !SHR) | !SCR))) | !AUXINS)))'}, {'target': 8, 'finally_formula': '(ARF & (AUXINS & (IAA & (JKD & (MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !IAA & !((MGP | (((WOX) | !SHR) | !SCR)) | !JKD))) | !ARF & (AUXINS & (JKD & (MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR))))))', 'border_size': 10, 'source': 11, 'finally_size': 20, 'border_formula': '(ARF & (AUXINS & (IAA & (JKD & (SCR & (SHR & (WOX)))) | !IAA & !((MGP | (((WOX) | !SHR) | !SCR)) | !JKD))) | !ARF & !((IAA | !(JKD & (SCR & (SHR & (WOX))))) | !AUXINS))'}, {'target': 10, 'finally_formula': '(ARF & (AUXINS & (IAA & (JKD & (MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !IAA & !((MGP | (((WOX) | !SHR) | !SCR)) | !JKD))) | !ARF & (AUXINS & (JKD & (MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR))))))', 'border_size': 12, 'source': 11, 'finally_size': 20, 'border_formula': '(!(ARF & (((MGP | (((WOX) | !SHR) | !SCR)) | !JKD) | !AUXINS) | !ARF & !(AUXINS & (JKD & (MGP & (SCR & (SHR & (WOX))) | !MGP & !(((WOX) | !SHR) | !SCR))))))'}], 'multigraph': False}
        expected = json_graph.node_link_graph(data)
        print diagrams_are_equal(diagram, expected)
        diagram2image(diagram, primes, FnameIMAGE="Junk/diagram.pdf", StyleInputs=True)

        igraph = InteractionGraphs.primes2igraph(primes)
        InteractionGraphs.igraph2image(igraph,"Junk/igraph.pdf")

        diagram2abstract_image(diagram, "Junk/abstraction.pdf")
    
    # print json_graph.node_link_data(diagram)
    


    
if __name__=="__main__":

    if 1:
        tests()

if 0:    
    bnet = ExampleNetworks.grieco_mapk
    bnet = tnet2
    primes = FileExchange.bnet2primes(bnet)
    update = "asynchronous"

    attractors = TrapSpaces.trap_spaces(primes, "min")
    #diagram1, count = basins_diagram_naive( primes, update, attractors, Silent=False )
    #diagram2image(diagram1, primes, FnameIMAGE="diagram_naive.pdf", StyleInputs=False)
    
    diagram2 = basins_diagram( primes, update, attractors )
    diagram2image(diagram2, primes, FnameIMAGE="Junk/diagram.pdf", StyleInputs=False)


                            



