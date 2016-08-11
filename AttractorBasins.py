

import os
import sys
import itertools
import math
import random
import operator
import functools
import networkx

BASE = os.path.normpath(os.path.abspath(os.path.join(os.path.dirname(__file__))))
sys.path.append(BASE)

import PyBoolNet.FileExchange
import PyBoolNet.ModelChecking
import PyBoolNet.TemporalQueries
import PyBoolNet.TrapSpaces
import PyBoolNet.AttractorDetection
import PyBoolNet.StateTransitionGraphs
import PyBoolNet.InteractionGraphs
import PyBoolNet.PrimeImplicants
import PyBoolNet.Utility

config = PyBoolNet.Utility.Misc.myconfigparser.SafeConfigParser()
config.read( os.path.join(BASE, "Dependencies", "settings.cfg") )
CMD_DOT = os.path.join( BASE, "Dependencies", config.get("Executables", "dot") )



def basins_diagram( Primes, Update, Attractors=None, ComputeBorders=False, Silent=True, ReturnCounter=False ):
    """
    Creates the basin diagram, a networkx.DiGraph, of the STG defined by *Primes* and *Update*.
    The nodes of the diagram represent states that can reach the exact same subset of *Attractors*.
    Nodes are labeled by the index of the attractor in the order given in *Attractors* and the number of states
    that are represented. Edges indicate the existence of a transition between two states in the respective sets.

    The algorithm requires model checking with accepting states, i.e., NuSMV-a.
    Basic steps towards increased efficiency are implemented:
    out-DAGs (aka output cascades) are discarded during model checking, and
    disconnected components are considered separately (and recombined using a cartesian product of diagrams).

    **arguments**:
        * *Primes*: prime implicants
        * *Update* (str): the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
        * *Attractors* (list): list of states or subspaces representing the attractors. *None* results in the computation of the minimal trap spaces.
        * *ComputeBorders* (bool): whether the computation of the so-called border states should be included in the diagram
        * *Silent* (bool): whether information regarding the execution of the algorithm should be printed
        * *ReturnCounter* (bool): whether the number of performed model checks should be returned

    **returns**::
        * *BasinsDiagram* (netowrkx.DiGraph): the basins diagram
        * *Counter* (int): number of model checks performed, if *ReturnCounter=True*

    **example**::

        >>> primes = REPO.get_primes("xiao_wnt5a")
        >>> diagram = basins_diagram(primes, "asynchronous")
        >>> diagram.order()
        6
        >>> diagram.node[4]["formula"]
        '(x4 & (x7))'
        >>> diagram.node[4]["size"]
        32
    """
    
    assert(Update in ["synchronous", "mixed", "asynchronous"])

    if not Attractors:
        Attractors = PyBoolNet.TrapSpaces.trap_spaces(Primes, "min")
    
    if not Primes:
        print("what are the basins of an empty Boolean network?")
        raise Exception

    igraph = PyBoolNet.InteractionGraphs.primes2igraph(Primes)
    outdags = PyBoolNet.InteractionGraphs.find_outdag(igraph)
    igraph.remove_nodes_from(outdags)
    if not Silent:
        print("basin_diagram(..)")
        print(" excluding the out-dag %s"%outdags)

    components = networkx.connected_components(igraph.to_undirected())
    components = [list(x) for x in components]
    if not Silent:
        print(" working on %i connected component(s)"%len(components))
        
    counter = 0
    diagrams = []
    for component in components:
        subprimes = PyBoolNet.PrimeImplicants.copy(Primes)
        remove = [x for x in Primes if not x in component]
        PyBoolNet.PrimeImplicants.remove_variables(subprimes, remove)
        
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
        print(" total executions of NuSMV: %i"%counter)

    if ReturnCounter:
        return diagram, counter
    else:
        return diagram


def basins_diagram_naive( Primes, Update, Attractors, ComputeBorders, Silent ):
    """
    Also computes the basin diagram but without removing out-DAGs or considering connected components separately.
    Not meant for general use. Use basins_diagram(..) instead.
    """
    
    assert(Update in ["synchronous", "mixed", "asynchronous"])
    
    if not Primes:
        print("what are the basins of an empty Boolean network?")
        raise Exception

    # case by case for inputs
    inputs = PyBoolNet.PrimeImplicants.find_inputs(Primes)
    if inputs:
        cases = []
        for combination in PyBoolNet.PrimeImplicants.input_combinations(Primes):
            init = "INIT %s"%PyBoolNet.TemporalQueries.subspace2proposition(Primes,combination)
            attr = [x for x in Attractors if PyBoolNet.Utility.Misc.dicts_are_consistent(x,combination)]
            cases.append((init,attr))
    else:
        cases = [("INIT TRUE",Attractors)]

    counter = 0

    if not Silent:
        print(" basins_diagram_naive(..)")
        print("  inputs: %i"%len(inputs))
        print("  cases:  %i"%len(cases))

    # create nodes
    node = 0
    total_potential_nodes = 0
    states_per_case = 2**(len(Primes)-len(inputs))
    diagram = networkx.DiGraph()
    for i, (init, attr) in enumerate(cases):
        total_potential_nodes+= 2**len(attr)-1
        states_covered = 0
        specs = [PyBoolNet.TemporalQueries.subspace2proposition(Primes,x) for x in attr]
        vectors = len(attr)*[[0,1]]
        vectors = list(itertools.product(*vectors))
        random.shuffle(vectors)

        if not Silent:
            print("  case %i, potential nodes: %i"%(i,2**len(attr)-1))
        
        for vector in vectors:
            if sum(vector)==0: continue
            if states_covered==states_per_case:
                if not Silent:
                    print("  avoided executions of NuSMV due to state counting")
                break

            if len(vector)==1:
                data = {"attractors":   attr,
                        "size":         2**(len(Primes)-len(inputs)),
                        "formula":      init.split()[1]}
                
            else:
                spec = " & ".join("EF(%s)"%x if flag else "!EF(%s)"%x for flag, x in zip(vector, specs))
                spec = "CTLSPEC %s"%spec

                answer, accepting = PyBoolNet.ModelChecking.check_primes_with_acceptingstates(Primes, Update, init, spec)
                counter+=1
                
                data = {"attractors":   [x for flag,x in zip(vector,attr) if flag],
                        "size":         accepting["INITACCEPTING_SIZE"],
                        "formula":      accepting["INITACCEPTING"]}

            if data["size"]>0:
                diagram.add_node(node, data)
                node+=1
                states_covered+= data["size"]

    if not Silent:
        perc = "= %.2f%%"%(100.*diagram.order()/total_potential_nodes) if total_potential_nodes else ""
        print("  total potential nodes: %i"%total_potential_nodes)
        print("  actual nodes: %i %s"%(diagram.order(),perc))

    # list potential targets
    potential_targets = {}
    for source, source_data in diagram.nodes(data=True):
        succs = []
        for target, target_data in diagram.nodes(data=True):
            if source==target: continue
            if all(x in source_data["attractors"] for x in target_data["attractors"]):
                succs.append((target,target_data))
                
        potential_targets[source] = succs

    if not Silent:
        total_potential_edges = sum(len(x) for x in potential_targets.values())
        print("  potential edges: %i"%total_potential_edges)
        
    # create edges
    for source, source_data in diagram.nodes(data=True):
        for target, target_data in potential_targets[source]:

            # computation of edges with borders ...
            if ComputeBorders:
                init = "INIT %s"%source_data["formula"]
                spec = "CTLSPEC EX(%s)"%target_data["formula"]
                answer, accepting = PyBoolNet.ModelChecking.check_primes_with_acceptingstates(Primes, Update, init, spec)
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
                        answer, accepting = PyBoolNet.ModelChecking.check_primes_with_acceptingstates(Primes, Update, init, spec)
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
                answer, accepting = PyBoolNet.ModelChecking.check_primes_with_acceptingstates(Primes, Update, init, spec)
                counter+=1

                data = {}
                data["finally_size"] = accepting["INITACCEPTING_SIZE"]
                data["finally_formula"] = accepting["INITACCEPTING"]

                if data["finally_size"]>0:
                    diagram.add_edge(source, target, data)
                    
    if not Silent:
        perc = "= %.2f%%"%(100.*diagram.size()/total_potential_edges) if total_potential_edges else ""
        print("  actual edges: %i %s"%(diagram.size(),perc))
        print("  total executions of NuSMV: %i"%counter)

    return diagram, counter


def diagram2image(Primes, Diagram, FnameIMAGE, FnameATTRACTORS=None, StyleInputs=True, StyleAdvanced=False):
    """
    Creates the image file *FnameIMAGE* for the basin diagram given by *Diagram*.
    Use *FnameATTRACTORS* to create a separate image in which the indices of the diagram are mapped to the given attractors.
    The flag *StyleInputs* can be used to highlight which basins belong to which input combination.
    *StyleAdvanced* draws edges and nodes slightly differently to indicates whether transitions are reachable from all source
    states and whether all successor basins are reachable from all source states.

    **arguments**:
        * *Primes*: prime implicants, needed for pretty printing of the attractors.
        * *Diagram* (networkx.DiGrap): a basin diagram
        * *FnameIMAGE* (str): name of the diagram image
        * *FnameATTRACTORS* (str): name of the attractor key file, if wanted
        * *StyleInputs* (bool): whether basins should be grouped by input combinations
        * *StyleAdvanced* (bool): modifies edges and nodes according to "homogeneity"
        
    **returns**::
        * *None*

    **example**::

        >>> diagram2image(primes, diagram, "basins.pdf")
        >>> diagram2image(primes, diagram, "basins.pdf", "attractors.pdf")
    """
    

    size_total = float(2**len(Primes))
    
    graph = networkx.DiGraph()
    graph.graph["node"]  = {"shape":"rect","style":"filled","color":"none"}
    graph.graph["edge"]  = {}
    #graph.graph["splines"] = "ortho"

    attractors = [x["attractors"] for _,x in Diagram.nodes(data=True)]
    attractors = [x for x in attractors if len(x)==1]
    attractors = set(PyBoolNet.StateTransitionGraphs.subspace2str(Primes,x[0]) for x in attractors)
    attractors = sorted(attractors)

    label = ["attractors:"]+["A%i = %s"%x for x in enumerate(attractors)]
    label = "<%s>"%"<br/>".join(label)

    if FnameATTRACTORS:
        key = networkx.DiGraph()
        key.add_node("Attractors",label=label,style="filled",fillcolor="cornflowerblue", shape="rect")
        PyBoolNet.Utility.DiGraphs.digraph2image(key, FnameATTRACTORS, "dot")
        
    else:
        graph.add_node("Attractors",label=label,style="filled",fillcolor="cornflowerblue")

    for node, data in Diagram.nodes(data=True):
        attr = sorted("A%i"%attractors.index(PyBoolNet.StateTransitionGraphs.subspace2str(Primes,x)) for x in data["attractors"])
        attr = PyBoolNet.Utility.Misc.divide_list_into_similar_length_lists(attr)
        attr = [",".join(x) for x in attr]
        label = attr+["states: %s"%data["size"]]
        label = "<br/>".join(label)
        label = "<%s>"%label

        graph.add_node(node, label=label)

        if len(data["attractors"])==1:
            graph.node[node]["color"] = "cornflowerblue"
            graph.node[node]["penwidth"] = "4"

        size_percent = data["size"] / size_total
        
        graph.node[node]["fillcolor"] = "0.0 0.0 %.2f"%(1-size_percent)
        if size_percent>0.5: graph.node[node]["fontcolor"] = "0.0 0.0 0.8"            

        if StyleAdvanced:
            if all(d["finally_size"]==data["size"] for _,_,d in Diagram.out_edges(node,data=True)):
                graph.node[node]["fontcolor"] = "cornflowerblue"
        

    for source, target, data in Diagram.edges(data=True):
        graph.add_edge(source, target)
        if StyleAdvanced:
            if data["finally_size"] < Diagram.node[source]["size"]:
                graph.edge[source][target]["style"]="dashed"
        

    if StyleInputs:
        subgraphs = []
        for inputs in PyBoolNet.PrimeImplicants.input_combinations(Primes):
            nodes = [x for x in Diagram.nodes() if PyBoolNet.Utility.Misc.dicts_are_consistent(inputs,Diagram.node[x]["attractors"][0])]
            label = PyBoolNet.StateTransitionGraphs.subspace2str(Primes,inputs)
            subgraphs.append((nodes,{"label":"inputs: %s"%label, "color":"none"}))
            
        if subgraphs:
            graph.graph["subgraphs"] = []

        PyBoolNet.Utility.DiGraphs.add_style_subgraphs(graph, subgraphs)


    mapping = {x:str(x) for x in graph.nodes()}
    networkx.relabel_nodes(graph,mapping,copy=False)
        
    PyBoolNet.Utility.DiGraphs.digraph2image(graph, FnameIMAGE, "dot")


def diagram2aggregate_image(Primes, Diagram, FnameIMAGE ):
    """
    Creates the image file *FnameIMAGE* for the aggregated basin diagram given by *Diagram*.
    The aggregated basin diagram takes the union of all basins from which the same number of attractors
    can be reached even if they are not the exact same set.
    
    **arguments**:
        * *Primes*: prime implicants, needed for pretty printing of the attractors.
        * *Diagram* (networkx.DiGrap): a basin diagram
        * *FnameIMAGE* (str): name of the aggragated diagram image
        
    **returns**::
        * *None*

    **example**::

        >>> diagram2aggregate_image(diagram, "aggregated.pdf")
    """
    
    graph = networkx.DiGraph()
    graph.graph["node"]  = {"shape":"rect","style":"filled","color":"none"}

    for node, data in Diagram.nodes(data=True):
        x = len(data["attractors"])
        if not x in graph:
            graph.add_node(x, size=data["size"])
        else:
            graph.node[x]["size"]+= data["size"]

    size_total = float(2**len(Primes))
    for x, data in graph.nodes(data=True):
        size_percent = data["size"] / size_total
        graph.node[x]["label"] = "<attractors: %s<br/>states: %s>"%(x,data["size"])
        graph.node[x]["fillcolor"] = "0.0 0.0 %.2f"%(1-size_percent)
        if size_percent>0.5: graph.node[x]["fontcolor"] = "0.0 0.0 0.8"

    for source, target in Diagram.edges():
        x = len(Diagram.node[source]["attractors"])
        y = len(Diagram.node[target]["attractors"])
        graph.add_edge(x,y)

        
    mapping = {x:str(x) for x in graph.nodes()}
    networkx.relabel_nodes(graph,mapping,copy=False)
        
    PyBoolNet.Utility.DiGraphs.digraph2image(graph, FnameIMAGE, "dot")


## auxillary functions

def project_attractors( Attractors, Names ):
    result = set()
    for space in Attractors:
        projection = tuple((k,v) for k,v in sorted(space.items()) if k in Names)
        result.add(projection)

    result = [dict(x) for x in result]

    return result


def lift_attractors( Attractors, Projection ):
    return [x for x in Attractors for y in Projection if PyBoolNet.Utility.Misc.dicts_are_consistent(x,y)]


def cartesian_product( Diagrams, Factor, ComputeBorders ):
    """
    creates the cartesian product of *Diagrams*.
    """

    diagram = networkx.DiGraph()

    # create nodes
    nodes = [x.nodes(data=True) for x in Diagrams]
    for product in itertools.product(*nodes):
        data = {}
        data["size"] = functools.reduce(operator.mul,[x["size"] for _,x in product]) * Factor
        data["formula"] = " & ".join("(%s)"%x["formula"] for _,x in product)
            
        attrs = [x["attractors"] for _,x in product]
        attrs = list(itertools.product(*attrs))
        attrs = [PyBoolNet.Utility.Misc.merge_dicts(x) for x in attrs]
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




    
if __name__=="__main__":
    print("nothing to do")



                            



