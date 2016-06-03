

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



    
def primes2basins( Primes, Update, FnameIMAGE=None ):
    """
    Creates the basins of attraction graph for the STG of the network defined by *Primes* and *Update*.
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


    mints_primes = TrapSpaces.trap_spaces(Primes, "min")
    
    inputs = PrimeImplicants.find_inputs(subprimes)

    


    # divide the problem by input combinations
    subprimes = PrimeImplicants.copy(Primes)
    constants = PrimeImplicants.percolate_constants( subprimes, RemoveConstants=True )
    factor = float(2**len(constants))

    cases = []
    inputs = PrimeImplicants.find_inputs(subprimes)
    if inputs:
        input_combinations = PrimeImplicants.input_combinations(subprimes)
        
        for input_combination in input_combinations:
            newsubprimes = PrimeImplicants.copy(subprimes)
            PrimeImplicants.create_constants(newsubprimes, input_combination)
            newconstants = PrimeImplicants.percolate_constants(newsubprimes, RemoveConstants=True)
            newfactor = factor * 2**(len(newconstants)-len(inputs))
            newconstants = dict(constants, **newconstants)
            
            cases+= [(input_combination, newsubprimes)]
    else:
        cases+= [(constants, subprimes, factor),]

    summe = 0.
    for constants, subprimes, factor in cases:
        print "constants", constants.keys()
        print "subprimes", subprimes.keys()
        print "factor", factor
        print
        summe+= factor

    print "2**n=",float(2**len(Primes))
    print "sum =",summe

    ig = InteractionGraphs.primes2igraph(Primes)
    InteractionGraphs.igraph2image(ig, "igraph.pdf")
    stg = StateTransitionGraphs.primes2stg(Primes, "asynchronous")
    StateTransitionGraphs.stg2image(stg, "stg.pdf")

    mints_primes = TrapSpaces.trap_spaces(Primes, "min")
    
    graph = networkx.DiGraph()
    graph.graph["node"]  = {"shape":"rect","color":"none","fillcolor":"none"}
    graph.graph["edge"]  = {}
    
    nodes = {}

    for constants, subprimes, factor in cases:

        # if this happens then there are only input components!
        if not subprimes:
            
            node = constants
            prefix = StateTransitionGraphs.subspace2str(Primes,constants)

            node = ["1" if node==x else "0" for x in mints_primes]
            node = "".join(node)

            size = factor
            label = "<%s<br/>%i>"%(node, size)
            
            graph.add_node(node, label=label, style="filled")
            accepting = TemporalQueries.subspace2proposition(Primes, {k:v for k,v in constants.items() if k in inputs})
            nodes[node] = {"INITACCEPTING": accepting,
                           "INITACCEPTING_SIZE": size}

        else:
            mints_subprimes = TrapSpaces.trap_spaces(subprimes, "min")

            # easy: one attractor
            if len(mints_subprimes) == 1:
                
                node = dict(constants, **mints_subprimes[0])
                node = ["1" if node==x else "0" for x in mints_primes]
                node = "".join(node)

                size = factor * 2**len(subprimes)
                label = "<%s<br/>%i>"%(node, size)
                
                graph.add_node(node, label=label, style="filled")
                accepting = TemporalQueries.subspace2proposition(Primes, {k:v for k,v in constants.items() if k in inputs})
                nodes[node] = {"INITACCEPTING": accepting,
                               "INITACCEPTING_SIZE": size}

            # difficult: several attractors
            else:
        
                props = [TemporalQueries.subspace2proposition(subprimes,x) for x in mints_subprimes]
                vectors = len(mints_subprimes)*[[0,1]]
                vectors = itertools.product(*vectors)
                
                for vector in vectors:
                    if sum(vector)==0: continue
                    
                    spec = ["EF(%s)"%p if v else "!EF(%s)"%p for v,p in zip(vector,props)]
                    spec = " & ".join(spec)
                    spec = "CTLSPEC %s"%spec
                    init = "INIT TRUE"

                    print "spec", spec
                    answer, accepting = ModelChecking.check_primes(subprimes, Update, init, spec, AcceptingStates=True)
                    print 'accepting["INITACCEPTING_SIZE"]', accepting["INITACCEPTING_SIZE"]

                    if accepting["INITACCEPTING_SIZE"]>0:
                        
                        node = [dict(constants, **x) for v,x in zip(vector,mints_subprimes) if v]
                        node = ["1" if x in node else "0" for x in mints_primes]
                        node = "".join(node)
                        print "node", node

                        size = factor * accepting["INITACCEPTING_SIZE"]
                        label = "<%s<br/>%i>"%(node, size)
                        
                        graph.add_node(node, label=label, style="filled")
                        nodes[node] = accepting


                # add edges
                for source in nodes.keys():
                    
                    subvectors = [[0,1] if x=="1" else [0] for x in source]
                    subvectors = itertools.product(*subvectors)

                    for subvector in subvectors:
                        if sum(subvector)==0: continue
                        target = "".join([str(v) for v in subvector])

                        if target in nodes.keys():
                            if source==target: continue
                            
                            init = "INIT %s"%nodes[source]["ACCEPTING"]
                            spec = "CTLSPEC  E[%s U %s]"%(nodes[source]["ACCEPTING"],nodes[target]["ACCEPTING"])

                            answer, accepting = ModelChecking.check_primes(subprimes, Update, init, spec, AcceptingStates=True)
                            if 0 < accepting["INITACCEPTING_SIZE"] < nodes[source]["INITACCEPTING_SIZE"]:
                                graph.add_edge(source, target, style="dashed")
                                
                            elif accepting["INITACCEPTING_SIZE"] == nodes[source]["INITACCEPTING_SIZE"]:
                                graph.add_edge(source, target, style="solid")
                        


                S = float(2**len(Primes))
                for source in nodes.keys():
                    accepting = nodes[source]
                    value = 1 - accepting["INITACCEPTING_SIZE"] / S
                    
                    graph.node[source]["fillcolor"] = "0.0 0.0 %.2f"%value
                    if value<.5:
                        graph.node[source]["fontcolor"] = "white"

                    if graph.out_degree(source)==0: continue
                    if all(graph.edge[source][x]["style"]=="solid" for x in graph.successors(source)):
                        graph.node[source]["color"] = "cornflowerblue"
                        graph.node[source]["penwidth"] = "5"


    if FnameIMAGE:
        
        StateTransitionGraphs.stg2dot(graph, FnameIMAGE.replace("pdf","dot"))
        StateTransitionGraphs.stg2image(graph, FnameIMAGE)


    return graph
    

         

if __name__=="__main__":
    import FileExchange
    test = 7
    
    if test==1:
        bnet = ExampleNetworks.arellano_antelope
    elif test==2:
        bnet = ExampleNetworks.isolated_circuit(3, "negative")
    elif test==3:
        bnet = """
        v1, 1
        v2, v2
        v3, v4
        v4, !v3 | v2
        """
    elif test==4:
        bnet = """
        v1, 1
        v2, 0
        """
    elif test==5:
        bnet = """
        v1, v1
        v2, v2
        """
    elif test==6:
        bnet = """
        v1, v1
        v2, v1
        v3, v2 & v3
        """
    elif test==7:
        bnet = ExampleNetworks.davidich_yeast
        print bnet
        primes = FileExchange.bnet2primes(bnet)
        ig = InteractionGraphs.primes2igraph(primes)
        InteractionGraphs.igraph2image(ig, "davidich_yeast_ig.pdf")

    else:
    
        primes = FileExchange.bnet2primes(bnet)
        update = "asynchronous"
        primes2basins( primes, update, "test%i.pdf"%test )
    



