

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
    

    graph = networkx.DiGraph()
    graph.graph["node"]  = {"shape":"rect","color":"none","fillcolor":"none"}
    graph.graph["edge"]  = {}


    subspaces = [{}]
    inputs = PrimeImplicants.find_inputs(Primes)
    if inputs:
        subspaces = PrimeImplicants.input_combinations(Primes)

    for subspace in subspaces:
        print "subspace", subspace
        prefix = StateTransitionGraphs.subspace2str(Primes,subspace)
        
        subprimes = PrimeImplicants.copy(Primes)
        PrimeImplicants.create_constants(subprimes, Activities=subspace)
        constants = PrimeImplicants.percolate_constants( subprimes, RemoveConstants=True )

        mints = TrapSpaces.trap_spaces(subprimes, "min")
        
        props = [TemporalQueries.subspace2proposition(subprimes,x) for x in mints]
        vectors = len(mints)*[[0,1]]
        vectors = itertools.product(*vectors)

        k = len(constants)-len(inputs)
        factor = 2**k

        # add nodes
        nodes = {}
        for vector in vectors:
            if sum(vector)==0: continue
            
            spec = ["EF(%s)"%p if v else "!EF(%s)"%p for v,p in zip(vector,props)]
            spec = " & ".join(spec)
            spec = "CTLSPEC %s"%spec
            init = "INIT TRUE"

            if len(vector)==1:
                accepting = {"INITACCEPTING_SIZE": 2**(len(Primes)-len(inputs)),
                             "ACCEPTING": "TRUE"}
            else:
                answer, accepting = ModelChecking.check_primes(subprimes, Update, init, spec, AcceptingStates=True)
                

            if accepting["INITACCEPTING_SIZE"]>0:
                node = "".join([str(v) for v in vector])
                size = factor * accepting["INITACCEPTING_SIZE"]

                sub = "%s<br/>"%prefix if subspace else prefix
                label = "<%s<br>%s<br/>%i>"%(sub, node, size)
                
                graph.add_node(prefix+node, label=label, style="filled")

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

                    answer, accepting = ModelChecking.check_primes(Primes, Update, init, spec, AcceptingStates=True)
                    if 0 < accepting["INITACCEPTING_SIZE"] < nodes[source]["INITACCEPTING_SIZE"]:
                        graph.add_edge(prefix+source, prefix+target, style="dashed")
                    elif accepting["INITACCEPTING_SIZE"] == nodes[source]["INITACCEPTING_SIZE"]:
                        graph.add_edge(prefix+source, prefix+target, style="solid")
                


        S = float(2**len(Primes))
        for source in nodes.keys():
            accepting = nodes[source]
            value = 1 - accepting["INITACCEPTING_SIZE"] / S
            
            graph.node[prefix+source]["fillcolor"] = "0.0 0.0 %.2f"%value
            if value<.5:
                graph.node[prefix+source]["fontcolor"] = "white"

            if graph.out_degree(prefix+source)==0: continue
            if all(graph.edge[prefix+source][x]["style"]=="solid" for x in graph.successors(prefix+source)):
                graph.node[prefix+source]["color"] = "cornflowerblue"
                graph.node[prefix+source]["penwidth"] = "5"


    if FnameIMAGE:
        
        StateTransitionGraphs.stg2dot(graph, FnameIMAGE.replace("pdf","dot"))
        StateTransitionGraphs.stg2image(graph, FnameIMAGE)


    return graph
    

         

if __name__=="__main__":
    import FileExchange
    bnet = ExampleNetworks.arellano_antelope
    primes = FileExchange.bnet2primes(bnet)
    update = "asynchronous"
    primes2basins( primes, update, "arellano_antelope_2.pdf" )
    



