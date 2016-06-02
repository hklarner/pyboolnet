

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
import Utility

config = Utility.myconfigparser.SafeConfigParser()
config.read( os.path.join(BASE, "Dependencies", "settings.cfg") )
CMD_DOT = os.path.join( BASE, "Dependencies", config.get("Executables", "dot") )



def diagram2image( Primes, Update, FnameIMAGE, Silent=False ):
    """
    Creates an image of the attractor diagram for the STG of the network defined by *Primes* and *Update*.

    **arguments**:
        * *Primes*: primes implicants
        * *Update* (str): either *"asynchronous"* or *"synchronous"*
        * *FnameIMAGE* (str): name of output file

    **example**::

        >>> primes = FEX.read_primes("mapk.primes")
        >>> update = "asynchronous"
        >>> diagram2image(primes, update, "diagram.pdf")
        created diagram.pdf         
    """

    mints = TrapSpaces.trap_spaces(Primes, "min")
    if mints == [{}]:
        print("!!trivial case")

    diagram = networkx.DiGraph()
    diagram.graph["node"]  = {"shape":"rect","color":"none","fillcolor":"none"}
    diagram.graph["edge"]  = {}

    props = [TemporalQueries.subspace2proposition(primes,x) for x in mints]
    vectors = len(mints)*[[0,1]]
    vectors = itertools.product(*vectors)

    n = float(2**len(Primes))

    # add nodes
    nodes = {}
    for vector in vectors:
        if sum(vector)==0: continue
        
        spec = ["EF(%s)"%p if v else "!EF(%s)"%p for v,p in zip(vector,props)]
        spec = " & ".join(spec)
        spec = "CTLSPEC %s"%spec
        init = "INIT TRUE"

        answer, accepting = ModelChecking.check_primes(Primes, Update, init, spec, AcceptingStates=True)
        

        if accepting["INITACCEPTING_SIZE"]>0:
            node = "".join([str(v) for v in vector])
            label = "<%s<br/>%i>"%(node, accepting["INITACCEPTING_SIZE"])
            
            diagram.add_node(node, label=label, style="filled")

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
                    diagram.add_edge(source, target, style="dashed")
                elif accepting["INITACCEPTING_SIZE"] == nodes[source]["INITACCEPTING_SIZE"]:
                    diagram.add_edge(source, target, style="solid")
            


    for source in diagram.nodes():
        accepting = nodes[source]
        value = 1 - accepting["INITACCEPTING_SIZE"] / n
        diagram.node[source]["fillcolor"] = "0.0 0.0 %.2f"%value
        if value<.5:
            diagram.node[source]["fontcolor"] = "white"

        if diagram.out_degree(source)==0: continue
        if all(diagram.edge[source][x]["style"]=="solid" for x in diagram.successors(source)):
            diagram.node[source]["color"] = "cornflowerblue"
            diagram.node[source]["penwidth"] = "5"


    StateTransitionGraphs.stg2dot(diagram, FnameIMAGE.replace("pdf","dot"))
    StateTransitionGraphs.stg2image(diagram, FnameIMAGE)
        
        


         

if __name__=="__main__":
    import FileExchange
    bnet = ExampleNetworks.davidich_yeast
    primes = FileExchange.bnet2primes(bnet)
    update = "asynchronous"
    diagram2image( primes, update, "davidich_yeast.pdf" )
    



