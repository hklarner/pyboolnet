

import sys
import os

BASE = os.path.normpath(os.path.abspath(os.path.join(os.path.dirname(__file__), "../..")))
sys.path.insert(0,BASE)

import PyBoolNet


if __name__=="__main__":

#    for name in ["grieco_mapk", "remy_tumorigenesis"]:
#    for name in ["n5_steady3"]:
    for name in PyBoolNet.Repository.names_with_fast_basin_computation():
        
        primes = PyBoolNet.FileExchange.bnet2primes(os.path.join(name,name+".bnet"))
        igraph = PyBoolNet.InteractionGraphs.primes2igraph(primes)
        PyBoolNet.InteractionGraphs.add_style_sccs(igraph)
        PyBoolNet.InteractionGraphs.add_style_interactionsigns(igraph)
        fname_igraph = os.path.join(name,name+"_igraph.pdf")
        PyBoolNet.InteractionGraphs.igraph2image(igraph,fname_igraph)

        fname_attr = os.path.join(name,name+"_attractors.md")
        PyBoolNet.AttractorDetection.create_attractor_report(primes, fname_attr)

        attractors = PyBoolNet.TrapSpaces.trap_spaces(primes, "min")
        fname_basins = os.path.join(name,name+"_commitment.pdf")
        
        diagram = PyBoolNet.Basins.commitment_diagram(primes, "asynchronous", Silent=False)
        PyBoolNet.Basins.diagram2image(primes, diagram, fname_basins)
