

import sys
import os

BASE = os.path.normpath(os.path.abspath(os.path.join(os.path.dirname(__file__), "../..")))
sys.path.insert(0,BASE)

import PyBoolNet


if __name__=="__main__":

    rootdir = '.'

    for subdir, _, files in os.walk(rootdir):
        for fname in files:
            if fname not in ["remy_tumorigenesis.bnet"]: continue#,"klamt_tcr.bnet","grieco_mapk.bnet"]: continue
            
            if fname.split(".")[1]=="bnet":
                primes = PyBoolNet.FileExchange.bnet2primes(os.path.join(subdir,fname))
                igraph = PyBoolNet.InteractionGraphs.primes2igraph(primes)
                PyBoolNet.InteractionGraphs.add_style_sccs(igraph)
                PyBoolNet.InteractionGraphs.add_style_interactionsigns(igraph)
                fname_igraph = os.path.join(subdir,fname.split(".")[0]+"_igraph.pdf")
                PyBoolNet.InteractionGraphs.igraph2image(igraph,fname_igraph)
                

                fname_attr = os.path.join(subdir,fname.split(".")[0]+"_attractors.md")
                #PyBoolNet.AttractorDetection.create_attractor_report(primes, fname_attr)

                attractors = PyBoolNet.TrapSpaces.trap_spaces(primes, "min")
                fname_basins = os.path.join(subdir,fname.split(".")[0]+"_basins.pdf")
                fname_key = os.path.join(subdir,fname.split(".")[0]+"_basins_key.pdf")
                
                diagram = PyBoolNet.AttractorBasins.commitment_diagram(primes, "asynchronous")
                PyBoolNet.AttractorBasins.diagram2image(primes, diagram, fname_basins, FnameATTRACTORS=fname_key)
                fname_abstract = os.path.join(subdir,fname.split(".")[0]+"_basins_abstract.pdf")
                PyBoolNet.AttractorBasins.diagram2aggregate_image(primes, diagram, fname_abstract)

                
