

import sys
import os

BASE = os.path.normpath(os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))
sys.path.append(BASE)

import FileExchange
import InteractionGraphs
import StateTransitionGraphs
import TrapSpaces
import AttractorDetection
import AttractorBasins


if __name__=="__main__":

    rootdir = '.'

    for subdir, _, files in os.walk(rootdir):
        for fname in files:
            if fname in ["remy_tumorigenesis.bnet", "grieco_mapk.bnet", "klamt_tcr.bnet"]:
                continue
            
            if fname.split(".")[1]=="bnet":
                primes = FileExchange.bnet2primes(os.path.join(subdir,fname))
                igraph = InteractionGraphs.primes2igraph(primes)
                InteractionGraphs.add_style_sccs(igraph)
                InteractionGraphs.add_style_interactionsigns(igraph)
                fname_igraph = os.path.join(subdir,fname.split(".")[0]+"_igraph.pdf")
                InteractionGraphs.igraph2image(igraph,fname_igraph)
                

                fname_attr = os.path.join(subdir,fname.split(".")[0]+"_attractors.md")
                #AttractorDetection.create_attractor_report(primes, fname_attr)

                attractors = TrapSpaces.trap_spaces(primes, "min")
                fname_basins = os.path.join(subdir,fname.split(".")[0]+"_basins.pdf")
                diagram = AttractorBasins.basins_diagram( primes, "asynchronous", attractors, ComputeBorders=False, Silent=False )
                AttractorBasins.diagram2image(diagram, primes, fname_basins, StyleInputs=True, StyleDetails=False)
                fname_abstract = os.path.join(subdir,fname.split(".")[0]+"_basins_abstract.pdf")
                AttractorBasins.diagram2abstract_image(diagram, primes, fname_abstract)

                
