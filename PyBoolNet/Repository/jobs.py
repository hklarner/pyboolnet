

import sys
import os

BASE = os.path.normpath(os.path.abspath(os.path.join(os.path.dirname(__file__), "../..")))
sys.path.insert(0,BASE)

import PyBoolNet


def run():

    for name in PyBoolNet.Repository.get_all_names():
        if name=="n12c5": continue
        
        primes = PyBoolNet.FileExchange.bnet2primes(os.path.join(name,name+".bnet"))

        fname = os.path.join(name,name+"_igraph.pdf")
        PyBoolNet.InteractionGraphs.create_image(primes,fname)
        
    
    for name in PyBoolNet.Repository.names_with_fast_analysis():
        
        name = "davidich_yeast"
        
        primes = PyBoolNet.FileExchange.bnet2primes(os.path.join(name,name+".bnet"))

        fname = os.path.join(name,name+"_attractors.md")
        PyBoolNet.AttractorDetection.create_attractor_report(primes, fname)

        fname = os.path.join(name,name+"_commitment_diagram.pdf")        
        PyBoolNet.Basins.commitment_diagram(primes, "asynchronous", Silent=False, FnameImage=fname)

        fname = os.path.join(name,name+"_commitment_pie.pdf")        
        PyBoolNet.Basins.commitment_pie(primes, "asynchronous", Silent=False, FnameImage=fname)

        fname = os.path.join(name,name+"_all_basins.pdf")        
        PyBoolNet.Basins.all_basins(primes, "asynchronous", FnameImage=fname, Title="All Basins - %s"%name)

        fname = os.path.join(name,name+"_strong_basins.pdf")        
        PyBoolNet.Basins.strong_basins(primes, "asynchronous", FnameImage=fname, Title="Strong Basins - %s"%name)

        break

if __name__=="__main__":
    run()
