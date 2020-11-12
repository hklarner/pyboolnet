
# -*- coding: utf-8 -*-

import os
import sys
sys.path.insert(0,"/home/hannes/github/PyBoolNet")

import PyBoolNet



def compute_jsons(Primes, Name, FnameDiagram, FnamePie, Rename=False):

    UPDATE = "asynchronous"
    markers = ["Proliferation", "Growth_arrest", "Apoptosis_medium", "Apoptosis_high"]

    fname = "remy_{n}_attrs.json".format(n=Name)
    if os.path.isfile(fname):
        print(" opening {x}.".format(x=fname))
        attrs = PyBoolNet.Attractors.open_json(fname)
    else:
        print(" creating {x}.".format(x=fname))
        attrs = PyBoolNet.Attractors.compute_json(Primes, UPDATE, FnameJson=fname)

    fname = "remy_{n}_phenos.json".format(n=Name)
    if os.path.isfile(fname):
        print(" opening {x}.".format(x=fname))
        phenos = PyBoolNet.Phenotypes.open_json(fname)
    else:
        phenos = PyBoolNet.Phenotypes.compute_json(attrs, markers, FnameJson=fname)

    if Rename:
        names = {
                # markers = ["Proliferation", "Growth_arrest", "Apoptosis_medium", "Apoptosis_high"]

                # wild type
                "0100": "GA",
                "1000": "P",
                "0110": "A",
                "--00": "OscP/GA",

                # double mutant RB1=0 RBL2=0
                "0000": "x0000",
                "-000": "x-000",
                "----": "x----",


                }

        for x in phenos["phenotypes"]:
            print(" renaming pheno with pattern {y}: {n1} --> {n2}".format(y=x["pattern"], n1=x["name"], n2=names[x["pattern"]]))

            names[x["name"]] = names[x["pattern"]]        # needed for renaming diagram nodes
            x["name"] = names[x["pattern"]]

            steady = len([state for state in x["states"] if state["is_steady"]])
            cyclic = len([state for state in x["states"] if state["is_cyclic"]])
            print("{x}. steady states={y}. cyclic attractors={z}".format(x=x["name"], y=steady, z=cyclic))


    fname = "remy_{n}_phenodiagram.json".format(n=Name)
    if os.path.isfile(fname):
        print(" opening {x}.".format(x=fname))
        diagram = PyBoolNet.Phenotypes.open_diagram(fname)
    else:
        print(" creating {x}.".format(x=fname))
        diagram = PyBoolNet.Phenotypes.compute_diagram(phenos, FnameJson=fname)

    print(" Diagram has {x} nodes".format(x=diagram.order()))
    if Rename:
        colors = {
                  # Wiltype
                  ('GA',):    "#ff7c00",        # orange
                  ('A',):    "#919191",        # gray
                  ('P',):    "#c8fbc0",        # green
                  ('OscP/GA',):    "#c8fbc0",    # green + hatch
                  ('A', 'P'):    "white",
                  ('GA', 'P'):     "white",

                  # double mutant RB1=0 RBL2=0
                  ('x0000',):     "white",
                  ('x-000',):     "white",
                  ('x----',):     "white",
                  }



        for x in diagram:

            #diagram.node[x]["names"] = tuple(sorted(names[y] for y in diagram.node[x]["names"]))

            fillcolor = colors[diagram.node[x]["names"]]
            diagram.node[x]["fillcolor"] = fillcolor

            if fillcolor=="white":
                diagram.node[x]["color"] = "black"

            if diagram.node[x]["names"] == ('OscP/GA',):
                diagram.node[x]["hatch"] = "//"
                diagram.node[x]["color"] = "#ff7c00"
                diagram.node[x]["penwidth"] = 3

    PyBoolNet.Phenotypes.diagram2image(diagram, FnameImage=FnameDiagram)
    PyBoolNet.Phenotypes.create_piechart(diagram, FnameImage=FnamePie, Title="")


def create_figure_05():

    Rename = True

    print("Wildtype")
    primes = PyBoolNet.Repository.get_primes("remy_tumorigenesis")
    compute_jsons(primes, Name="wildtype", FnameDiagram="wildtype_diagram.pdf", FnamePie="wildtype_pie.svg", Rename=Rename)

    print("Wildtype with DNA-damage=0")
    primes = PyBoolNet.Repository.get_primes("remy_tumorigenesis")
    PyBoolNet.PrimeImplicants.create_constants(primes, {"DNA_damage": 0})
    PyBoolNet.PrimeImplicants.substitute_and_remove(primes, Names=["DNA_damage"], Copy=False)
    compute_jsons(primes, Name="wildtype_DNA0", FnameDiagram="wildtype_DNA0_diagram.pdf", FnamePie="wildtype_DNA0_pie.svg", Rename=Rename)

    print("Wildtype with DNA-damage=1")
    primes = PyBoolNet.Repository.get_primes("remy_tumorigenesis")
    PyBoolNet.PrimeImplicants.create_constants(primes, {"DNA_damage": 1})
    PyBoolNet.PrimeImplicants.substitute_and_remove(primes, Names=["DNA_damage"], Copy=False)
    compute_jsons(primes, Name="wildtype_DNA1", FnameDiagram="wildtype_DNA1_diagram.pdf", FnamePie="wildtype_DNA1_pie.svg", Rename=Rename)

    if 0:
        print("Double Mutant RB1=0 RBL2=0")
        primes = PyBoolNet.Repository.get_primes("remy_tumorigenesis")
        PyBoolNet.PrimeImplicants.create_constants(primes, {"RB1": 0, "RBL2":0})
        PyBoolNet.PrimeImplicants.substitute_and_remove(primes, Names=["RB1", "RBL2"], Copy=False)
        compute_jsons(primes, Name="double_mutant", FnameDiagram="double_mutant_diagram.pdf", FnamePie="double_mutant_pie.svg", Rename=Rename)

    print("Single Mutant RB1=0")
    primes = PyBoolNet.Repository.get_primes("remy_tumorigenesis")
    PyBoolNet.PrimeImplicants.create_constants(primes, {"RB1": 0})
    PyBoolNet.PrimeImplicants.substitute_and_remove(primes, Names=["RB1"], Copy=False)
    compute_jsons(primes, Name="single_mutant", FnameDiagram="single_mutant_diagram.pdf", FnamePie="single_mutant_pie.svg", Rename=Rename)


if __name__=="__main__":
    create_figure_05()




















# end of file
