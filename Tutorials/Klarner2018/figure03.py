
# -*- coding: utf-8 -*-



import PyBoolNet

bnet = """
# created using http://page.mi.fu-berlin.de/klarner/iBoolNet/iBoolNet.html
v1, !v1&v2 | v1&!v2&!v3
v2, v1&v3
v3, v2
"""

PRIMES = PyBoolNet.FileExchange.bnet2primes(bnet)
UPDATE = "asynchronous"
ATTRS = PyBoolNet.Attractors.compute_json(PRIMES, UPDATE)
PyBoolNet.Basins.compute_basins(ATTRS)




def style_stg_commitment(stg, diagram):
    for i,node in enumerate(diagram):
        for x in PyBoolNet.StateTransitionGraphs.enumerate_states(PRIMES, diagram.node[node]["formula"]):
            stg.node[x]["fillcolor"] = PyBoolNet.Commitment.COMMITMENT_COLORS[i]
            diagram.node[node]["fillcolor"] = PyBoolNet.Commitment.COMMITMENT_COLORS[i]

    stg.graph["node"]["shape"] = "circle"
    stg.graph["node"]["color"] = "black"

    stg.node["000"]["shape"] = "doublecircle"
    stg.node["100"]["shape"] = "doublecircle"



def create_figure_03():

    engine = "neato"

    diagram = PyBoolNet.Commitment.compute_diagram(ATTRS)
    stg = PyBoolNet.StateTransitionGraphs.primes2stg(PRIMES, UPDATE)
    style_stg_commitment(stg, diagram)
    PyBoolNet.StateTransitionGraphs.stg2image(stg, FnameIMAGE="figure03a.pdf", LayoutEngine=engine)
    PyBoolNet.Commitment.diagram2image(diagram, FnameImage="figure03b.pdf")
    PyBoolNet.Commitment.create_piechart(diagram, FnameImage="figure03c.pdf", Title="")




if __name__=="__main__":

    create_figure_03()


















# end of file
