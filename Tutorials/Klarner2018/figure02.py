
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


def create_figure_02():

    PyBoolNet.Basins.create_barplot(ATTRS, Yunit="size", FnameImage="figure02a.pdf", Title="")
    PyBoolNet.Basins.create_piechart(ATTRS, Yunit="size", FnameImage="figure02b.pdf", Title="")



if __name__=="__main__":
    create_figure_02()


















# end of file
