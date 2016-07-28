


import subprocess
import shutil
import os
import sys

import networkx

sys.path = ['..'] + sys.path

import PyBoolNet
from PyBoolNet import FileExchange as FEX
from PyBoolNet import StateTransitionGraphs as STGs
from PyBoolNet import InteractionGraphs as IGs
from PyBoolNet import QuineMcCluskey as QMC
from PyBoolNet import ModelChecking as MC
from PyBoolNet import TrapSpaces as TS
from PyBoolNet import AttractorDetection as AD



def pairs(List):
    if not List:
        return List
    x = None
    result = []
    if len(List)%2:
        x = List.pop()
    for i in range(len(List)/2):
        result+= [List[2*i]+", "+List[2*i+1]]
    if x:
        if result:
            result[-1] = result[-1]+","
        result+=[x]

    return result
    

def run():


    RUN_ALL = 1

    if 0 or RUN_ALL:
        print "primes from Python functions"

        f1 = lambda v2,v3,v4,v5: sum([v2,v3,v4,v5])>=2
        
        def f2(v1,v2,v3):
            if f1(v2,v3,0,0):
                return 0
            else:
                return sum([v1,v2,v3]) % 2
        
        f3 = lambda v4,v5: not (v4 or not f2(v4,v4,v5))
        f4 = lambda: 1
        f5 = lambda v5: v5

        funcs = {"v1":f1, "v2":f2, "v3":f3, "v4":f4, "v5":f5}
        primes = QMC.functions2primes(funcs)

        dnf = QMC.functions2mindnf(funcs)
        print dnf["v1"]

    if 0 or RUN_ALL:
        print "figure01.pdf - basic interaction graph"

        bnet = "\n".join(["v1, v1|v3","v2, 1", "v3, v1&!v2 | !v1&v2"])
        primes = FEX.bnet2primes(bnet)
        igraph = IGs.primes2igraph(primes)
        print igraph.nodes()
        print igraph.edges()
        print igraph.edge["v3"]["v1"]["sign"]
        print igraph.edge["v1"]["v3"]["sign"]

        IGs.igraph2image(igraph, "source/figure01.pdf")

    if 0 or RUN_ALL:
        print "graph, node and edge attributes"

        bnet = "\n".join(["v1, v2 & (!v1 | v3)","v2, !v3","v3, v2 | v1"])
        primes = FEX.bnet2primes(bnet)
        igraph = IGs.primes2igraph(primes)
        igraph.graph["node"]["shape"] = "circle"
        igraph.graph["node"]["color"] = "blue"
        igraph.node["v2"]["shape"] = "rpromoter"
        igraph.node["v2"]["color"] = "black"
        igraph.edge["v3"]["v1"]["arrowhead"] = "inv"
        igraph.edge["v3"]["v1"]["color"] = "red"
        igraph.graph["splines"] = "ortho"
        igraph.graph["label"] = "Example 3: Interaction graph with attributes"
        igraph.graph["rankdir"] = "LR"
        IGs.igraph2image(igraph, "source/figure02.pdf")

    if 0 or RUN_ALL:
        print "the interaction signs style"

        funcs = {"v1":lambda v1,v2,v3: v1+v2+v3==1,
                 "v2":lambda v1: not v1,
                 "v3":lambda v2: v2}
        primes = QMC.functions2primes(funcs)
        igraph = IGs.primes2igraph(primes)
        IGs.add_style_interactionsigns(igraph)
        igraph.graph["label"] = "Example 4: Signed interaction graph"
        igraph.graph["rankdir"] = "LR"
        IGs.igraph2image(igraph, "source/figure03.pdf")

    if 0 or RUN_ALL:
        print "styles for inputs, outputs and constants"

        bnet = ["v1, v1", "v2, v2", "v3, 1", "v4, v1 | v3",
                "v5, v4 & v2 | v6", "v6, 0", "v7, !v5",
                "v8, v7", "v9, v5 & v7"]
        bnet = "\n".join(bnet)
        primes = FEX.bnet2primes(bnet)
        igraph = IGs.primes2igraph(primes)
        IGs.add_style_inputs(igraph)
        IGs.add_style_constants(igraph)   
        IGs.add_style_outputs(igraph)
        igraph.graph["label"] = "Example 5: Interaction graph with styles for inputs, outputs and constants"
        IGs.igraph2image(igraph, "source/figure04.pdf")

    if 0 or RUN_ALL:
        print "the SCC and condensation style"

        bnet = ["v1, v1", "v2, v3 & v5", "v3, v1", "v4, v1", "v5, 1",
                "v6, v7", "v7, v6 | v4", "v8, v6", "v9, v8", "v10, v7 & v11",
                "v11, v10 | v4", "v12, v10"]
        bnet = "\n".join(bnet)
        primes = FEX.bnet2primes(bnet)
        igraph = IGs.primes2igraph(primes)
        IGs.add_style_sccs(igraph)
        igraph.graph["label"] = "Example 6: Interaction graph with SCC style"
        IGs.igraph2image(igraph, "source/figure05.pdf")

        IGs.add_style_condensation(igraph)
        igraph.graph["label"] = "Example 7: Interaction graph with SCC and condensation style"
        IGs.igraph2image(igraph, "source/figure06.pdf")

    if 0 or RUN_ALL:
        print "the subgraph style"
        
        bnet = ["v1, v7", "v2, v1 & v6", "v3, v2 | v7", "v4, v3",
                "v5, v1 | v4", "v6, v5", "v7, v6"]
        bnet = "\n".join(bnet)
        primes = FEX.bnet2primes(bnet)
        igraph = IGs.primes2igraph(primes)
        subgraphs = [["v2","v6"],
                     (["v1","v4"],{"label":"Genes", "fillcolor":"lightblue"})]
        IGs.add_style_subgraphs(igraph, subgraphs)
        igraph.graph["label"] = "Example 8: Interaction graph with a subgraph style"
        IGs.igraph2image(igraph, "source/figure07.pdf")

    if 0 or RUN_ALL:
        print "the activities style and animations"
                
        bnet = ["v1, v7",
                   "v2, v1 & v6",
                   "v3, v2 | v7",
                   "v4, v3",
                   "v5, v1 | v4",
                   "v6, v5",
                   "v7, v6"]
        bnet = "\n".join(bnet)
        primes = FEX.bnet2primes(bnet)
        igraph = IGs.primes2igraph(primes)
        activities = {"v2":1, "v3":0, "v4":0}
        IGs.add_style_activities(igraph, activities)
        igraph.graph["label"] = "Example 9: Interaction graph with a activities style"
        igraph.graph["rankdir"] = "LR"
        
        IGs.igraph2image(igraph, "source/figure08.pdf")


    if 0 or RUN_ALL:
        print "the default style"

        bnet = ["v1, v1", "v2, v3 & !v5", "v3, !v1", "v4, v1", "v5, 1",
                "v6, v7", "v7, v6 & !v4 | !v6 & v4", "v8, !v6", "v9, v8", "v10, v7 & !v11",
                "v11, v10 | v4", "v12, v10"]
        bnet = "\n".join(bnet)
        primes = FEX.bnet2primes(bnet)
        igraph = IGs.primes2igraph(primes)
        IGs.add_style_default(igraph)
        IGs.igraph2image(igraph, "PyBoolNet-screenshot.jpg")
        igraph.graph["label"] = "Example 10: Interaction graph with default style"
        IGs.igraph2image(igraph, "source/figure09.pdf")

    if 0 or RUN_ALL:
        print "Drawing the State Transition Graph - Asynchronous"


        bnet = "\n".join(["v1, v3","v2, v1", "v3, v2"])
        primes = FEX.bnet2primes(bnet)
        update = "asynchronous"
        stg = STGs.primes2stg(primes, "asynchronous")
        print repr(stg)
        print stg.nodes()[0]
        print networkx.has_path(stg, "100", "111")
        stg.graph["label"] = "Example 11: The STG of a positive circuit"
        stg.graph["rankdir"] = "LR"
        STGs.stg2image(stg, "source/figure10.pdf")

        init = ["000", "111"]
        stg = STGs.primes2stg(primes, update, init)
        init = ["000", {"v1":1,"v2":1,"v3":1}]
        stg = STGs.primes2stg(primes, update, init)
        init = lambda x: x["v1"]>=x["v2"]
        stg = STGs.primes2stg(primes, update, init)
        init = "--1"
        stg = STGs.primes2stg(primes, update, init)
        init = {"v3":1}
        stg = STGs.primes2stg(primes, update, init)

    if 0 or RUN_ALL:
        print "Drawing the State Transition Graph - Synchronous"
        
        bnet = "\n".join(["v1, !v3","v2, v1", "v3, v2"])
        primes = FEX.bnet2primes(bnet)
        stg = STGs.primes2stg(primes, "synchronous")
        stg.graph["label"] = "Example 12: The synchronous STG of a negative circuit"
        stg.graph["rankdir"] = "LR"
        STGs.add_style_tendencies(stg)
        STGs.stg2image(stg, "source/figure11.pdf")

    if 0 or RUN_ALL:
        print "path style"

        bnet = "\n".join(["x, !x|y", "y, !x&!z|x&!y&z", "z, x|!y"])
        primes = FEX.bnet2primes(bnet)
        stg = STGs.primes2stg(primes, "asynchronous")
        stg.graph["label"] = "Example 13: STG with path style"

        path = ["011","010","110","100","000"]   
        STGs.add_style_path(stg, path, "red")
        STGs.stg2image(stg, "source/figure12.pdf")

    if 0 or RUN_ALL:
        print "scc style for STGs"

        bnet = "\n".join(["x, !x|y", "y, x&!y|!z", "z, x&z|!y"])
        primes = FEX.bnet2primes(bnet)
        stg = STGs.primes2stg(primes, "asynchronous")
        stg.graph["label"] = "Example 14: STG with SCC style"   
        STGs.add_style_sccs(stg)
        STGs.stg2image(stg, "source/figure13.pdf")

    if 0 or RUN_ALL:
        print "min trap spaces style"

        bnet = "\n".join(["x, !x|y&z", "y, x&!y|!z", "z, z|!y"])
        primes = FEX.bnet2primes(bnet)
        stg = STGs.primes2stg(primes, "asynchronous")
        stg.graph["label"] = "Example 15: STG with min trap spaces style"   
        STGs.add_style_mintrapspaces(primes, stg)
        STGs.stg2image(stg, "source/figure14.pdf")


    if 0 or RUN_ALL:
        print "STG subspaces style"

        bnet = "\n".join(["x, !x|y&z", "y, x&!y|!z", "z, z|!y"])
        primes = FEX.bnet2primes(bnet)
        stg = STGs.primes2stg(primes, "asynchronous")
        stg.graph["label"] = "Example 16: STG with subspaces style"
        sub1 = ({"x":0},{"label":"x is zero"})
        sub2 = {"x":1,"y":0}
        subspaces = [sub1, sub2]
        STGs.add_style_subspaces(primes, stg, subspaces)
        
        STGs.stg2image(stg, "source/figure15.pdf")
        

    if 0 or RUN_ALL:
        print "STG default style"

        bnet = "\n".join(["x, !x|y&z", "y, x&!y|!z", "z, z|!y"])
        primes = FEX.bnet2primes(bnet)
        stg = STGs.primes2stg(primes, "asynchronous")
        stg.graph["label"] = "Example 17: STG with default style"   
        STGs.add_style_default(primes, stg)
        
        STGs.stg2image(stg, "source/figure16.pdf")

    if 0 or RUN_ALL:
        print "model checking 1"

        bnet = ["Erk,  Erk & Mek | Mek & Raf",
                "Mek,  Erk | Mek & Raf",
                "Raf,  !Erk | !Raf"]
        bnet = "\n".join(bnet)
        primes = FEX.bnet2primes(bnet)
        stg = STGs.primes2stg(primes, "asynchronous")
        stg.graph["label"] = "Example 18: STG of the Erk-Mek-Raf network"

        STGs.stg2image(stg, "source/figure17a.pdf")

        ## description not in the manual
        ts_basic = STGs.copy(stg)
        ts_basic.graph["label"] = "Example 19: Basic transition system of Erk-Mek-Raf"
        ts_auxillary = STGs.copy(stg)
        ts_auxillary.graph["label"] = "Example 20: Transition system of Erk-Mek-Raf with auxillary variables"
        for x in stg.nodes():
            x_dict = STGs.str2state(primes, x)
            ap_basic = [name for name in sorted(x_dict) if x_dict[name]]
            ap_auxillary = list(ap_basic)
            outdegree = len(list(y for y in stg.successors(x) if y!=x))
            
            suc = STGs.successor_synchronous(primes, x_dict)
            ap_auxillary+= [name+"_STEADY" for name in sorted(x_dict) if suc[name]==x_dict[name]]
            if not outdegree:
                ap_auxillary+= ["STEADYSTATE"]
            ap_auxillary+= ["SUCCESSORS=%i"%outdegree]
            
            ap_basic = pairs(ap_basic)
            ts_basic.node[x]["label"] = "{"+"\\n".join(ap_basic)+"}"

            ap_auxillary = pairs(ap_auxillary)
            ts_auxillary.node[x]["label"] = "{"+"\\n".join(ap_auxillary)+"}"
            
        
        STGs.stg2image(ts_basic, "source/figure17b.pdf")

        proc = subprocess.Popen(["pdflatex", "merge_figure17.tex"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        out, err = proc.communicate()

        proc = subprocess.Popen(["pdfcrop", "merge_figure17.pdf"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        out, err = proc.communicate()
        shutil.copyfile("merge_figure17-crop.pdf", "source/figure17.pdf")

        STGs.stg2image(ts_auxillary, "source/figure18.pdf")        


    if 0 or RUN_ALL:
        print "LTL queries"

        bnet = ["Erk,  Erk & Mek | Mek & Raf",
                "Mek,  Erk | Mek & Raf",
                "Raf,  !Erk | !Raf"]
        bnet = "\n".join(bnet)
        primes = FEX.bnet2primes(bnet)
        init = "INIT TRUE"
        spec = "LTLSPEC F(Raf)"
        update = "asynchronous"
        print MC.check_primes(primes, update, init, spec)


        init = "INIT Erk & SUCCESSORS<2"
        spec = "LTLSPEC G(F(Raf) & F(!Raf))"
        answer = MC.check_primes(primes, "asynchronous", init, spec)
        print init, spec, "is", answer

        init = "INIT Mek"
        spec = "LTLSPEC G(count(Erk_STEADY,Mek_STEADY,Raf_STEADY)>=2)"
        answer = MC.check_primes(primes, "asynchronous", init, spec)
        print init, spec, "is", answer


        print "#### Counterexamples ####"
        init = "INIT TRUE"
        spec = "LTLSPEC F(Raf & F(STEADYSTATE))"
        update = "asynchronous"
        answer, counterex = MC.check_primes(primes, update, init, spec, False)
        print answer
        if counterex:
            print " -> ".join(STGs.state2str(x) for x in counterex)

    if 0 or RUN_ALL:
        print "counterexample path style"

        bnet = ["Erk,  Erk & Mek | Mek & Raf",
                "Mek,  Erk | Mek & Raf",
                "Raf,  !Erk | !Raf"]
        bnet = "\n".join(bnet)
        primes = FEX.bnet2primes(bnet)
        update = "asynchronous"
        
        init = "INIT TRUE"
        spec = "LTLSPEC F(Raf & F(STEADYSTATE))"
        answer, counterex = MC.check_primes(primes, update, init, spec, False)
        if counterex:
            " -> ".join(STGs.state2str(x) for x in counterex)
        
        stg = STGs.primes2stg(primes, update)
        STGs.add_style_path(stg, counterex, "red")
        stg.graph["label"] = "Example 19: A LTL counterexample"
        STGs.stg2image(stg, "source/figure19.pdf")

        igraph = IGs.primes2igraph(primes)
        IGs.activities2animation(igraph, counterex, "counterexample.gif")

    if 0 or RUN_ALL:
        print "CTL examples"

        bnet = ["GrowthFactor,  0",
                "Proliferation, GrowthFactor | Proliferation & !DNAdamage",
                "DNAdamage,     !GrowthFactor & DNAdamage"]
        bnet = "\n".join(bnet)
        primes = FEX.bnet2primes(bnet)
        update = "asynchronous"

        stg = STGs.primes2stg(primes, update)
        for x in stg.nodes():
            x_dict = STGs.str2state(primes, x)
            if x_dict["GrowthFactor"]:
                stg.node[x]["style"] = "filled"
                stg.node[x]["fillcolor"] = "gray"
        sub = ({"Proliferation":1},{"label":"proliferation"})
        STGs.add_style_subspaces(primes, stg, [sub])
        stg.graph["label"] = "Example 20: STG of the Proliferation network"

        STGs.stg2image(stg, "source/figure20.pdf")


        init = "INIT GrowthFactor"
        spec = "LTLSPEC F(Proliferation)"
        answer, counterex = MC.check_primes(primes, update, init, spec, False)
        print init, spec, "is", answer
        STGs.add_style_path(stg, counterex, "red")
        stg.graph["label"] = "Example 21: Counterexample"

        STGs.stg2image(stg, "source/figure21.pdf")

        spec = "CTLSPEC EF(Proliferation)"
        answer = MC.check_primes(primes, update, init, spec)
        print init, spec, "is", answer

    if 0 or RUN_ALL:
        bnet = ["GrowthFactor,  0",
                "Proliferation, GrowthFactor | Proliferation & !DNAdamage",
                "DNAdamage,     !GrowthFactor & DNAdamage"]
        bnet = "\n".join(bnet)
        primes = FEX.bnet2primes(bnet)
        update = "asynchronous"

        init = "INIT !DNAdamage & GrowthFactor"
        c1 = "Proliferation"
        c2 = "DNAdamage_STEADY"
        spec = "CTLSPEC AG(EF(AG(%s | %s)))"%(c1,c2)
        answer = MC.check_primes(primes, update, init, spec)
        print init, spec, "is", answer

        init = "INIT Proliferation"
        condition = "STEADYSTATE"
        spec = "CTLSPEC AG(EF(AG(%s)))"%condition
        answer = MC.check_primes(primes, update, init, spec)
        print init, spec, "is", answer

        init = "INIT Proliferation"
        condition = "STEADYSTATE | (!Proliferation & DNAdamage)"
        spec = "CTLSPEC AG(EF(AG(%s)))"%condition
        answer = MC.check_primes(primes, update, init, spec)
        print init, spec, "is", answer

        init = "INIT Proliferation"
        spec = "CTLSPEC EX(Proliferation)"
        answer, counterex = MC.check_primes(primes, update, init, spec, False)
        print init, spec, "is", answer
        print counterex
        for x in counterex:
            print STGs.state2str(x)

        for x in STGs.successors_asynchronous(primes, "101"):
            print x
                
    if 0 or RUN_ALL:
        bnet = ["x0,   !x0&x1 | x2",
                "x1,   !x0 | x1 | x2",
                "x2,   x0&!x1 | x2"]
        bnet = "\n".join(bnet)
        primes = FEX.bnet2primes(bnet)

        stg = STGs.primes2stg(primes, "asynchronous")
        attractor1 = (["010", "110"],{"label":"Attractor1"})
        attractor2 = (["111"],{"label":"Attractor2"})
        for x in stg.nodes():
            if x[1]=="0":
                stg.node[x]["style"] = "filled"
                stg.node[x]["fillcolor"] = "gray"

        stg.graph["label"] = "Example 22: Existential queries"
        STGs.stg2image(stg, "source/figure22.pdf")
        
        init = "INIT !x1"
        specQ1 = "CTLSPEC  EF(AG(x0_STEADY))"
        specQ2 = "CTLSPEC !EF(AG(x0_STEADY))"
        update = "asynchronous"
        Q1 = MC.check_primes(primes, update, init, specQ1)
        print Q1
        Q2 = not MC.check_primes(primes, update, init, specQ2)
        print Q2

        notQ2, counterex = MC.check_primes(primes, update, init, specQ2, False)
        state = counterex[0]
        print STGs.state2str(state)

        print counterex
        
    if 0 or RUN_ALL:
        
        bnet = ["x, !x | y | z",
                "y, !x&z | y&!z",
                "z, x&y | z"]
        bnet = "\n".join(bnet)
        primes = FEX.bnet2primes(bnet)
        tspaces = TS.trap_spaces(primes, "all")
        for x in tspaces:
            print STGs.subspace2str(primes, x)

        print ", ".join(STGs.subspace2str(primes, x) for x in tspaces)

        stg = STGs.primes2stg(primes, "asynchronous")
        STGs.add_style_subspaces(primes, stg, tspaces)

        stg.graph["label"] = "Example 23: All trap spaces"
        STGs.stg2image(stg, "source/figure23.pdf")

        
        mintspaces = TS.trap_spaces(primes, "min")
        print "mintspaces", ", ".join(STGs.subspace2str(primes, x) for x in mintspaces)
        for x in mintspaces:
            sub = (x,{"fillcolor":"salmon"})
            STGs.add_style_subspaces(primes, stg, [sub])
        maxtspaces = TS.trap_spaces(primes, "max")
        print "maxtspaces", ", ".join(STGs.subspace2str(primes, x) for x in maxtspaces)
        for x in maxtspaces:
            if x in mintspaces:
                sub = (x,{"fillcolor":"lightyellow"})
                STGs.add_style_subspaces(primes, stg, [sub])
            else:
                sub = (x,{"fillcolor":"lightblue"})
                STGs.add_style_subspaces(primes, stg, [sub])
        stg.graph["label"] = "Example 24: Minimal and maximal trap spaces"

        STGs.stg2image(stg, "source/figure24.pdf")


    if 1 or RUN_ALL:
        bnet = ["v1, !v1 | v3",
                "v2, !v1 | v2&!v3",
                "v3, !v2"]
        bnet = "\n".join(bnet)
        primes = FEX.bnet2primes(bnet)
        stg = STGs.primes2stg(primes, "asynchronous")
        STGs.add_style_sccs(stg)
        attractors = AD.compute_attractors_tarjan(primes, stg)
        for A in attractors:
            print [STGs.state2str(x) for x in A]
        
        stg.graph["label"] = "Example 25: A network with a cyclic attractor and a steady state."
        STGs.stg2image(stg, "source/figure25.pdf")

        state = AD.find_attractor_by_randomwalk_and_ctl(primes, "asynchronous")
        print STGs.state2str(state)

        update = "asynchronous"
        mintspaces = TS.trap_spaces(primes, "min")
        for x in mintspaces:
            answer_univocal, _, _ = AD.univocal( primes, update, x )
            answer_faithful, _    = AD.faithful( primes, update, x )
            print "min trap space:", STGs.subspace2str(primes, x)
            print "  is univocal:", answer_univocal
            print "  is faithful:", answer_faithful

        answer_complete, _ = AD.completeness_naive( primes, update, mintspaces )
        print "min trap spaces are complete:", answer_complete
        
        
    if False:
        
        bnet = ["v1, !v1&!v2&v3 | !v1&v2&!v3 | v1&!v2&!v3 | v1&v2&v3",
               "v2, !v1&!v2&!v3 | !v1&v2&v3 | v1&!v2&v3 | v1&v2&!v3",
               "v3, !v1&!v2&v3 | !v1&v2&!v3 | v1&!v2&!v3 | v1&v2&v3"]
        bnet = "\n".join(bnet)
        primes = FEX.bnet2primes(bnet)
        mintspaces = TS.trap_spaces(primes, "min")
        stg = STGs.primes2stg(primes, "asynchronous")
        mintspaces = TS.trap_spaces(primes, "min")
        print [STGs.subspace2str(primes, x) for x in mintspaces]
        
        STGs.add_style_sccs(stg)
        STGs.add_style_subspaces(primes, stg, mintspaces)
        
        stg.graph["label"] = "Example xx: An STG whose minimal trap space '---' is not complete"
        STGs.stg2image(stg, "source/figurexx.pdf")        

        
        
        
        
if __name__=="__main__":
    run()
    
    
   
