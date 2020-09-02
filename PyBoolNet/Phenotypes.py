
# -*- coding: utf-8 -*-


import sys
sys.path.insert(0,"/home/hannes/github/PyBoolNet")

import itertools
import networkx
import networkx.readwrite.json_graph
import PyBoolNet



def compute_json(AttrJson, Markers, FnameJson=None, Silent=False):
    """
    todo: finish code
    todo: add unit tests

    Computes the phenotypes object for given *Markers*.

    structure:
        primes: dict
        update: str
        markers: tuple
        phenotypes: (tuple)
            name: str
            pattern: str
            activated_markers: list of markers
            inhibited_markers: list of markers
            stateformula: disjunction over all state props

            states: (tuple)
                str: state string
                dict: state dict
                prop: state proposition
                is_steady: bool
                is_cyclic: bool

                mintrapspace:
                    str: subspace string
                    dict: subspace dict
                    prop: subspace proposition


    **arguments**:
        * *AttrJson* (dict): json attractor data, see :ref:`attractors_compute_json`
        * *Markers* (list): list of names
        * *Silent* (bool): print infos to screen
        * *FnameJson* (str): save phenotypes as json

    **returns**::
        * *Phenotypes* (dict): the phenotypes data

    **example**::

        >>> markers = ["raf", "mek"]
        >>> compute_json(primes, markers)
    """

    assert(AttrJson["is_complete"]=="yes")
    assert(all(x["mintrapspace"]["is_univocal"] for x in AttrJson["attractors"]))
    assert(all(x["mintrapspace"]["is_faithful"] for x in AttrJson["attractors"]))

    NAMES = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"


    primes = PyBoolNet.PrimeImplicants.copy(AttrJson["primes"])

    ignored = [x for x in Markers if x not in primes]
    Markers = [x for x in Markers if x in primes]

    if not Silent:
        print("compute_json(..)")
        if ignored: print(" ignored markers (not in primes): {x}".format(x=", ".join(ignored)))

    phenos = {}
    phenos["primes"] = primes
    phenos["update"] = AttrJson["update"]
    phenos["markers"] = list(Markers)
    phenos["phenotypes"] = []

    seen_patterns = []

    i = 0
    for attr in AttrJson["attractors"]:

        # the phenotype pattern is fully determined by the minimal trap space of the attractor
        pattern = "".join(str(attr["mintrapspace"]["dict"][x]) if x in attr["mintrapspace"]["dict"] else "-" for x in Markers)

        state = {}
        state["str"] = str(attr["state"]["str"])
        state["dict"] = dict(attr["state"]["dict"])
        state["prop"] = str(attr["state"]["prop"])
        state["is_steady"] = bool(attr["is_steady"])
        state["is_cyclic"] = bool(attr["is_cyclic"])
        state["mintrapspace"] = {}
        state["mintrapspace"]["str"] = str(attr["mintrapspace"]["str"])
        state["mintrapspace"]["dict"] = dict(attr["mintrapspace"]["dict"])
        state["mintrapspace"]["prop"] = str(attr["mintrapspace"]["prop"])


        # modify existing phenotype
        if pattern in seen_patterns:

            for pheno in phenos["phenotypes"]:
                if pheno["pattern"] == pattern:
                    pheno["states"].append(state)
                    break

        # create new phenotype
        else:
            seen_patterns.append(pattern)

            pheno = {}
            if i<=26:
                pheno["name"] = "Pheno %s"%"ABCDEFGHIJKLMNOPQRSTUVWXYZ"[i]
            else:
                pheno["name"] = "Pheno %i"%i
            i+=1

            pheno["pattern"] = pattern
            pheno["activated_markers"] = sorted(x for x in Markers if (x,1) in attr["mintrapspace"]["dict"].items())
            pheno["inhibited_markers"] = sorted(x for x in Markers if (x,0) in attr["mintrapspace"]["dict"].items())
            pheno["oscillating_markers"] = sorted(x for x in Markers if x not in attr["mintrapspace"]["dict"])
            pheno["states"] = [state]

            phenos["phenotypes"].append(pheno)



    # create stateformulas
    for pheno in phenos["phenotypes"]:
        pheno["states"] = tuple(sorted(pheno["states"], key=lambda x: x["mintrapspace"]["str"]))
        pheno["stateformula"] = "("+ " | ".join(x["prop"] for x in pheno["states"]) +")"

    if FnameJson:
        save_json(phenos, FnameJson)

    return phenos


def save_json(PhenosObj, Fname, Silent=False):
    """
    todo: finish code
    todo: add unit tests, add to sphinx

    saves the phenotypes object as a JSON file.

    **arguments**:
      * *PhenoJson*: phenotypes data, see todo: add :ref:`xxx`
      * *Fname* (str): file name

    **returns**:
      * *None*

    **example**::

        >>> compute_json(attrs, markers)
        >>> save_phenotype(phenos, "pheno.json")
        created pheno.json
    """

    PyBoolNet.Utility.Misc.save_json_data(PhenosObj, Fname, Silent=Silent)


def open_json(Fname):
    """
    todo: finish code
    todo: add unit tests, add to sphinx

    opens the phenotypes object, see todo: add :ref:`xxx`

    **arguments**:
      * *Fname* (str): file name

    **returns**:
      * *PhenoJson*: phenotypes data, see todo: add :ref:`xxx`

    **example**::

      >>> phenos = open_json("pheno.json")
    """

    phenos = PyBoolNet.Utility.Misc.open_json_data(Fname)

    return phenos


def compute_diagram(PhenosObj, FnameJson=None, FnameImage=None, Silent=False):
    """
    todo: finish code
    todo: add unit tests

    computes the phenotype diagram from the phenotypes object obtained from :ref:`phenotypes_compute_json`.
    save the diagram as json data with *FnameJson*. useful for e.g. manually renaming nodes.

    **arguments**:
        * *PhenosObj* (dict): result of compute_json(..)
        * *FnameJson* (str): save diagram as json
        * *FnameImage* (str): generate image for diagram
        * *Silent* (bool): print infos to screen

    **returns**::
        * *Diagram* (networkx.DiGraph): the phenotype diagram

    **example**::

        >>> phenos = compute_json(attrobj, markers)
        >>> compute_diagram(phenos, FnameImage="phenos.pdf")
        created phenos.pdf
    """

    Primes = PhenosObj["primes"]
    Update = PhenosObj["update"]

    assert(Update in PyBoolNet.StateTransitionGraphs.UPDATE_STRATEGIES)
    assert(Primes)

    if not Silent:
        print("Phenotypes.compute_diagram(..)")

    diagram = networkx.DiGraph()
    for key in PhenosObj:
        diagram.graph[key] = PyBoolNet.Utility.Misc.copy_json_data(PhenosObj[key])

    # nodes
    node_id = 0
    Flags = [[0,1]]*len(PhenosObj["phenotypes"])
    for i,flags in enumerate(itertools.product(*Flags)):

        stateformulas, names = [], []
        for j, flag in enumerate(flags):
            if flag:
                stateformulas.append(PhenosObj["phenotypes"][j]["stateformula"])
                names.append(PhenosObj["phenotypes"][j]["name"])

        stateformulas.sort()
        names = tuple(sorted(names))


        if not stateformulas:
            unreach = " & ".join("!EF({x})".format(x=x["stateformula"]) for x in PhenosObj["phenotypes"])
            spec = "CTLSPEC {x}".format(x=unreach)

        else:
            reach = ["EF({x})".format(x=x) for x in stateformulas]
            reach_all  = " & ".join(reach)
            reach_some = " | ".join(reach)
            spec = "CTLSPEC {x} & AG({y})".format(x=reach_all,y=reach_some)

        init = "INIT TRUE"
        answer, accepting = PyBoolNet.ModelChecking.check_primes_with_acceptingstates(Primes, Update, init, spec)

        data = {"names":    names,
                "init":        init,
                "spec":        spec,
                "initaccepting_size":    accepting["INITACCEPTING_SIZE"],
                "initaccepting":          accepting["INITACCEPTING"]}

        if data["initaccepting_size"]>0:
            if not Silent:
                print(" [{x}] = {y}".format(x=", ".join(names), y=data["initaccepting_size"]))

            diagram.add_node(node_id)
            for key, value in data.items():
                diagram.nodes[node_id][key] = value
            node_id+= 1

    # edges
    for source in diagram:
        for target in diagram:
            if source==target: continue

            sourceset = set(diagram.nodes[source]["names"])
            targetset = set(diagram.nodes[target]["names"])

            if targetset.issubset(sourceset):
                init = "INIT {x}".format(x=diagram.nodes[source]["initaccepting"])
                spec = "CTLSPEC EX({x})".format(x=diagram.nodes[target]["initaccepting"])

                answer, accepting = PyBoolNet.ModelChecking.check_primes_with_acceptingstates(Primes, Update, init, spec)

                if accepting["INITACCEPTING_SIZE"]>0:

                    data = {"init": init,
                            "spec":    spec,
                            "initaccepting_size":    accepting["INITACCEPTING_SIZE"],
                            "initaccepting":        accepting["INITACCEPTING"]}

                    diagram.add_edge(source, target)
                    for key, value in data.items():
                        diagram.edges[source, target][key] = value

                    if not Silent:
                        print(" [{x}] --{s}--> [{y}]".format(
                            x=", ".join(diagram.nodes[source]["names"]),
                            s=data["initaccepting_size"],
                            y=", ".join(diagram.nodes[target]["names"])))


    if FnameImage:
        diagram2image(diagram, FnameImage)

    if FnameJson:
        save_diagram(diagram, FnameJson)

    return diagram


def save_diagram(Diagram, Fname):
    """
    todo: finish code
    todo: add unit tests

    description

      **arguments**:
        * *Primes*: prime implicants
        * *arg* (type): description

      **returns**:
        * *arg* (type): description

      **example**::

        >>> save_diagram(..)
        result
    """

    data = networkx.readwrite.json_graph.adjacency_data(Diagram)

    PyBoolNet.Utility.Misc.save_json_data(data, Fname)


def open_diagram(Fname):
    """
    todo: finish code
    todo: add unit tests

    description

    **arguments**:
        * *arg* (type): description

    **returns**:
        * *arg* (type): description

    **example**::

        >>> open_diagram(..)
        result
    """

    data = PyBoolNet.Utility.Misc.open_json_data(Fname)

    diagram = networkx.readwrite.json_graph.adjacency_graph(data)

    for x in diagram:
        diagram.nodes[x]["names"] = tuple(diagram.nodes[x]["names"]) # lost in json conversion

    return diagram


def diagram2image(Diagram, FnameImage=None):
    """
    creates an image of the abstract commitment diagram.

    **arguments**:
        * *Diagram* (networkx.DiGraph): a phenotype diagram
        * *FnameImage* (str): name of the diagram image

    **returns**::
        * *StyledDiagram* (networkx.DiGraph): the styled abstract commitment diagram

    **example**::

        >>> diagram2image(primes, diagram, "diagram.pdf")
    """

    assert(type(Diagram)==type(networkx.DiGraph()))

    Primes = Diagram.graph["primes"]

    size_total = PyBoolNet.StateTransitionGraphs.size_state_space(Primes)

    image = networkx.DiGraph()
    image.graph["node"]  = {"shape":"rect","style":"filled","color":"none","fillcolor":"lightgray"}
    image.graph["edge"]  = {}



    labels = {}
    # "labels" is used for node labels
    # keys:
    # head = reachable attractors
    # size = number of states


    for node, data in Diagram.nodes(data=True):

        labels[node] = {}
        image.add_node(node)

        head = PyBoolNet.Utility.Misc.divide_list_into_similar_length_lists(data["names"])
        head = [",".join(x) for x in head]
        labels[node]["head"] = "<br/>".join(head)

        if "fillcolor" in data:
            image.nodes[node]["fillcolor"] = data["fillcolor"]
        elif len(data["names"])==1:
            image.nodes[node]["fillcolor"] = "cornflowerblue"

        if "color" in data:
            image.nodes[node]["color"] = data["color"]

        if "penwidth" in data:
            image.nodes[node]["penwidth"] = data["penwidth"]

    for source, target, data in Diagram.edges(data=True):
        image.add_edge(source, target)

    for x in Diagram.nodes():
        perc = 100.* Diagram.nodes[x]["initaccepting_size"] / size_total
        labels[x]["initaccepting_size"] = "states: {x}%".format(x=PyBoolNet.Utility.Misc.perc2str(perc))

    for x in Diagram.nodes():
        image.nodes[x]['label'] = "<{x}>".format(x="<br/>".join(labels[x].values()))

    ranks = {}
    for node, data in Diagram.nodes(data=True):

        x = len(data["names"])
        if not x in ranks:
            ranks[x]=[]
        ranks[x].append(node)

    ranks=list(ranks.items())
    ranks.sort(key=lambda x: x[0])

    for _,names in ranks:
        names = ['"{x}"'.format(x=x) for x in names]
        names = "; ".join(names)
        image.graph["{rank = same; %s;}"%names]=""

    if FnameImage:
        PyBoolNet.Utility.DiGraphs.digraph2image(image, FnameImage, LayoutEngine="dot")

    return image


def create_piechart(Diagram, FnameImage, Title=None, ColorMap=None, Silent=False):
    """
    creates the abstract commitment pie.

    **arguments**:
        * *Diagram* (networkx.DiGraph): precomputed commitment diagram
        * *FnameImage* (str): name of the output image
        * *Title* (str): optional title of plot
        * *ColorMap* (dict): assignment of diagram nodes to colors for custom colors
        * *Silent* (bool): print infos to screen

    **returns**::
        * *None*

    **example**::

        >>> attrs = Attractors.compute_json(primes, update)
        >>> phenos = Phenotypes.compute_json(attrs, markers)
        >>> diagram = Phenotypes.create_diagram(phenos)
        >>> Phenotypes.create_piechart(diagram, "piechart.pdf")
    """

    debug = True

    import matplotlib.pyplot
    matplotlib.rcParams['hatch.linewidth'] = 4.0     # special hatching for paper
    matplotlib.rcParams['hatch.color'] = "#ff7c00"    # special hatching for paper

    indeces = sorted(Diagram, key=lambda x: Diagram.nodes[x]["initaccepting_size"])

    labels = [", ".join(Diagram.nodes[x]["names"]) for x in indeces]
    sizes  = [Diagram.nodes[x]["initaccepting_size"] for x in indeces]

    total = sum(sizes)
    is_small_network = total <= 1024

    figure = matplotlib.pyplot.figure()
    if ColorMap:
        colors = [ColorMap[x] for x in indeces]
    else:
        colors = [matplotlib.pyplot.cm.rainbow(1.*x/(4+1)) for x in range(len(Diagram)+2)][1:-1]
        colors = [matplotlib.pyplot.cm.rainbow(1.*x/(len(Diagram)+1)) for x in range(len(Diagram)+2)][1:-1]

    for i,x in enumerate(indeces):
        if "fillcolor" in Diagram.nodes[x]:
            colors[i] = Diagram.nodes[x]["fillcolor"]

    autopct = (lambda p: '{:.0f}'.format(p * total / 100)) if is_small_network else '%.1f%%'
    stuff = matplotlib.pyplot.pie(sizes, explode=None, labels=labels, colors=colors, autopct=autopct, shadow=True, startangle=45)
    patches = stuff[0] # required because matplotlib.pyplot.pie returns variable number of things depending on autopct!!

    ### delete me
    patches, texts, autotexts = stuff
    [ _.set_fontsize(15) for _ in texts ]
    [ _.set_fontsize(15) for _ in autotexts ]


    for i, patch in enumerate(patches):
        if "hatch" in Diagram.nodes[indeces[i]]:
            patch.set_hatch(Diagram.nodes[indeces[i]]["hatch"]) #hatching = "//","||",'\\\\',"--",'+'
            #patch.set_linewidth(3.)
            #patch.set_linestyle("--")
            #patch.set_fc("blue")
            #patch.set_ec("black")
            #print(patch.get_lw())
        elif "fillcolor" in Diagram.nodes[indeces[i]]:
            #if Diagram.nodes[indeces[i]]["fillcolor"]=="white":
            patch.set_ec("black")

    matplotlib.pyplot.axis('equal')

    if Title==None:
        Title = 'Phenotype Commitment Sets'
    matplotlib.pyplot.title(Title, y=1.08)

    matplotlib.pyplot.tight_layout()

    figure.savefig(FnameImage, bbox_inches='tight')
    if not Silent: print("created %s"%FnameImage)
    matplotlib.pyplot.close(figure)




if __name__=="__main__":

    diagram = networkx.DiGraph()
    diagram.add_node(0, initaccepting_size=2900, names=["GA"], fillcolor="#ff7c00")
    diagram.add_node(1, initaccepting_size=5000, names=["A"], fillcolor="#919191")
    diagram.add_node(2, initaccepting_size=600, names=["OscP/GA"], fillcolor="#c8fbc0", hatch="//", penwidth=3, color="#ff7c00")
    diagram.add_node(3, initaccepting_size=1500, names=["P"], fillcolor="#c8fbc0")

    create_piechart(diagram, FnameImage="remy_pie.svg", Title="", ColorMap=None, Silent=False)
























# end of file
