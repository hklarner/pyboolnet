


Quick Manual
============
Boolean Networks
----------------
Create a Boolean network from a text based definition file in *boolnet* format.
Use ``&``, ``|`` and ``!`` for conjunction, disjunction and negation and separate the variable name from its activation expression by a comma.
Values for constant activation are ``0`` and ``1``.
Example of BNET file::

     v1,    !v1
    v2,    1
    v3,    v2 & (!v1 | v3)

Read a BNET file or its string contents with the function :ref:`bnet2primes` of the module :ref:`FileExchange`.
It returns the prime implicant representation of a network::

    >>> primes = PyBoolNet.FileExchange.bnet2primes(bnet)

Use the module :ref:`PrimeImplicants` to inspect and modify a network.
For example, find all constant variables using :ref:`find_constants`::

    >>> const = PrimeImplicants.find_constants(primes)
    >>> print(const)
    {'v2': 1}

Or create new variables using :ref:`create_variables`::

    >>> PyBoolNet.PrimeImplicants.create_variables(primes, {"v4": "v4 | v2"})

You may also use python functions to define the update of a variable::

    >>> PyBoolNet.PrimeImplicants.create_variables(primes, {"v5": lambda v1,v2,v3: sum(v1,v2,v3)==1})

Convert to primes back to the BNET format using :ref:`primes2bnet`::

    >>> print(PyBoolNet.FileExchange.primes2bnet(primes))
    v2,  1

    v1,  !v1
    v3,  v2&v3 | v2&!v1
    v4,  v4 | v2

    v5,  !v2&v3&!v1 | v2&!v3&!v1 | !v2&!v3&v1


PyBoolNet has its own network repository.
To browse it online, visit

* github.com/hklarner/pyboolnet/tree/master/pyboolnet/Repository

To access a network from the repository use the function :ref:`get_primes` of the module :ref:`Repository`::

    >>> primes = get_primes("remy_tumorigenesis")
    >>> print(PyBoolNet.FileExchange.primes2bnet(primes))
    DNA_damage,         DNA_damage
    EGFR_stimulus,      EGFR_stimulus
    FGFR3_stimulus,     FGFR3_stimulus
    ...
    Growth_arrest,      p21CIP | RBL2 | RB1
    Proliferation,      CyclinE1 | CyclinA


Read the references for :ref:`FileExchange` and :ref:`PrimeImplicants` for more on this topic.
For a tutorial script on this topic see `01_boolean_networks.py` in the tutorials folder at

* github.com/hklarner/pyboolnet/tree/master/Tutorials


Interaction Graphs
------------------
The basic function for drawing interaction graphs is :ref:`igs_create_image` of the module :ref:`InteractionGraphs`::

    >>> primes = get_primes("remy_tumorigenesis")
    >>> PyBoolNet.InteractionGraphs.create_image(primes, "igraph.pdf")
    created igraph.pdf

The look of the interaction graph may be modified by one of the predefined styles::

    >>> PyBoolNet.InteractionGraphs.create_image(primes, "igraph2.pdf", Styles=["sccs", "anonymous"])
    created igraph2.pdf

The next level of customizing the look of an interaction graph is to style the interaction graph with graphviz properties.
Examples of node properties are *shape*, *label*, *style*, *width*, *color* and *fillcolor*.
Examples of edge properties are *arrowhead*, *label* and *color*.
To obtain the interaction graph use :ref:`primes2igraph` of the module :ref:`InteractionGraphs`.
To draw a styled igraph use :ref:`igraph2image`::

    >>> for x in igraph.nodes():
    ...        if "GF" in x:
    ...         igraph.node[x]["shape"] = "square"
    ...            igraph.node[x]["fillcolor"] = "lightblue"

    >>> PyBoolNet.InteractionGraphs.igraph2image(igraph, "igraph3.pdf")
    created igraph3.pdf

You may also compute the local interaction graph of a given state.
To generate a random state, use :ref:`random_state` of the module :ref:`StateTransitionGraphs`.
To compute the local interaction graph use :ref:`local_igraph_of_state` of  :ref:`InteractionGraphs`::

    >>> state = PyBoolNet.StateTransitionGraphs.random_state(primes)
    >>> local_igraph = PyBoolNet.InteractionGraphs.local_igraph_of_state(state)
    >>> PyBoolNet.InteractionGraphs.add_style_interactionsigns(local_igraph)
    >>> PyBoolNet.InteractionGraphs.igraph2image(local_igraph, "local_igraph.pdf")
    created local_igraph.pdf



Read the references for :ref:`InteractionGraphs` for more on this topic.
For a tutorial script on this topic see `02_interaction_graphs.py` in the tutorials folder at

* github.com/hklarner/pyboolnet/tree/master/Tutorials




State  Transition Graphs
------------------------
Drawing and styling state transition graphs is analogous to interaction graphs::

    >>> primes = get_primes("xiao_wnt5a")
    >>> PyBoolNet.StateTransitionGraphs.create_image(primes, "asynchronous", "stg.pdf")
    created stg.pdf

The update may be either *asynchronous* or *synchronous*.
You may specify initial states as a single state or several states, a subspace or a python indicator function::

    >>> PyBoolNet.StateTransitionGraphs.create_image(primes, "asynchronous", "stg2.pdf", InitialStates={"x6":0, "x7":0}, Styles=["anonymous", "tendencies", "mintrapspaces"])
    created stg2.pdf

To draw paths use :ref:`add_style_path`.
A random walk ma be computed using :ref:`random_walk`::

    >>> path = PyBoolNet.StateTransitionGraphs.random_walk(primes, "asynchronous", InitialState="11---00", Length=4)
    >>> stg = PyBoolNet.StateTransitionGraphs.primes2stg(primes, "asynchronous")
    >>> PyBoolNet.StateTransitionGraphs.add_style_path(stg, path, Color="red")
    >>> PyBoolNet.StateTransitionGraphs.stg2image(stg, "stg3.pdf")
    created stg3.pdf


The module :ref:`StateTransitionGraphs` contains also functions to compute factor graphs in which the state space is partitioned into classes.
The classical example is the SCC graph::

    >>> primes = get_primes("randomnet_n7k3")
    >>> stg = PyBoolNet.StateTransitionGraphs.primes2stg(primes, "asynchronous")
    >>> scc_graph = PyBoolNet.StateTransitionGraphs.stg2sccgraph(stg)
    >>> PyBoolNet.StateTransitionGraphs.sccgraph2image(scc_graph, "scc_graph.pdf")

The condensation graph is like the scc graph but transient states are removed::

    >>> cograph = PyBoolNet.StateTransitionGraphs.stg2condensationgraph(stg)
    >>> PyBoolNet.StateTransitionGraphs.sccgraph2image(cograph, "cograph.pdf")

The hierarchical transition graph is even further compressed by considering the attractors of the stg::

    >>> htg = PyBoolNet.StateTransitionGraphs.stg2htg(stg)
    >>> PyBoolNet.StateTransitionGraphs.htg2image(htg, "htg.pdf")


Reachability questions of the form "Is there a path from an initial state X to a goal state Y?" may be answered by a best first search algorithm with the function :ref:`best_first_reachability`.
The search is guided by reducing the hamming distance to the goal space::

    >>> X = "0--1-1-"
    >>> Y = "1--0---"
    >>> path = PyBoolNet.StateTransitionGraphs.best_first_reachability(primes, InitialSpace=X, GoalSpace=Y)
    >>> if path:
    ...        for x in path:
    ...            print(x)
    ... else:
    ...        print("no path found")

    0011011
    ...
    1000001

Finally, you may compute the integer-valued energy of a state, based on "frozen variables" with the function :ref:`energy`::

    >>> x = "0001011"
    >>> e = PyBoolNet.StateTransitionGraphs.energy(primes, x)
    >>> print(e)


Read the references for :ref:`StateTransitionGraphs` for more on this topic.
For a tutorial script on this topic see `03_state_transition_graphs.py` in the tutorials folder at

* github.com/hklarner/pyboolnet/tree/master/Tutorials



Model Checking
--------------

The basic function for LTL and CTL model checking is :ref:`check_primes` of the module :ref:`ModelChecking`.
The initial states and the specification must be given in NuSMV syntax.
For LTL specs use the keyword `LTLSPEC`, for CTL specs use `CTLSPEC` and for initial states use `INIT`::

    >>> primes = get_primes("remy_tumorigenesis")
    >>> init = "INIT TRUE"
    >>> spec = "CTLSPEC DNA_damage -> AG(EF(Apoptosis_medium))"
    >>> answer = PyBoolNet.ModelChecking.check_primes(primes, "asynchronous", init, spec)

For model checking with accepting states use :ref:`check_primes_with_acceptingstates`.
The function returns a dictionary of further information regarding the initial and accepting states::

    >>> answer, accepting = PyBoolNet.ModelChecking.check_primes_with_acceptingstates(primes, "asynchronous", init, spec)
    >>> for key, value in accepting.items():
    ...        print("{} = {}".format(key, value))

    INIT_SIZE = 8153726976
    INITACCEPTING_SIZE = 8153726976
    INIT = E2F1_medium & (ATM_medium & (CHEK1_2_medium ... | !(Apoptosis_high)))))))))
    ACCEPTING = TRUE
    ACCEPTING_SIZE = 34359738368
    INITACCEPTING = E2F1_medium & (ATM_medium & (CHEK1_2_medium & (E2F3_medium & (Apoptosis_medium | ... !(Apoptosis_high)))))))))


Finally, the function :ref:`check_primes_with_counterexample` returns a CTL or LTL counter example, if the query is false::

    >>> spec = "CTLSPEC DNA_damage -> AG(EF(Proliferation))"
    >>> answer, counterex = PyBoolNet.ModelChecking.check_primes_with_counterexample(primes, "asynchronous", init, spec)
    >>> print(answer)
    >>> if counterex:
    ...     for state in counterex:
    ...         print(state)
    {'RB1': 0, 'GRB2': 0, 'RAS': 0, 'p16INK4a': 0, 'Proliferation': 0, ..., 'DNA_damage': 1, 'FGFR3': 0, 'Apoptosis_high': 0, 'CyclinD1': 0, 'p21CIP': 0}



Read the references for :ref:`StateTransitionGraphs` for more on this topic.
For a tutorial script on this topic see `04_model_checking.py` in the tutorials folder at

* github.com/hklarner/pyboolnet/tree/master/Tutorials


Attractors
----------

The two basic functions for finding attractors are Tarjan's algorithm and the random walk algorithm.
Tarjan's algorithm is exact but requires the full STG as input and is therefore limited to smaller networks::

    >>> primes = get_primes("tournier_apoptosis")
    >>> stg = PyBoolNet.StateTransitionGraphs.primes2stg(primes, "asynchronous")
    >>> steady, cyclic = PyBoolNet.Attractors.compute_attractors_tarjan(stg)
    >>> steady
    ['000101010000', '011000010000']
    >>> cyclic
    [{'011000010011', '111010010111', ..., '111010001111', '011010000011', '011010001001'}]

The random walk algorithm works for larger networks but it finds only a single attractor::

    >>> state = PyBoolNet.Attractors.find_attractor_state_by_randomwalk_and_ctl(primes, "asynchronous")
    >>> print(state)


To compute all attractors with an advanced model checking algorithm use the function :ref:`attractors_compute_json`::

    >>> attrs = PyBoolNet.Attractors.compute_json(primes, "asynchronous", FnameJson="attrs.json")

Inspect the json structure with e.g. http://jsonviewer.stack.hu/.
Iterate of the attractors and print representative states::

    >>> attrs["is_complete"]
    yes
    >>> for x in attrs["attractors"]:
    ...        print(x["is_steady"])
    ...        print(x["state"]["str"])



Basins
------
To compute the weak, strong and cycle-free basins of a subspace use the functions :ref:`weak_basins`, :ref:`strong_basin` and :ref:`cyclefree_basin`::

    >>> primes = get_primes("tournier_apoptosis")
    >>> attrs = PyBoolNet.Attractors.compute_json(primes, "asynchronous")
    >>> state = attrs["attractors"][0]["state"]["str"]
    >>> weak = PyBoolNet.Basins.weak_basin(primes, "asynchronous", state)
    >>> for key, value in weak.items():
    ...        print("{} = {}".format(key, value))

    formula = !(TNF | !(NFkB | (NFkBnuc | ((IKKa | ((CARP | (IAP | !(C8a))) | !C3a)) | !IkB))))
    size = 2040
    perc = 49.8046875

    >>> strong = PyBoolNet.Basins.strong_basin(primes, "asynchronous", state)
    >>> for key, value in strong.items():
    ...        print("{} = {}".format(key, value))

    size = 704
    perc = 17.1875
    formula = !(TNF | (IKKa | (C3a | !(T2 & (CARP & (IAP | !(C8a)) | !CARP & (IAP)) | !T2 & (IAP | !(C8a))))))

    >>> cycfree = PyBoolNet.Basins.cyclefree_basin(primes, "asynchronous", state)
    >>> for key, value in cycfree.items():
    ...        print("{} = {}".format(key, value))

    formula = !(TNF | (IKKa | (C3a | !(T2 & (CARP & (IAP | !(C8a)) | !CARP & (IAP)) | !T2 & (IAP | !(C8a))))))
    size = 352
    perc = 8.59375


To plot the sizes of the basins as a bar plot or a pie chart use :ref:`compute_basins`.
It extends the attrs data obtained from :ref:`compute_json`.

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_basins_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_basins_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_basins_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_basins_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_basins_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_basins_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_basins_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_basins_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_basins_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_basins_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_basins_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_basins_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_basins_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_basins_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_basins_of_attraction_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_phenotypes_piechart(attrs, "basin_piechart.pdf")

    >>> PyBoolNet.Basins.compute_basins(attrs)
    >>> PyBoolNet.Basins.create_barplot(attrs, "basin_barplot.pdf")
    >>> PyBoolNet.Basins.create_piechart(attrs, "basin_piechart.pdf")


Commitment
----------

To compute the commitment diagram use the function :ref:`create_diagram` of the module :ref:`Commitment`.
It requires the attractors data as input::

    >>> primes = get_primes("tournier_apoptosis")
    >>> attrs = PyBoolNet.Attractors.compute_json(primes, "asynchronous")
    >>> diag = PyBoolNet.Commitment.compute_diagram(attrs)

Commitment diagrams may be visualized as graphs or piecharts::

    >>> PyBoolNet.Commitment.diagram2image(diag, "commitment_diag.pdf")
    >>> PyBoolNet.Commitment.create_piechart(diag, "commitment_pie.pdf")


Phenotypes
----------

To compute phenotypes you need the attractors data and define markers::

    >>> primes = get_primes("arellano_rootstem")
    >>> attrs = PyBoolNet.Attractors.compute_json(primes, "asynchronous")
    >>> markers = ["WOX", "MGP"]
    >>> phenos = PyBoolNet.Phenotypes.compute_json(attrs, markers)

Inspect the json structure with e.g. http://jsonviewer.stack.hu/.
Access the existing marker patterns via::

    >>> for pheno in phenos["phenotypes"]:
    ...     print(pheno["name"])
    ...     print(pheno["pattern"])

    Pheno A
    00
    Pheno B
    10
    Pheno C
    01

And draw the diagram with :ref:`phenotypes_compute_diagram`::

    >>> PyBoolNet.Phenotypes.compute_diagram(phenos, FnameImage="phenos_diagram.pdf")


Trap spaces
-----------

The main function for computing minimal and maximal trap spaces is :ref:`trap_spaces`::

    >>> primes = get_primes("remy_tumorigenesis")
    >>> mints = PyBoolNet.AspSolver.trap_spaces(primes, "min")
    >>> len(mints)
    25
    >>> maxts = PyBoolNet.AspSolver.trap_spaces(primes, "max")
    >>> len(maxts)
    8

As a special case use the ASP solver to compute all steady states::

    >>> steady = PyBoolNet.AspSolver.steady_states(primes)
    >>> len(steady)
    20










end of file.
