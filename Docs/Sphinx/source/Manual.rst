


Manual
======
Importing Boolean networks
--------------------------

prime implicants
****************
The prime implicants are a unique representation for Boolean networks that serves as a foundation for tasks
like computing the interaction graph or state transition graph and computing steady states or trap spaces.
See :ref:`Klarner2015(a) <klarner2015trap>` for the background.
The 1-implicants of a Boolean expression correspond to those clauses in propositional logic
that imply that the expression is true while 0-implicants are those clauses that imply that the expression is false.
Prime implicants are the shortest implicants, i.e.,
a clause is prime if removing any literal results in the negation of the original implication.

Consider the expression::

   v2 & (!v1 | v3)
   
where ``&``, ``|`` and ``!`` represent conjunction, disjunction and negation, respectively.
One of its 1-implicants is::

   v1 & v2 & v3
   
because::

   (v1 & v2 & v3) => (v2 & (!v1 | v3))
   
is valid.
But it is not prime since removing the literal *v1* is a shorter 1-implicant::

   (v2 & v3) => (v2 & (!v1 | v3))
   
is also valid. In Python we represent prime implicants as nested dictionaries and lists.
The prime implicants of a network with three components *v1*, *v2*, *v3* and three update functions *f1*, *f2*, *f3* that are defined by::

   f1 := v2 & (!v1 | v3)
   f2 := !v3
   f3 := v2 | v1

   
is represented by a dictionary, say *primes*, whose keys are the names of the components, here *"v1"*, *"v2"* and *"v3"*.
The values of each name are lists of length two that contain the 0 and 1 prime implicants.
To access the 1-prime implicants of *v1* use::

   >>> primes["v1"][1]
   [{'v2':1,'v1':0},{'v2':1,'v3':1}]
   
The returned list states that *f1* has two 1-prime implicants and each consists of two literals.
Clauses are therefore represented by dictionaries whose keys are names of components and whose values are either 0 or 1,
depending on whether the corresponding literal is negative or positive.

It can be difficult to enumerate all prime implicants of a network and |software| uses the program :ref:`BNetToPrime <installation_bnettoprime>` to do it.
As a user you define a network in terms of Boolean expressions, Python functions or you import it from other tools, like GINsim_.
The steps in each case are explained in the following sections.


.. _states_subspaces_paths:

states, subspaces and paths
***************************
Apart from primes, there are three more fundamental data structures: *states*, *subspaces* and *paths*.
A *subspace* is a Python dictionary whose items describe which components are fixed at which level, i.e., the keys are component names and the values are the corresponding activities.
A *state* is a special case of a subspace.
It contains *n* items where *n* is the number of components.
The number of components is usually accessible by::

   >>> n = len(primes)
   
A *path* is sequence of states represented by a Python iterable, usually a tuple or list.

A state and subspace of the example network above are::

   >>> state = {"v1":0,"v2":1,"v3":0}
   >>> subspace = {"v1":0}
   
.. Note:
   The empty dictionary ``{}`` is a valid subspace - it represents the full state space.


States and subspaces may also be defined using string representations, i.e., strings of 0s, 1s and dashes::

   >>> state = "010"
   >>> subspace = "0--"
   
String and dictionary representations may be converted into each other using the functions
:ref:`state2str`, :ref:`str2state` and :ref:`subspace2str`, :ref:`str2subspace`.

   
A path that consists of two states is for example::

   >>> x = {"v1":0,"v2":1,"v3":0}
   >>> y = {"v1":1,"v2":1,"v3":1}
   >>> path = [x,y]
   





.. _primes_from_bnet_files:

primes from BNet files
**********************
A *bnet* file contains a single line for every component.
Each line consists of the name of the variable that is being defined separated by a comma from the Boolean expression that defines its update function.
The network above in *bnet* format is::

   v1,   v2 & (!v1 | v3)
   v2,   !v3
   v3,   v2 | v1

We chose this syntax for its simplicity and to be compatible with BoolNet_, see :ref:`Müssel2010 <Müssel2010>`.
Save it in a text file called *example01.bnet*.
To generate its prime implicants use the function :ref:`bnet2primes` of the module :ref:`FileExchange`::

   >>> from PyBoolNet import FileExchange as FEX
   >>> primes = FEX.bnet2primes("example01.bnet")
   
Instead of a file name the functions also takes string contents of a *bnet* file::

   >>> primes = FEX.bnet2primes("v1,v2 \n v2,v1")
   
and a second argument can be used for saving the prime implicants as a *json* file::

   >>> primes = FEX.bnet2primes("example01.bnet", "example01.primes")
   
Saving prime implicants in a separate file is useful in case the network has many components with high in-degrees.
For such networks the computation of all primes might take a long time.
Previously saved primes can be read with :ref:`read_primes`::

   >>> primes = FEX.read_primes("example01.primes")
   
Previously generated primes can be saved as *json* files using :ref:`write_primes`::

   >>> FEX.write_primes(primes, "example01.primes")
   
You may also want to save primes as a *bnet* file.
To do so use :ref:`primes2bnet`::

   >>> FEX.primes2bnet(primes, "example01.bnet")
   
The module :ref:`FileExchange` can also export primes to *bns* and *genysis* files to use as inputs for the tools BNS_ of :ref:`Dubrova2011 <Dubrova2011>` and GenYsis_ of :ref:`Garg2008 <Garg2008>`, namely :ref:`primes2bns` and :ref:`primes2genysis`.

.. _primes_from_ginsim_files:

primes from GINsim files
************************

Open the *zginml* or *ginml* file with :ref:`GINsim <installation_ginsim>` and generate a *sbml-qual* file, for example *mapk.sbml*, by clicking::

   File > Export > SBML-qual > run
   
Generate a *bnet* file from *mapk.sbml* with :ref:`BoolNet <installation_boolnet>`::

   $ R
   > library(BoolNet)
   > net = loadSBML("mapk.sbml")
   > saveNetwork(net, "mapk.bnet")
   
.. note::

   In general, GINsim files define multi-valued networks. If you generate primes from a GINsim file be sure that the underlying network is Boolean.

.. _primes_from_python_functions:

primes from Python functions
****************************

An alternative to defining Boolean networks by Boolean expressions and *bnet* files is to create a Python function for every component.
This allows the use of arithmetic and arbitrary Python code to express the conditions under which components are activated or inhibited.
Suppose, for example, that a gene *v1* is regulated by four transcription factors *v2,...,v5* and that *v1* is activated iff two or more of them are present.
It is tedious to express such a condition in terms of a Boolean expression but easy using the Python function *sum*::

   >>> f1 = lambda v2,v3,v4,v5: sum([v2,v3,v4,v5])>=2

Note that due to Python's typecasting we may use *True* and *False* synonymously for 1 and 0::

   >>> f1(False, True, True, False)
   True
   >>> f1(0,1,1,0)
   True

The lambda construct is convenient for single line definitions but more complex functions can be defined using the standard *def* block::

   >>> def f2(v1,v2,v3):
   ...     if f1(v2,v3,0,0):
   ...         return 0
   ...     else:
   ...         return sum([v1,v2,v3]) % 2
         
The definition of *f2* involves the variables *v1,v2,v3* and *f1*: it returns 0 if *f1(v2,v3,0,0)* is 1 and otherwise *v1+v2+v3 mod 2*.
Note that *f2* returns 1 and 0 instead of *True* and *False*.
Function can also you Python logic operators::

   >>> f3 = lambda v4,v5: not (v4 or not f2(v4,v4,v5))

Constant functions always return 1 or 0 and inputs are only regulated by themselves::

   >>> f4 = lambda: 1
   >>> f5 = lambda v5: v5
   
To generate a primes object from these functions use :ref:`functions2primes` of the module :ref:`QuineMcCluskey`.
Its argument is a dictionary of component names and Boolean functions::

   >>> from PyBoolNet import QuineMcCluskey as QMC
   >>> funcs = {"v1":f1, "v2":f2, "v3":f3, "v4":f4, "v5":f5}
   >>> primes = QMC.functions2primes(funcs)

In case you want to see a minimal *disjunctive normal form* (DNF) of the functions you defined, use :ref:`functions2mindnf`::

   >>> dnf = QMC.functions2mindnf(funcs)
   >>> dnf["v1"]
   ((v4 & v3) | (v5 & v3) | (v5 & v4) | (v5 & v2) | (v4 & v2) | (v3 & v2))


.. _drawing_interaction_graphs:

Drawing the Interaction Graph
-----------------------------

Prime implicants can be used to derive the *interaction graph* (IG) of a network.
The algorithm is based on the fact that a variable *vi* interacts with a variable *vj* if and only if *vj*
has a prime implicant whose conjunction involves a *vi* literal.
The interaction is positive if and only if there is a 1-prime with a positive literal *vi* or a 0-prime with a negative literal *not vi*.
Similarly, the interaction is negative if and only if there is a 1-prime with a negative literal *not vi* or a 0-prime with a positive literal *vi*.
To compute the interaction graph use the function :ref:`primes2igraph` of the module :ref:`InteractionGraphs`.
It returns a directed graph in the :ref:`installation_networkx` format, that is, a :py:func:`networkx.DiGraph` object::

   >>> from PyBoolNet import InteractionGraphs as IGs
   >>> bnet = "\n".join(["v1, v1|v3","v2, 1", "v3, v1&!v2 | !v1&v2"])
   >>> primes = FEX.bnet2primes(bnet)
   >>> igraph = IGs.primes2igraph(primes)
   >>> igraph
   <networkx.classes.digraph.DiGraph object at 0xb513efec>
   
The nodes and edges of *igraph* can be accessed via the :ref:`installation_networkx` functions :py:func:`edges` and :py:func:`nodes`::

   >>> igraph.nodes()
   ['v1', 'v2', 'v3']
   >>> igraph.edges()
   [('v1', 'v1'), ('v1', 'v3'), ('v2', 'v3'), ('v3', 'v1')]
   
The sign of an interaction is either either positive, negative or both.
Signs are stored as the edge attribute *sign* and are accessible via the standard :ref:`installation_networkx` edge attribute syntax::

   >>> igraph.edge["v3"]["v1"]["sign"]
   set([1])
   
Signs are implemented as Python sets and contain 1 if the interaction is positive and -1 if it is negative or both if the interaction is ambivalent,
i.e., sometimes positive and sometimes negative::

   >>> igraph.edge["v1"]["v3"]["sign"]
   set([1, -1])

To create a drawing of an interaction graph use the function :ref:`igraph2image`::

   >>> IGs.igraph2image(igraph, "example02_igraph.pdf")
   
It uses :ref:`installation_graphviz` and the layout engine *dot* to create the given image file.
The result is shown in :ref:`the figure below <figure01>`.

.. _figure01:

.. figure:: figure01.pdf
   :scale: 60%
   :align: center
   
   The interaction graph "*example02_igraph.pdf*" of the network defined above. 


graph, node and edge attributes
*******************************

|software| generates a *dot* file from an interaction graph by inspecting all its edge, node and graph attributes.
Attributes are just dictionaries that are attached to nodes, edges and the graph itself, see :ref:`installation_networkx` for an introduction.
Use these attributes to change the appearance of the graph.
The idea is that you either change the appearance of individual nodes and edges using node and edge attributes,
or change their default appearance using graph attributes.
For a list of all available attributes see http://www.graphviz.org/doc/info/attrs.html.

Some node attributes are:

   * *shape*: sets the shape of the node, e.g. *"rect"*, *"square"*, *"circle"*, *"plaintext"*, *"triangle"*, *"star"*, *"lpromoter"*, *"rpromoter"*
   * *label* (default is the component name): sets the label of a node
   * *style*: *"filled"* to fill with a color, *"invis"* to hide or *""* to revert to default
   * *fillcolor*: sets the fill color, requires *style="filled"*
   * *color*: sets the stroke color
   * *fontcolor*: sets the font color
   * *fontsize* (default is *14*): sets the font size in pt, e.g. *5*, *10*, *15*
   * *fixedsize*: specifies whether the width of a node is fixed, either *"true"* or *"false"*
   * *width*: sets the node width, e.g. *5*, *10*, *15*
      
Colors can be set by names like *"red"*, *"green"* or *"blue"*,
or by space-separated HSV values, e.g. *"0.1 0.2 1.0"*,
or by a RGB value, e.g *"#40e0d0"*.
For a list of predefined color names see for example http://www.graphviz.org/doc/info/colors.html.

The basic edge attributes are:

   * *arrowhead*: sets the shape of the arrow, e.g. *"dot"*, *"tee"*, *"normal"* 
   * *arrowsize*: sets the size of the arrow, e.g. *5*, *10*, *15*
   * *style*: sets the pen style of the edge, e.g. *"dotted"*, *"dashed"*
   * *color*: sets the edge color
   * *label*: sets the label of an edge
   * *penwidth* (default is *1*): sets the width of an edge, e.g. *5*, *10*, *15*
   * *constraint* (default is *"true"*): whether the edge should be included in the calculation of the layout, either *"true"* or *"false"*
   * *weight* (default is *1*): sets the cost for stretching the edge during layout computation, for example *"5"*, *"10"*, *"15"*

To set node or edge defaults, add them to the *node* or *edge* attribute of the graph field::

   >>> bnet = "\n".join(["v1, v2 & (!v1 | v3)","v2, !v3","v3, v2 | v1"])
   >>> primes = FEX.bnet2primes(bnet)
   >>> igraph = IGs.primes2igraph(primes)
   >>> igraph.graph["node"]["shape"] = "circle"
   >>> igraph.graph["node"]["color"] = "blue"
   
To change the appearance of specific nodes or edges, add attributes to the node or edge field::

   >>> igraph.node["v2"]["shape"] = "rpromoter"
   >>> igraph.node["v2"]["color"] = "black"
   >>> igraph.edge["v3"]["v1"]["arrowhead"] = "inv"
   >>> igraph.edge["v3"]["v1"]["color"] = "red"
   
In addition, *dot* graphs have general graph attributes, for example:

   * *splines*: sets how edges are drawn, e.g. *"line"*, *"curved"* or *"ortho"* for orthogonal edges
   * *label*: adds a label to the graph
   * *rankdir* (default is *"TB"*): sets the direction in which layout is constructed, e.g. *"LR"*, *"RL"*, *"BT"*
 
To change graph attributes, add them to the graph dictionary::

   >>> igraph.graph["splines"] = "ortho"
   >>> igraph.graph["rankdir"] = "LR"
   >>> igraph.graph["label"] = "Example 3: Interaction graph with attributes"
   >>> IGs.igraph2image(igraph, "example03_igraph.pdf")
   
   
The result is shown in :ref:`the figure below <figure02>`.

.. _figure02:

.. figure:: figure02.pdf
   :scale: 60%
   :align: center
   
   The interaction graph "*example03_igraph.pdf*". 



the interaction signs style
***************************

|software| has predefined styles for adding attributes to interaction graphs.
The function :ref:`add_style_interactionsigns` adds or overwrites color and arrowhead attributes to indicate whether an interaction is activating, inhibiting or both.
Activating interactions are black with normal arrowheads,
inhibiting interactions are red with blunt arrowhead and
interactions that are both activating and inhibiting are blue with round arrowheads.

Consider a network with a *exclusive or* regulation::

   >>> funcs = {"v1":lambda v1,v2,v3: v1+v2+v3==1,
   ...          "v2":lambda v1: not v1,
   ...          "v3":lambda v2: v2}
   >>> primes = QMC.functions2primes(funcs)
   >>> igraph = IGs.primes2igraph(primes)
   >>> IGs.add_style_interactionsigns(igraph)
   >>> igraph.graph["label"] = "Example 4: Signed interaction graph"
   >>> igraph.graph["rankdir"] = "LR"
   >>> IGs.igraph2image(igraph, "example04_igraph.pdf")
   

The result is shown in :ref:`the figure below <figure03>`.

.. _figure03:

.. figure:: figure03.pdf
   :scale: 60%
   :align: center
   
   The interaction graph "*example04_igraph.pdf*" with attributes added by :ref:`add_style_interactionsings`. 


styles for inputs, outputs and constants
****************************************

*Inputs* are components that are only regulated by themselves.
Usually, inputs regulate themselves positively but we also consider inputs that regulate themselves negatively as inputs.
*Outputs* are components that do not regulate other components and *constants* are components whose update function is constant and always returns either *True* or *False*.

To highlight inputs and outputs by grouping them inside a box use the functions :ref:`add_style_inputs` and :ref:`add_style_outputs`.
They add *dot* subgraphs that contain all components of the respective type and add the label *"inputs"* or *"outputs"*.
The function :ref:`add_style_constants` changes the shape of constants to *"plaintext"*,
their font to *"Time-Italic"* and the color of all interactions involving constants to *"gray"*.

Consider this example::

   >>> bnet = ["v1, v1", "v2, v2", "v3, 1", "v4, v1 | v3",
   ...         "v5, v4 & v2 | v6", "v6, 0", "v7, !v5",
   ...         "v8, v7", "v9, v5 & v7"]
   >>> bnet = "\n".join(bnet)
   >>> primes = FEX.bnet2primes(bnet)
   >>> igraph = IGs.primes2igraph(primes)
   >>> IGs.add_style_inputs(igraph)
   >>> IGs.add_style_constants(igraph)   
   >>> IGs.add_style_outputs(igraph)
   >>> igraph.graph["label"] = "Example 5: Interaction graph with styles for"+
   ...                         "inputs, outputs and constants"
   >>> IGs.igraph2image(igraph, "example05_igraph.pdf")

The result is shown in :ref:`the figure below <figure04>`.

.. _figure04:

.. figure:: figure04.pdf
   :scale: 60%
   :align: center
   
   The interaction graph "*example05.pdf*" with styles added by :ref:`add_style_inputs`, :ref:`add_style_outputs` and :ref:`add_style_constants`.

the SCCs and condensation style
*******************************

The function :ref:`add_style_sccs` defines a *dot* subgraph for every non-trivial *strongly connected component* (SCC) of the interaction graph.
Each SCC subgraph is filled by a shade of gray that indicates the longest path of SCCs leading to it,
a unique number that intuitively represents "the depth in the SCC hierarchy", see :ref:`Klarner2015(b) <klarner2015approx>` for a formal definition.
The further down the hierarchy, the darker the shade of gray will be.
Shades of gray repeat after a depth of nine.

Consider the network::

   >>> bnet = ["v1, v1", "v2, v3 & v5", "v3, v1", "v4, v1", "v5, 1",
   ...         "v6, v7", "v7, v6 | v4", "v8, v6", "v9, v8", "v10, v7 & v11",
   ...         "v11, v10 | v4", "v12, v10"]
   >>> bnet = "\n".join(bnet)
   >>> primes = FEX.bnet2primes(bnet)
   >>> igraph = IGs.primes2igraph(primes)
   >>> IGs.add_style_sccs(igraph)
   >>> igraph.graph["label"] = "Example 6: Interaction graph with SCC style"
   >>> IGs.igraph2image(igraph, "example06_igraph.pdf")

The result is shown in :ref:`the figure below <figure05>`.

In addition you may use :ref:`add_style_condensation` to add a small "map" of the SCC graph, which we call the condensation graph.
Each SCC is replaced by a single node and there is an edge between two SCCs iff there is a "cascade path" between them,
see :ref:`Klarner2015(b) <klarner2015approx>` for a formal definition.
Since styles are additive we generate example 7 by the following lines::

   >>> IGs.add_style_condensation(igraph)
   >>> igraph.graph["label"] = "Example 7: Interaction graph with SCC and condensation style"
   >>> IGs.igraph2image(igraph, "example07_igraph.pdf")   
 
The result is shown in :ref:`the figure below <figure06>`.

.. _figure05:

.. figure:: figure05.pdf
   :scale: 60%
   :align: center
   
   The interaction graph "*example06_igraph.pdf*" with attributes added by :ref:`add_style_sccs`.

.. _figure06:

.. figure:: figure06.pdf
   :scale: 80%
   :align: center
   
   The interaction graph "*example07_igraph.pdf*" with attributes added by :ref:`add_style_sccs` and :ref:`add_style_condensation`.

         

the subgraphs style
*******************

The function :ref:`add_style_subgraphs` allows you to specify subsets of nodes that will be added to a *dot* subgraph.
The subgraphs may be specified either as a list of names of variables or as a tuple that consists of a list of names and a dictionary
of *dot* attributes for that subgraph, e.g., a label or background color.

.. note::
   *Subgraphs* must satisfy this property:
   Any two subgraphs have either empty intersection or one is a subset of the other.
   The reason for this requirement is that *dot* can not draw intersecting subgraphs.

Consider the network::

   >>> bnet = ["v1, v7", "v2, v1 & v6", "v3, v2 | v7", "v4, v3",
   ...         "v5, v1 | v4", "v6, v5", "v7, v6"]
   >>> bnet = "\n".join(bnet)
   >>> primes = FEX.bnet2primes(bnet)
   >>> igraph = IGs.primes2igraph(primes)
   >>> subgraphs = [["v2","v6"],
   ...              (["v1","v4"],{"label":"Genes", "fillcolor":"lightblue"})]
   >>> IGs.add_style_subgraphs(igraph, subgraphs)
   >>> igraph.graph["label"] = "Example 8: Interaction graph with a subgraph style"
   >>> IGs.igraph2image(igraph, "example08_igraph.pdf")

The result is shown in :ref:`the figure below <figure07>`.

.. _figure07:

.. figure:: figure07.pdf
   :scale: 60%
   :align: center
   
   The interaction graph "*example08_igraph.pdf*" with attributes added by :ref:`add_style_subgraphs`. 

the activities style and animations
***********************************

The function :ref:`add_style_activities` colors components according to a given dictionary of activities, i.e., a state or subspace.
Components that are active are colored in red, inactive ones blue and the attributes of the remaining components are not changed.
In addition, interactions that involve activated or inhibited components are grayed out to reflect that they are ineffective.

Here is an example::

   >>> bnet = ["v1, v7", "v2, v1 & v6", "v3, v2 | v7", "v4, v3",
   ...         "v5, v1 | v4", "v6, v5", "v7, v6"]
   >>> bnet = "\n".join(bnet)
   >>> primes = FEX.bnet2primes(bnet)
   >>> igraph = IGs.primes2igraph(primes)
   >>> activities = {"v2":1, "v3":0, "v4":0}
   >>> IGs.add_style_activities(igraph, activities)
   >>> igraph.graph["label"] = "Example 9: Interaction graph with a activities style"
   >>> igraph.graph["rankdir"] = "LR"
   >>> IGs.igraph2image(igraph, "example09_igraph.pdf")

The result is shown in :ref:`the figure below <figure08>`.

.. _figure08:

.. figure:: figure08.pdf
   :scale: 80%
   :align: center
   
   The interaction graph "*example09_igraph.pdf*" with attributes added by :ref:`add_style_activities`.
   
You can also create an animated *gif* from an interaction graph and a sequence of activities.
Note that as mentioned in :ref:`states_subspaces_paths`, activities may be given as strings that consist of 0s, 1s and dashes
using the function :ref:`activities2animation`::

   >>> activities = ["-100", "-110", "-010"]
   >>> IGs.activities2animation(igraph, activities, "animation.gif")
   
   

   


   

the default style
*****************

The default style combines the SCCs, inputs, outputs, constants and interaction sign styles.



Consider the network::

   >>> bnet = ["v1, v1", "v2, v3 & !v5", "v3, !v1", "v4, v1", "v5, 1",
   ...         "v6, v7", "v7, v6 & !v4 | !v6 & v4", "v8, !v6", "v9, v8", "v10, v7 & !v11",
   ...         "v11, v10 | v4", "v12, v10"]
   >>> bnet = "\n".join(bnet)
   >>> primes = FEX.bnet2primes(bnet)
   >>> igraph = IGs.primes2igraph(primes)
   >>> IGs.add_style_default(igraph)
   >>> igraph.graph["label"] = "Example 10: Interaction graph with default style"
   >>> IGs.igraph2image(igraph, "example10_igraph.pdf")

The result is shown in :ref:`the figure below <figure09>`.

.. _figure09:

.. figure:: figure09.pdf
   :scale: 60%
   :align: center
   
   The interaction graph "*example10_igraph.pdf*" with attributes added by :ref:`add_style_default`.
       
       
       

Drawing the State Transition Graph
----------------------------------

Prime implicants can be used to derive the *state transition graph* (STG) of a network.
To compute it, use the function :ref:`primes2stg` of the module :ref:`StateTransitionGraphs`.
It returns an instance of the :ref:`installation_networkx` digraph class::

   >>> from PyBoolNet import StateTransitionGraphs as STGs
   >>> bnet = "\n".join(["v1, v3","v2, v1", "v3, v2"])
   >>> primes = FEX.bnet2primes(bnet)
   >>> update = "asynchronous"
   >>> stg = STGs.primes2stg(primes, update)
   >>> stg
   <networkx.classes.digraph.DiGraph object at 0xb3c7d64c>

The second argument to :ref:`primes2stg` is either *"synchronous"* or *"asynchronous"* for the fully synchronous or the fully asynchronous transition relation, see e.g. :ref:`Klarner2015(b) <klarner2015approx>` for a formal definition.
The nodes of an STG are string representations of states, e.g. *"110"*, see :ref:`states_subspaces_paths`.
You may use :ref:`state2str` to convert a state dictionary into a state string.
They are vectors of activities, sorted by component names::

   >>> stg.nodes()[0]
   '010'
   
You may use :ref:`installation_networkx` functions on *stg*, for example networkx.has_path_::

   >>> import networkx
   >>> networkx.has_path(stg, "100", "111")
   True
   
State transition graphs can be styled in the same way as interaction graphs, see :ref:`drawing_interaction_graphs`.
Use the function :ref:`stg2image` to generate a drawing of the STG::

   >>> stg.graph["label"] = "Example 11: The asynchronous STG of a positive circuit"
   >>> stg.graph["rankdir"] = "LR"
   >>> STGs.stg2image(stg, "example11_stg.pdf")

The result is shown in :ref:`the figure below <figure10>`.

.. _figure10:

.. figure:: figure10.pdf
   :scale: 80%
   :align: center
   
   The state transition graph "*example11_stg.pdf*" of an isolated feedback circuit.

By default, the full STG is constructed.
If you want to draw the part of a STG that is reachable from an initial state or a set of initial states
pass a third argument to :ref:`primes2stg`.
For convenience you may choose one of several ways of specifying initial states.
Either a list of states in *dict* or *str* format (see :ref:`states_subspaces_paths`)::

   >>> init = ["000", "111"]
   >>> init = ["000", {"v1":1,"v2":1,"v3":1}]

or as a function that is called on every state and must return either *True* or *False* to indicate whether the state ought to be initial::

   >>> init = lambda x: x["v1"]>=x["v2"]
   
or by a subspace in which case all the states contained in it are initial::

   >>> init = "--1"
   >>> init = {"v3":1}

To construct the STG starting from initial states call::

   >>> stg = STGs.primes2stg(primes, update, init)
       

   

.. warning::
   You should not draw asynchronous STGs with more than 2^7=128 states as *dot* will take very long to compute the layout.
   For synchronous STGs you should not go above 2^12=4096 states.
   Use different layout engines like *twopi* and *circo* by generating the *dot* file with :ref:`stg2dot` and compiling it manually.



the tendencies style
********************

The tendencies style for state transition graphs is similar to the interaction sign style for interaction graphs.
It colors state transitions according to whether all changing variables increase (black), or all of them decrease (red) or some increase and some decrease (blue).
The latter is only possible for synchronous transition graphs.

Here is an example::

   >>> bnet = "\n".join(["v1, !v3","v2, v1", "v3, v2"])
   >>> primes = FEX.bnet2primes(bnet)
   >>> stg = STGs.primes2stg(primes, "synchronous")
   >>> stg.graph["rankdir"] = "LR"
   >>> stg.graph["label"] = "Example 12: The synchronous STG of a negative circuit"
   >>> STGs.add_style_tendencies(stg)
   >>> STGs.stg2image(stg, "example12_stg.pdf")


The result is shown in :ref:`the figure below <figure11>`.

.. _figure11:

.. figure:: figure11.pdf
   :scale: 80%
   :align: center
   
   The state transition graph "*example12_stg.pdf*" with attributes added by :ref:`add_style_tendencies`.
   


the path style
**************

The path style is used to highlight a path in the state transition graph.
It changes the *penwidth* and *color* of transitions.

Consider the following example::

   >>> bnet = "\n".join(["x, !x|y", "y, !x&!z|x&!y&z", "z, x|!y"])
   >>> primes = FEX.bnet2primes(bnet)
   >>> stg = STGs.primes2stg(primes, "asynchronous")
   >>> stg.graph["label"] = "Example 13: STG with path style"
   
Now add the path style::

   >>> path = ["011","010","110","100","000"]   
   >>> STGs.add_style_path(stg, path, "red")
   >>> STGs.stg2image(stg, "example13_stg.pdf")  

The result is shown in :ref:`the figure below <figure12>`.

.. _figure12:

.. figure:: figure12.pdf
   :scale: 60%
   :align: center
   
   The state transition graph "*example13_stg.pdf*" with attributes added by :ref:`add_style_path`.
   
   
   

the SCCs style
**************

The SCC style is almost identical to the one for interaction graphs except that it adds a label to the attractors, i.e.,
steady states and cyclic attractors.::

   >>> bnet = "\n".join(["x, !x|y", "y, x&!y|!z", "z, x&z|!y"])
   >>> primes = FEX.bnet2primes(bnet)
   >>> stg = STGs.primes2stg(primes, "asynchronous")
   >>> stg.graph["label"] = "The SCC style"   
   >>> STGs.add_style_sccs(stg)
   >>> STGs.stg2image(stg, "example14_stg.pdf")

The result is shown in :ref:`the figure below <figure13>`.

.. _figure13:

.. figure:: figure13.pdf
   :scale: 60%
   :align: center
   
   The state transition graph "*example14_stg.pdf*" with attributes added by :ref:`add_style_sccs`.
     


the min trap spaces style
*************************

The min trap spaces style is adds a *dot* subgraph for every minimal trap space of the state transition graph.
For an introduction to trap spaces, see :ref:`Klarner2015(a) <klarner2015trap>` and also :ref:`trap_spaces_and_attractors`::

   >>> bnet = "\n".join(["x, !x|y&z", "y, x&!y|!z", "z, z|!y"])
   >>> primes = FEX.bnet2primes(bnet)
   >>> stg = STGs.primes2stg(primes, "asynchronous")
   >>> stg.graph["label"] = "Example 15: STG with min trap spaces style"   
   >>> STGs.add_style_mintrapspaces(primes, stg)
   >>> STGs.stg2image(stg, "example15_stg.pdf")  

The result is shown in :ref:`the figure below <figure14>`.

.. _figure14:

.. figure:: figure14.pdf
   :scale: 60%
   :align: center
   
   The state transition graph "*example15_stg.pdf*" with attributes added by :ref:`add_style_mintrapspaces`.
     



the subspaces style
*******************

The subspace style is identical to the subgraph style of interaction graphs.
It adds a subgraph for every given subspace.
As for interaction graphs, you may add pairs of subspace and attribute dictionaries if you want to change the label, or color etc. of the subgraphs::

   >>> bnet = "\n".join(["x, !x|y&z", "y, x&!y|!z", "z, z|!y"])
   >>> primes = FEX.bnet2primes(bnet)
   >>> stg = STGs.primes2stg(primes, "asynchronous")
   >>> stg.graph["label"] = "Example 16: STG with subspaces style"
   >>> sub1 = ({"x":0},{"label":"x is zero"})
   >>> sub2 = {"x":1,"y":0}
   >>> subspaces = [sub1, sub2]
   >>> STGs.add_style_subspaces(primes, stg, subspaces)
   >>> STGs.stg2image(stg, "example16_stg.pdf")  

The result is shown in :ref:`the figure below <figure15>`.

.. note::
   *Subspaces* must satisfy this property:
   Any two subspaces have either empty intersection or one is a subset of the other.
   The reason for this requirement is that *dot* can not draw intersecting subgraphs.


.. _figure15:

.. figure:: figure15.pdf
   :scale: 60%
   :align: center
   
   The state transition graph *"example16_stg.pdf"* with attributes added by :ref:`add_style_subspaces`.
  

the default style
*****************

The default style combines the SCCs with the tendencies and the minimal trap spaces styles::


   >>> bnet = "\n".join(["x, !x|y&z", "y, x&!y|!z", "z, z|!y"])
   >>> primes = FEX.bnet2primes(bnet)
   >>> stg = STGs.primes2stg(primes, "asynchronous")
   >>> stg.graph["label"] = "Example 16: STG with default style"
   >>> STGs.add_style_default(primes, stg)
   >>> STGs.stg2image(stg, "example17_stg.pdf")

The result is shown in :ref:`the figure below <figure16>`.

.. _figure16:

.. figure:: figure16.pdf
   :scale: 80%
   :align: center
   
   The state transition graph *"example17_stg.pdf"* with attributes added by :ref:`add_style_default`.
  




.. _sec:model_checking:

Model Checking
--------------
|software| uses :ref:`installation_nusmv` to decide model checking queries for Boolean networks.
A model checking problem is defined by a transition system, its initial states and a temporal specification.
For a formal introduction to model checking see for example :ref:`Baier2008 <Baier2008>`.

Transition Systems
******************
Transition systems are very similar to state transition graphs but in addition to states and transitions there are *atomic propositions*
which are the statements that are available for specifying states.
As an example, consider the following network::

   >>> bnet = ["Erk,  Erk & Mek | Mek & Raf",
   ...         "Mek,  Erk | Mek & Raf",
   ...         "Raf,  !Erk | !Raf"]
   >>> bnet = "\n".join(bnet)
   >>> primes = FEX.bnet2primes(bnet)
   >>> stg = STGs.primes2stg(primes, "asynchronous")
   >>> stg.graph["label"] = "Example 18: STG of the Erk-Mek-Raf network"
   >>> STGs.stg2image(stg, "example18_stg.pdf")
   
The state transition graph is shown in :ref:`the figure below <figure17>`.

When model checking, |Software| translates state transition graphs into transition systems.
The basic approach to doing so is shown in :ref:`the figure below <figure17>`.
Here, each state string is replaced by a subset of atomic propositions.
The subset is chosen to correspond with the state string, i.e.,
a state is labeled with *Mek* iff Mek is activated in it which is the case for all states in the subspace *"-1-"*.

.. _figure17:

.. figure:: figure17.pdf
   :scale: 120%
   :align: center
   
   The state transition graph *"example18_stg.pdf"* of the Erk-Mek-Raf network on the left
   and the corresponding basic transition system on the right.
   
Since the choice of atomic propositions affects the expressiveness and conciseness of the model checking queries that users can formulate
we have decided to extend this basic transition system by some *auxiliary variables*.
First, we add a proposition that states whether a variable is steady, i.e., whether its activity is equal to the value of its update function.
Those propositions add *_STEADY* to each variable, e.g. *Mek_STEADY* for *Mek*.
Second, we add a proposition *STEADYSTATE* that is true iff the respective state is a steady state.
Finally, we add a proposition *SUCCESSORS=k* where *k* is an integer,
that is true iff the respective state has exactly *k* successors (excluding itself).
The propositions *SUCCESSORS=0* and *STEADYSTATE* are therefore equivalent.

.. note::
   The :ref:`installation_nusmv` language is case sensitive.
   
The transition system with the extended set of atomic propositions is shown in :ref:`the figure below <figure18>`.

.. _figure18:

.. figure:: figure18.pdf
   :height: 7cm
   :align: center
   
   The extended transition system for the Erk-Mek-Raf network.

LTL Model Checking
******************
Apart from a transition system, a model checking problem requires a *temporal specification*.
Since |Software| uses :ref:`installation_nusmv` for solving model checking problems, two specification languages are available:
*linear time logic* (LTL) and *computational tree logic* (CTL).

LTL specifications are statements about the sequence of events that are expressed in terms of atomic propositions and temporal operators.
A LTL specification is either true or false for a given linear sequence, i.e., infinite path, in a given transition system.
The basic temporal operators for LTL are:

   * *F(..)* which means *finally*
   * *G(..)* which means *globally*
   * *[..U..]* which means *until*
   * *X(..)* which means *next*
   
LTL statements may be combined by the usual logical operators which are:

   * *|* which means *disjunction*
   * *&* which means *conjunction*
   * *!* which means *negation*
   
in :ref:`installation_nusmv` syntax.
For a formal definition of LTL formulas see for example :ref:`Baier2008 <Baier2008>`.

Finally, model checking problems allow the user to specify some states of the transition system to be *initial*.
A LTL specification is then defined to be true for a transition system with initial states iff every path that starts from an initial state
satisfies the LTL specification.

As an example consider again the Erk-Mek-Raf network :ref:`from above <figure17>`.
Let us query whether along every path in its transition system there is eventually a state in which *Raf* is activated::

   >>> from PyBoolNet import ModelChecking as MC
   >>> init = "INIT TRUE"
   >>> spec = "LTLSPEC F(Raf)"
   >>> update = "asynchronous"
   >>> answer = MC.check_primes(primes, update, init, spec)
   >>> answer
   True
   
The first line imports the module :ref:`ModelChecking`.
The next line defines the initial states in :ref:`installation_nusmv` syntax with the keyword *INIT* to indicate an initial condition and 
the expression *TRUE* which evaluates to true in every state.
The next line starts with the keyword *LTLSPEC* which must precede the definition of a LTL specification and the formula *F(Raf)* which
states that eventually a state will be reached that is labeled by *Raf*, i.e., in which *Raf* is activated.
The fifth line calls the function :ref:`check_primes` which constructs the extended transition system and
uses :ref:`installation_nusmv` to answer model checking queries.
Note that the function requires a parameter that specifies the update rule, i.e., either *"asynchronous"*, *"synchronous"* or *"mixed"*
and that it returns a Boolean value.

Even for this small example network it is not trivial to see why *True* is the correct answer,
because a brute force approach would require the enumeration of all paths but the transition system contains an infinite number of paths.
Convince yourself that every path eventually reaches the state 101 or the state 111 or the state 001.   
In all cases *Raf*, which is the third digit in the state string, is equal to 1 which is what *F(Raf)* requires.
Hence *True* is the correct answer.

The second example is a slightly more complicated *reachability* query::

   >>> spec = "LTLSPEC F(Raf & F(STEADYSTATE))"
   >>> answer = MC.check_primes(primes, update, init, spec)
   >>> answer
   False
   
The LTL formula queries whether every path will eventually come across a state in which *Raf* is activated followed by a steady state.
Note that the formula asserts an order on the sequence of events: first *Raf* and then *STEADYSTATE*.
To see why the specification is false we only need to find one infinite path from an initial state that does not satisfy the LTL formula.
Since all states are initial the following path will do::

   101 -> 100 -> 110 -> 111 -> 110 -> 111 -> 110 -> ...
   
The last two states, 111 and 110, are repeated for ever and neither is labeled with *STEADYSTATE* in the extended transition system,
see :ref:`this figure <figure18>`.
Hence *False* is the correct answer.

The third example specifies a proper subset of states as initial and queries the existence of *sustained oscillations* in *Raf*::

   >>> init = "INIT Erk & SUCCESSORS<2"
   >>> spec = "LTLSPEC G(F(Raf) & F(!Raf))"
   >>> answer = MC.check_primes(primes, update, init, spec)
   >>> answer
   True
   
Here, a state is initial iff *Erk* is activated in it and the number of its successors - with respect to the given the update rule - is less than two.
The formula *G((F(Raf) & F(!Raf))* requires that however far down the sequence of states, i.e., *globally*,
it is true that *Raf* will eventually be activated and also that *Raf* will eventually be inhibited.
The extended transition system, see :ref:`this figure <figure18>`, shows that exactly three state are initial: 110, 011 and 111.
Any path starting in one of those state will eventually end in the infinite sequence::

   111 -> 110 -> 111 -> 110 -> 111 -> ...
   
Hence, any path that starts in one of the initial states satisfies *G((F(Raf) & F(!Raf))*, i.e.,
a sustained oscillation in *Raf*, and hence the truth of the query.

The fourth example involves another feature: the use of :ref:`installation_nusmv` built-in functions, in this case *count*::

   >>> init = "INIT Mek"
   >>> spec = "LTLSPEC G(count(Erk_STEADY,Mek_STEADY,Raf_STEADY)>=2)"
   >>> answer = MC.check_primes(primes, update, init, spec)
   >>> answer
   False

The LTL formula also uses the auxiliary variables *Erk_STEADY*, *Mek_STEADY* and *Raf_STEADY* which are true in states in which the respective variables
are equal to the values of their update functions.
The formula states that along any path that starts from an initial state at least two of the variables *Erk*, *Mek* and *Raf* are steady.
Since the query is false there must be a path that does not satisfy the specifications, for example this one::

   010 -> 011 -> 111 -> 110 -> 111 -> 110 -> ...
   
It does not satisfy the LTL formula because in the state 010 only *Erk* is steady and
hence *count(...)* which counts the number of true expressions is equal to one and hence *G(count(...)>=2)* is false.
See the :ref:`installation_nusmv` manual for more built-in functions like *count()*.

The existence of so-called *counterexamples* is essential to LTL model checking
and :ref:`installation_nusmv` can be asked to return one if it finds one.


LTL Counterexamples
*******************
If a LTL query is false then :ref:`installation_nusmv` can return a finite path that proves that the formula is false.

.. note::
   Since the transition systems of Boolean networks are finite, a counterexample will always be a finite sequence of states -
   possibly ending in a cycle.
   For a justification, see for example :ref:`Baier2008 <Baier2008>` Sec. 5.2.

To return a counterexample pass the argument *DisableCounterExamples=False* to the function :ref:`check_primes`.
The function will then always return a tuple that consists of the answer and a counterexample.
Reconsider the following query, which we know is false, from above::

   >>> init = "INIT TRUE"
   >>> spec = "LTLSPEC F(Raf & F(STEADYSTATE))"
   
To retrieve the answer and a counterexample call::

   >>> answer, counterex = MC.check_primes(primes, update, init, spec, False)

The counterexample will be a Python tuple of state dictionaries (recall :ref:`states_subspaces_paths`) if the query is false
and *None* in case it is true and no counterexample exists.
Hence, a typical way to inspect a counterexample involve a Python if-statement::

   >>> if counterex:
   ...     print " -> ".join(STGs.state2str(x) for x in counterex)
   100 -> 101 -> 100
   
Here, :ref:`state2str` is a function of the module :ref:`StateTransitionGraphs` that generates a state string from a state dictionary.
An alternative way of inspecting counterexample is by :ref:`STGs.add_style_path <add_style_path>`::

   >>> stg = STGs.primes2stg(primes, update)
   >>> STGs.add_style_path(stg, counterex, "red")
   >>> stg.graph["label"] = "Example 19: A LTL counterexample"
   >>> STGs.stg2image(stg, "example19_stg.pdf")


.. _figure19:

.. figure:: figure19.pdf
   :scale: 60%
   :align: center
   
   The state transition graph *"example18_stg.pdf"* of the Erk-Mek-Raf network with a path style that indicates a counterexample to
   the LTL query with all states being initial and the formula *F(Raf & F(STEADYSTATE))*.

A second alternative is to generate an animated *gif* of the changing activities in each state
and using :ref:`IGs.activities2animation <activities2animation>`::

   >>> igraph = IGs.primes2igraph(primes)
   >>> IGs.activities2animation(igraph, counterex, "counterexample.gif")


CTL Model Checking
******************
:ref:`installation_nusmv` can also solve model checking problems that involve *computation tree logic* (CTL).
CTL formulas are constructed like LTL formulas but the temporal operators *F*, *G*, *X* and *U* must be quantified by *E* which means *for some path*
or *A* which means *for all paths*.
A CTL formula is not evaluated for paths but for trees of successors rooted in some initial state.

.. note::

   Some properties can be specified in LTL or CTL, other properties can only be stated in either LTL or CTL.
   See Sec. 6.3 in :ref:`Baier2008 <Baier2008>` for a discussion of the expressiveness of CTL and LTL.

Consider the following toy model of cell proliferation:

   >>> bnet = ["GrowthFactor,  0",
   ...         "Proliferation, GrowthFactor | Proliferation & !DNAdamage",
   ...         "DNAdamage,     !GrowthFactor & DNAdamage"]
   >>> bnet = "\n".join(bnet)
   >>> primes = FEX.bnet2primes(bnet)
   >>> update = "asynchronous"

Suppose we want to find out whether the presence of *GrowthFactor* implies the possibility of *Proliferation*.
By "possibility" we mean that there is a path that leads to a state in which proliferation is activated.
Let us first determine whether this property holds in the network above by drawing the state transition graph with
the initial states and the proliferation states highlighted by filled rectangles and a subgraph, respectively::

   >>> stg = STGs.primes2stg(primes, update)
   >>> for x in stg.nodes():
   ...     x_dict = STGs.str2state(primes, x)
   ...     if x_dict["GrowthFactor"]:
   ...         stg.node[x]["style"] = "filled"
   ...         stg.node[x]["fillcolor"] = "gray"
   >>> sub = ({"Proliferation":1},{"label":"proliferation"})
   >>> STGs.add_style_subspaces(stg, [sub])
   >>> stg.graph["label"] = "Example 20: STG of the Proliferation network"
   >>> STGs.stg2image(stg, "example20_stg.pdf")
   
It is easy to see, in the :ref:`figure below <figure20>`, that for every initial state there is a path to a proliferation state.
There are two initial states in which *Proliferation* is inhibited, namely *110* and *010*.
For each there is a path leading to a state in which *Proliferation* is activated, namely::

   110 -> 111 and 010 -> 011

Perhaps surprisingly, this property can not be formulated in LTL.
The LTL formula is *F(Proliferation)*, for example, requires that *all paths* lead to a proliferation state which is
not the same as *some paths* lead to proliferation.
In fact, the property *F(Proliferation)* is false, as :ref:`the figure below <figure21>` for the following counterexample demonstrates::

   >>> init = "INIT GrowthFactor"
   >>> spec = "LTLSPEC F(Proliferation)"
   >>> answer, counterex = MC.check_primes(primes, update, init, spec, False)
   >>> answer
   False
   >>> STGs.add_style_path(stg, counterex, "red")
   >>> stg.graph["label"] = "Example 21: Counterexample"
   >>> STGs.stg2image(stg, "example21_stg.pdf")

.. _figure20:

.. figure:: figure20.pdf
   :scale: 60%
   :align: center
   
   The state transition graph *"example20_stg.pdf"* of the Proliferation network with initial states highlighted by gray rectangles
   and proliferation states gathered in a subgraph.


.. _figure21:

.. figure:: figure21.pdf
   :scale: 60%
   :align: center
   
   The state transition graph *"example21_stg.pdf"* of the Proliferation network with a counterexample highlighted by path.

The property can, however, be formulated in CTL using the existential quantifier::

   >>> spec = "CTLSPEC EF(Proliferation)"
   >>> answer = MC.check_primes(primes, update, init, spec)
   True

.. note::   
   The LTL formula *F(Proliferation)* is equivalent to the CTL formula *AF(Proliferation)*.
   In general, however, there are LTL formulas for which no equivalent CTL formula exists, and vice versa.

CTL model checking is also required when querying properties about the *attractors* of the state transition graph.
Attractors are defined to be the *terminal SCCs* of the STG or, equivalently, they are its *minimal trap sets*.
For a formal definition see for example :ref:`Klarner2015(b) <klarner2015approx>` Sec. 2.2.

Suppose we want to find out whether, for the initial states defined *Proliferation*,
all attractors are located in the subset of states that are defined by *!DNAdamage*.
In English, this property states that "along any path starting from any initial state it is possible to reach a state from
which all reachable states satisfy *!DNAdamage*".
In CTL, it can be formulated using the *AG(EF(AG(...)))* query pattern where "..." is the condition that describes the attractor states::

   >>> init = "INIT Proliferation"
   >>> condition = "!DNAdamage"
   >>> spec = "CTLSPEC AG(EF(AG(%s)))"%condition
   >>> answer = MC.check_primes(primes, update, init, spec)
   True
   
Other frequently used conditions are *STEADYSTATE* to query whether all attractors are steady states::

   >>> init = "INIT Proliferation"
   >>> condition = "STEADYSTATE"
   >>> spec = "CTLSPEC AG(EF(AG(%s)))"%condition
   >>> answer = MC.check_primes(primes, update, init, spec)
   True
   
or disjunctions and conjunctions of basic propositions::

   >>> init = "INIT Proliferation"
   >>> condition = "STEADYSTATE | (!Proliferation & DNAdamage)"
   >>> spec = "CTLSPEC AG(EF(AG(%s)))"%condition
   >>> answer = MC.check_primes(primes, update, init, spec)
   True
   
.. note::
   The CTL formula *AG(EF(AG(STEADYSTATE)))* is equivalent to *AG(EF(STEADYSTATE)* because if a steady is steady then it has no successors.
   
.. note::
   To query whether *there is* an attractor of a certain type reachable from every initial state,
   rather than whether *all* attractors are of a certain type, use the query pattern *EF(AG(...))* instead of *AG(EF(AG(...)))*.

CTL Counterexamples
*******************
If a CTL formula is false then :ref:`installation_nusmv` can return a finite path that starts with an initial state that does not satisfy the formula.

.. note::
   There is a fundamental difference between LTL and CTL counterexamples.
   LTL counterexamples prove that the formula is false in the sense that any transition system that contains that path will not satisfy the formula.
   CTL counterexamples, on the other hand, can not be used as general proofs.
   They merely contain an initial state that does not satisfy the formula *in the given transition system*.
   
Suppose we want to find out whether each initial states defined by *Proliferation* has a successor state that also satisfies *Proliferation*.
To define this property we use the CTL operator *EX*::

   >>> init "INIT Proliferation"
   >>> spec "CTLSPEC EX(Proliferation)"
   >>> answer = MC.check_primes(primes, update, init, spec)
   False
   >>> answer, counterex = MC.check_primes(primes, update, init, spec, False)
   >>> counterex
   ({'DNAdamage': 1, 'Proliferation': 1, 'GrowthFactor': 0},)
   >>> STGs.state2str(counterex[0])
   101
         
The counterexample returns a paths that consists of a single state, namely 101, that does not satisfy *EX(Proliferation)*,
i.e., that does not have a successor that is a proliferation state.
The correctness of this answer can be confirmed by enumerating all successors of 101 (in this case a single successor)
by using :ref:`STGs.successors_asynchronous <successors_asynchronous>`::

   >>> for x in STGs.successors_asynchronous(primes, "101"):
   ...     print x
   {'DNAdamage': 1, 'Proliferation': 0, 'GrowthFactor': 0}
   
and checking that *Proliferation=0* for all of them.

.. note::
   CTL counterexamples are in general also paths, for an explanation see e.g. :ref:`Baier2008 <Baier2008>`,
   but the length of the path and which sub-formula is not satisfied by the state it leads to depend on the given formula.
   It is often easier to just return the initial state that does not satisfy the whole formula, using::
   
      >>> answer, counterex = MC.check_primes(primes, update, init, spec, False)
      >>> state = counterex[0]

Existential Queries
*******************
By definition, a LTL query is true iff *all paths* that are rooted in an initial state satisfy the LTL formula.
Likewise, a CTL query is true iff *all initial states* satisfy the CTL formula.
Without modifying the standard algorithms it is also possible to answer existential queries of the form:
"Is there a path rooted in some initial state that satisfies a given LTL formula?"
and "Is there an initial state that satisfies a given CTL formula?".
The idea is to apply the following logical equivalences:

   There is an initial state that satisfies a given CTL formula iff
   it is *false* that every initial state satisfies the *negation* of the CTL formula.
   
and

   There is a path rooted in some initial state that satisfies a given LTL formula iff
   it is *false* that all paths satisfy the *negation* of the LTL formula.
   
As an example consider the following network::

   >>> bnet = ["x0,   !x0&x1 | x2",
   ...         "x1,   !x0 | x1 | x2",
   ...         "x2,   x0&!x1 | x2"]
   >>> bnet = "\n".join(bnet)
   >>> primes = FEX.bnet2primes(bnet)
   
and the queries "Every state that satisfies *x1=0* can reach an attractor in which *x0* is steady" (Q1)
and "There is a state that satisfies *x1=0* that can reach an attractor in which *x0* is steady" (Q2).
Note that the equivalence from above states that "Q2 is true iff not Q1 is false".

Let us first answer these queries without model checking, that is, by inspecting the state transition graph.
As before, we highlight the initial states:

   >>> stg = STGs.primes2stg(primes, "asynchronous")
   >>> for x in stg.nodes():
   ...     if x[1]=="0":
   ...         stg.node[x]["style"] = "filled"
   ...         stg.node[x]["fillcolor"] = "gray"
   >>> stg.graph["label"] = "Example 22: Existential queries"
   >>> STGs.stg2image("example22_stg.pdf")

The result is shown in :ref:`the figure below <figure22>`.
It is easy to see that the network has two attractors, the steady state 111 (in which *x0* is steady) and a cyclic attractor which consists of the states 010 and 110, in which *x0* is not steady.
It is also not hard to confirm that Q1 does not hold,
because the initial state 000 can only reach the cyclic attractor,
and that Q2 does hold, because 100 is an initial state that can reach the steady state 111.

.. _figure22:

.. figure:: figure22.pdf
   :scale: 60%
   :align: center
   
   The state transition graph *"example22_stg.pdf"* with initial states highlighted by gray rectangles.
   The attractors are the steady state 111 and the cyclic attractor that consists of the states 010 and 110.
   
To decide the queries with CTL model checking we use the following encoding::

   >>> init = "INIT !x1"
   >>> specQ1 = "CTLSPEC  EF(AG(x0_STEADY))"
   >>> specQ2 = "CTLSPEC !EF(AG(x0_STEADY))"

   >>> update = "asynchronous"
   >>> Q1 = MC.check_primes(primes, update, init, specQ1)
   >>> Q1
   False
   >>> Q2 = not MC.check_primes(primes, update, init, specQ2)
   >>> Q2
   True

Note that *specQ2* is exactly the negation of *specQ1* and the result of checking *specQ2* has to be negated to obtain the answer to Q2.

.. note::
   
   The queries *specQ1* and *specQ2* are both false although one is exactly the negation of the other.
   In LTL and CTL model checking, a formula as well as its negation may be false *simultaneously*.
   For CTL, this is the case when some initial state satisfy the formula and some other initial state does not.
   For LTL, this is the case when some admissible path satisfies the formula and some other path does not.
   
   
Note also that since *specQ2* is false we can ask :ref:`installation_nusmv` to generate a counterexample, i.e.,
an initial state that does not satisfy *specQ2*, i.e., a state that satisfies Q2.
Counterexamples of existential queries are therefore often also called *witnesses*.

   >>> notQ2, counterex = MC.check_primes(primes, update, init, specQ2, False)
   >>> state = counterex[0]
   >>> STGs.state2str(state)
   100
   
   
Computing Trap Spaces
---------------------
Maximal, Minimal and All Trap Spaces 
The term *trap space* merges the notions "subspace" and "trap set".
Hence, once a trajectory enters a trap space it can not escape.
Trap spaces have a number of interesting properties: they are independent of the update strategy, i.e.,
they are identical for all state transition graphs, they satisfy a partial order defined by set inclusion of the respective states contained in them
and they can be computed efficiently for networks with hundreds of components.
Intuitively, trap spaces can be seen as generalizations of steady states (note that steady states have the same three properties).
For a formal introduction, an algorithm for computing trap spaces and a benchmark see :ref:`Klarner2015(a) <klarner2015trap>`.

|Software| uses the module :ref:`TrapSpaces` and the function :ref:`trap_spaces` to compute trap spaces.
As an example, consider the following network which has five trap spaces::

   >>> from PyBoolNet import TrapSpaces as TS
   >>> bnet = ["x, !x | y | z",
   ...         "y, !x&z | y&!z",
   ...         "z, x&y | z"]
   >>> bnet = "\n".join(bnet)
   >>> primes = FEX.bnet2primes(bnet)
   >>> tspaces = TS.trap_spaces(primes, "all")
   >>> print ", ".join(STGs.subspace2str(primes, x) for x in tspaces)
   ---, --1, 1-1, -00, 101

The trap space ``---``, i.e., the full state space, is also called the trivial trap space.
``101`` is a steady state and there are three more trap spaces, ``--1``, ``1-1`` and ``-00``.
Note that some trap spaces are comparable using subset inclusion, i.e.,
``1-1`` < ``--1`` because the two states contained in ``1-1`` are also contained in ``--1``,
while others are not comparable, for example ``--1`` and ``-00``.

The trap spaces are illustrated in :ref:`the figure below <figure23>` using the subspaces style::

   >>> stg = STGs.primes2stg(primes, "asynchronous")
   >>> STGs.add_style_subspaces(primes, stg, tspaces)
   >>> stg.graph["label"] = "Example 23: All trap spaces"
   >>> STGs.stg2image(stg, "example23_stg.pdf")

.. _figure23:

.. figure:: figure23.pdf
   :scale: 60%
   :align: center
   
   The state transition graph *"example23_stg.pdf"* with every trap space highlighted by its own subgraph.

The number of all trap spaces of a network can be very large and one is often only interested in the subset of minimal or maximal trap spaces.
These can also be computed using :ref:`trap_spaces` by passing *"min"* or *"max"* instead of the previously used value *"all"* for the second parameter::

   >>> mintspaces = TS.trap_spaces(primes, "min")
   >>> for x in mintspaces:
   ...     sub = (x,{"fillcolor":"salmon"})
   ...     STGs.add_style_subspaces(primes, stg, [sub])
   >>> maxtspaces = TS.trap_spaces(primes, "max")
   >>> for x in maxtspaces:
   ...     if x in mintspaces:
   ...         sub = (x,{"fillcolor":"lightyellow"})
   ...         STGs.add_style_subspaces(primes, stg, [sub])
   ...     else:
   ...         sub = (x,{"fillcolor":"lightblue"})
   ...         STGs.add_style_subspaces(primes, stg, [sub])
   >>> stg.graph["label"] = "Example 24: Minimal and maximal trap spaces"
   >>> STGs.stg2image(stg, "example24_stg.pdf")

The result is shown in :ref:`the figure below <figure24>` in which ``-00`` is minimal and maximal (yellow),
``--1`` is maximal (blue), ``1-1`` is neither maximal nor minimal (green), and ``101`` is minimal (red).

.. _figure24:

.. figure:: figure24.pdf
   :scale: 60%
   :align: center
   
   The state transition graph *"example24_stg.pdf"* with minimal trap spaces in red, maximal trap spaces in blue,
   trap spaces that are minimal and maximal at the same time in yellow and the remaining trap spaces in green.
   

.. note::
   It is possible that two non-minimal trap spaces intersect in which case the intersection is again a trap space.
   Since :ref:`installation_graphviz` can not draw intersecting subgraphs it is therefore not always possible to draw all trap spaces.
   Minimal trap spaces on the other hand, can not intersect and can always be drawn in the same STG.








Attractors
----------

Attractor Detection
*******************
Attractors capture the long-term activities of the components of Boolean networks.
Two different types of attractors are possible: either all activities stabilize at some values and the network enters a steady state or at least one component shows sustained oscillations and the network enters a cyclic attractor.
Formally, attractors are defined as the inclusion-wise minimal trap sets of a given STG which is equivalent to the so-called terminal SCCs of the state transition graph.
One approach to computing the attractors is to use Tarjan's algorithm for computing the SCCs of a directed graph, see :ref:`Tarjan1972 <Tarjan1972>` and then to select those SCCs that are terminal, i.e., those for which there is no path to another SCC.
This approach is implemented in the function :ref:`compute_attractors_tarjan`.
As an example for computing attractors with this algorithm
consider the following network and its asynchronous STG which is given in :ref:`the figure below <figure25>`::

   >>> import AttractorDetection as AD
   >>> bnet = ["v1, !v1 | v3",
   ...         "v2, !v1 | v2&!v3",
   ...         "v3, !v2"]
   >>> bnet = "\n".join(bnet)
   >>> primes = FEX.bnet2primes(bnet)
   >>> stg = STGs.primes2stg(primes, "asynchronous")
   >>> STGs.add_style_sccs(stg)
   >>> stg.graph["label"] = "Example 25: A network with a cyclic attractor and a steady state."
   >>> STGs.stg2image(stg, "example25_stg.pdf")
   >>> attractors = AD.compute_attractors_tarjan(primes, stg)
   >>> len(attractors)
   2
   >>> for A in attractors:
   ...     print [STGs.state2str(x) for x in A]
   ['101']
   ['010', '110']

.. _figure25:

.. figure:: figure25.pdf
   :scale: 60%
   :align: center
   
   The asynchronous STG *"example25_stg.pdf"* of a network with a steady state and a cyclic attractor.   
   
Due to the state space explosion problem, the approach of computing the terminal SCCs by explicitly
constructing the underlying STG as a digraphis limited to networks with less than 15~20 components.

There are algorithms for larger networks, but the "best" algorithm for solving the detection problem will depend on the chosen update strategy.
For synchronous STGs we suggest to use an approach that was suggested
by :ref:`Dubrova2011 <Dubrova2011>` and involves a SAT solver and bounded LTL model checking.
It has been implemented as a tool called *bns* which is available at https://people.kth.se/~dubrova/bns.html.

.. note::

   Boolean networks can be converted into *bns* file format with :ref:`primes2bns`.

.. note::

   Whereas the steady states of the synchronous and asynchronous STGs are identical,
   the number and composition of cyclic attractors depends, in general, on the chosen update strategy.
   
A fairly efficient approach to detecting at least some attractors or larger networks is mentioned in :ref:`Klarner2015(a) <klarner2015trap>`
and based on the idea of generating a random walk in the STG, starting from some initial state,
and then testing with CTL model checking whether the final state is indeed part of an attractor.
This approach is based on the observation that, in practice, a random walk will quickly reach states that belong to an attractor.
It is implemented in the function :ref:`find_attractor_by_randomwalk_and_ctl`::

   >>> state = AD.find_attractor_by_randomwalk_and_ctl(primes, "asynchronous")
   >>> STGs.state2str(state)
   110
   
The function takes three optional parameters: *InitialState* which allows to specify a subspace from which to sample the initial state,
*Length* which is an integer that specifies the number of transitions for the generation of the random walk,
and *Attempts* which is the maximal number of random walks that are generated if each time the last state does not belong to an attractor.
Though unlikely, it is possible that the function will not find an attractor in which case it will raise an exception.
Hence, :ref:`find_attractor_by_randomwalk_and_ctl` should always be encapsulated in a *Try-Except* block::

   >>> try:
   ...     state = AD.find_attractor_by_randomwalk_and_ctl(primes, "asynchronous")
   ...     print STGs.state2str(state)
   ... except:
   ...     print "did not find an attractor. try increasing the length or attempts parameters"

Approximations
**************

This section is based on the results published in :ref:`Klarner2015(a) <klarner2015trap>`.
The overall goal is to efficiently compute all attractors of an asynchronous STG.
In particular we are interested in the cyclic attractors of an asynchronous STG
because its steady states are identical to the steady states of synchronous STGs which can already be computed efficiently using SAT solvers,
e.g., the approach suggested in :ref:`Dubrova2011 <Dubrova2011>`.

The idea is based on the observation that the efficiency of computing minimal trap spaces is about as efficient as computing steady states
and using similar techniques, i.e., solvers for 0-1 problems.
Also, trap spaces always contain at least some attractors.
It is therefore try to quanity what "some" means.
This section asks whether

#. the minimal trap spaces are **complete**, i.e., whether every attractor of the given STG is contained in one of its minimal trap spaces
#. each minimal trap space is **univocal**, i.e., whether each minimal trap spaces contains exactly one attractor
#. each minimal trap space is **faithful**, i.e., the number of its free variables is equal to the number of oscillating variables in each of its attractors

In :ref:`Klarner2015(a) <klarner2015trap>` we demonstrate that completeness, univocality and faithfulness can all be decided using CTL model checking.
The functions :ref:`completeness_naive`, :ref:`univocal` and :ref:`faithful` automatically generate and test the respective queries,
which are defined in Sections 4.1, 4.2 and 4.3 of :ref:`Klarner2015(a) <klarner2015trap>`.

As an example of a network whose minimal trap spaces are complete, univocal and faithful
consider again the network defined in :ref:`the figure above <figure25>`.
The functions :ref:`univocal` and :ref:`faithful` each require the primes, update strategy and a trap space.
Since :ref:`univocal` is based on detecting at least one attractor (via the random walk algorithm explained above),
and since a counterexample to the univocality query contains information about additional attractors,
the function returns a triplet consisting of the answer, an attractor state and a counterexample (if the trap space is not univocal),
see :ref:`univocal` for details.
The function :ref:`faithful` returns a tuple that consists of the answer and a counterexample (if it exists), again see :ref:`faithful` for details.
For now we are only interested in printing the answer of each property for each trap space::

   >>> update = "asynchronous"
   >>> mintspaces = TS.trap_spaces(primes, "min")
   >>> for x in mintspaces:
   ...     answer_univocal, _, _ = AD.univocal( primes, update, x )
   ...     answer_faithful, _    = AD.faithful( primes, update, x )
   ...     print "min trap space:", STGs.subspace2str(primes, x)
   ...     print "  is univocal:", answer_univocal
   ...     print "  is faithful:", answer_faithful
   min trap space: -10
     is univocal: True
     is faithful: True
   min trap space: 101
     is univocal: True
     is faithful: True

The naive function for deciding whether a set of trap spaces if complete requires also three arguments, the primes,
the update strategy and a list of trap spaces.
It returns a tuple consisting of the answer and a counterexample, if it exists.
See :ref:`completeness_naive` for details.
     
   >>> answer_complete, _ = AD.completeness_naive( primes, update, mintspaces )
   >>> "min trap spaces are complete:", answer_complete
   min trap spaces are complete: True



As an illustration, consider network (A) given in Figure 1 of :ref:`Klarner2015(a) <klarner2015trap>`.
It is defined by the following functions::



The resulting STG is shown in :ref:`the figure below <figure25>`.


Its STG contains two cyclic attractors and its minimal trap space ``---`` contains two cyclic attractors and it therefore not univocal.

   >>> bnet = ["v1, !v1&!v2&v3 | !v1&v2&!v3 | v1&!v2&!v3 | v1&v2&v3",
   ...         "v2, !v1&!v2&!v3 | !v1&v2&v3 | v1&!v2&v3 | v1&v2&!v3",
   ...         "v3, !v1&!v2&v3 | !v1&v2&!v3 | v1&!v2&!v3 | v1&v2&v3"]
   >>> bnet = "\n".join(bnet)
   >>> primes = FEX.bnet2primes(bnet)
   >>> mintspaces = TS.trap_spaces(primes, "min")
   >>> stg = STGs.primes2stg(primes, "asynchronous")
   >>> mintspaces = TS.trap_spaces(primes, "min")
   >>> print [STGs.subspace2str(primes, x) for x in mintspaces]
        
   >>> STGs.add_style_sccs(stg)
   >>> STGs.add_style_subspaces(primes, stg, mintspaces)


.. _figure26:

.. figure:: figure25.pdf
   :scale: 60%
   :align: center
   
   The state transition graph *"example25_stg.pdf"* in which the minimal trap space "---" is not univocal.
   

   >>> mintspaces = TS.trap_spaces(primes, "min")
   >>> print [STGs.subspace2str(primes, x) for x in mintspaces]
   ['---']
   >>> STGs.add_style_subspaces(stg, mintspaces)
   >>> stg.graph["label"] = "Example 26: An STG whose minimal trap space '---' is not univocal"





.. include:: Substitutions.rst




