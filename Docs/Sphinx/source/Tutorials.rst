



Tutorials
=========

Tutorial A: Getting started
---------------------------

.. _topic:create_a_boolean_network_using_boolnet_files:

create a Boolean network using BoolNet files
********************************************

Currently, the default syntax for specifying Boolean networks is the one defined for *BoolNet*, see :ref:`Müssel2010 <Müssel2010>`.
For each variable of the network there is a line that defines the corresponding update function.
Lines start with the variable name followed by the separator "``,``" and a Boolean expression.
The disjunction, conjunction and negation of expressions are defined by ``|``, ``&`` and ``!``, respectively.
The values of constants are ``0`` and ``1``.
Comments start with a ``#`` symbol.
As an example, save the following lines of text in file called :file:`tutorial_A.bnet`::
   
   # input layer
   v1,   v1
   v2,   0
   v3,   v4
   v4,   v3
   
   # computational layer
   v5,   v1 & v2
   v6,   v2 | !v3
   v7,   !v3
   v8,   v5 & !v10 | !v5 & v10
   v9,   v6 & !v8 | !v7
   v10,  v9 | v4 & !v9 

Note that names must start with a letter and consist of at least two characters if you plan to do model checking.
NuSMV_ keywords, for example ``VAR``, are not admissible names.
You may use white lines to structure the network file.
If conjunction and disjunction are mixed without brackets the usual operator precedence applies: ``!`` binds stronger than ``&`` which binds stronger than ``|``.
With brackets, the expression of ``v8`` would be::

   v8,   (v5 & !(v10)) | (!(v5) & v10)
   
The module that opens and saves network files is called :ref:`FileExchange <sec:FileExchange>`.
Most of what |software| does, including the computation of the interaction graph, requires the *prime implicants* of a network,
see :ref:`Klarner2014 <Klarner2014>` for a definition.
Hence, the first step is usually to convert a network into its prime implicants.
The function that converts *BoolNet* files into prime implicants is called :ref:`bnet2primes <sec:bnet2primes>`.
Example::

   import PyBoolNet as bn
   primes = bn.FileExchange.bnet2primes("tutorial_A.bnet", "tutorial_A.primes")

The function takes two parameters, the input *BoolNet* file and the output *Json* file.
It computes the prime implicants, returns them as a list and saves them as a text file in *Json* format.
Since computing prime implicants may take some time for larger networks, in particular if there are components with high in-degrees, reading a previously saved
*Json* file may be much faster than recomputing prime implicants each time.
To read an existing prime implicant file use :ref:`read_primes <sec:read_primes>` and to save a primes object use :ref:`write_primes <sec:write_primes>`.

.. _topic:basic_operations_on_prime_implicants:

basic operations on prime implicants
************************************

The data type of the returned prime implicants is a nesting of dictionaries and lists.
The top level is a dictionary with a key for every variable of the network.
The values of each name are lists of length two that contains the ``0`` and ``1`` prime implicants, i.e.,
the minimal length logical conjunctions of literals that ensure that the respective Boolean expression evaluates to ``0`` or ``1`` (see :ref:`Klarner2014 <Klarner2014>` for details).
To access the ``1``-prime implicants of ``v6`` use::

   print primes["v6"][1]
   >>> [{"v2": 1}, {"v3": 0}]
   
The returned list shows that there are two prime implicants and each consists of a single literal.
The Boolean expression of ``v6`` therefore evaluates to ``1`` if either ``v2=1`` or ``v3=0``.
To access the ``0``-prime implicants of ``v6`` use::

   print primes["v6"][0]
   >>> [{"v2": 0, "v3": 1}]
   
which states that the expression of ``v6`` evaluates to ``0`` iff ``(v2=0)&(v3=1)`` where ``&`` represents logical conjunction.

Functions that modify the primes of a network, for example to derive knock-in or knock-out variants, are contained in the :ref:`PrimeImplicants <sec:PrimeImplicants>` module.
The functions are designed to treat the primes as an immutable data type, like tuples or strings.
They will create and return new prime implicants objects rather than changing existing primes.

As an example suppose we would like to change the update function of ``v2`` to be constant at ``1`` rather than ``0``.
To do so we use the function :ref:`fix <sec:fix>`::

   p2 = bn.PrimeImplicants.fix(primes, {"v2":1})
   
with the first argument a primes object and the second a dictionary of names and values.
Since :ref:`fix <sec:fix>` does not change ``primes`` we need another name, here ``p2``, to store the modified version of ``primes``.
To test whether two prime implicant objects are equal, use :ref:`is_equal <sec:is_equal>`::

   print bn.PrimeImplicants.is_equal(primes, p2)
   >>> False
   
To create a copy use :ref:`copy <sec:copy>`::

   p3 = bn.PrimeImplicants.copy(primes)
   print bn.PrimeImplicants.is_equal(primes, p3)
   >>> True

The module :ref:`PrimeImplicants <sec:PrimeImplicants>` also contains two functions for selecting the constants and inputs of a network,
namely :ref:`find_inputs <sec:find_inputs>` and :ref:`find_constants <sec:find_constants>`.
The former returns a list of names the latter a dictionary of names and values::

   >>> bn.PrimeImplicants.find_inputs(primes)
   ["v1"]
   >>> bn.PrimeImplicants.find_constants(primes)
   {"v2":0}
   
To create a new network ``p4`` in which all inputs are fixed to the value ``1`` we may therefore use::

   >>> inputs = bn.PrimeImplicants.find_inputs(primes)
   >>> fix = dict([(x,1) for x in inputs])
   >>> p4 = bn.PrimeImplicants.fix(primes, fix)

   

.. _topic:create_a_pdf_of_the_interaction_graph:
create a drawing of the interaction graph
*****************************************

* *Requires* :ref:`Graphviz <sec:installation_graphviz>` *and* :ref:`NetworkX <sec:installation_networkx>`

.. figure:: InteractionGraphs.pdf
   :align: center
   
   Drawing interaction graphs is a four step process.
   (1) The igraph object is computed from a primes object.
   (2) The igraph object is annotated by edge, node and graph attributes.
   (3) The igraph object is used to generate a `dot` file.
   (4) An image, for example a `jpg` or `pdf`, is generated from the `dot` file.

Prime implicants can also be used to derive the **signed interaction graph** of a network.
The algorithm is based on the fact that a variable ``vi`` interacts with a variable ``vj`` if and only if ``vj``
has a prime implicant whose conjunction involves a ``vi`` literal.
The interaction is positive if and only if there is a ``1``-prime with a positive literal ``vi=1`` or a ``0``-prime with a negative literal ``vi=0``.
Similarly, the interaction is negative if and only if there is a ``1``-prime with a negative literal ``vi=0`` or a ``0``-prime with a positive literal ``vi=1``.
For example, since ``{"v2": 1}`` is a ``1``-prime implicant of ``v6`` there is a positive interaction from ``v2`` to ``v6``.
To compute the interaction graph use the function :ref:`primes2igraph <sec:primes2igraph>` of the module :ref:`InteractionGraphs <sec:InteractionGraphs>`.
It returns a directed graph in the NetworkX_ format, i.e., a :py:func:`networkx.DiGraph` object::

   >>> primes = bn.read_primes("tutorial_A.primes")
   >>> igraph = bn.InteractionGraphs.primes2igraph(primes)
   >>> igraph
   <networkx.classes.digraph.DiGraph object at 0xb513efec>
   
NetworkX_ is a python package "for the creation, manipulation, and study of networks".
The nodes and edges of ``igraph`` can be accessed via the NetworkX_ functions :py:func:`edges` and :py:func:`nodes`::

   >>> igraph.nodes()
   ["v10", "v1", "v2", "v3", "v4", "v5", "v6", "v7", "v8", "v9"]
   >>> igraph.edges()
   [("v10", "v8"), ("v1", "v1"), ("v1", "v5"), ("v2", "v5"), ("v2", "v6"), ("v3", "v4"),
   ("v3", "v6"), ("v3", "v7"), ("v4", "v10"), ("v4", "v3"), ("v5", "v8"), ("v6", "v9"),
   ("v7", "v9"), ("v9", "v10")]
   
The sign of an interaction is either ``1`` or ``-1`` or both and implemented as a python set, accessible via the edge attribute with key ``"sign"``.
For details on edge, node and graph attributes of NetworkX_ objects read the NetworkX_ manual.
The sign of the edge ``("v10", "v8")`` is, for example, both positive and negative::

   >>> igraph.edge["v10"]["v8"]["sign"]
   set([1, -1])

To create a drawing of the interaction graph we first create a *dot* file which
contains instructions on how to draw the graph, i.e., its colors, the line widths, shapes, etc.::

   >>> bn.InteractionGraphs.igraph2dot(igraph, "tutorial_a_igraph.dot")
   
and the create a *pdf*, *jpg*, *png* or *svg* file from the *dot* file using :ref:`dot2image <sec:dot2image>`::

   >>> bn.InteractionGraphs.dot2image("tutorial_a_igraph.dot", "tutorial_A_igraph.pdf")
   >>> bn.InteractionGraphs.dot2image("tutorial_a_igraph.dot", "tutorial_A_igraph.jpg")

To go via the *dot* file is useful if you want to inspect how the image was created or modify parts manually.
You can also create the image directly from the igraph via the function :ref:`igraph2image <fig:igraph2image>`::

   >>> bn.InteractionGraphs.igraph2image(igraph, "tutorial_A_igraph.jpg")

The result is an image like the ones shown in the :ref:`figure below<fig:tutorial_a_figure1>`.

Important for the purpose of drawing interaction graphs are node, edge and graph attributes that translate into *dot* commands.
The *dot* language supports the definition of defaults as well as setting attributes of specific nodes or edges.
For a list of attributes see for example http://www.graphviz.org/doc/info/attrs.html.
Basic node attributes are:

   * **shape**:
      sets the shape of the node, for example ``rect, square, circle, plaintext, triangle, star, lpromoter, rpromoter``
      
   * **label**:
      changes the label of a node, default is the variable name
   
   * **style**:
      the style ``filled`` is required if you want to fill nodes with a color
   
   * **fillcolor**:
      sets the fill color, requires the ``style`` to be set to ``filled``
      
   * **color**:
      sets the stroke color
      
   * **fontcolor**:
      sets the color of the label text
      
   * **fontsize**:
      sets the font size, for example ``5,10,15``
      
   * **fixedwidth**:
      specifies whether node shape has a fixed width, either ``true`` or ``false``
      
   * **width**:
      sets the node width, for example ``5,10,15``
      
Colors can be set by names like ``red, green`` or ``blue``,
or by space-separated HSV values, e.g. ``0.1 0.2 1.0``,
or by a RGB value, e.g ``#40e0d0``.
For a list of predefined color names see for example http://www.graphviz.org/doc/info/colors.html.

The basic edge attributes are:

   * **arrowhead**: sets the shape of the arrow, for example ``dot, tee, normal``
   
   * **arrowsize**: sets the size of the arrow, for example ``5,10,15``
   
   * **style**: sets the pen style of the edge, for example ``dotted, dashed``.
   
   * **color**: sets the edge color
   
   * **label**: adds a label to an edge
   
   * **penwidth** (default ``1``): sets the width of an edge, for example ``5,10,15``
   
   * **constraint** (default ``true``): whether the edge should be included in the calculation of the layout (node positions), either ``true`` or ``false``
   
   * **weight** (default ``1``): sets the cost for stretching the edge during layout computation, for example ``5,10,15``

Node and edge attributes can either be set globally, i.e., as defaults, by adding them as graph attributes to an interaction graph::

   >>> igraph.graph["node"]["shape"] = "square"
   >>> igraph.graph["edge"]["penwidth"] = "12"
   
or for specific nodes or edges which overwrite the defaults::

   >>> igraph.node["v6"]["shape"] = "circle"
   >>> igraph.edge["v10"]["v8"]["penwidth"] = "8"
   
In addition to node and edge attributes there are general graph attributes, for example:

   * **splines**: sets how edges are drawn, for example ``line, curved`` or ``ortho`` for orthogonal edges
   
   * **label**: adds a label to the graph
   
   * **rankdir**: sets the direction in which layout is constructed, default is from top to bottom (``TB``), other values are ``LR, RL, BT``
 
As an example consider the following statements and the resulting graph in the :ref:`figure below<fig:tutorial_a_figure1>`::

   >>> g1 = igraph.copy()
   >>> g1.graph["splines"] = "ortho"
   >>> g1.graph["label"] = "tutorial_A_g1.pdf"
   >>> g1.graph["rankdir"] = "BT"
   >>> g1.graph["node"]["shape"] = "circle"
   >>> g1.node["v1"]["shape"] = "star"
   >>> g1.node["v2"]["fontsize"] = "20"
   >>> g1.node["v3"]["penwidth"] = "3"
   >>> g1.node["v9"]["shape"] = "rpromoter"
   >>> g1.node["v9"]["fillcolor"] = "lightblue"
   >>> g1.edge["v8"]["v9"]["label"] = "uncertain"
   >>> g1.edge["v8"]["v9"]["style"] = "dashed"
   >>> for i in range(1,6):
        g1.node["v%i"%i]["fillcolor"] = "/accent5/%i"%i
        g1.node["v%i"%i]["color"] = "gold"
        g1.node["v%i"%i]["penwidth"] = "4"
   >>> bn.InteractionGraphs.igraph2image(g1, "tutorial_A_g1.pdf")
 
The module :ref:`InteractionGraphs <sec:InteractionGraphs>` contains three functions for setting frequently used combinations of attributes.
The first one, :ref:`add_style_interactionsigns <sec:add_style_interactionsigns>`,
sets the color and arrowhead of each edge according to whether the interaction is activating, inhibiting or both::

   >>> g2 = bn.InteractionGraphs.add_style_interactionsigns(igraph)
   >>> g2.graph["label"] = "tutorial_A_signs.pdf"
   >>> bn.InteractionGraphs.igraph2image(g2, "tutorial_A_signs.pdf")
   
The second one, :ref:`add_style_activities <sec:add_style_activities>`, colors nodes according to a given dictionary of activities::

   >>> activities = {"v1":0,"v2":1,"v7":1,"v8":0}
   >>> g3 = bn.InteractionGraphs.add_style_activities(igraph, activities)
   >>> g3.graph["label"] = "tutorial_A_activities.pdf"
   >>> bn.InteractionGraphs.igraph2image(g3, "tutorial_A_activities.pdf")
   
where activated nodes are shown in red and inhibited ones in blue.
Edges involving activated or inhibited nodes are not considered during the computation of the layout.
The third is called :ref:`add_style_sccs <sec:add_style_sccs>` and combines the interaction signs with different colors for the SCCs:

   >>> g4 = bn.InteractionGraphs.add_style_sccs(igraph)
   >>> g4.graph["label"] = "tutorial_A_sccs.pdf"
   >>> bn.InteractionGraphs.igraph2image(g4, "tutorial_A_sccs.pdf")
   
The four different interaction graph are shown in the :ref:`figure below<fig:tutorial_a_figure1>`.

.. _fig:tutorial_a_figure1:

.. figure:: tutorial_A_figure1_cropped.pdf
   :scale: 150%
   :align: center
   
   The differently styled interaction graphs of the above examples.
   (1) The default: filled rectangles.
   (2) Interactions styled according to their signs: activating interactions are black, inhibitions red and interactions that are both are blue.
   (3) The style for visualizing activities: activated components are red, inhibited components blue, interactions that involve activated or inhibited components
   are grayed out to emphasize that they are ineffective.
   (4) The style for visualizing the strongly connected components as gray boxes.
   The brightness of a SCC indicates how many SCCs are above it (its depth in the SCC hierarchy) where input SCCs are lightest.





Tutorial B: Model Checking
--------------------------

.. _topic:import_a_boolean_network_from_ginsim:
import a Boolean network from GINsim
************************************

* *Requires* :ref:`GINsim <sec:installation_ginsim>` *and the* :ref:`R package BoolNet <sec:installation_boolnet>`
   
   
As an example consider the MAPK network of :ref:`Grieco2013 <Grieco2013>`.
The full model and three reduced versions are available from the GINsim_ model repository.
For efficiency, let us work with the reduced model `MAPK_red3_19062013.zginml`. 
Download the file `MAPK_red3_19062013.zginml` from the repository at http://ginsim.org/node/173 and open it with GINsim_.
Generate a `sbml` file from the model by clicking::

   File > Export > SBML-qual > run

Now open R_, load the library BoolNet_, import the `sbml` network file and generate a `bnet` file::

   $ R
   > library(BoolNet)
   > net = loadSBML("MAPK_red3_19062013.sbml")
   > saveNetwork(net, "MAPK_red3_19062013.bnet")

From here we follow the steps of the previous tutorial to create a `primes` object and text file::

   >>> primes = bn.PrimeImplicants.bnet2primes("MAPK_red3_19062013.bnet", "MAPK_red3_19062013.primes")
   
   
.. _topic:decide_whether_a_CTL_or_LTL_query_holds:
decide whether a CTL or LTL query holds
***************************************

* *Requires* :ref:`NuSMV <sec:installation_nusmv>`

The main function for interfacing the model checking software NuSMV_ is :ref:`check_primes <sec:check_primes>` of the module :ref:`ModelChecking <sec:ModelChecking>`.
It generates the `smv` file contents from a `primes` object and pipes them directly to NuSMV_ without generating a `smv` file.
:ref:`check_primes <sec:check_primes>` takes three arguments for specifying the state transition graph:

* **Update**: the update strategy, either ``synchronous``, ``asynchronous`` or ``mixed``, which allows any number of variables to update during a transition (but at least one),
* **InitialStates**: a description of the initial states in NuSMV_ syntax for Boolean variables and including the special keyword ``INIT``, example: ``INIT v1&!v2``.
* **Specification**: a CTL or LTL formula in NuSMV_ syntax and including one of the special keywords ``CTLSPEC`` or ``LTLSPEC``, example: ``LTLSPEC F(G(!v1&!v2))``.

and two arguments for additional features that are discussed in the sections after this one:

* **DisableCounterExamples**: A Boolean that controls the counterexample plugin (default: *True*)
* **TransitionCounterMax**: An integer that controls whether the length of trajectories should be included in the transition system. The defaul is *0* which means that the counter is disabled.
   
To formulate a query, consider first the interaction graph in the :ref:`figure below<fig:tutorial_b_figure1>` which was generated by::

   >>> igraph = bn.InteractionGraphs.primes2igraph(primes)
   >>> g1 = bn.InteractionGraphs.add_style_sccs(igraph)
   >>> g1.graph["label"] = "mapk.pdf"
   >>> bn.InteractionGraphs.igraph2image(g1, "mapk.pdf")

.. _fig:tutorial_b_figure1:

.. figure:: tutorial_B_figure1.pdf
   :scale: 100%
   :align: center
   
   The interaction graph of the reduced MAPK network. There are four inputs, three of them growth factors and one representing DNA damage,
   and one SCC consisting of nine variables. 
   
It consists of four inputs of which three are growth factors and one represents DNA damage, a SCC of nine variables and three output variables
that represent growth arrest, apoptosis and cell proliferation.
As an example query, consider the property "If DNA is damaged then the cell can induce apoptosis or growth arrest."
We formalize it in terms of initial states and CTL as follows::

   >>> init = "INIT DNA_damage"
   >>> spec = "CTLSPEC EF(Growth_Arrest | Apoptosis)"

To check whether it holds in the asynchronous state transition graph we use::

   >>> update = "asynchronous"
   >>> bn.ModelChecking.check_primes(primes, update, init, spec)
   True

The other two currently implemented update strategies are ``synchronous`` and ``mixed``, see :ref:`check_primes <sec:check_primes>` for details.
Note that it makes a difference whether we formulate this property as CTL or LTL::

   >>> spec = "LTLSPEC F(Growth_Arrest | Apoptosis)"
   >>> bn.ModelChecking.check_primes(primes, update, init, spec)
   False
   
The difference between the two queries is that in CTL we are asking "Is there a path from every initial state to a goal state?" (*true*)
and in LTL we ask "Do all paths that start with an initial state eventually reach a goal state?" (*false*).
For a textbook on model checking with CTL and LTL see for example :ref:`[Baier2008] <Baier2008>`.

.. _topic:counterexamples:
inspect counterexamples
***********************

* *Requires* :ref:`NuSMV <sec:installation_nusmv>`, :ref:`Graphviz <sec:installation_graphviz>` and :ref:`ImageMagick <sec:installation_imagemagick>`

If a query is false we can switch the counterexample plugin on via the NuSMV_ option `DisableCounterExamples`.
In that case the function :ref:`check_primes <sec:check_primes>` returns a tuple ``(answer, counterex)`` where ``answer`` states whether the query holds and
``counterex`` is a sequence of states that disproves the query.
Note that LTL counterexamples must end in a loop, i.e., in a sequence of repeating states,
while CTL counterexamples do not (see :ref:`[Baier2008] <Baier2008>` and :ref:`[Clarke2002] <Clarke2002>`).
To inspect the counterexample to the above LTL property use::

   >>> answer, counterex = bn.ModelChecking.check_primes(primes, update, init, spec, False)
   >>> for state in counterex:
         print bn.StateTransitionGraphs.state2str(state)
      0101001000000010
      0101001001000010
      0101001000000010   

Note that the counterexample you find might be a different one.
The function :ref:`state2str <sec:state2str>` of the module :ref:`StateTransitionGraphs <sec:StateTransitionGraphs>` turns a state dictionary into a string of activities, sorted by the names of the variables.
The counterexample consists of three states and is a single loop because the first and last states are identical.
To retrieve the name of the variable that changes use for example::

   >>> changing = [x for x in counterex[0] if counterex[0][x]!=counterex[1][x]]
   >>> print changing
   ["MDM2"]
   
A look at the interaction graph in the :ref:`figure above<fig:tutorial_b_figure1>` shows that there is a self-inhibition on the component ``MDM2`` which
is a requirement for such a behavior.

An alternative method of inspecting the counterexample is to generate an image for every state of the sequence with the nodes colored according to the activities::

   >>> igraph = bn.InteractionGraphs.primes2igraph(primes)
   >>> for i, state in enumerate(counterex):
      dummy = bn.InteractionGraphs.add_style_activities(igraph, state)
      dummy.graph["label"] = "Counterexample - State %i"%i
      bn.InteractionGraphs.igraph2image(dummy, "counterex%i.jpg"%i)
      
The result can be seen in the :ref:`figure below<fig:tutorial_b_figure2>`.       
      
.. _fig:tutorial_b_figure2:

.. figure:: tutorial_B_figure2_cropped.pdf
   :scale: 150%
   :align: center
   
   The three states of the counterexample to the specification ``"LTLSPEC F(Growth_Arrest | Apoptosis)"``.
      

Finally, it is also possible to create an animated *gif* with the function :ref:`states2animation <sec:states2animation>`
of the module :ref:`StateTransitionGraphs <sec:StateTransitionGraphs>`::

   >>> bn.StateTransitionGraphs.states2animation(primes, counterex, "animation.gif")
   
By default the animation loops forever at two frames a second, see :ref:`states2animation <sec:states2animation>` for additional parameters.

   
.. _topic:use_auxillary_variables:
use auxillary variables
***********************

* *Requires* :ref:`NuSMV <sec:installation_nusmv>`

Model checking queries are decided on transition systems that are defined in the *smv* format and derived from a *primes* object.
LTL and CTL formulas are built on atomic propositions involving the activities of the Boolean components::

   >>> spec = "CTLSPEC EF(GRB2 | !ERK xor RAS -> !JNK)"
   
   

In addition, the function :ref:`primes2smv <sec:primes2smv>` that generates the *smv* transition system introduces several auxillary variables:

   * **<name>_IMAGE** (bool):       where ``<name>`` is the name of a variable is the value of the update function of ``<name>``, example: ``ERK_IMAGE``.
   * **<name>_STEADY** (bool):      indicates whether the variable ``<name>`` is steady, example: ``ERK_STEADY``.
   * **STEADYSTATE** (bool):        indicates whether the current state is a steady state, example: ``CTLSPEC EF(STEADYSTATE & !ERK)``
   * **VARIABLESCHANGING** (int):   the number of variables whose update funcation are not equal to their current activities, example: ``LTLSPEC G(VARIABLESCHANGING<=2)``.


To find out whether a steady state can be reached for every DNA damage state, we formulate and check the property::

   >>> init = "INIT DNA_damage"
   >>> spec = "CTLSPEC EF(STEADYSTATE)"
   >>> bn.ModelChecking.check_primes(primes, update, init, spec)
   False
   
The negative answer tells us that there is an initial state that does not satisfy ``EF(STEADYSTATE)`` and so all attractors reachable from it are cyclic attractors.
Since this may be the case for all initial states we do not yet know whether a steady state is reachable from any DNA damage state.
To find out we query the negation::

   >>> spec = "CTLSPEC !EF(STEADYSTATE)"
   >>> bn.ModelChecking.check_primes(primes, update, init, spec)
   False

Since the answer is *False* there must be an initial state that does not satisfy ``!EF(STEADYSTATE)``, i.e., it satisfies ``EF(STEADYSTATE)`` and so there must be at least one steady state.

.. note::
   A formula *phi* and its negation *not phi* may be false *at the same time* if the initial condition defines more than one state.
   This holds of CTL and LTL formulas.

Rather than asking whether all variables will eventually be steady, we may ask whether a particular variable is steady when an attractor is reached,
using the ``AG(EF(AG(..)))`` pattern::

   >>> spec = "CTLSPEC AG(EF(AG(p38_STEADY)))"
   >>> bn.ModelChecking.check_primes(primes, update, init, spec)
   True

The positive answer tells us that *p38* is steady in all attractors reachable from a state with DNA damage.
   
.. note:: The pattern we use to decide whether a formula *phi* holds *in every attractor state* depends on the initial condition.
   If the initial condition defines a *trap set* then the shorter ``EF(AG(phi))`` pattern is sufficient, otherwise the longer ``AG(EF(AG(phi)))`` pattern is necessary.
   Since ``INIT DNA_damage`` does in fact define a trap set we could also use ``EF(AG(p38_STEADY))`` in the example above.
   If you are not sure about trap sets use the ``AG(EF(AG(phi)))`` pattern or find out whether an initial condition *psi* defines a trap set by the query
   ``INIT psi`` with ``CTLSPEC AG(psi)`` or, equivalently, ``LTLSPEC G(psi)``.

Such queries about attractors may, for example, be relevant to check the behavior of "output variables".
These types of variables are expected to describe the response of a network to certain stimuli after the information was processed in intermediate signaling layers.
The MAPK network, for example, has three output variables: *Proliferation*, *Growth Arrest* and *Apoptosis*.
It is easier to interpret the response of a network to stimuli if the output variables are steady in all attractors, which is true for the MAPK model::

   >>> condition1 = "Growth_Arrest_STEADY & Apoptosis_STEADY & Proliferation_STEADY"
   >>> spec = "CTLSPEC AG(EF(AG( %s )))"%condition1
   >>> bn.ModelChecking.check_primes(primes, update, init, spec)
   True
   
We may add similar sanity checks, like "Is the value of *Apoptosis* equal to the negation of *Proliferation* in every attractor?", i.e.,
an attractor may be harder to interpret if *Apoptosis* and *Proliferation* are both active and the cell therefore proliferating and undergoing apoptosis the same time.
Again, the MAPK model satisfies this condition::

   >>> condition2 = "Proliferation <-> !Apoptosis"
   >>> spec = "CTLSPEC AG(EF(AG( %s )))"%condition2
   >>> bn.ModelChecking.check_primes(primes, update, init, spec)
   True
   
Further examples of queries are::

   >>> spec = "CTLSPEC AG(EF(AG( VARIABLESCHANGING<=3 )))"
   >>> bn.ModelChecking.check_primes(primes, update, init, spec)
   True
   
which states that at most three variables are unsteady in all attractor states, and::

   >>> condition3 = "count(!ERK_STEADY, !PI3K_STEADY, !MDM2_STEADY, !RAS_STEADY)<=1"
   >>> spec = "CTLSPEC AG(EF(AG( %s )))"%condition3
   >>> bn.ModelChecking.check_primes(primes, update, init, spec)
   True
   
which states that at most one of *ERK*, *PI3K*, *MDM2* and *RAS* are unsteady in a given attractor state. 

Note that counterexample inspection may, for example, be used to animate a path from a DNA damage state to a steady state::

   >>> spec = "CTLSPEC AG(!STEADYSTATE)"
   >>> answer, counterex = bn.ModelChecking(primes, update, init, spec, DisableCounterExamples=False)
   >>> bn.StateTransitionGraphs.states2animation(primes, counterex, "steadystate.gif")


.. _topic:use_the_transition_counter:
use the transition counter
**************************

The function :ref:`check_primes <sec:check_primes>` has a parameter called *TransitionCountMax*
that enables the generation of a variable called ``TRANSITIONCOUNT`` in the *smv* file.
It is an integer variable that increases during every transition except for self-loops on steady states
until its value reaches *TransitionCountMax+1* at which point it remains constant,
indicating that "more than *TransitionCountMax* transitions were required to get to the current state".

The inclusion of this variable in the transition system is costly as it generates up to *TransitionCounterMax+1* many copies of the original transition system.
But, it also increases the expressibility of queries by allowing statements about the **length of a path**.
It should be set to the highest value occuring in the spec.

For the following query we are interested in the existence of an initial state rather than the default "all initial states satisfy" queries.

.. note:: Since NuSMV_ is designed for "all initial states satisfy" type queries we need to translate queries about the existence of initial states
   into queries for all initial state.
   The two types of statements are related by the equivalence "there is an initial state that satisfies *phi*" iff "not all initial states satisfy *not phi*".

To find out if there is an intial state that satisfies::

   >>> init = "INIT DNA_damage & PLCG & MDM2 & ERK & !JNK"
   
and from which a steady state can be reached within three transitions, we query::

   >>> spec = "CTLSPEC !EF( STEADYSTATE & TRANSITIONCOUNT<=3 )"
   >>> answer, counterex = bn.ModelChecking.check_primes(primes, update, init, spec, False, 3)
   >>> answer
   True

Since the answer is *true* we deduce, by the note above, that there is no initial state that can reach a steady state within three transitions.
Note that the parameter *TransitionCountMax* of :ref:`check_primes <sec:check_primes>` is set to 3, the highest value occuring in the CTL formula.
In the transition system it may therefore also take the value 4 which represents "more than three transitions".

Maybe there is a path path that consists of four transitions?::

   >>> spec = "CTLSPEC !EF( STEADYSTATE & TRANSITIONCOUNT<=4 )"
   >>> answer, counterex = bn.ModelChecking.check_primes(primes, update, init, spec, False, 4)
   >>> answer
   False

The answer is *false* and we deduce that there is a path to a steady state in four transitions, and the counterexample is such a path.
The option *TransitionCounterMax* and corresponding variable ``TRANSITIONCOUNT`` may therefore be used to retrieve **shortest paths** by repeated querying.
It may also be used to retrieve long paths::

   >>> spec = "CTLSPEC !EF( STEADYSTATE & TRANSITIONCOUNT>=100 )"
   >>> answer, counterex = bn.ModelChecking.check_primes(primes, update, init, spec, False, 100)
   >>> answer
   False
   >>> len(counterex)
   101

Note that there may not be a longest path for a given property due to potential cycles in the transition system.


use query patterns
******************

* AGEF_subspaces
* EF_subspaces
* EF_unsteady



Tutorial C: Attractor Detection
-------------------------------
define a Boolean network with Python functions
**********************************************

* *Requires* :ref:`NuSMV <sec:installation_nusmv>`, :ref:`Graphviz <sec:installation_graphviz>` and :ref:`ImageMagick <sec:installation_imagemagick>`

The third way of defining a Boolean network is by creating a Python function for every variable.
It allows the use of arithmetic and to express the conditions under which variables are activated or inhibited.
Suppose, for example, that a gene *v1* is regulated by four transcription factors *v2,...,v5* and that *v1* is activated iff two or more of them are present.
It is tedious to express such a condition in terms of Boolean logic but easy using Python::

   >>> f1 = lambda v2,v3,v4,v5: sum([v2,v3,v4,v5])>=2
   
Note that we may use *True* and *False* synonymously for 1 and 0, a feature of Python's typecasting::

   >>> f1(False, True, True, False)
   True
   >>> f1(0,1,1,0)
   True

The lambda construct is convenient for single line definitions, more complex functions may be defined using the standard ``def`` block::

   >>> def f2(v1,v2,v3):
      if f1(v2,v3,0,0):
         return 0
      else:
         return sum([v1,v2,v3]) % 2
         
The definition of *f2* involves the variables *v1,v2,v3* and *f1*: it returns 0 if ``f1(v2,v3,0,0)`` is 1 and otherwise ``v1+v2+v3 mod 2``.
Note that *f2* returns 1 and 0 instead of *True* and *False*.
Let us also define *f3*, *f4* and *f5*::

   >>> f3 = lambda v4,v5: not (v4 and not v5)
   >>> f4 = lambda v1,v4: not f3(v1,v4)
   >>> f5 = lambda v1,v3,v5 : 1
   
*f3* is defined in terms of Python logic, *f4* is the negation of *f3* and *f5* is constant.
To generate a primes object from the update functions use the function :ref:`functions2primes <sec:functions2primes>`
of the module :ref:`QuineMcClusky <sec:QuineMcCluskey>`. Its argument is a dictionary with the names of the variables as keys and the functions as values::

   >>> funcs = {"v1":f1, "v2":f2, "v3":f3, "v4":f4, "v5":f5}
   >>> primes = bn.QuineMcCluskey.functions2primes(funcs)
   >>> primes["v1"][1]
   ((v4 & v3) | (v5 & v3) | (v5 & v4) | (v5 & v2) | (v4 & v2) | (v3 & v2))
   
You may use the argument *FnamePRIMES* or the function :ref:`write_primes <sec:write_primes>` of the module :ref:`FileExchange <sec:FileExchange>`
to create a *json* file for the primes object::

   >>> primes = bn.QuineMcClusky.functions2primes(funcs, "five.primes")
   >>> bn.FileExchange.write_primes(primes, "five.primes")


create a drawing of the state transition graph
**********************************************

* *Requires* :ref:`Graphviz <sec:installation_graphviz>`

To create a drawing of the **state transition graph** (STG) we use a similar approach as to drawing the interaction graph,
see the :ref:`section above <topic:create_a_pdf_of_the_interaction_graph>`.
The function :ref:`primes2stg <sec:primes2stg>` creates a *networkx digraph* of the transition system defined by a primes object,
a transition rule (currently *synchronous* or *asynchronous*) and *InitialStateFunction*, a Boolean function that flags state dictionaries as initial states.
By default it returns *True* for every state and the function will therefore create the full state transition graph::

   >>> update = "asynchronous"
   >>> stg = bn.StateTransitionGraphs.primes2stg(primes, update)
   
As for interaction graphs, there is a function :ref:`stg2dot <sec:stg2dot>` that creates a *dot* file from an STG object and a corresponding function
:ref:`dot2image <sec:dot2image>` that generates an image from a *dot* file.
Also, there is a function :ref:`stg2image <sec:stg2image>` that creates and image straight from a STG without creating an intermediate *dot* file::
   
   >>> stg.graph["label"] = "five_stg.pdf"
   >>> bn.StateTransitionGraphs.stg2image(stg, "five_stg.pdf")
   
The result can be seen in the :ref:`figure below<fig:tutorial_c_figure1>`.       
A STG can be styled in the same way as an interaction graph (see :ref:`previous section <topic:create_a_pdf_of_the_interaction_graph>`).
To shortcut functions for frequent attributes are provided.
The first one is called :ref:`add_style_tendencies <sec:add_style_tendencies>` and colors the transitions according to the following rule:
if all variables that change decrease the color of the transition is *red*,
if all variables increase it is green and otherwise (only possible for synchronous update) it remains *black*.


   >>> stg2 = bn.StateTransitionGraphs.add_style_tendencies(stg)
   >>> stg2.graph["label"] = "five_stg_tendencies.pdf"
   >>> bn.StateTransitionGraphs.stg2image(stg2, "five_stg_tendencies.pdf")
   
The result can be seen in the :ref:`figure below<fig:tutorial_c_figure1>`.
The second one is called :ref:`add_style_sccs <sec:add_style_sccs>` and is similar to the SCC style for interaction graphs.
It gathers states that form a SCC in a subgraph whose background color indicates the depth in the SCC hierarchy::

   >>> stg3 = bn.StateTransitionGraphs.add_style_sccs(stg)
   >>> stg3.graph["label"] = "five_stg_sccs.pdf"
   >>> bn.StateTransitionGraphs.stg2image(stg3, "five_stg_sccs.pdf")

The result can be seen in the :ref:`figure below<fig:tutorial_c_figure2>`.

.. _fig:tutorial_c_figure1:

.. figure:: tutorial_C_figure1_cropped.pdf
   :scale: 150%
   :align: center
   
   The asynchronous STG of the five variable system defined by Python functions *f1,...,f5* and
   the same transition graph with edges colored green if the changing variable
   increases, red if it decreases and black otherwise, i.e., if it is a self-loop on a steady state.

.. _fig:tutorial_c_figure2:

.. figure:: tutorial_C_figure2.pdf
   :scale: 100%
   :align: center
   
   The asynchronous STG of the five variable system defined by Python functions *f1,...,f5* with
   the edges colored according to whether the transition is increasing or decreasing.
   SCCs are highlighted by gray boxes whose color indicates the *depth* in the SCC hierarchy.
    


compute trap spaces
*******************

* *Requires* :ref:`Potassco <sec:installation_potassco>`

A **trap space** is a subspace of state space that no trajectory can leave and so trap spaces are relevant for the prediction of the attractors of a network.
They generalize the notion of steady states from single states to whole subspaces and like steady states they are independent of the update strategy.
They can be computed efficiently for networks with hundreds of variables using the Potassco_ ASP solver clasp_, see :ref:`[Klarner2015(a)] <sec:klarner2015trap>`.

To compute trap spaces use the function :ref:`trap_spaces <sec:trap_spaces>` of the module :ref:`TrapSpaces <sec:TrapSpaces>`
with the argument ``min`` for minimal and ``max`` for maximal trap spaces::

   >>> mints = bn.TrapSpaces.trap_spaces(primes, "min")
   >>> maxts = bn.TrapSpaces.trap_spaces(primes, "max")  



bounds on the size of trap spaces
*********************************

* *Requires* :ref:`Potassco <sec:installation_potassco>`





projected trap spaces
*********************

* *Requires* :ref:`Potassco <sec:installation_potassco>`


completeness, univocality and faithfulness
******************************************

* *Requires* :ref:`NuSMV <sec:installation_nusmv>`, :ref:`Graphviz <sec:installation_graphviz>` and :ref:`ImageMagick <sec:installation_imagemagick>`


refinement-based attractor detection
************************************

* *Requires* :ref:`NuSMV <sec:installation_nusmv>`, :ref:`Graphviz <sec:installation_graphviz>` and :ref:`ImageMagick <sec:installation_imagemagick>`

















.. include:: Substitutions.rst
