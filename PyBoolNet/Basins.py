

import os
import sys
import itertools
import math
import random
import operator
import functools
import networkx

BASE = os.path.normpath(os.path.abspath(os.path.join(os.path.dirname(__file__))))
sys.path.append(BASE)

import PyBoolNet.FileExchange
import PyBoolNet.ModelChecking
import PyBoolNet.TemporalLogic
import PyBoolNet.AspSolver
import PyBoolNet.Attractors
import PyBoolNet.StateTransitionGraphs
import PyBoolNet.InteractionGraphs
import PyBoolNet.PrimeImplicants
import PyBoolNet.Utility

config = PyBoolNet.Utility.Misc.myconfigparser.SafeConfigParser()
config.read(os.path.join(BASE, "Dependencies", "settings.cfg"))
CMD_DOT = os.path.join(BASE, "Dependencies", config.get("Executables", "dot"))


perc2str = PyBoolNet.Utility.Misc.perc2str


def weak_basin(Primes, Update, Minimize, Attractor):
	"""
	todo: finish code
	todo: add unit tests

	computes a single strong basin

	  **arguments**:
		* *Primes*: prime implicants
		* *<arg>* (<type>): <description>

	  **returns**:
		* *<arg>* (<type>): <description>

	  **example**::

		>>> (..)
		<result>
	"""

	return _basin_handle(Primes, Update, Minimize, Attractor, CTLpattern="CTLSPEC EF(%s)")


def strong_basin(Primes, Update, Minimize, Attractor):
	"""
	todo: finish code
	todo: add unit tests

	computes a single strong basin

	  **arguments**:
		* *Primes*: prime implicants
		* *<arg>* (<type>): <description>

	  **returns**:
		* *<arg>* (<type>): <description>

	  **example**::

		>>> (..)
		<result>
	"""

	return _basin_handle(Primes, Update, Minimize, Attractor, CTLpattern="CTLSPEC AG(EF(%s))")


def cycfree_basin(Primes, Update, Minimize, Attractor):
	"""
	todo: finish code
	todo: add unit tests

	computes a single cycle-free basin

	  **arguments**:
		* *Primes*: prime implicants
		* *<arg>* (<type>): <description>

	  **returns**:
		* *<arg>* (<type>): <description>

	  **example**::

		>>> (..)
		<result>
	"""

	return _basin_handle(Primes, Update, Minimize, Attractor, CTLpattern="CTLSPEC AF(%s)")


def _basin_handle(Primes, Update, Minimize, Attractor, CTLpattern):
	"""
	todo: finish code
	todo: add unit tests

	<description>

	  **arguments**:
		* *Primes*: prime implicants
		* *Attractor* (str / dict): a subspace

	  **returns**:
		* *<arg>* (<type>): <description>

	  **example**::

		>>> (..)
		<result>
	"""

	prop = PyBoolNet.TemporalLogic.subspace2proposition(Primes,Attractor)
	init = "INIT TRUE"
	spec = CTLpattern%prop
	ans, acc = PyBoolNet.ModelChecking.check_primes_with_acceptingstates(Primes,Update,init,spec)

	size = acc["INITACCEPTING_SIZE"]
	formula = acc["INITACCEPTING"]

	if Minimize and formula not in ["TRUE","FALSE"]:
		formula = PyBoolNet.BooleanLogic.minimize_espresso(formula)

	size_total = PyBoolNet.PrimeImplicants.size_state_space(Primes, Type="total")

	return {"size":	size,
			"formula": formula,
			"perc":	100.* size / size_total}


def _default_basin(Primes):
	"""
	todo: add unit tests

	<description>

	  **arguments**:
		* *Primes*: prime implicants
		* *<arg>* (<type>): <description>

	  **returns**:
		* *<arg>* (<type>): <description>

	  **example**::

		>>> (..)
		<result>
	"""

	size_total = PyBoolNet.PrimeImplicants.size_state_space(Primes, Type="total")

	return {"size":	size_total,
			"formula": "TRUE",
			"perc":	100.}


def all_basins(Primes, Update, FnameImage=None, Attractors=None, Minimize=False, Title=None, Silent=True):
	"""
	todo: proof read docstring

	Uses model checking with accepting states to compute the three types of basins of attraction for each attractor.
	*Attractors* may be used to specify a list of representative states for the attractors.
	Otherwise the basins of the minimal trap spaces is returned.
	Use *FnameImage* to create a bar plot, this requires https://matplotlib.org.
	The basins are returned in the form of a dictionary::

		* '01100--0': (str of attractor representantion)
			* 'weak'
				* 'formula': '(!Erk & !Mek)' (Boolean expression for states)
				* 'perc':	0.5			 (percentage of state space)
				* 'size':	8			   (number of states)
			* 'strong'
				...
			* 'cycfree'
				...

	**arguments**:
		* *Primes*: prime implicants
		* *Update* (str): the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
		* *Attractors* (list): list of states or subspaces representing the attractors. *None* results in the computation of the minimal trap spaces.
		* *Minimize* (bool): minimize the resulting expressions
		* *FnameImage* (str): file name of bar chart of weak basins
		* *Title* (str): optional title of plot
		* *Silent* (bool): print infos to screen

	**returns**::
		* *Basins* (dict): the basins of attraction

	**example**::

		>>> primes = Repository.get_primes("raf")
		>>> all_basins(primes, "asynchronous")
			{   '001': {'weak': {'formula': '(!Erk & !Raf) | (!Mek)', 'perc': 62.5, 'size': 5L},...},
				'11-': {'weak': {'formula': '(Mek) | (Erk)', 'perc': 75.0, 'size': 6L}},...}}
	"""

	if not Attractors:
		Attractors = PyBoolNet.AspSolver.trap_spaces(Primes,"min")

	weak = {}
	strong = {}
	cycfree = {}


	if not Silent:
		print("all_basins(..)")

	for x in Attractors:
		if not Silent:
			print(" working on attractor %s"%PyBoolNet.StateTransitionGraphs.subspace2str(Primes,x))

		label = PyBoolNet.StateTransitionGraphs.subspace2str(Primes,x)

		# weak basin
		if len(Attractors) == 1:
			label = PyBoolNet.StateTransitionGraphs.subspace2str(Primes,Attractors[0])
			weak[label] = _default_basin(Primes)
		else:
			weak[label] = weak_basin(Primes, Update, Minimize, Attractor=x)

		# strong basin
		if len(Attractors) == 1:
			label = PyBoolNet.StateTransitionGraphs.subspace2str(Primes,Attractors[0])
			strong[label] = _default_basin(Primes)

		else:
			strong[label] = strong_basin(Primes, Update, Minimize, Attractor=x)

		# cycle-free basin
		cycfree[label] = cycfree_basin(Primes, Update, Minimize, Attractor=x)

	if FnameImage:
		try:
			import matplotlib.pyplot
			success = True

		except ImportError:
			print("ERROR: can not import matplotlib.pyplot")
			success = False

		if success:

			figure = matplotlib.pyplot.figure()

			labels = sorted(weak, key=lambda x: weak[x]["perc"], reverse=True)



			y1 = [cycfree[x]["perc"] for x in labels]
			y2 = [strong[x]["perc"]-cycfree[x]["perc"] for x in labels]
			y3 = [weak[x]["perc"]-strong[x]["perc"] for x in labels]

			N = len(y1)
			x = range(N)
			width = 1/1.5

			h3 = matplotlib.pyplot.bar(x, y1, width, color="black", align='center', label='cycle-free')
			h2 = matplotlib.pyplot.bar(x, y2, width, bottom=y1, color="gray", align='center', label='strong')
			h1 = matplotlib.pyplot.bar(x, y3, width, bottom=[sum(x) for x in zip(y1,y2)], color="lightgrey", align='center', label='weak')
			matplotlib.pyplot.xticks(range(len(labels)), labels, rotation=40, ha="right")
			matplotlib.pyplot.ylim((0,100))
			matplotlib.pyplot.legend(handles = [h1,h2,h3], loc='upper left')

			if Title:
				matplotlib.pyplot.title(Title, y=1.08)
			else:
				matplotlib.pyplot.title('Basins of Attraction', y=1.08)

			matplotlib.pyplot.ylabel('% of state space')
			matplotlib.pyplot.xlabel('attractors')
			matplotlib.pyplot.tight_layout()

			figure.savefig(FnameImage, bbox_inches='tight')
			print("created %s"%FnameImage)
			matplotlib.pyplot.close(figure)


	result = {}
	for x in weak:
		result[x] = {}
		result[x]["weak"] = weak[x]

	for x in strong:
		result[x]["strong"] = strong[x]

	for x in cycfree:
		result[x]["cycfree"] = cycfree[x]

	return result


def strong_basins(Primes, Update, FnameImage=None, Attractors=None, Minimize=False, Title=None, Silent=True):
	"""
	todo: proofread docstring

	Uses model checking with accepting states to compute the strong basins of attraction of the network defined by *Primes* and *Update*.
	*Attractors* may be used to specify a list of representative states for the attractors.
	Otherwise the strong basins of the minimal trap spaces is returned.
	Use *FnameImage* to create a pie chart of the strong basins, this requires https://matplotlib.org.
	The strong basins are returned in the form of a dictionary::

		* '01100--0': (str of attractor representant)
			* 'formula': '(!Erk & !Mek)' (Boolean expression for states)
			* 'perc':	0.5			 (percentage of state space)
			* 'size':	8			   (number of states)
		...
		* 'outside':  (special name for all states that do not belong to a strong basin)
			...
			...

	**arguments**:
		* *Primes*: prime implicants
		* *Update* (str): the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
		* *Attractors* (list): list of states or subspaces representing the attractors. *None* results in the computation of the minimal trap spaces.
		* *Minimize* (bool): minimize the resulting expressions
		* *FnameImage* (str): file name of pie chart of strong basins
		* *Title* (str): optional title of plot
		* *Silent* (bool): print infos to screen

	**returns**::
		* *StrongBasins* (dict): the strong basins

	**example**::

		>>> primes = Repository.get_primes("raf")
		>>> strong_basins(primes, "asynchronous")
			{   '001': {   'formula': '(!Erk & !Mek)', 'perc': 25.0, 'size': 2L},
				'11-': {   'formula': '(Mek & Raf) | (Erk & Mek)', 'perc': 37.5, 'size': 3L},
				'outside': {   'formula': '(!Erk & Mek & !Raf) | (Erk & !Mek)',
							   'perc': 37.5,
							   'size': 3L}}
	"""

	if not Attractors:
		Attractors = PyBoolNet.AspSolver.trap_spaces(Primes,"min")

	res = {}

	if len(Attractors) == 1:

		label = PyBoolNet.StateTransitionGraphs.subspace2str(Primes,Attractors[0])
		res[label] = _default_basin(Primes)


	else:
		count = 0

		total_size = PyBoolNet.PrimeImplicants.size_state_space(Primes, Type="total")

		if not Silent:
			print("strong_basins(..)")

		for x in Attractors:
			if not Silent:
				print(" working on attractor %s"%PyBoolNet.StateTransitionGraphs.subspace2str(Primes,x))

			label = PyBoolNet.StateTransitionGraphs.subspace2str(Primes,x)
			res[label] = strong_basin(Primes, Update, Minimize, Attractor=x)
			count+= res[label]["size"]


		if count<total_size:

			init = "INIT TRUE"
			prop = " & ".join("!(%s)"%x["formula"] for x in res.values())
			spec = "CTLSPEC %s"%prop
			ans, acc = PyBoolNet.ModelChecking.check_primes_with_acceptingstates(Primes,Update,init,spec)

			size = acc["INITACCEPTING_SIZE"]
			count+=size

			assert(count==total_size)

			formula = acc["INITACCEPTING"]
			if Minimize:
				formula = PyBoolNet.BooleanLogic.minimize_espresso(formula)

			res["None"] = {"size":	size,
						   "formula": formula,
						   "perc":	100.* size / total_size}

		else:
			res["None"] = {"size":	0,
						   "formula": "0",
						   "perc":	.0}


	if FnameImage:
		try:
			import matplotlib.pyplot
			success = True

		except ImportError:
			print("ERROR: can not import matplotlib.pyplot")
			success = False

		if success:

			figure = matplotlib.pyplot.figure()

			labels = sorted(res)

			if Update=="synchronous":
				labels.remove("not in any strong basin")
				explode = None

			sizes  = [res[x]["size"] for x in labels]
			colors = [matplotlib.pyplot.cm.rainbow(1.*x/(len(labels)+1)) for x in range(len(labels)+2)][1:-1]

			if Update=="asynchronous":
				colors[-1] = "white"
				explode = [0]*(len(labels)-1)+[.08]

			matplotlib.pyplot.pie(sizes, explode=explode, labels=labels, colors=colors, autopct='%1.1f%%', shadow=True, startangle=140)
			matplotlib.pyplot.axis('equal')

			if Title:
				matplotlib.pyplot.title(Title, y=1.08)
			else:
				matplotlib.pyplot.title('Strong Basins of Attraction', y=1.08)

			matplotlib.pyplot.tight_layout()

			figure.savefig(FnameImage, bbox_inches='tight')
			print("created %s"%FnameImage)
			matplotlib.pyplot.close(figure)

	return res


def abstract_commitment_diagram(Primes, Update, Queries, FnameImage=None, Silent=False):
	"""
	todo: proofread docstring

	this is the abstract version of "commitment_diagram(..)"


	data structure of diagram:

	* nodes are integers starting from 0

	* node attributes:
		* "formula" (str): a Boolean expression that encodes the states
		* "size" (int): the number of states
		* "queries" (set of str): subset of queries valid in node

	* edge attributes:
		* "EX_formula" (str): a Boolean expression that encodes the border states
		* "EX_size" (int): the number of border states

	**arguments**:
		* *Primes*: prime implicants
		* *Update* (str): the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
		* *Queries* (list / dict): queries / named queries {query:name}
		* *FnameImage* (str): will call commitment_diagram2image(..)
		* *Silent* (bool): print infos to screen

	**returns**::
		* *AbstractCommitmentDiagram* (netowrkx.DiGraph): the abstract commitment diagram

	**example**::

		>>> primes = Repository.get_primes("xiao_wnt5a")
		>>> queries = ["raf & mek", "!raf | (erk & mek)"]
		>>> diagram = abstract_commitment_diagram(primes, "asynchronous", queries)
	"""

	assert(Update in PyBoolNet.StateTransitionGraphs.UPDATE_STRATEGIES)
	assert(Primes)

	if not Silent:
		print("abstract_commitment_diagram(..)")


	if not type(Queries) == dict:
		queries_dict = {}
		for i,x in enumerate(Queries):
			queries_dict[x] = "Query%i"%(i+1)
		Queries = queries_dict

	diagram = networkx.DiGraph()

	# nodes
	node_id = 0
	Flags = [[0,1]]*len(Queries)
	for i,flags in enumerate(itertools.product(*Flags)):

		signature = [x for flag, x in zip(flags, Queries) if flag]
		signature = dict(item for item in Queries.items() if item[0] in signature)

		init = "INIT TRUE"

		if not signature:
			unreach = " & ".join("!EF(%s)"%x for x in Queries)
			spec = "CTLSPEC %s"%unreach

		else:
			reach = ["EF(%s)"%x for x in signature]
			reach_all  = " & ".join(reach)
			reach_some = " | ".join(reach)

			spec = "CTLSPEC %s & AG(%s)"%(reach_all,reach_some)

		answer, accepting = PyBoolNet.ModelChecking.check_primes_with_acceptingstates(Primes, Update, init, spec)



		data = {"queries":   signature,
				"size":	  accepting["INITACCEPTING_SIZE"],
				"formula":   accepting["INITACCEPTING"]}

		if data["size"]>0:
			if not Silent:
				print(" combination %i %s: %i, node id: %i"%(i,flags, accepting["INITACCEPTING_SIZE"], node_id))

			diagram.add_node(node_id, data)
			node_id+= 1


	# edges
	for source in diagram:
		for target in diagram:
			if source==target: continue
			sourceset = set(diagram.node[source]["queries"])
			targetset = set(diagram.node[target]["queries"])

			if targetset.issubset(sourceset):
				init = "INIT %s"%diagram.node[source]["formula"]
				spec = "CTLSPEC EX(%s)"%diagram.node[target]["formula"]

				answer, accepting = PyBoolNet.ModelChecking.check_primes_with_acceptingstates(Primes, Update, init, spec)

				if accepting["INITACCEPTING_SIZE"]>0:

					data = {}
					data["EX_size"] = accepting["INITACCEPTING_SIZE"]
					data["EX_formula"] = accepting["INITACCEPTING"]

					diagram.add_edge(source, target, data)

					if not Silent:
						print(" edge %i -> %i exists"%(source,target))


	if FnameImage:
		abstract_commitment_diagram2image(Primes, Diagram=diagram, FnameImage=FnameImage)

	return diagram


def abstract_commitment_diagram2image(Primes, Diagram, FnameImage=None):
	"""
	creates an image of the abstract commitment diagram.

	**arguments**:
		* *Primes*: prime implicants, needed for pretty printing of the attractors.
		* *Diagram* (networkx.DiGraph): a basin diagram
		* *FnameImage* (str): name of the diagram image

	**returns**::
		* *StyledDiagram* (networkx.DiGraph): the styled abstract commitment diagram

	**example**::

		>>> abstract_commitment_diagram2image(primes, diagram, "diagram.pdf")
	"""

	assert(type(Primes)==dict)
	assert(type(Diagram)==type(networkx.DiGraph()))

	size_total = PyBoolNet.PrimeImplicants.size_state_space(Primes, Type="total")

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

		head = PyBoolNet.Utility.Misc.divide_list_into_similar_length_lists(data["queries"].values())
		head = [",".join(x) for x in head]
		labels[node]["head"] = "<br/>".join(head)

		if "fillcolor" in data:
			image.node[node]["fillcolor"] = data["fillcolor"]

		elif len(data["queries"])==1:
			image.node[node]["fillcolor"] = "cornflowerblue"

	for source, target, data in Diagram.edges(data=True):
		image.add_edge(source, target)

	for x in Diagram.nodes():
		perc = 100.* Diagram.node[x]["size"] / size_total
		labels[x]["size"] = "states: %s%%"%perc2str(perc)

	for x in Diagram.nodes():
		image.node[x]['label'] = "<%s>"%"<br/>".join(labels[x].values())

	ranks = {}
	for node, data in Diagram.nodes(data=True):

		size = len(data["queries"])
		if not size in ranks:
			ranks[size]=[]
		ranks[size].append(node)

	ranks=list(ranks.items())
	ranks.sort(key=lambda x: x[0])

	for _,names in ranks:
		names = ['"%s"'%x for x in names]
		names = "; ".join(names)
		image.graph["{rank = same; %s;}"%names]=""

	if FnameImage:
		PyBoolNet.Utility.DiGraphs.digraph2image(image, FnameImage, LayoutEngine="dot")

	return image


# todo: refactor: 1. AttrObj instead of Attractors, remove Update. 2. returns CommitmentObj
def commitment_diagram(Primes, Update, Attractors=None, AdditionalEdgeData=False, FnameImage=None, Silent=False, ReturnCounter=False):
	"""
	Creates the commitment diagram, a networkx.DiGraph, of the STG defined by *Primes* and *Update*.
	The nodes of the diagram represent states that can reach the exact same subset of *Attractors*.
	Nodes are labeled by the index of the attractor in the order given in *Attractors* and the number of states
	that are represented. Edges indicate the existence of a transition between two nodes in the respective sets.
	Edges are labeled by the number of states of the source set that can reach the target set and,
	if *AdditionalEdgeData* is true, additionally by the size of the border.

	The algorithm requires model checking with accepting states, i.e., NuSMV-a.
	Basic steps towards increased efficiency are implemented:

		1. out-DAGs (output cascades) are discarded during model checking, and
		2. disconnected components are considered separately (and recombined using a cartesian product of diagrams).

	**arguments**:
		* *Primes*: prime implicants
		* *Update* (str): the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
		* *Attractors* (list): list of states or subspaces representing the attractors. *None* results in the computation of the minimal trap spaces.
		* *AdditionalEdgeData* (bool): whether the computation of the so-called border states should be included in the diagram
		* *FnameImage* (str): will call commitment_diagram2image(..)
		* *Silent* (bool): print infos to screen
		* *ReturnCounter* (bool): whether the number of performed model checks should be returned, used for statistics

	**returns**::
		* *CommitmentDiagram* (netowrkx.DiGraph): the commitment diagram
		* *Counter* (int): number of model checks performed, if *ReturnCounter=True*

	**example**::

		>>> primes = Repository.get_primes("xiao_wnt5a")
		>>> diagram = commitment_diagram(primes, "asynchronous")
		>>> diagram.order()
		6
		>>> diagram.node[4]["formula"]
		'(x4 & (x7))'
		>>> diagram.node[4]["size"]
		32
	"""

	assert(Update in PyBoolNet.StateTransitionGraphs.UPDATE_STRATEGIES)
	assert(Primes)

	if not Silent:
		print("commitment_diagram(..)")

	if not Attractors:
		Attractors = PyBoolNet.AspSolver.trap_spaces(Primes, "min")
	else:
		Attractors = map(lambda x: PyBoolNet.StateTransitionGraphs.subspace2dict(Primes, x), Attractors)

	size_total = PyBoolNet.PrimeImplicants.size_state_space(Primes, Type="total")

	if len(Attractors)==1:
		if not Silent:
			print(" single attractor, trivial case.")
		diagram = networkx.DiGraph()
		counter_mc = 0

		diagram.add_node("0")
		diagram.node["0"]["attractors"]	= Attractors
		diagram.node["0"]["size"]		= size_total
		diagram.node["0"]["formula"]	= "TRUE"

	else:

		igraph = PyBoolNet.InteractionGraphs.primes2igraph(Primes)
		outdags = PyBoolNet.InteractionGraphs.find_outdag(igraph)

		attractor_nodes = [x for A in Attractors for x in A]
		critical_nodes = PyBoolNet.Utility.DiGraphs.ancestors(igraph, attractor_nodes)
		outdags = [x for x in outdags if not x in critical_nodes]

		igraph.remove_nodes_from(outdags)
		if not Silent:
			print(" excluding the non-critical out-dag nodes %s"%outdags)

		components = networkx.connected_components(igraph.to_undirected())
		components = [list(x) for x in components]
		if not Silent:
			print(" working on %i connected component(s)"%len(components))

		counter_mc = 0
		diagrams = []
		for component in components:
			subprimes = PyBoolNet.PrimeImplicants.copy(Primes)
			PyBoolNet.PrimeImplicants.remove_all_variables_except(subprimes, component)

			attrs_projected = project_attractors(Attractors, component)

			diagram, count = _commitment_diagram_component(subprimes, Update, attrs_projected, AdditionalEdgeData, Silent)
			counter_mc+=count

			diagrams.append(diagram)

		factor = 2**len(outdags)
		diagram = cartesian_product(diagrams, factor, AdditionalEdgeData)


		nodes_sum = 0
		for x in diagram.nodes():
			projection = diagram.node[x]["attractors"]
			diagram.node[x]["attractors"] = lift_attractors(Attractors, projection)
			nodes_sum+= diagram.node[x]["size"]

		if not nodes_sum==size_total:
			print("WARNING: commitment diagram does not partition the state space, this may be due to rounding of large numbers.")

		sorted_ids = sorted(diagram, key=lambda x: diagram.node[x]["formula"])
		mapping = {x:str(sorted_ids.index(x)) for x in diagram}
		networkx.relabel_nodes(diagram,mapping,copy=False)

	if not Silent:
		print(" total executions of NuSMV: %i"%counter_mc)


	if FnameImage:
		commitment_diagram2image(Primes, Diagram=diagram, FnameImage=FnameImage, StyleInputs=True,
								 StyleSplines="curved", StyleEdges=AdditionalEdgeData, StyleRanks=True, FirstIndex=1)


	if ReturnCounter:
		return diagram, counter_mc
	else:
		return diagram


def _commitment_diagram_component(Primes, Update, Attractors, AdditionalEdgeData, Silent):
	"""
	Also computes the commitment diagram but without removing out-DAGs or considering connected components separately.
	Not meant for general use. Use commitment_diagram(..) instead.
	"""

	assert(Update in PyBoolNet.StateTransitionGraphs.UPDATE_STRATEGIES)
	assert(Primes)

	# create nodes
	counter_mc = 0
	node_id = 0
	worst_case_nodes = 0
	inputs = PyBoolNet.PrimeImplicants.find_inputs(Primes)

	states_per_case = PyBoolNet.PrimeImplicants.size_state_space(Primes, Type="per_input_combination")

	diagram = networkx.DiGraph()

	if not Silent:
		print(" _commitment_diagram_component(..)")
		print("  inputs: %i"%len(inputs))
		print("  combinations:  %i"%2**len(inputs))

	for i, combination in enumerate(PyBoolNet.PrimeImplicants.input_combinations(Primes)):

		attr = [x for x in Attractors if PyBoolNet.StateTransitionGraphs.A_is_subspace_of_B(Primes, A=x, B=combination)]

		worst_case_nodes+= 2**len(attr)-1
		states_covered = 0
		specs = [PyBoolNet.TemporalLogic.subspace2proposition(Primes,x) for x in attr]
		vectors = len(attr)*[[0,1]]
		vectors = list(itertools.product(*vectors))
		random.shuffle(vectors)

		combination_formula = PyBoolNet.TemporalLogic.subspace2proposition(Primes,combination)

		if not Silent:
			print("  input combination %i, worst case #nodes: %i"%(i,2**len(attr)-1))

		for vector in vectors:
			if sum(vector)==0: continue
			if states_covered==states_per_case:
				if not Silent:
					print("  avoided executions of NuSMV due to state counting")
				break

			if len(vector)==1:
				data = {"attractors":   attr,
						"size":		 	states_per_case,
						"formula":	  	combination_formula}

			else:

				init = "INIT %s"%combination_formula

				reach = ["EF(%s)"%x for flag, x in zip(vector, specs) if flag]
				reach_all  = " & ".join(reach)
				reach_some = " | ".join(reach)
				spec = "CTLSPEC %s & AG(%s)"%(reach_all,reach_some)

				answer, accepting = PyBoolNet.ModelChecking.check_primes_with_acceptingstates(Primes, Update, init, spec)
				counter_mc+=1

				data = {"attractors":   [x for flag,x in zip(vector,attr) if flag],
						"size":		 	accepting["INITACCEPTING_SIZE"],
						"formula":	  	accepting["INITACCEPTING"]}

			if data["size"]>0:
				diagram.add_node(node_id, data)
				node_id+=1
				states_covered+= data["size"]

	if not Silent:
		perc = "= %.2f%%"%(100.*diagram.order()/worst_case_nodes) if worst_case_nodes else ""
		print("  worst case #nodes: %i"%worst_case_nodes)
		print("  actual nodes: %i %s"%(diagram.order(),perc))

	# list potential targets
	potential_targets = {}
	for source, source_data in diagram.nodes(data=True):
		succs = []
		for target, target_data in diagram.nodes(data=True):
			if source==target: continue
			if all(x in source_data["attractors"] for x in target_data["attractors"]):
				succs.append((target,target_data))

		potential_targets[source] = succs

	if not Silent:
		worst_case_edges = sum(len(x) for x in potential_targets.values())
		print("  worst case #edges: %i"%worst_case_edges)

	# create edges
	for source, source_data in diagram.nodes(data=True):
		for target, target_data in potential_targets[source]:

			init = "INIT %s"%source_data["formula"]
			spec = "CTLSPEC EX(%s)"%target_data["formula"]
			answer, accepting = PyBoolNet.ModelChecking.check_primes_with_acceptingstates(Primes, Update, init, spec)
			counter_mc+=1

			data = {}
			data["EX_size"] = accepting["INITACCEPTING_SIZE"]
			data["EX_formula"] = accepting["INITACCEPTING"]

			if data["EX_size"]>0:

				if AdditionalEdgeData:
					if len(potential_targets[source])==1:
						data["EF_size"] = source_data["size"]
						data["EF_formula"] = source_data["formula"]

					else:
						spec = "CTLSPEC E[%s U %s]"%(source_data["formula"],target_data["formula"])
						answer, accepting = PyBoolNet.ModelChecking.check_primes_with_acceptingstates(Primes, Update, init, spec)
						counter_mc+=1

						data["EF_size"] = accepting["INITACCEPTING_SIZE"]
						data["EF_formula"] = accepting["INITACCEPTING"]

				diagram.add_edge(source, target, data)

	if not Silent:
		perc = "= %.2f%%"%(100.*diagram.size()/worst_case_edges) if worst_case_edges else ""
		print("  actual edges: %i %s"%(diagram.size(),perc))
		print("  total executions of NuSMV: %i"%counter_mc)

	return diagram, counter_mc


def commitment_diagram2image(Primes, Diagram, FnameImage=None, StyleInputs=True,
				  StyleSplines="curved", StyleEdges=False, StyleRanks=True, FirstIndex=1, Silent=True):
	"""
	Creates the image file *FnameImage* for the basin diagram given by *Diagram*.
	The flag *StyleInputs* can be used to highlight which basins belong to which input combination.
	*StyleEdges* adds edge labels that indicate the size of the "border" (if *ComputeBorder* was enabled in :ref:`commitment_diagram`)
	and the size of the states of the source basin that can reach the target basin.

	**arguments**:
		* *Primes*: prime implicants, needed for pretty printing of the attractors.
		* *Diagram* (networkx.DiGraph): a basin diagram
		* *FnameImage* (str): name of the diagram image
		* *StyleInputs* (bool): whether basins should be grouped by input combinations
		* *StyleSplines* (str): dot style for edges, e.g. "curved", "line" or "ortho" for orthogonal edges
		* *StyleEdges* (bool): whether edges should be size of border / reachable states
		* *StyleRanks* (bool): style that places nodes with the same number of reachable attractors on the same rank (level)
		* *FirstIndex* (int): first index of attractor names
		* *Silent* (bool): print infos to screen

	**returns**::
		* *StyledDiagram* (networkx.DiGraph)

	**example**::

		>>> commitment_diagram2image(primes, diagram, "basins.pdf")
		>>> commitment_diagram2image(primes, diagram, "basins.pdf", "attractors.pdf")
	"""

	assert(type(Primes)==dict)
	assert(type(Diagram)==type(networkx.DiGraph()))

	size_total = PyBoolNet.PrimeImplicants.size_state_space(Primes, Type="total")
	size_per_input_combination = PyBoolNet.PrimeImplicants.size_state_space(Primes, Type="per_input_combination")

	result = networkx.DiGraph()
	result.graph["node"]  = {"shape":"rect","style":"filled","color":"none"}
	result.graph["edge"]  = {}

	if StyleInputs:
		result.graph["node"]["fillcolor"] = "grey95"
	else:
		result.graph["node"]["fillcolor"] = "lightgray"

	attractors = [x["attractors"] for _,x in Diagram.nodes(data=True)]
	attractors = [x for x in attractors if len(x)==1]
	attractors = set(PyBoolNet.StateTransitionGraphs.subspace2str(Primes,x[0]) for x in attractors)
	attractors = sorted(attractors)

	# do test if the following two lines may be deleted
	# legend = ['A%i = <font face="Courier New">%s</font>'%(i+FirstIndex,A) for i,A in enumerate(attractors)]
	# legend = "<%s>"%"<br/>".join(legend)


	labels = {}
	# "labels" is used for node labels
	# keys:
	# head = reachable attractors
	# size = number of states in % (depends on StyleInputs)


	for node, data in Diagram.nodes(data=True):

		labels[node] = {}
		result.add_node(node)

		if len(data["attractors"])==1:
			result.node[node]["fillcolor"] = "cornflowerblue"

			attr  = PyBoolNet.StateTransitionGraphs.subspace2str(Primes,data["attractors"][0])
			index = attractors.index(attr)+FirstIndex
			labels[node]["head"] = 'A%i = <font face="Courier New">%s</font>'%(index,attr)

		else:
			head = sorted("A%i"%(attractors.index(PyBoolNet.StateTransitionGraphs.subspace2str(Primes,x))+FirstIndex) for x in data["attractors"])
			head = PyBoolNet.Utility.Misc.divide_list_into_similar_length_lists(head)
			head = [",".join(x) for x in head]
			labels[node]["head"] = "<br/>".join(head)


		if "fillcolor" in data:
			result.node[node]["fillcolor"] = data["fillcolor"]



	for source, target, data in Diagram.edges(data=True):
		result.add_edge(source, target)

		if StyleEdges:
			edge_label = []


			#perc = 100.* data["EX_size"] / Diagram.node[source]["size"]
			#edge_label.append("EX: %s%%"%perc2str(perc))

			if "EF_size" in data:
				#perc = 100.* data["EF_size"] / Diagram.node[source]["size"]
				#edge_label.append("EF: %s%%"%perc2str(perc))

				if data["EF_size"] < Diagram.node[source]["size"]:
					result.edge[source][target]["color"]="lightgray"

			#result.edge[source][target]["label"] = "<%s>"%("<br/>".join(edge_label))


	for x in Diagram.nodes():
		perc = 100.* Diagram.node[x]["size"] / size_total
		labels[x]["size"] = "states: %s%%"%perc2str(perc)

	subgraphs = []
	if StyleInputs:
		for inputs in PyBoolNet.PrimeImplicants.input_combinations(Primes):
			if not inputs: continue
			nodes = [x for x in Diagram.nodes() if PyBoolNet.Utility.Misc.dicts_are_consistent(inputs,Diagram.node[x]["attractors"][0])]
			label = PyBoolNet.StateTransitionGraphs.subspace2str(Primes,inputs)
			subgraphs.append((nodes,{"label":"inputs: %s"%label, "color":"none", "fillcolor":"lightgray"}))


			for x in nodes:
				perc = 100.* Diagram.node[x]["size"] / size_per_input_combination
				labels[x]["size"] = "states: %s%%"%perc2str(perc)


		if subgraphs:
			result.graph["subgraphs"] = []
			PyBoolNet.Utility.DiGraphs.add_style_subgraphs(result, subgraphs)


	for x in Diagram.nodes():
		result.node[x]['label'] = "<%s>"%"<br/>".join(labels[x].values())

	if StyleRanks:
		if subgraphs:
			to_rank = result.graph["subgraphs"]
		else:
			to_rank = [result]

		for graph in to_rank:
			ranks = {}
			for node, data in Diagram.nodes(data=True):
				if not node in graph:continue

				size = len(data["attractors"])
				if not size in ranks:
					ranks[size]=[]
				ranks[size].append(node)
			ranks=list(ranks.items())
			ranks.sort(key=lambda x: x[0])

			for _,names in ranks:
				names = ['"%s"'%x for x in names]
				names = "; ".join(names)
				graph.graph["{rank = same; %s;}"%names]=""


	if FnameImage:
		PyBoolNet.Utility.DiGraphs.digraph2image(result, FnameImage, LayoutEngine="dot")

	return result


def commitment_pie(Primes, Update, FnameImage, Diagram=None, Attractors=None, ColorMap=None, Silent=False, Title=None):
	"""
	Creates the commitment pie chart, using matplotlib, of the STG defined by *Primes* and *Update*.
	The pieces of the chart represent states that can reach the exact same subset of *Attractors*.
	They are labeled by the index of the attractor in the order given in *Attractors* and the number of states
	that are represented.

	The algorithm requires model checking with accepting states, i.e., NuSMV-a.
	Basic steps towards increased efficiency are implemented:
	out-DAGs (a.k.a. output cascades) are discarded during model checking, and
	disconnected components are considered separately (and recombined using a cartesian product of diagrams).

	**arguments**:
		* *Primes*: prime implicants
		* *Update* (str): the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
		* *FnameImage* (str): name of the output image
		* *Diagram* (networkx.DiGraph): precomputed commitment diagram
		* *Attractors* (list): list of states or subspaces representing the attractors. *None* results in the computation of the minimal trap spaces.
		* *ColorMap* (dict): assignment of diagram nodes to colors for custom colors
		* *Silent* (bool): print infos to screen
		* *Title* (str): optional title of plot

	**returns**::
		* *None*

	**example**::

		>>> primes = Repository.get_primes("xiao_wnt5a")
		>>> commitment_pie(primes, "asynchronous", "pie.pdf")
	"""

	try:
		import matplotlib.pyplot
		success = True

	except ImportError:
		print("ERROR: can not import matplotlib.pyplot")
		return

	if not Diagram:
		Diagram = commitment_diagram(Primes, Update, Attractors=Attractors, AdditionalEdgeData=False, FnameImage=None, Silent=Silent, ReturnCounter=False)

	figure = matplotlib.pyplot.figure()

	ids = sorted(Diagram, key=lambda x: len(Diagram.node[x]["attractors"]))

	labels = []
	for x in ids:
		label = sorted(PyBoolNet.StateTransitionGraphs.subspace2str(Primes,y) for y in Diagram.node[x]["attractors"])
		labels.append("\n".join(label))

	sizes  = [Diagram.node[x]["size"] for x in ids]

	if ColorMap:
		colors = [ColorMap[x] for x in ids]
	else:
		colors = [matplotlib.pyplot.cm.rainbow(1.*x/(len(Diagram)+1)) for x in range(len(Diagram)+2)][1:-1]


	matplotlib.pyplot.pie(sizes, explode=None, labels=labels, colors=colors, autopct='%1.1f%%', shadow=True, startangle=140)
	matplotlib.pyplot.axis('equal')

	if Title:
		matplotlib.pyplot.title(Title, y=1.08)
	else:
		matplotlib.pyplot.title('Commitment Sets', y=1.08)

	matplotlib.pyplot.tight_layout()

	figure.savefig(FnameImage, bbox_inches='tight')
	print("created %s"%FnameImage)
	matplotlib.pyplot.close(figure)


def abstract_commitment_pie(Primes, Update, FnameImage=None, Diagram=None, Queries=None, ColorMap=None, Title=None, Silent=False):
	"""
	creates the abstract commitment pie.

	**arguments**:
		* *Primes*: prime implicants
		* *Update* (str): the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
		* *FnameImage* (str): name of the output image
		* *Diagram* (networkx.DiGraph): precomputed commitment diagram
		* *Queries* (list / dict): list of CTL queries or named queries {CTL queries:label}
		* *ColorMap* (dict): assignment of diagram nodes to colors for custom colors
		* *Title* (str): optional title of plot
		* *Silent* (bool): print infos to screen

	**returns**::
		* *None*

	**example**::

		>>> primes = Repository.get_primes("xiao_wnt5a")
		>>> abstract_commitment_pie(primes, "asynchronous", "pie.pdf")
	"""

	try:
		import matplotlib.pyplot
		success = True

	except ImportError:
		print("ERROR: can not import matplotlib.pyplot")
		return

	if not Diagram:
		assert(Queries)
		Diagram = abstract_commitment_diagram(Primes, Update, Queries=Queries, FnameImage=None, Silent=Silent)

	figure = matplotlib.pyplot.figure()

	ids = sorted(Diagram, key=lambda x: len(Diagram.node[x]["queries"]))
	labels = ["\n".join(Diagram.node[x]["queries"].values()) for x in ids]
	sizes  = [Diagram.node[x]["size"] for x in ids]

	if ColorMap:
		colors = [ColorMap[x] for x in ids]
	else:
		colors = [matplotlib.pyplot.cm.rainbow(1.*x/(len(Diagram)+1)) for x in range(len(Diagram)+2)][1:-1]

	matplotlib.pyplot.pie(sizes, explode=None, labels=labels, colors=colors, autopct='%1.1f%%', shadow=True, startangle=140)
	matplotlib.pyplot.axis('equal')

	if Title:
		matplotlib.pyplot.title(Title, y=1.08)
	else:
		matplotlib.pyplot.title('Commitment Sets', y=1.08)

	matplotlib.pyplot.tight_layout()

	figure.savefig(FnameImage, bbox_inches='tight')
	print("created %s"%FnameImage)
	matplotlib.pyplot.close(figure)


###### Auxillary Functions ######


def project_attractors(Attractors, Names):
	result = set()
	for space in Attractors:
		projection = tuple((k,v) for k,v in sorted(space.items()) if k in Names)
		result.add(projection)

	result = [dict(x) for x in result]

	return result


def lift_attractors(Attractors, Projection):
	return [x for x in Attractors for y in Projection if PyBoolNet.Utility.Misc.dicts_are_consistent(x,y)]


def cartesian_product(Diagrams, Factor, AdditionalEdgeData):
	"""
	creates the cartesian product of *Diagrams*.
	"""

	result = networkx.DiGraph()

	# create nodes
	nodes = [x.nodes(data=True) for x in Diagrams]

	for product in itertools.product(*nodes):
		data = {}
		data["size"] = functools.reduce(operator.mul,[x["size"] for _,x in product]) * Factor
		data["formula"] = " & ".join("(%s)"%x["formula"] for _,x in product)

		attrs = [x["attractors"] for _,x in product]
		attrs = list(itertools.product(*attrs))
		attrs = [PyBoolNet.Utility.Misc.merge_dicts(x) for x in attrs]
		data["attractors"] = attrs

		node = tuple(x for x,_ in product)

		result.add_node(node, data)

	# create edges
	for source in result.nodes():
		for s, diagram in zip(source, Diagrams):
			factor = result.node[source]["size"] / diagram.node[s]["size"]
			for _, t, data in diagram.out_edges(s,data=True):

				data = {}
				basic_formula = ["(%s)"%g.node[x]["formula"] for x,g in zip(source,Diagrams) if not g==diagram]
				data["EX_size"]	= factor * diagram.edge[s][t]["EX_size"]
				formula = basic_formula + ["(%s)"%diagram.edge[s][t]["EX_formula"]]
				data["EX_formula"]  = " & ".join(formula)

				if AdditionalEdgeData:
					data["EF_size"]	 = factor * diagram.edge[s][t]["EF_size"]
					formula = basic_formula + ["(%s)"%diagram.edge[s][t]["EF_formula"]]
					data["EF_formula"]  = " & ".join(formula)

				target = tuple(x if not g==diagram else t for x,g in zip(source,Diagrams))

				result.add_edge(source, target, data)

	# relabel nodes
	result = networkx.convert_node_labels_to_integers(result)

	return result


def diagrams_are_equal(Diagram1, Diagram2):
	"""
	removes for formulas, which are different for naive / product diagrams.
	"""

	g1 = Diagram1.copy()
	g2 = Diagram2.copy()

	for g in [g1,g2]:
		for x in g.nodes():
			g.node[x].pop("formula")
		for x,y in g.edges():
			if "border_formula" in g.edge[x][y]:
				g.edge[x][y].pop("border_formula")
				g.edge[x][y].pop("finally_formula")

	em = lambda x,y:x==y

	return networkx.is_isomorphic(g1,g2,edge_match=em)
