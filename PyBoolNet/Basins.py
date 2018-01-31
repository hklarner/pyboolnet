

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


def create_barplot(Primes, Update, FnameImage=None, Attractors=None, Minimize=False, Title=None, Silent=True):
	"""
	todo: use attr object
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
		>>> create_barplot(primes, "asynchronous")
			{   '001': {'weak': {'formula': '(!Erk & !Raf) | (!Mek)', 'perc': 62.5, 'size': 5L},...},
				'11-': {'weak': {'formula': '(Mek) | (Erk)', 'perc': 75.0, 'size': 6L}},...}}
	"""

	if not Attractors:
		Attractors = PyBoolNet.AspSolver.trap_spaces(Primes,"min")

	weak = {}
	strong = {}
	cycfree = {}


	if not Silent:
		print("create_barplot(..)")

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


def create_piechart(Primes, Update, FnameImage=None, Attractors=None, Minimize=False, Title=None, Silent=True):
	"""
	todo: add cycle-free subset to plot using pairs of similar colours
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
		>>> create_piechart(primes, "asynchronous")
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
			print("create_piechart(..)")

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
