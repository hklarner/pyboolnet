

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

BASIN_COLORS = ["#ddf2db", "#a0dcb5", "#2ba0c6"] # weak, strong, cycle-free
PIE_COLORS = ["#ffb3ae", "#aecce1", "#c8eac6", "#dfcae2", "#ffd8a8", "#ffffce", "#e6d7bd", "#e6d7bd", "#e6d7bd"] # pastel19 color scheme

def weak_basin(Primes, Update, Subspace, Minimize=False):
	"""
	todo: add unit tests

	Computes the weak basin of *Subspace* via the CTL query AG(EF(Subspace)), for details see :ref:`Klarner2018 <klarner2018>`.

	  **arguments**:
		* *Primes*: prime implicants
		* *Update* (str):  the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
		* *Minimize* (bool): minimize the Boolean expressions
		* *Subspace* (str/dict): a subspace

	  **returns**:
		* *Basin* (dict): with keys "size"=number of states, "formula"=state formula and "perc"=percentage of state space

	  **example**::

		>>> weak_basin(primes, update, True, "0---1")
		{"size":	134,
		"formula":	"Erk & !Raf | Mek",
		"perc":		12.89338}
	"""

	return _basin_handle(Primes, Update, Subspace, Minimize, CTLpattern="CTLSPEC EF({x})")


def strong_basin(Primes, Update, Subspace, Minimize=False):
	"""
	todo: add unit tests

	Computes the strong basin of *Subspace* via the CTL query AG(EF(Subspace)), for details see :ref:`Klarner2018 <klarner2018>`.

	  **arguments**:
		* *Primes*: prime implicants
		* *Update* (str):  the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
		* *Minimize* (bool): minimize the Boolean expressions
		* *Subspace* (str/dict): a subspace

	  **returns**:
		* *Basin* (dict): with keys "size"=number of states, "formula"=state formula and "perc"=percentage of state space

	  **example**::

		>>> strong_basin(primes, update, True, "0---1")
		{"size":	134,
		"formula":	"Erk & !Raf | Mek",
		"perc":		12.89338}
	"""

	return _basin_handle(Primes, Update, Subspace, Minimize, CTLpattern="CTLSPEC AG(EF({x}))")


def cyclefree_basin(Primes, Update, Subspace, Minimize=False):
	"""
	todo: add unit tests

	Computes the cycle-free basin of *Subspace* via the CTL query AG(EF(Subspace)), for details see :ref:`Klarner2018 <klarner2018>`.

	  **arguments**:
		* *Primes*: prime implicants
		* *Update* (str):  the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
		* *Minimize* (bool): minimize the Boolean expressions
		* *Subspace* (str/dict): a subspace

	  **returns**:
		* *Basin* (dict): with keys "size"=number of states, "formula"=state formula and "perc"=percentage of state space

	  **example**::

	  	>>> cyclefree_basin(primes, update, True, "0---1")
		{"size":	134,
		"formula":	"Erk & !Raf | Mek",
		"perc":		12.89338}
	"""

	return _basin_handle(Primes, Update, Subspace, Minimize, CTLpattern="CTLSPEC AF({x})")


def _basin_handle(Primes, Update, Subspace, Minimize, CTLpattern):
	"""
	todo: add unit tests

	The handle for :ref:`weak_basin`, :ref:`strong_basin` and :ref:`cyclefree_basin`.

	  **arguments**:
		* *Primes*: prime implicants
		* *Update* (str):  the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
		* *Minimize* (bool): minimize the Boolean expressions
		* *Subspace* (str/dict): a subspace
		* *CTLpattern* (str):

	  **returns**:
		* *Basin* (dict): with keys "size"=number of states, "formula"=state formula and "perc"=percentage of state space

	  **example**::

		>>> _basin_handle(primes, update, True, "0---1", "CTLSPEC EF({x})")
		{"size":	134,
		"formula":	"Erk & !Raf | Mek",
		"perc":		12.89338}
	"""

	prop = PyBoolNet.TemporalLogic.subspace2proposition(Primes, Subspace)
	init = "INIT TRUE"
	spec = CTLpattern.format(x=prop)
	ans, acc = PyBoolNet.ModelChecking.check_primes_with_acceptingstates(Primes, Update, init, spec)

	size = acc["INITACCEPTING_SIZE"]
	formula = acc["INITACCEPTING"]

	if Minimize and formula not in ["TRUE","FALSE"]:
		formula = PyBoolNet.BooleanLogic.minimize_espresso(formula)

	size_total = PyBoolNet.StateTransitionGraphs.size_state_space(Primes)

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

	size_total = PyBoolNet.StateTransitionGraphs.size_state_space(Primes)

	return {"size":	size_total,
			"formula": "TRUE",
			"perc":	100.}


def compute_basins(AttrJson, Weak=True, Strong=True, CycleFree=True, FnameBarplot=None, FnamePiechart=None, Minimize=False, Silent=False):
	"""
	todo: add unit tests

	Extends *AttrJson* with basin of attraction.
	Use *FnameBarplot* and *FnamePiechart* to create plots of the basins, see :ref:`create_barplot` and :ref:`basins_create_piechart`.

	**arguments**:
		* *AttrJson* (dict): json attractor data, see :ref:`attractors_compute_json`
		* *Weak* (bool): compute weak basins
		* *Strong* (bool): compute strong basins
		* *CycleFree* (bool): compute cycle-free basins
		* *FnameBarplot* (str): file name of bar plot
		* *FnamePiechart* (str): file name of pie chart
		* *Minimize* (bool): minimize the Boolean expressions
		* *Silent* (bool): print infos to screen

	**returns**::
		* *None*

	**example**::

		>>> primes = Repository.get_primes("raf")
		>>> attrs = Attractors.compute_json(primes, update)
		>>> compute_basins(attrs)
	"""

	Primes = AttrJson["primes"]
	Update = AttrJson["update"]

	if not Silent:
		print("compute_basins(..)")

	n = len(AttrJson["attractors"])
	for i,x in enumerate(AttrJson["attractors"]):
		i+=1
		if not Silent:
			print(" working on attractor {i}/{n}: {l}".format(i=i,n=n,l=x["state"]["str"]))

		# weak basin
		if n == 1:
			x["weak_basin"] = _default_basin(Primes)
		else:
			x["weak_basin"] = weak_basin(Primes, Update, Subspace=x["mintrapspace"]["dict"], Minimize=Minimize)

		# strong basin
		if n == 1:
			x["strong_basin"] = _default_basin(Primes)

		else:
			x["strong_basin"] = strong_basin(Primes, Update, Subspace=x["mintrapspace"]["dict"], Minimize=Minimize)

		# cycle-free basin
		x["cyclefree_basin"] = cyclefree_basin(Primes, Update, Subspace=x["mintrapspace"]["dict"], Minimize=Minimize)

	if FnameBarplot:
		create_barplot(AttrJson, FnameBarplot, Minimize, Title=None, Silent=Silent)

	if FnamePiechart:
		create_piechart(AttrJson, FnamePiechart, Title=None, Silent=Silent)


def create_barplot(AttrJson, FnameImage, Title=None, Silent=False):
	"""
	todo: add unit tests

	Creates a bar plot of the basins of attraction specified in *AttrJson*.
	Requires that *AttrJson* has been extended with basins information by :ref:`compute_basins`.
	Requires https://matplotlib.org.

	**arguments**:
		* *AttrJson* (dict): json attractor data, see :ref:`attractors_compute_json`
		* *FnameImage* (str): create image for bar plot
		* *Title* (str): optional title of plot
		* *Silent* (bool): print infos to screen

	**returns**:
		* *None*

	**example**::

		>>> attrs = Attractors.compute_json(primes, update)
		>>> compute_basins(attrs)
		>>> create_barplot(attrs, "barplot.pdf")
		created barplot.pdf
	"""

	import matplotlib.pyplot

	Attrs = AttrJson["attractors"]
	Primes = AttrJson["primes"]
	assert(all(basin in x for basin in ["weak_basin", "strong_basin", "cyclefree_basin"] for x in Attrs))

	total = PyBoolNet.StateTransitionGraphs.size_state_space(Primes)
	is_small_network = total <= 1024
	key = "size" if is_small_network else "perc"

	indeces = range(len(Attrs))
	indeces.sort(key=lambda i: Attrs[i]["weak_basin"]["perc"], reverse=True)

	y1 = [Attrs[i]["cyclefree_basin"][key] for i in indeces]
	y2 = [Attrs[i]["strong_basin"][key] - Attrs[i]["cyclefree_basin"][key]  for i in indeces]
	y3 = [Attrs[i]["weak_basin"][key]   - Attrs[i]["strong_basin"][key]   for i in indeces]

	N = len(y1)
	x = range(N)
	width = 1/1.5

	labels = [Attrs[i]["mintrapspace"]["str"] for i in indeces]

	figure = matplotlib.pyplot.figure()
	h3 = matplotlib.pyplot.bar(x, y1, width, color=BASIN_COLORS[2], align='center', label='cycle-free basin')
	h2 = matplotlib.pyplot.bar(x, y2, width, bottom=y1, color=BASIN_COLORS[1], align='center', label='strong basin')
	h1 = matplotlib.pyplot.bar(x, y3, width, bottom=[sum(x) for x in zip(y1,y2)], color=BASIN_COLORS[0], align='center', label='weak basin')
	matplotlib.pyplot.xticks(range(len(labels)), labels, rotation=40, ha="right")

	ylim = (0,total) if is_small_network else (0,100)
	matplotlib.pyplot.ylim(ylim)

	matplotlib.pyplot.legend(handles = [h1,h2,h3], loc='upper right')

	if Title==None:
		Title = 'Basins of Attraction'

	matplotlib.pyplot.title(Title, y=1.08)

	ylabel = "number of states" if is_small_network else "percent of state space"
	matplotlib.pyplot.ylabel(ylabel)
	matplotlib.pyplot.xlabel('attractors')
	matplotlib.pyplot.tight_layout()

	figure.savefig(FnameImage, bbox_inches='tight')
	matplotlib.pyplot.close(figure)

	if not Silent:
		print("created {x}".format(x=FnameImage))


def create_piechart(AttrJson, FnameImage, Title=None, Silent=False):
	"""
	todo: add cycle-free subset to plot using pairs of similar colours
	todo: add unit tests

	Creates a pie chart of the basins of attraction specified in *AttrJson*.
	Requires that *AttrJson* has been extended with basins information by :ref:`compute_basins`.
	Requires https://matplotlib.org.

	**arguments**:
		* *AttrJson* (dict): json attractor data, see :ref:`attractors_compute_json`
		* *FnameImage* (str): create image for pie chart
		* *Title* (str): optional title of plot
		* *Silent* (bool): print infos to screen

	**returns**:
		* *None*

	**example**::

		>>> attrs = Attractors.compute_json(primes, update)
		>>> compute_basins(attrs)
		>>> create_piechart(attrs, "piechart.pdf")
		created piechart.pdf
	"""

	import matplotlib.pyplot

	Primes = AttrJson["primes"]
	Attrs = AttrJson["attractors"]

	assert(all(basin in x for basin in ["weak_basin", "strong_basin", "cyclefree_basin"] for x in Attrs))

	if not Silent:
		print("create_piechart(..)")

	total = PyBoolNet.StateTransitionGraphs.size_state_space(Primes)
	strong = sum(x["strong_basin"]["size"] for x in Attrs)
	outside = total - strong
	is_small_network = total <= 1024
	key = "size" if is_small_network else "perc"

	indeces = range(len(Attrs))
	indeces.sort(key=lambda i: Attrs[i]["strong_basin"]["perc"], reverse=True)

	figure = matplotlib.pyplot.figure()
	sizes  = [Attrs[i]["strong_basin"]["size"] for i in indeces] + [outside]

	if len(Attrs)<=9:
		colors = [PIE_COLORS[i] for i,x in enumerate(Attrs)]
	else:
		colors = [matplotlib.pyplot.cm.rainbow(1.*x/(len(indeces)+1)) for x in range(len(indeces)+2)][1:-1]

	colors.append("white") # for slice that represents "outside" states

	explode = [0]*len(indeces)+[.08]
	labels = [Attrs[i]["mintrapspace"]["str"] for i in indeces] + [""]

	autopct = lambda p: '{:.0f}'.format(p * total / 100) if is_small_network else "%1.1f%%"
	matplotlib.pyplot.pie(sizes, explode=explode, labels=labels, colors=colors, autopct=autopct, shadow=True, startangle=140)

	matplotlib.pyplot.axis('equal')

	if Title==None:
		Title = 'Strong Basins of Attraction'

	matplotlib.pyplot.title(Title, y=1.08)
	matplotlib.pyplot.tight_layout()
	figure.savefig(FnameImage, bbox_inches='tight')
	matplotlib.pyplot.close(figure)

	if not Silent:
		print("created %s"%FnameImage)




























# end of file
