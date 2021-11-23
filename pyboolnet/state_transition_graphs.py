

import heapq
import itertools
import logging
import random
from typing import List, Union
from typing import Optional

import networkx

from pyboolnet import find_command
from pyboolnet.digraphs import convert_nodes_to_anonymous_strings, digraph2image
from pyboolnet.digraphs import digraph2condensationgraph
from pyboolnet.digraphs import digraph2dot
from pyboolnet.digraphs import has_edge, has_path, find_successors, digraph2sccgraph
from pyboolnet.helpers import divide_list_into_similar_length_lists
from pyboolnet.state_space import hamming_distance, list_states_in_subspace
from pyboolnet.state_space import subspace2dict, subspace2str, state2dict, state2str, random_state
from pyboolnet.trap_spaces import trap_spaces
from pyboolnet.trap_spaces import trapspaces_that_contain_state

CMD_DOT = find_command("dot")
UPDATE_STRATEGIES = ["asynchronous", "synchronous", "mixed"]

log = logging.getLogger(__name__)


def energy(primes: dict, state) -> int:
    """
    This integer valued energy function E for Boolean networks is decreasing with transitions.
    That is, E(x) >= E(y) holds for any transition x -> y.
    It is based on the number of free variables in the smallest trapspace that contains *state*.
    The energy is therefore n >= E(x) >= 0 and E(x)=0 for steady states holds.

    **arguments**:
        * *primes*: prime implicants
        * *state*: a state

    **returns**:
        * *energy*: number of free variables in smallest trapspace containing *state*

    **example**::

        >>> primes = Repository.get_primes("raf")
        >>> StateTransitionGraphs.energy(primes, "000")
        1
        >>> StateTransitionGraphs.energy(primes, "010")
        3
        >>> StateTransitionGraphs.energy(primes, "001")
        0
    """
    
    tspace = trapspaces_that_contain_state(primes, state, type_="min", fname_asp=None, representation="str")[0]
    energy = tspace.count('-')
    
    return energy


def primes2stg(primes: dict, update: str, initial_states=lambda x: True) -> networkx.DiGraph:
    """
    Creates the state transition graph (STG) of a network defined by *primes* and *update*.
    The *initial_states* are either a list of states (in *dict* or *str* representation),
    a function that flags states that belong to the initial states, or
    a subspace (in *dict* or *str* representation).
    If *initial_states* is a function then it must take a single parameter *state* in dict representation
    and return a Boolean value that indicates whether it belongs to the initial states or not.

    The STG is constructed by a depth first search (DFS) starting from the given initial states.
    The default for *initial_states* is ``lambda x: True``, i.e., every state is initial.
    For a single initial state, say *"100"* use *initial_states="100"*,
    for a set of initial states use *initial_states=["100", "101"]* and
    for a initial subspace use *initial_states="1--"* or the *dict* representation of subspaces.

    **arguments**:
        * *primes*: prime implicants
        * *update*: either *"asynchronous"* or *"synchronous"*
        * *initial_states*: a function, a subspace, a state or a list of states

    **returns**:
        * *stg*: state transition graph

    **example**::

        >>> primes = FEX.read_primes("mapk.primes")
        >>> update = "asynchronous"
        >>> init = lambda x: x["ERK"]+x["RAF"]+x["RAS"]>=2
        >>> stg = primes2stg(primes, update, init)

        >>> stg.order()
        32

        >>> stg.edges()[0]
        ('01000','11000')

        >>> init = ["00100", "00001"]
        >>> stg = primes2stg(primes, update, init)

        >>> init = {"ERK":0, "RAF":0, "RAS":0, "MEK":0, "p38":1}
        >>> stg = primes2stg(primes, update, init)
    """
    
    if update not in ['asynchronous', 'synchronous']:
        log.warning("The chosen update might lead to a very big STG")
    
    if len(primes) > 15:
        log.warning(f"The state transition graph will consist of up to 2**{len(primes)}={2 ** len(primes)} states, depending on the initial states.")
    
    stg = networkx.DiGraph()
    
    if len(primes) == 0:
        log.warning("No Primes were given. Hence, the stg is empty.")
        return stg   

    if update == "asynchronous":
        successors = lambda x: successors_asynchronous(primes, x)

    if update == "synchronous":
        successors = lambda x: [successor_synchronous(primes, x)]

    if update == "mixed":
        successors = lambda x: successors_mixed(primes, x)
    
    names = sorted(primes)
    space = len(names) * [[0, 1]]
    
    if hasattr(initial_states, "__call__"):
        fringe = [dict(zip(names, values)) for values in itertools.product(*space)]
        fringe = [state2str(x) for x in fringe if initial_states(x)]
    
    elif type(initial_states) in [str, dict]:
        fringe = list_states_in_subspace(primes=primes, subspace=initial_states)
    
    else:
        fringe = [state2str(x) for x in initial_states]
    
    seen = set([])
    while fringe:
        source = fringe.pop()
        if source in seen:
            continue
        
        for target in successors(source):
            target = state2str(target)
            stg.add_edge(source, target)
            
            if target not in seen:
                fringe.append(target)
        
        seen.add(source)
    
    stg.graph["node"] = {"shape": "rect", "color": "none", "style": "filled", "fillcolor": "none"}
    stg.graph["edge"] = {}
    stg.graph["subgraphs"] = []
    
    if update == "synchronous":
        stg.graph["overlap"] = "compress"
    else:
        stg.graph["overlap"] = "scale"
    
    return stg


def stg2dot(stg: networkx.DiGraph, fname_dot: Optional[str] = None) -> str:
    """
    Creates a *dot* file from a state transition graph.
    Graph, node and edge attributes are passed to the *dot* file by adding the respective key and value pairs to the graph, node or edge data.
    Node and edge defaults are set by the specials graph keys *"node"* and *"edge"* and must have attribute dictionaries as values.
    For a list of attributes see http://www.graphviz.org/doc/info/attrs.html.

    **arguments**:
        * *stg*: state transition graph
        * *fname_dot*: name of *dot* file or *None*

    **returns**:
        * *text_dot*: content of dot file

    **example**::

          >>> stg = primes2stg(primes, update, init)
          >>> stg.graph["label"] = "IRMA Network - State Transition Graph"
          >>> stg.graph["node"] = {"style":"filled", "color":"red"}
          >>> stg.graph["edge"] = {"arrowsize": 2.0}
          >>> stg.nodes["001000"]["fontsize"] = 20
          >>> stg.adj["001110"]["001010"]["style"] = "dotted"
          >>> stg2image(stg, "irma_stg.pdf")
    """
    
    return digraph2dot(stg, fname_dot)


def stg2image(stg: networkx.DiGraph, fname_image: str, layout_engine: str = "fdp"):
    """
    Creates an image file from a state transition graph using :ref:`installation_graphviz` and the *layout_engine*.
    Use ``dot -T?`` to find out which output formats are supported on your installation.

    **arguments**:
        * *stg*: state transition graph
        * *fname_image*: name of output file
        * *layout_engine*: one of "dot", "neato", "fdp", "sfdp", "circo", "twopi"

    **example**::

          >>> stg2image(stg, "mapk_stg.pdf")
          >>> stg2image(stg, "mapk_stg.jpg", "neato")
          >>> stg2image(stg, "mapk_stg.svg", "dot")
    """
    
    digraph2image(digraph=stg, fname_image=fname_image, layout_engine=layout_engine)


def create_stg_image(primes: dict, update: str, fname_image: str, initial_states=lambda x: True, styles: List[str] = [], layout_engine: str = "dot"):
    """
    A convenience function for drawing state transition graphs directly from the prime implicants.
    *styles* must be a sublist of ["tendencies", "sccs", "mintrapspaces", "anonymous"].

    **arguments**:
        * *primes*: prime implicants
        * *fname_image*: name of image
        * *initial_states*: a function, a subspace, a state or a list of states
        * *styles*: the styles to be applied
        * *layout_engine*: one of "dot", "neato", "fdp", "sfdp", "circo", "twopi"

    **example**::

          >>> create_stg_image(primes, "asynchronous", "mapk_stg.pdf", styles=["interactionsigns", "anonymous"])
    """
    
    assert (set(styles).issubset(set(["tendencies", "sccs", "mintrapspaces", "anonymous"])))
    
    stg = primes2stg(primes, update, initial_states)
    
    if "tendencies" in styles:
        add_style_tendencies(stg)
    if "sccs" in styles:
        add_style_sccs(stg)
    if "mintrapspaces" in styles:
        add_style_mintrapspaces(primes, stg)
    if "anonymous" in styles:
        add_style_anonymous(stg)
    
    stg2image(stg=stg, fname_image=fname_image, layout_engine=layout_engine)


def copy_stg(stg: networkx.DiGraph) -> networkx.DiGraph:
    """
    Creates a copy of *stg* including all *dot* attributes.

    **arguments**:
        * *stg*: state transition graph

    **returns**:
        * *stg_copy*: new state transition graph

    **example**::

        >>> stg_copy = copy_stg(stg)
    """
    
    stg_copy = stg.copy()
    if stg_copy.graph["subgraphs"]:
        stg_copy.graph["subgraphs"] = [x.copy_primes() for x in stg_copy.graph["subgraphs"]]
    
    return stg_copy


def add_style_tendencies(stg: networkx.DiGraph):
    """
    Sets or overwrites the edge colors to reflect whether a transition increases values (*black*),
    decreases values (*red*), or both (*blue*) which is only possible for non-asynchronous transitions.

    **arguments**:
        * *stg*: state transition graph

    **example**::

          >>> add_style_tendencies(stg)
    """
    
    for source, target, attr in sorted(stg.edges(data=True)):
        inc = any([source[x] + target[x] == "01" for x in range(len(source))])
        dec = any([source[x] + target[x] == "10" for x in range(len(source))])
        
        if inc and dec:
            stg.adj[source][target]["color"] = "dodgerblue"
        
        if inc:
            continue
        
        if dec:
            stg.adj[source][target]["color"] = "red"


def add_style_sccs(stg: networkx.DiGraph):
    """
    Adds a subgraph for every non-trivial strongly connected component (SCC) to the *dot* representation of *stg*.
    Nodes that belong to the same *dot* subgraph are contained in a rectangle and treated separately during layout computations.
    Each subgraph is filled by a shade of gray that gets darker with an increasing number of SCCs that are above it in the condensation graph.
    Shadings repeat after a depth of 9.

    **arguments**:
        * *stg*: state transition graph

    **example**::

          >>> add_style_sccs(stg)
    """
    
    condensation_graph = digraph2condensationgraph(stg)
    
    for i, scc in enumerate(condensation_graph.nodes()):
        depth = condensation_graph.nodes[scc]["depth"]
        col = 2 + (depth % 8)
    
        subgraph = networkx.DiGraph()
        subgraph.add_nodes_from(scc)
        subgraph.graph["style"] = "filled"
        subgraph.graph["color"] = "black"
        subgraph.graph["fillcolor"] = f"/greys9/{col}"

        if not list(condensation_graph.successors(scc)):
            if len(scc) == 1:
                subgraph.graph["label"] = "steady state"
            else:
                subgraph.graph["label"] = "cyclic attractor"

        if not stg.graph["subgraphs"]:
            stg.graph["subgraphs"] = []

        for x in list(stg.graph["subgraphs"]):
            if sorted(x.nodes()) == sorted(subgraph.nodes()):
                stg.graph["subgraphs"].remove(x)

        stg.graph["subgraphs"].append(subgraph)


def add_style_subspaces(primes: dict, stg: networkx.DiGraph, subspaces):
    """
    Adds a *dot* subgraph for every subspace in *subspace* to *stg* - or overwrites them if they already exist.
    Nodes that belong to the same *dot* subgraph are contained in a rectangle and treated separately during layout computations.
    To add custom labels or fillcolors to a subgraph supply a tuple consisting of the
    subspace and a dictionary of subgraph attributes.

    .. note::

        *subgraphs* must satisfy the following property:
        Any two subgraphs have either empty intersection or one is a subset of the other.
        The reason for this requirement is that *dot* can not draw intersecting subgraphs.

    **arguments**:
        * *primes*: prime implicants
        * *stg*: state transition graph
        * *subspaces*: list of subspaces in string or dict representation

    **example**:

        >>> subspaces = [{"v1":0},{"v1":0,"v3":1},{"v1":1,"v2":1}]
        >>> add_style_subspaces(primes, stg, subspaces)
        >>> subspaces = ["0--","0-1","11-"]
        >>> add_style_subspaces(primes, stg, subspaces)
    """

    if not stg.graph["subgraphs"]:
        stg.graph["subgraphs"] = []
    
    for x in subspaces:
        attr = None
        
        if type(x) is not dict and len(x) == 2 and type(x[1]) is dict:
            subspace, attr = x
            
            if type(subspace) is str:
                subspace = subspace2dict(primes, subspace)
            elif type(subspace) != dict:
                raise Exception("Invalid Argument 'Subspaces'")
        
        else:
            if type(x) is str:
                subspace = subspace2dict(primes, x)
            elif type(x) is dict:
                subspace = x
            else:
                raise Exception("Invalid Argument 'Subspaces'")
        
        subgraph = networkx.DiGraph()
        subgraph.add_nodes_from(list_states_in_subspace(primes, subspace))
        subgraph.graph["color"] = "black"
        subgraph.graph["label"] = "subspace %s" % subspace2str(primes, subspace)
        if attr:
            subgraph.graph.update(attr)
        
        for x in list(stg.graph["subgraphs"]):
            if sorted(x.nodes()) == sorted(subgraph.nodes()):
                stg.graph["subgraphs"].remove(x)
        
        stg.graph["subgraphs"].append(subgraph)


def add_style_subgraphs(stg: networkx.DiGraph, subgraphs):
    """
    Adds the subgraphs given in *subgraphs* to *stg* - or overwrites them if they already exist.
    Nodes that belong to the same *dot* subgraph are contained in a rectangle and treated separately during layout computations.
    *subgraphs* must consist of tuples of the form *NodeList*, *Attributs* where *NodeList* is a list of graph nodes and *Attributes*
    is a dictionary of subgraph attributes in *dot* format.

    .. note::

        *subgraphs* must satisfy the following property:
        Any two subgraphs have either empty intersection or one is a subset of the other.
        The reason for this requirement is that *dot* can not draw intersecting subgraphs.

    **arguments**:
        * *stg*: state transition graph
        * *subgraphs*: pairs of lists and subgraph attributes

    **example**:

        >>> sub1 = (["001","010"], {"label":"critical states"})
        >>> sub2 = (["111","011"], {})
        >>> subgraphs = [sub1,sub2]
        >>> add_style_subgraphs(stg, subgraphs)
    """
    
    add_style_subgraphs(stg, subgraphs)


def add_style_mintrapspaces(primes: dict, stg: networkx.DiGraph, max_output: int = 100):
    """
    A convenience function that combines :ref:`add_style_subspaces` and :ref:`trap_spaces <trap_spaces>`.
    It adds a *dot* subgraphs for every minimal trap space to *stg* - subgraphs that already exist are overwritten.

    **arguments**:
        * *primes*: prime implicants
        * *stg*: state transition graph
        * *MaxOutput*: maximal number of minimal trap spaces, see :ref:`trap_spaces <sec:trap_spaces>`

    **example**:

        >>> add_style_mintrapspaces(primes, stg)
    """

    states = stg.nodes()
    
    for tspace in trap_spaces(primes, "min", max_output=max_output):
        subgraph = networkx.DiGraph()
        subgraph.add_nodes_from([x for x in list_states_in_subspace(primes, tspace) if x in states])
        if not subgraph.nodes():
            continue
        
        subgraph.graph["color"] = "black"
        if len(tspace) == len(primes):
            subgraph.graph["label"] = "steady state"
        else:
            subgraph.graph["label"] = "min trap space %s" % subspace2str(primes, tspace)
        
        if not stg.graph["subgraphs"]:
            stg.graph["subgraphs"] = []
        
        for x in list(stg.graph["subgraphs"]):
            if sorted(x.nodes()) == sorted(subgraph.nodes()):
                stg.graph["subgraphs"].remove(x)
        
        stg.graph["subgraphs"].append(subgraph)


def add_style_path(stg: networkx.DiGraph, path: Union[List[str], List[dict]], color: str, pen_width: int = 3):
    """
    Sets the color of all nodes and edges involved in the given *path* to *color*.

    **arguments**:
        * *stg*: state transition graph
        * *path*: state dictionaries or state strings
        * *color*: color of the path
        * *pen_width*: width of nodes and edges involved in *path* in pt

    **example**::

        >>> path = ["001", "011", "101"]
        >>> add_style_path(stg, path, "red")
    """
    
    assert path is not None
    
    path = [state2str(x) for x in path]
    
    for x in path:
        stg.nodes[x]["color"] = color
        stg.nodes[x]["penwidth"] = pen_width
    
    if len(path) > 1:
        for x, y in zip(path[:-1], path[1:]):
            stg.adj[x][y]["color"] = color
            stg.adj[x][y]["penwidth"] = pen_width


def add_style_default(primes: dict, stg: networkx.DiGraph):
    """
    A convenience function that adds styles for tendencies, SCCs and minimal trap spaces.

    **arguments**:
        * *primes*: primes implicants
        * *stg*: state transition graph

    **example**::

        >>> add_style_default(stg)
    """
    
    add_style_sccs(stg)
    add_style_tendencies(stg)
    add_style_mintrapspaces(primes, stg)


def add_style_anonymous(stg: networkx.DiGraph):
    """
    Removes the labels and draws each state as a filled circle.

    **arguments**:
        * *stg*: state transition graph

    **example**::

        >>> add_style_anonymous(stg)
    """
    
    stg.graph["node"]["shape"] = "circle"
    stg.graph["node"]["style"] = "filled"
    stg.graph["node"]["fillcolor"] = "lightgray"
    stg.graph["node"]["color"] = "none"
    
    for x in stg:
        stg.nodes[x]["label"] = ""


def successor_synchronous(primes: dict, state: Union[dict, str]) -> dict:
    """
    Returns the successor of *state* in the fully synchronous transition system defined by *primes*.
    See :ref:`Klarner2015(b) <klarner2015approx>` Sec. 2.2 for a formal definition.

    **arguments**:
        * *primes*: prime implicants
        * *state*: a state

    **returns**:
        * *successor*: the synchronous successor of *state*

    **example**::
        >>> primes = {
        'v1': [[{'v2': 0}], [{'v2': 1}]],
        'v2': [[{'v3': 0}, {'v1': 0}], [{'v1': 1, 'v3': 1}]],
        'v3': [[{'v1': 1, 'v2': 0}], [{'v2': 1}, {'v1': 0}]]
        }
        >>> state = "100"
        >>> successor_synchronous(primes, state)
        {'v1': 0, 'v2': 0, 'v3': 0}
    """
    
    if type(state) is str:
        state = state2dict(primes, state)
    
    successor = {}
    for name in primes:
        stop = False
        for value in [0, 1]:
            if stop:
                break
            for prime in primes[name][value]:
                if stop:
                    break

                if all([state[d] == v for d, v in prime.items()]):
                    successor[name] = value
                    stop = True
    
    return successor


def successors_asynchronous(primes: dict, state: Union[dict, str]) -> List[dict]:
    """
    Returns the successors of *state* in the fully asynchronous transition system defined by *primes*.
    See :ref:`Klarner2015(b) <klarner2015approx>` Sec. 2.2 for a formal definition.

    **arguments**:
        * *primes*: prime implicants
        * *state*: a state

    **returns**:
        * *successors*: the asynchronous successors of *state*

    **example**::
        >>> primes = {
        'v1': [[{'v2': 0}], [{'v2': 1}]],
        'v2': [[{'v3': 0}, {'v1': 0}], [{'v1': 1, 'v3': 1}]],
        'v3': [[{'v1': 1, 'v2': 0}], [{'v2': 1}, {'v1': 0}]]}
        >>> state = "101"
        >>> successors_asynchronous(primes, state)
        [{'v1': 0, 'v2': 0, 'v3': 1}, {'v1': 1, 'v2': 1, 'v3': 1}, {'v1': 1, 'v2': 0, 'v3': 0}]
    """
    
    if type(state) is str:
        state = state2dict(primes, state)
    
    target = successor_synchronous(primes, state)
    if target == state:
        return [target]
    
    successors = []
    for name in target:
        if state[name] != target[name]:
            successor = state.copy()
            successor[name] = target[name]
            successors.append(successor)
    
    return successors


def successors_mixed(primes: dict, state: Union[dict, str]) -> List[dict]:
    """
    Returns the successors of *state* in the mixed transition system defined by *primes*.
    The mixed update contains the synchronous and asynchronous STGs
    but it also allows transitions in which an arbitrary number of unstable components (but at least one) are updated.

    .. note::
        There are up to 2^n mixed successors for a state (n is the number of variables).

    **arguments**:
        * *primes*: prime implicants
        * *state*: a state

    **returns**:
        * *successors*: the mixed successors of *state*

    **example**::
        >>> primes = {
        'v1': [[{'v2': 0}], [{'v2': 1}]],
        'v2': [[{'v3': 0}, {'v1': 0}], [{'v1': 1, 'v3': 1}]],
        'v3': [[{'v1': 1, 'v2': 0}], [{'v2': 1}, {'v1': 0}]]
        }
        >>> state = "010"
        >>> successors_mixed(primes, state)
        [{'v1': 1, 'v2': 1, 'v3': 0},
         {'v1': 0, 'v2': 0, 'v3': 0},
         {'v1': 0, 'v2': 1, 'v3': 1},
         {'v1': 1, 'v2': 0, 'v3': 0},
         {'v1': 1, 'v2': 1, 'v3': 1},
         {'v1': 0, 'v2': 0, 'v3': 1},
         {'v1': 1, 'v2': 0, 'v3': 1}]
    """
    if type(state) == str:
        state = state2dict(primes, state)

    target = successor_synchronous(primes, state)
    if target == state:
        return [target]

    successors = []

    diff = [x for x in target if target[x] != state[x]]
    combinations = itertools.chain.from_iterable(itertools.combinations(diff, r) for r in range(1, len(diff) + 1))

    for combination in combinations:
        successor = state.copy()
        for name in combination:
            successor[name] = target[name]
        successors.append(successor)

    return successors


def random_successor_mixed(primes: dict, state: Union[dict, str]) -> dict:
    """
    Returns a random successor of *state* in the mixed transition system defined by *primes*.
    The mixed update contains the synchronous and asynchronous STGs
    but it also allows transitions in which an arbitrary number of unstable components (but at least one) are updated.

    .. note::
        The reason why this function returns a random mixed transition rather than all mixed successors is that there are up to
        2^n mixed successors for a state (n is the number of variables).

    **arguments**:
        * *primes*: prime implicants
        * *state*: a state

    **returns**:
        * *successor*: a random successor of *state* using the mixed update

    **example**::

        >>> state = "100"
        >>> random_successor_mixed(primes, state)
        {'v1':1, 'v2':1, 'v3':1}
    """

    if type(state) is str:
        state = state2dict(primes, state)

    target = successor_synchronous(primes, state)
    if target == state:
        return target
    
    names = [x for x in target if target[x] != state[x]]
    k = random.randint(1, len(names))
    
    successor = state.copy()
    for name in random.sample(names, k):
        successor[name] = target[name]
    
    return successor


def random_successor_asynchronous(primes: dict, state: Union[dict, str]) -> dict:
    """
    Returns a random asynchronous successor of *state* in the transition system defined by *primes*.

    **arguments**:
        * *primes*: prime implicants
        * *state*: a state

    **returns**:
        * *successor*: a random asynchronous successor of *state*
    """

    return random.choice(successors_asynchronous(primes, state))


def random_walk(primes: dict, update: str, initial_state: Union[dict, str], length: int):
    """
    Returns a random walk of *length* many states in the transition system defined by *primes* and *update*
    starting from a state defined by *initial_state*.
    If *initial_state* is a subspace then :ref:`random_state` will be used to draw a random state from inside it.

    **arguments**:
        * *primes*: prime implicants
        * *update*: the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
        * *initial_state*: an initial state or subspace
        * *length*: length of the random walk

    **returns**:
        * *path*: sequence of states

    **example**::

        >>> path = random_walk(primes, "asynchronous", "11---0", 4)
    """
    
    assert update in UPDATE_STRATEGIES
    
    if type(initial_state) is str:
        assert (len(initial_state) <= len(primes))
        x = {}
        for name, value in zip(sorted(primes), initial_state):
            if value.isdigit():
                x[name] = int(value)
        initial_state = x
    else:
        assert (set(initial_state).issubset(set(primes)))
    
    if update == "asynchronous":
        transition = lambda current_state: random.choice(successors_asynchronous(primes, current_state))
    
    elif update == "synchronous":
        transition = lambda current_state: successor_synchronous(primes, current_state)
    
    else:
        transition = lambda current_state: random_successor_mixed(primes, current_state)
    
    x = random_state(primes, subspace=initial_state)
    
    path = [x]
    while len(path) < length:
        path.append(transition(path[-1]))
    
    return path


def list_reachable_states(primes: dict, update: str, initial_states: List[str], memory: int):
    """
    Performs a depth-first search in the transition system defined by *primes* and *update* to list all states that
    are reachable from the *inital states*. *Memory* specifies the maximum number of states that can be kept in
    memory as "already explored" before the algorithm terminates.

    **arguments**:
        * *primes*: prime implicants
        * *update*: update strategy (either asynchronous or snchronous)
        * *initial_states*: a list of initial states
        * *memory*: maximal number of states memorized before search is stopped

    **returns**:
        * *reachable_states*: a list of all states explored

    **example**::

        >>> initial_states = ["1000", "1001"]
        >>> update = "asynchronous"
        >>> memory = 1000
        >>> states = list_reachable_states(primes, update, initial_states, memory)
        >>> print(len(states))
        287
    """
    
    if not initial_states:
        return []

    if type(initial_states) in [dict, str]:
        initial_states = [initial_states]

    initial_states = [subspace2str(primes, x) for x in initial_states]

    assert update in ["asynchronous", "synchronous"]
    
    if update == "asynchronous":
        transition_func = lambda state: successors_asynchronous(primes, state)
    else:
        transition_func = lambda state: [successor_synchronous(primes, state)]
    
    explored = set([])
    stack = set(initial_states)
    
    memory_reached = False
    counter = 0

    while stack:
        state = stack.pop()
        new_states = set([state2str(x) for x in transition_func(state)])
        not_explored = new_states.difference(explored)
        stack.update(not_explored)
        explored.add(state2str(state))
        counter += 1
        
        if len(explored) > memory:
            memory_reached = True
            break

    log.info(f"states explored: {counter}")
    if memory_reached:
        log.info(f"result incomplete. stack size at termination: {len(stack)} increase memory parameter")

    return explored


def best_first_reachability(primes: dict, initial_space: Union[str, dict], goal_space: Union[str, dict], memory: int = 1000):
    """
    Performs a best-first search in the asynchronous transition system defined by *primes* to answer the question whether there
    is a path from a random state in *InitalSpace* to a state in *GoalSpace*.
    *Memory* specifies the maximal number of states that can be kept in memory as "already explored" before the algorithm terminates.
    The search is guided by minimizing the Hamming distance between the current state of an incomplete path and the *GoalSpace*
    where variables that are free in *GoalSpace* are ignored.

    .. note::
        If the number of variables is less than 40 you should use LTL or CTL model checking to answer questions of reachability.
        :ref:`best_first_reachability` is meant for systems with more than 40 variables.
        If :ref:`best_first_reachability` returns *None* then that does not prove that there is no path between *InitialSpace* and *GoalSpace*.

    **arguments**:
        * *primes*: prime implicants
        * *initial_space*: initial subspace
        * *goal_space*: goal subspace
        * *memory*: maximal number of states memorized before search is stopped

    **returns**:
        * *path*: a path from *InitalSpace* to *GoalSpace* if it was found, or *None* otherwise.

    **example**::

        >>> initspace = "1--0"
        >>> goalspace = "0--1"
        >>> path = best_first_reachability(primes, initialstate, goalspace)
        >>> if path: print(len(path))
        4
    """
    
    if type(initial_space) is str:
        initial_space = subspace2dict(primes, initial_space)
    if type(goal_space) is str:
        goal_space = subspace2dict(primes, goal_space)
    
    xdict = random_state(primes, subspace=initial_space)
    x = state2str(xdict)
    
    fringe = []
    seen = set([])
    heapq.heappush(fringe, (hamming_distance(xdict, goal_space), [x]))
    seen.add(x)
    
    while fringe:
        dist, path = heapq.heappop(fringe)
        if dist == 0:
            return path
        
        x = path[-1]
        for ydict in successors_asynchronous(primes, state2dict(primes, x)):
            y = state2str(ydict)
            if y not in seen:
                seen.add(y)
                heapq.heappush(fringe, (hamming_distance(ydict, goal_space), path + [y]))
        
        if len(seen) > memory:
            break

    log.info(f"explored {len(seen)} transitions, no path found.")


def stg2sccgraph(stg: networkx.DiGraph) -> networkx.DiGraph:
    """
    Computes the SCC graph of the *stg*. For a definition see Sec. 3.1 of :ref:`Tournier2009 <Tournier2009>`.

    **arguments**:
        * *stg*: state transition graph

    **returns**:
        * *scc_graph*: the SCC graph of *stg*

    **example**:

        >>> sccgraph = stg2sccgraph(stg)
    """
    
    graph = digraph2sccgraph(stg)
    graph.graph["node"] = {"color": "none", "style": "filled", "shape": "rect"}
    
    for node in graph.nodes():
        lines = [",".join(x) for x in divide_list_into_similar_length_lists(node)]
        graph.nodes[node]["label"] = "<%s>" % ",<br/>".join(lines)
        if len(node) > 1 or stg.has_edge(node[0], node[0]):
            graph.nodes[node]["fillcolor"] = "lightgray"
    
    return graph


def sccgraph2dot(scc_graph: networkx.DiGraph, fname_dot: str = None):
    """
    Creates a *dot* file from a SCC graph.

    **arguments**:
        * *scc_graph*: state transition graph
        * *fname_dot*: name of *dot* file or *None*

    **returns**:
        * *text_dot*: file as string if not *FnameDOT is None*, otherwise it returns *None*


    **example**::

          >>> sccgraph2dot(sccg, "sccgraph.dot")
    """
    
    graph = scc_graph.copy()
    convert_nodes_to_anonymous_strings(graph)
    return digraph2dot(graph, fname_dot)


def sccgraph2image(scc_graph: networkx.DiGraph, fname_image: str, layout_engine: str = "dot"):
    """
    Creates an image file from a SCC graph.

    **arguments**:
        * *scc_graph*: SCC graph
        * *fname_image*: name of output file
        * *layout_engine*: one of "dot", "neato", "fdp", "sfdp", "circo", "twopi"

    **example**::

          >>> sccgraph2image(sccgraph, "mapk_sccgraph.pdf")
    """
    
    graph = scc_graph.copy()
    convert_nodes_to_anonymous_strings(graph)
    digraph2image(graph, fname_image, layout_engine)


def stg2condensationgraph(stg: networkx.DiGraph) -> networkx.DiGraph:
    """
    Converts the *stg* into the condensation graph, for a definition see :ref:`Klarner2015(b) <klarner2015approx>`.

    **arguments**:
        * *stg*: state transition graph

    **returns**:
        * *cgraph*: the condensation graph of *stg*

    **example**::

        >>> cgraph = stg2condensationgraph(stg)
    """
    
    graph = digraph2condensationgraph(stg)
    graph.graph["node"] = {"color": "none", "style": "filled", "fillcolor": "lightgray", "shape": "rect"}
    
    for node in graph.nodes():
        lines = [",".join(x) for x in divide_list_into_similar_length_lists(node)]
        graph.nodes[node]["label"] = "<%s>" % ",<br/>".join(lines)
    
    return graph


def condensationgraph2dot(cgraph: networkx.DiGraph, fname_dot: str = None):
    """
    Creates a *dot* file from a condensation graph.

    **arguments**:
        * *cgraph*: state transition graph
        * *fname_dot*: name of *dot* file or *None*

    **returns**:
        * *text_dot*: file as string if not *FnameDOT is None*, otherwise it returns *None*

    **example**::

          >>> condensationgraph2dot(cgraph, "mapk_cgraph.dot")
    """
    
    graph = cgraph.copy()
    convert_nodes_to_anonymous_strings(graph)
    return digraph2dot(graph, fname_dot)


def condensationgraph2image(cgraph: networkx.DiGraph, fname_image: str, layout_engine: str = "dot"):
    """
    Creates an image file from the condensation graph.

    **arguments**:
        * *cgraph*: condensation graph
        * *fname_image*: name of output file
        * *layout_engine*: one of "dot", "neato", "fdp", "sfdp", "circo", "twopi"

    **example**::

          >>> condensationgraph2image(cgraph, "dot", "mapk_cgraph.pdf")
    """
    
    graph = cgraph.copy()
    convert_nodes_to_anonymous_strings(graph)
    digraph2image(graph, fname_image, layout_engine)


def stg2htg(stg: networkx.DiGraph):
    """
    Computes the HTG of the *stg*. For a definition see :ref:`Berenguier2013 <Berenguier2013>`.

    **arguments**:
        * *stg*: state transition graph

    **returns**:
        * *htg*: the HTG of *stg*

    **example**::

        >>> htg = stg2htg(stg)
    """
    
    graph = networkx.DiGraph()
    graph.graph["node"] = {"color": "none"}
    
    sccs = []
    cascades = []
    attractors = []
    for x in networkx.strongly_connected_components(stg):
        x = tuple(sorted(x))
        if len(x) > 1 or stg.has_edge(x[0], x[0]):
            sccs.append(x)
            suc = find_successors(stg, x)
            if set(suc) == set(x):
                attractors.append(x)
        else:
            cascades += x
    
    graph.add_nodes_from(sccs, style="filled", fillcolor="lightgray", shape="rect")
    
    sigma = {}
    for x in cascades:
        pattern = []
        for i, A in enumerate(sccs):
            if has_path(stg, x, A):
                pattern.append(i)
        pattern = tuple(pattern)
        
        if pattern not in sigma:
            sigma[pattern] = []
        sigma[pattern].append(x)
    
    I = [tuple(sorted(x)) for x in sigma.values()]
    graph.add_nodes_from(I)
    
    for X in graph.nodes():
        for Y in graph.nodes():
            if X == Y:
                continue
            
            if has_edge(stg, X, Y):
                graph.add_edge(X, Y)
    
    for node in graph.nodes():
        lines = [",".join(x) for x in divide_list_into_similar_length_lists(node)]
        graph.nodes[node]["label"] = "<%s>" % ",<br/>".join(lines)
    
    return graph


def htg2dot(htg: networkx.DiGraph, fname_dot: str = None) -> str:
    """
    Creates a *dot* file of the *HTG*.

    **arguments**:
        * *HTG*: HTG
        * *fname_dot*: name of *dot* file or *None*

    **returns**:
        * *text_dot*: text content of dot file

    **example**::

          >>> htg2dot(cgraph, "mapk_htg.dot")
    """
    
    graph = htg.copy()
    convert_nodes_to_anonymous_strings(graph)
    return digraph2dot(graph, fname_dot)


def htg2image(htg: networkx.DiGraph, fname_image: str, layout_engine: str = "dot"):
    """
    Creates an image file from the *HTG*.

    **arguments**:
        * *HTG*: HTG
        * *fname_image*: name of output file
        * *layout_engine*: one of "dot", "neato", "fdp", "sfdp", "circo", "twopi"

    **example**::

          >>> htg2image(cgraph, "mapk_htg.pdf")
    """
    
    graph = htg.copy()
    convert_nodes_to_anonymous_strings(graph)
    digraph2image(graph, fname_image, layout_engine)


