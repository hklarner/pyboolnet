

import random
import itertools
import heapq
import os
import ConfigParser
import subprocess

BASE = os.path.abspath(os.path.join(os.path.dirname(__file__)))
BASE = os.path.normpath(BASE)
config = ConfigParser.SafeConfigParser()
config.read( os.path.join(BASE, "Dependencies", "settings.cfg") )
CMD_DOT = os.path.join( BASE, "Dependencies", config.get("Executables", "dot") )

import networkx

import ModelChecking
import TemporalQueries
import TrapSpaces

import Utility
dot2image = Utility.dot2image





def primes2stg( Primes, Update, InitialStates=lambda x: True ):
    """
    Creates the state transition graph (STG) of a network defined by *Primes* and *Update*.
    The *InitialStates* are either a list of states (in *dict* or *str* representation),
    a function that flags states that belong to the initial states, or
    a subspace (in *dict* or *str* representation).
        
    The STG is constructed by a depth first search (DFS) starting from the given initial states.
    The default for *InitialStates* is ``lambda x: True``, i.e., every state is initial.
    For a single initial state, say *"100"* use *InitialStates="100"*,
    for a set of initial states use *InitialStates=["100", "101"]* and
    for a initial subspace use *InitialStates="1--"* or the *dict* representation of subspaces.

    **arguments**:
        * *Primes*: prime implicants
        * *Update* (str): either *"asynchronous"* or *"synchronous"*
        * *InitialStates* (func / str / dict / list): a function, a subspace, a state or a list of states

    **returns**:
        * *STG* (networkx.DiGraph): state transition graph

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

    assert(Update in ['asynchronous','synchronous'])

    if len(Primes)>15:
        print "The state transition graph will consist of up to 2**%i=%i states, depending on the InitialStates."%(len(Primes),2**len(Primes))
        print "This will take a while and we might run out of memory."

    stg = networkx.DiGraph()

    if Update=="asynchronous":
        successors = lambda x: successors_asynchronous(Primes, x)
    if Update=="synchronous":
        successors = lambda x: [successor_synchronous(Primes, x)]

    names =  sorted(Primes.keys())
    space = len(names)*[[0,1]]

    if hasattr(InitialStates, '__call__'):
        fringe = [dict(zip(names, values)) for values in itertools.product(*space)]
        fringe = [state for state in fringe if InitialStates(state)]

    elif type(InitialStates)==str:
        assert(len(InitialStates)==len(names))
        fringe = subspace2states(names, InitialStates)

    elif type(InitialStates)==dict:
        fringe = subspace2states(names, InitialStates)
        
    else:
        assert(all(len(x)==len(names) for x in InitialStates))
        fringe = [x if type(x)==dict else dict(zip(names,map(int,x))) for x in InitialStates]
        
    
    seen = set([])
    
    while fringe:
        state = fringe.pop()
        source = ''.join([str(state[x]) for x in names])

        if source in seen:
            continue
        
        for suc in successors(state):
            target = ''.join([str(suc[x]) for x in names])
            stg.add_edge(source, target)

            if target not in seen:
                if suc not in fringe:
                    fringe.append( suc )

        seen.add(source)

    # defaults
    stg.graph["node"]  = {"shape":"rect","color":"none","fillcolor":"none"}
    stg.graph["edge"]  = {}
    stg.graph["subgraphs"]  = []

    # heuristic scaling to avoid overlapping node labels
    if Update=="synchronous":
        stg.graph["overlap"] = "compress"
    else:
        stg.graph["overlap"] = "scale"
    return stg


def stg2dot( STG, FnameDOT=None ):
    """
    Creates a *dot* file from a state transition graph.
    Graph, node and edge attributes are passed to the *dot* file by adding the respective key and value pairs to the graph, node or edge data.
    Node and edge defaults are set by the specials graph keys *"node"* and *"edge"* and must have attribute dictionaries as values.
    For a list of attributes see http://www.graphviz.org/doc/info/attrs.html.

    **arguments**:
        * *STG*: state transition graph
        * *FnameDOT* (str): name of *dot* file or *None*

    **returns**:
        * *FileDOT* (str): file as string if not *FnameDOT==None*, otherwise it returns *None*


    **example**::

          >>> stg = primes2stg(primes, update, init)
          >>> igraph.graph["label"] = "IRMA Network - State Transition Graph"
          >>> igraph.graph["node"] = {"style":"filled", "color":"red"}
          >>> igraph.graph["edge"] = {"arrowsize": 2.0}      
          >>> igraph.node["001000"]["fontsize"] = 20
          >>> igraph.edge["001110"]["001010"]["style"] = "dotted"
          >>> stg2image( igraph, "irma_stg.pdf")
    """

    if STG.order()==0:
        print "State transition graph has no nodes."
        if FnameDOT!=None:
            print FnameDot, "was not created."
        return

    assert( type(STG.nodes()[0])==str )
    
    lines = ['digraph "State Transition Graph" {','']
    lines += Utility.digraph2dot(STG)
    lines += ['}']

    if FnameDOT==None:
        return '\n'.join(lines)
    
    with open(FnameDOT, 'w') as f:
        f.writelines('\n'.join(lines))
    print "created", FnameDOT
    


def stg2image(STG, FnameIMAGE, Silent=False):
    """
    Creates an image file from a state transition graph using :ref:`installation_graphviz` and the layout engine *dot*.
    Use ``dot -T?`` to find out which output formats are supported on your installation.
    
    **arguments**:
        * *STG*: state transition graph
        * *FnameIMAGE* (str): name of output file
        * *Silent* (bool): disables print statements
        
    **example**::

          >>> stg2image(stg, "mapk_stg.pdf")
          >>> stg2image(stg, "mapk_stg.jpg")
          >>> stg2image(stg, "mapk_svg.pdf")
    """

    assert( FnameIMAGE.count('.')>=1 and FnameIMAGE.split('.')[-1].isalnum() )

    filetype = FnameIMAGE.split('.')[-1]

    cmd = [CMD_DOT, "-T"+filetype, "-o", FnameIMAGE]
    dotfile = stg2dot( STG, FnameDOT=None)
    
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = proc.communicate( input=dotfile )
    proc.stdin.close()

    if not (proc.returncode == 0) or not os.path.exists(FnameIMAGE):
        print out
        print 'dot did not respond with return code 0'
        raise Exception
    
    if not Silent:
        print "created", FnameIMAGE

        
def copy( STG ):
    """
    Creates a copy of *STG* including all *dot* attributes.

    **arguments**:
        * *STG*: state transition graph

    **returns**:
        * *STG2*: new state transition graph

    **example**::

        >>> stg2 = copy(stg)
    """
    
    newgraph = STG.copy()
    if newgraph.graph["subgraphs"]:
        newgraph.graph["subgraphs"] = [x.copy() for x in newgraph.graph["subgraphs"]]

    return newgraph


def add_style_tendencies( STG ):
    """
    Sets or overwrites the edge colors to reflect whether a transition increases values (*black*),
    decreases values (*red*), or both (*blue*) which is only possible for non-asynchronous transitions.
    
    **arguments**:
        * *STG*: state transition graph
        
    **example**::

          >>> add_style_tendencies(stg)
    """
    
    for source, target, attr in sorted(STG.edges(data=True)):
        inc = any([source[x]+target[x]=="01" for x in range(len(source))])
        dec = any([source[x]+target[x]=="10" for x in range(len(source))])

        if inc and dec:
            STG.edge[source][target]["color"] = "dodgerblue"
            
        if inc:
            continue
        
        if dec:
            STG.edge[source][target]["color"] = "red"
            
def add_style_sccs( STG ):
    """
    Adds a subgraph for every non-trivial strongly connected component (SCC) to the *dot* representation of *STG*.
    Nodes that belong to the same *dot* subgraph are contained in a rectangle and treated separately during layout computations.
    Each subgraph is filled by a shade of gray that gets darker with an increasing number of SCCs that are above it in the condensation graph.
    Shadings repeat after a depth of 9.

    **arguments**:
        * *STG*: state transition graph
        
    **example**::

          >>> add_style_sccs(stg)
    """
    
    condensation_graph = Utility.digraph2condensationgraph(STG)

    for i,scc in enumerate(condensation_graph.nodes()):
        name = "cluster_%i"%i
        depth = condensation_graph.node[scc]["depth"]
        col = 2+(depth % 8)

        subgraph = networkx.DiGraph()
        subgraph.add_nodes_from(scc)
        subgraph.graph["style"] = "filled"
        subgraph.graph["color"] = "black"
        subgraph.graph["fillcolor"] = "/greys9/%i"%col

        if not condensation_graph.successors(scc):
            if len(scc)==1:
                subgraph.graph["label"] = "steady state"
            else:
                subgraph.graph["label"] = "cyclic attractor"

        if not STG.graph["subgraphs"]:
            STG.graph["subgraphs"] = []

        # overwrite existing subgraphs
        for x in list(STG.graph["subgraphs"]):
            if sorted(x.nodes()) == sorted(subgraph.nodes()):
                STG.graph["subgraphs"].remove(x)
                
        STG.graph["subgraphs"].append( subgraph )
        

def add_style_subspaces( Primes, STG, Subspaces ):
    """
    Adds a *dot* subgraph for every subspace in *Subspace* to *STG* - or overwrites them if they already exist.
    Nodes that belong to the same *dot* subgraph are contained in a rectangle and treated separately during layout computations.
    To add custom labels or fillcolors to a subgraph supply a tuple consisting of the
    subspace and a dictionary of subgraph attributes.

    .. note::
    
        *Subgraphs* must satisfy the following property:
        Any two subgraphs have either empty intersection or one is a subset of the other.
        The reason for this requirement is that *dot* can not draw intersecting subgraphs.

    **arguments**:
        * *Primes*: prime implicants
        * *STG*: state transition graph
        * *Subspaces* (list): list of subspaces in string or dict representation

    **example**:

        >>> subspaces = [{"v1":0},{"v1":0,"v3":1},{"v1":1,"v2":1}]
        >>> add_style_subspaces(primes, stg, subspaces)
        >>> subspaces = ["0--","0-1","11-"]
        >>> add_style_subspaces(primes, stg, subspaces)
    """

    names = sorted(Primes.keys())
    
    if not STG.graph["subgraphs"]:
        STG.graph["subgraphs"] = []

    for x in Subspaces:

        attr = None

        # (subspace, attributes)
        if type(x)!=dict and len(x)==2 and type(x[1])==dict:
            subspace, attr = x
            
            # subspace = "11--1-"
            if type(subspace)==str:
                subspace = str2subspace(Primes, subspace)
            elif not type(subspace)==dict:
                raise Exception("Invalid Argument 'Subspaces'")
            
        else:
            # subspace = "11--1-"
            if type(x)==str:
                subspace = str2subspace(Primes, x)
            # subspace = {"v1":0,"v5":1}
            elif type(x)==dict:
                subspace = x
            else:
                raise Exception("Invalid Argument 'Subspaces'")

        subgraph = networkx.DiGraph()
        subgraph.add_nodes_from([state2str(x) for x in subspace2states(Primes,subspace)])
        subgraph.graph["color"] = "black"
        subgraph.graph["label"] = "subspace %s"%subspace2str(Primes, subspace)
        if attr:
            subgraph.graph.update(attr)
            
        # overwrite existing subgraphs
        for x in list(STG.graph["subgraphs"]):
            if sorted(x.nodes()) == sorted(subgraph.nodes()):
                STG.graph["subgraphs"].remove(x)

        STG.graph["subgraphs"].append(subgraph)


def add_style_mintrapspaces( Primes, STG, MaxOutput=100):
    """
    A convenience function that combines :ref:`add_style_subspaces` and :ref:`TrapSpaces.trap_spaces <trap_spaces>`.
    It adds a *dot* subgraphs for every minimal trap space to *STG* - subgraphs that already exist are overwritten.

    **arguments**:
        * *Primes*: prime implicants
        * *STG*: state transition graph
        * *MaxOutput* (int): maximal number of minimal trap spaces, see :ref:`trap_spaces <sec:trap_spaces>`

    **example**:

        >>> add_style_mintrapspaces(primes, stg)
    """
    
    names = sorted(Primes.keys())
    states = STG.nodes()
    smallest_subspace = bounding_box(Primes,states)
    
    for tspace in TrapSpaces.trap_spaces_insideof(Primes, "min", smallest_subspace, MaxOutput=MaxOutput):

        subgraph = networkx.DiGraph()
        subgraph.add_nodes_from([state2str(x) for x in subspace2states(Primes,tspace) if state2str(x) in states])
        if not subgraph.nodes():
            continue

        subgraph.graph["color"] = "black"
        if len(tspace)==len(Primes):
            subgraph.graph["label"] = "steady state"
        else:
            subgraph.graph["label"] = "min trap space %s"%subspace2str(Primes,tspace)

        if not STG.graph["subgraphs"]:
            STG.graph["subgraphs"] = []

        # overwrite existing subgraphs
        for x in list(STG.graph["subgraphs"]):
            if sorted(x.nodes()) == sorted(subgraph.nodes()):
                STG.graph["subgraphs"].remove(x)

        STG.graph["subgraphs"].append( subgraph )


def add_style_condensation( STG ):
    """
    Adds a separate graph to *STG* that depicts the *condensation graph*, a map of how the SCCs regulate each other.
    A node in the condensation graph indicates how many states are contained in the respective SCC.
    If the SCC contains a single state then its name is displayed.
    
    **arguments**:
        * *STG*: state transition graph
        
    **example**::

          >>> add_style_condensation(stg)
    """

    condensation_graph = Utility.digraph2condensationgraph(STG)
    STG.graph["condensation"] = condensation_graph    
        

def add_style_path( STG, Path, Color, Penwidth=3 ):
    """
    Sets the color of all nodes and edges involved in the given *Path* to *Color*.

    **arguments**:
        * *STG*: state transition graph
        * *Path* (list): state dictionaries or state strings
        * *Color* (str): color of the path
        * *Penwidth* (int): width of nodes and edges involved in *Path* in pt
    
    **example**::

        >>> path = ["001", "011", "101"]
        >>> add_style_path(stg, path, "red")
    """

    assert( Path != None )

    Path = [state2str(x) if type(x)==dict else x for x in Path]

    for x in Path:
        STG.node[x]["color"] = Color
        STG.node[x]["penwidth"]  = "%i"%Penwidth
        
    if len(Path)>1:
        for x,y in zip(Path[:-1],Path[1:]):
            STG.edge[x][y]["color"]     = Color
            STG.edge[x][y]["penwidth"]  = "%i"%Penwidth
                    
            
def add_style_default( Primes, STG ):
    """
    A convenience function that adds styles for tendencies, SCCs, minimal trap spaces and the condensation graph.

    **arguments**:
        * *Primes*: primes implicants
        * *STG*: state transition graph
    
    **example**::

        >>> add_style_default(stg)
    """

    add_style_sccs(STG)
    add_style_tendencies(STG)
    add_style_condensation(STG)
    add_style_mintrapspaces(Primes, STG)


def successor_synchronous( Primes, State ):
    """
    Returns the successor of *State* in the fully synchronous transition system defined by *Primes*.
    See :ref:`Klarner2015(b) <klarner2015approx>` Sec. 2.2 for a formal definition.

    **arguments**:
        * *Primes*: prime implicants
        * *State* (str / dict): a state

    **returns**:
        * *Successor* (dict): the synchronous successor of *State* 

    **example**::

            >>> state = "100"
            >>> successor_synchronous(primes, state)
            {'v1':0, 'v2':1, 'v3':1}
    """
    if type(State)==str:
        State = str2state(Primes, State)
        
    successor = {}
    for name in Primes:
        stop = False
        for value in [0,1]:
            if stop: break
            for prime in Primes[name][value]:
                if stop: break
                if all([State[d]==v for d,v in prime.items()]):
                    successor[name]=value
                    stop = True
                    
    return successor


def successors_asynchronous( Primes, State ):
    """
    Returns the successors of *State* in the fully asynchronous transition system defined by *Primes*.
    See :ref:`Klarner2015(b) <klarner2015approx>` Sec. 2.2 for a formal definition.

    **arguments**:
        * *Primes*: prime implicants
        * *State* (str / dict): a state

    **returns**:
        * *Successors* (list): the asynchronous successors of *State* 

    **example**::

            >>> state = "100"
            >>> successors_asynchronous(primes, state)
            [{'v1':1, 'v2':1, 'v3':1},{'v1':0, 'v2':0, 'v3':1},{'v1':0, 'v2':1, 'v3':0}]
    """

    if type(State)==str:
        State = str2state(Primes, State)
        
    target = successor_synchronous(Primes,State)
    if target == State:
        return [target]
    
    successors = []
    for name in target:
        if State[name] != target[name]:
            successor = State.copy()
            successor[name] = target[name]
            successors.append( successor )
    
    return successors


def random_successor_mixed( Primes, State ):
    """
    Returns a random successor of *State* in the mixed transition system defined by *Primes*.
    The mixed update contains the synchronous and asynchronous STGs
    but it also allows transitions in which an arbitrary number of unstable components (but at least one) are updated.

    .. note::
        The reason why this function returns a random mixed transition rather than all mixed successors is that there are up to
        2^n mixed successors for a state (n is the number of variables).

    **arguments**:
        * *Primes*: prime implicants
        * *State* (str / dict): a state

    **returns**:
        * *Successor* (dict): a random successor of *State* using the mixed update

    **example**::

            >>> state = "100"
            >>> random_successor_mixed(primes, state)
            {'v1':1, 'v2':1, 'v3':1}
    """

    target = successor_synchronous(Primes,State)
    if target == State:
        return target

    names = [x for x in target if target[x]!=State[x]]
    k = random.randint(1,len(names))
    successor = State.copy()
    for name in random.sample(names, k):
        State[name]=target[name]

    return State


def random_state( Primes, Subspace={} ):
    """
    Generates a random state of the transition system defined by *Primes*.
    If *Subspace* is given then the state will be drawn from that subspace.

    **arguments**:
        * *Primes*: prime implicants
        * *Subspace* (str / dict): a subspace

    **returns**:
        * *State* (dict): random state inside *Subspace*

    **example**::
        
        >>> random_state(primes)
        {'v1':1, 'v2':1, 'v3':1}
        >>> random_state(primes, {"v1":0})
        {'v1':0, 'v2':1, 'v3':0}
        >>> random_state(primes, "0--")
        {'v1':0, 'v2':0, 'v3':1}
    """

    
    
    if type(Subspace)==str:
        assert(len(Subspace)==len(Primes))
        x = {}
        for name, value in zip(sorted(Primes.keys()), Subspace):
            if value.isdigit():
                x[name] = int(value)
        Subspace = x
    else:
        assert( set(Subspace.keys()).issubset(set(Primes.keys())) )

    return dict(Subspace.items() + [(x,random.choice([0,1])) for x in Primes if not x in Subspace])
    
    
def random_walk( Primes, Update, InitialState, Length ):
    """
    Returns a random walk of *Length* many states in the transition system defined by *Primes* and *Update*
    starting from a state defined by *InitialState*.
    If *InitialState* is a subspace then :ref:`random_state` will be used to draw a random state from inside it.

    **arguments**:
        * *Primes*: prime implicants
        * *Update* (str): the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
        * *InitialState* (str / dict): an initial state or subspace
        * *Length* (int): length of the random walk

    **returns**:
        * *Path* (list): sequence of states

    **example**::

        >>> path = random_walk(primes, "asynchronous", "11---0", 4)
    """

    assert( Update in ['asynchronous','synchronous', 'mixed'] )
    assert( set(InitialState.keys()) == set(Primes.keys()) )


    if Update=='asynchronous':
        transition = lambda current_state: random.choice(successors_asynchronous(Primes,current_state))
        
    elif Update=='synchronous':
        transition = lambda current_state: successor_synchronous(Primes,current_state)

    elif Update=='mixed':
        transition = lambda current_state: random_successor_mixed(Primes,current_state)

    x = random_state(Primes, Subspace=InitialState)

    Path = [dict(InitialState)]
    while len(Path)<Length:
        Path.append( transition(Path[-1]) )

    return Path
    
    

def best_first_reachability( Primes, InitialSpace, GoalSpace, Memory=1000 ):
    """
    Performs a best-first search in the asynchronous transition system defined by *Primes* to answer the question whether there
    is a path from a random state in *InitalSpace* to a state in *GoalSpace*.
    *Memory* specifies the maximal number of states that can be kept in memory as "already explored" before the algorithm terminates.
    The search is guided by minimizing the Hamming distance between the current state of an incomplete path and the *GoalSpace*
    where variables that are free in *GoalSpace* are ignored.

    .. note::
        If the number of variables is less than 40 you should use LTL or CTL model checking to answer questions of reachability.
        :ref:`best_first_reachability` is meant for systems with more than 40 variables.
        If :ref:`best_first_reachability` returns *None* then that does not prove that there is no path between *InitialSpace* and *GoalSpace*.
    
    **arguments**:
        * *Primes*: prime implicants
        * *InitialSpace* (str / dict): initial subspace
        * *GoalSpace* (str / dict): goal subspace
        * *Memory* (int): maximal number of states memorized before search is stopped

    **returns**:
        * *Path* (list): a path from *InitalSpace* to *GoalSpace* if it was found, or *None* otherwise.

    **example**::
    
            >>> initspace = "1--0"
            >>> goalspace = "0--1"
            >>> path = best_first_reachability(primes, initialstate, goalspace)
            >>> if path: print(len(path))
            4
    """
    
    assert( set(InitialSpace.keys()).issubset(set(Primes.keys())) )
    assert( set(GoalSpace.keys()).issubset(set(Primes.keys())) )

    x = random_state(Primes, Subspace=InitialSpace)
    
    fringe = []
    seen  = set([])
    heapq.heappush(fringe, (hamming_distance(x,GoalSpace), [x]))
    seen.add(state2str(x))

    while fringe:
        dist, path = heapq.heappop(fringe)
        if dist==0:
            return path

        x = path[-1]
        for y in successors_asynchronous(Primes, x):
            y_hash = state2str(y)
            if y_hash not in seen:
                seen.add(y_hash)
                heapq.heappush(fringe, (hamming_distance(y,GoalSpace), path+[y]))
                
        if len(seen)>Memory:
            return None
        
    return None


def state2str( State ):
    """
    Converts the dictionary representation of a state into the string representation of a state.

    **arguments**
        * *State* (dict): dictionary representation of state

    **returns**
        * *State* (str): string representation of state

    **example**::

        >>> state = {"v2":0, "v1":1, "v3":1}
        >>> state2str(primes, state)
        '101'
    """
    
    return ''.join([str(State[x]) for x in sorted(State)])


def str2state( Primes, State ):
    """
    Converts the string representation of a state into the dictionary representation of a state.

    **arguments**
        * *Primes*: prime implicants or a list of names
        * *State* (str): string representation of state

    **returns**
        * *State* (dict): dictionary representation of state

    **example**::

        >>> state = "101"
        >>> str2state(primes, state)
        {'v2':0, 'v1':1, 'v3':1}
    
    """
    
    assert(len(State)==len(Primes))

    return dict((k,int(v)) for k,v in zip(sorted(Primes.keys()), State))


def subspace2str( Primes, Subspace ):
    """
    Converts the dictionary representation of a subspace into the string representation of a subspace.
    Uses "-" to indicate free variables.
    
    **arguments**
        * *Primes*: prime implicants or a list of names
        * *Subspace* (dict): a subspace

    **returns**
        * *Subspace* (str): the string representation of *Subspace*

    **example**::

        >>> sub = {"v2":0, "v3":1}
        >>> subspace2str(primes, sub)
        '-01'
    """
    
    assert(set(Subspace.keys()).issubset(set(Primes)))
    
    return ''.join([str(Subspace[x]) if x in Subspace else "-" for x in sorted(Primes)])


def str2subspace( Primes, Str ):
    """
    Converts the string representation of a subspace into the dictionary representation of a subspace.
    Use "-" to indicate free variables.
    
    **arguments**
        * *Primes*: prime implicants or a list of names
        * *Subspace* (str): a subspace

    **returns**
        * *Subspace* (dict): the dictionary representation of subspace

    **example**::

        >>> sub = "-01"
        >>> str2subspace(primes, sub)
        {'v2':0, 'v3':1}
    """
    
    return dict([(name, int(value)) for name, value in zip(sorted(Primes), Str) if not value=="-"])




def subspace2states( Primes, Subspace ):
    """
    Generates all states contained in *Subspace*.

    **arguments**:
        * *Primes*: prime implicants or a list of names
        * *Subspace* (str or dict): a subspace

    **returns**:
        * *States* (list): the states contained in *Subspace*

    **example**:

        >>> subspace = "1-1"
        >>> subspace2states(primes,subspace)
        [{'v1':1,'v2':0,'v3':1},{'v1':1,'v2':1,'v3':1}]
    """

    names = sorted(Primes)
    ranges = [[Subspace[x]] if x in Subspace else [0,1] for x in names]

    states = []
    for values in itertools.product(*ranges):
        state = dict(zip(names,values))
        states.append(state)

    return states


def subspace_intersection( Subspaces ):
    # not in the manual
    """
    Returns the intersection of the *Subspaces*.
    Raises an exception if there are two subspaces that are not consistent.

    **arguments**:
        * *Subspaces*: a list of subspaces

    **returns**:
        * *Subspace*: the intersection

    **example**::

        subspaces = [{"v1":0},{"v2":0}]
        print subspace_intersection(subspaces)
        >>> {"v1":0,"v2":0}
    """

    items = set([])

    for x in Subspaces:
        items_new = set(x.items())
        intersection = items.intersection(items_new)
        if intersection:
            print intersection
            print "found inconsistent subspaces."
            raise Exception
        items.update(items_new)

    return dict(items)


def bounding_box(Primes, Subspaces):
    # not in the manual
    """
    returns the smallest subspaces that contains all *Subspaces*
    """

    names   = sorted(Primes.keys())
    seen    = set([])
    result  = {}
    
    for x in Subspaces:
        if type(x)==str:
            assert(len(x)==len(names))
            x = dict(zip(names,map(int,x)))
            
        for name in x:
            if name in seen:
                continue

            if name in result:
                if result[name] != x[name]:
                    seen.add(name)
                    result.pop(name)
            else:
                result[name] = x[name]
                
    return result


def hamming_distance(Subspace1, Subspace2):
    """
    Returns the Hamming distance between to subspaces.
    Variables that are free in either subspace are ignored.

    **arguments**:
        * *Subspace1, Subspace2* (dict): subspaces in dictionary representation

    **returns**:
        * *Distance* (int): the distance between *Subspace1* and *Subspace2*

    **example**:

        >>> hamming_distance({"v1":0,"v2":0}, {"v1":1,"v2":1})
        2
        >>> hamming_distance({"v1":1}, {"v2":0})
        0
    """
    
    return len([k for k,v in Subspace1.items() if k in Subspace2 and Subspace2[k]!=v])







