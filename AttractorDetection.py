

import datetime
import itertools
import random

from . import FileExchange
from . import PrimeImplicants
from . import StateTransitionGraphs
from . import TrapSpaces
from . import InteractionGraphs
from . import ModelChecking
from . import TemporalQueries
from . import Utility


def find_attractor_by_randomwalk_and_ctl( Primes, Update, InitialState={}, Length=0, Attempts=10 ):
    """
    Attempts to find a state inside an attractor by the "long random walk" method,
    see :ref:`Klarner2015(b) <klarner2015approx>` Sec. 3.2 for a formal definition.
    The method generates a random walk of *Length* many states, starting from a state defined by *InitialState*.
    If *InitialState* is a subspace then :ref:`random_state` will be used to draw a random state from inside it.
    The function then uses CTL model checking, i.e., :ref:`ModelChecking.check_primes <check_primes>`,
    to decide whether the last state of the random walk is inside an attractor.
    If so it is returned, otherwise the process is repeated.
    If no attractor state has been found after *Attempts* many trials an exception is raised.

    .. note::
        The default value for length, namely *Length=0*, will be converted::

            Length = 10*len(Primes)

        which proved sufficient in out computer experiments.
        
    **arguments**:
        * *Primes*: prime implicants
        * *Update* (str):  the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
        * *InitialState* (str / dict): an initial state or subspace
        * *Length* (int): length of random walk
        * *Attempts* (int): number of attempts before exception is raised

    **returns**:
        * *State* (dict): a state that belongs to some attractor
        * raises *Exception* if no attractor state is found

    **example**::

            >>> find_attractor_by_randomwalk_and_ctl(primes, "asynchronous")
            {'v1':1, 'v2':1, 'v3':1}
    """

    assert( Update in ['asynchronous','synchronous', 'mixed'] )
    assert( set(InitialState.keys()).issubset(set(Primes.keys())) )

    # length heuristic
    if Length==0:
        Length = 10*len(Primes)

    # transition function
    if Update=='asynchronous':
        transition = lambda current_state: random.choice(StateTransitionGraphs.successors_asynchronous(Primes,current_state))
        
    elif Update=='synchronous':
        transition = lambda current_state: StateTransitionGraphs.successor_synchronous(Primes,current_state)

    elif Update=='mixed':
        transition = lambda current_state: StateTransitionGraphs.random_successor_mixed(Primes,current_state)


    trials = 0
    while trials < Attempts:
        current_state = StateTransitionGraphs.random_state( Primes, InitialState )

        transitions = 0
        while transitions < Length:
            current_state = transition(current_state)
            transitions+=1

        spec = 'CTLSPEC ' + TemporalQueries.AGEF_oneof_subspaces(Primes, [current_state])
        init = 'INIT ' + TemporalQueries.subspace2proposition( Primes, current_state )
        if ModelChecking.check_primes(Primes, Update, init, spec):
            return current_state
        
        trials+=1

    print("found no attractor after generating %i random walks of length %i."%(Attempts, LengthRandomWalk))
    print("increase either or both values.")
    raise Exception


def compute_attractors_tarjan( Primes, STG ):
    """
    Uses `networkx.strongly_connected_components <https://networkx.github.io/documentation/latest/reference/generated/networkx.algorithms.components.strongly_connected.strongly_connected_components.html>`_
    , i.e., Tarjan's algorithm with Nuutila's modifications, to compute the SCCs of *STG* and
    `networkx.has_path <https://networkx.github.io/documentation/latest/reference/generated/networkx.algorithms.shortest_paths.generic.has_path.html>`_
    to decide whther a SCC is reachable from another.
    Returns the attractors, i.e., those SCCs from which no other SCC is reachable.
    

    **arguments**:
        * *Primes*: prime implicants
        * *STG*: state transition graph

    **returns**:
        * *Attractors* (list of tuples of states): the attractors

    **example**:

        >>> bnet = ["x, !x&y | z",
        ...         "y, !x | !z",
        ...         "z, x&!y"]
        >>> bnet = "\\n".join(bnet)
        >>> primes = FEX.bnet2primes(bnet)
        >>> stg = STGs.primes2stg(primes, "asynchronous")
        >>> attractors = STGs.compute_attractors_tarjan(stg)
        >>> for A in attractors:
        ...     print(A)
        [{'v1': 1, 'v2': 0, 'v3': 1}]
        [{'v1': 0, 'v2': 1, 'v3': 0}, {'v1': 1, 'v2': 1, 'v3': 0}]
    """

    condensation_graph = Utility.DiGraphs.digraph2condensationgraph(STG)

    attractors = []
    for scc in condensation_graph.nodes():
        if not condensation_graph.successors(scc):
            scc = [StateTransitionGraphs.str2state(Primes, x) for x in scc]
            attractors+= [scc]

    return attractors

        



def univocal( Primes, Update, Trapspace ):
    """
    The model checking and random-walk-based method for deciding whether *Trapspace* is univocal,
    i.e., whether there is a unique attractor contained in it,
    in the state transition graph defined by *Primes* and *Update*.
    The approach is described and discussed in :ref:`Klarner2015(a) <klarner2015trap>`.
    The function performs two steps: first it searches for a state that belongs to an attractor inside of *Trapspace* using
    the random-walk-approach and the function :ref:`random_walk <random_walk>`,
    then it uses CTL model checking, specifically the pattern :ref:`AGEF_oneof_subspaces <AGEF_oneof_subspaces>`,
    to decide if the attractor is unique inside *Trapspace*.
    
    .. note::
        In the (very unlikely) case that the random walk does not end in an attractor state an exception will be raised.

    .. note::
        Univocality depends on the update strategy, i.e.,
        a trapspace may be univocal in the synchronous STG but not univocal in the asynchronous STG or vice versa.

    .. note::
        A typical use case is to decide whether a minimal trap space is univocal.

    .. note::
        *Trapspace* is in fact not required to be a trap set, i.e., it may be an arbitrary subspace.
        If it is an arbitrary subspace then the involved variables are artificially fixed to be constant.
        
    **arguments**:
        * *Primes*: prime implicants
        * *Update* (str): the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
        * *Trapspace* (str / dict): a subspace
        
    **returns**:
        * *Answer* (bool): whether *Trapspace* is univocal in the STG defined by *Primes* and *Update*
        * *AttractorState* (dict): a state that belongs to an attractor
        * *CounterExample* (dict): a state that belongs to another attractor (if *Answer* is *False*)

    **example**::

        >>> mintspaces = TrapSpaces.trap_spaces(primes, "min")
        >>> trapspace = mintrapspaces[0]
        >>> answer, state, counterex = univocal(primes, trapspace, "asynchronous")
        >>> answer
        True
    """

    if type(Trapspace)==str:
        Trapspace=StateTransitionGraphs.str2subspace(Primes, Trapspace)

    # percolation
    primes = PrimeImplicants.copy(Primes)
    PrimeImplicants.create_constants(primes, Constants=Trapspace)
    constants  = PrimeImplicants.percolate_and_remove_constants(primes)
        
    # trivial case: constants = unique steady state
    if primes == {}:
        return (True, constants, None)

    # find attractor state
    attractor_state1 = find_attractor_by_randomwalk_and_ctl( primes, Update )

    # univocality
    spec = 'CTLSPEC ' + TemporalQueries.EF_oneof_subspaces(primes, [attractor_state1])
    init = 'INIT TRUE'
    answer, counterex = ModelChecking.check_primes_with_counterexample(primes, Update, init, spec)

    attractor_state1 = dict(list(attractor_state1.items()) + list(constants.items()))

    # success
    if answer:
        return (True, attractor_state1, None)

    # failure
    else:
        attractor_state2 = find_attractor_by_randomwalk_and_ctl( primes, Update, counterex[-1] )
        attractor_state2 = dict(list(attractor_state2.items()) + list(constants.items()))
        return (False, attractor_state1, attractor_state2)
    
    
            

def faithful( Primes, Update, Trapspace ):
    """
    The model checking approach for deciding whether *Trapspace* is faithful,
    i.e., whether all free variables oscillate in all of the attractors contained in it,
    in the state transition graph defined by *Primes* and *Update*.
    The approach is described and discussed in :ref:`Klarner2015(a) <klarner2015trap>`.
    It is decided by a single CTL query of the pattern :ref:`EF_all_unsteady <EF_all_unsteady>`.

    .. note::
        Faithfulness depends on the update strategy, i.e.,
        a trapspace may be faithful in the synchronous STG but not faithful in the asynchronous STG or vice versa.

    .. note::
        A typical use case is to decide whether a minimal trap space is faithful.

    .. note::
        *Trapspace* is in fact not required to be a trap set, i.e., it may be an arbitrary subspace.
        If it is an arbitrary subspace then the involved variables are artificially fixed to be constant.
        
    **arguments**:
        * *Primes*: prime implicants
        * *Update* (str): the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
        * *Trapspace* (str / dict): a subspace

    **returns**:
        * *Answer* (bool): whether *Trapspace* is faithful in the STG defined by *Primes* and *Update*
        * *CounterExample* (dict): a state that belongs to an attractor that does not oscillate in all free variables (if *Answer* is *False*)

    **example**::

        >>> mintspaces = TrapSpaces.trap_spaces(primes, "min")
        >>> answer, counterex = faithful(primes, mintspaces[0])
        >>> answer
        True
    """

    if type(Trapspace)==str:
        Trapspace=StateTransitionGraphs.str2subspace(Primes, Trapspace)

    # trivial case: steady state
    if len(Trapspace)==len(Primes):
        return True, None
    
    # percolation
    primes = PrimeImplicants.copy(Primes)
    PrimeImplicants.create_constants(primes, Constants=Trapspace)
    constants  = PrimeImplicants.percolate_and_remove_constants(primes)

    # trivial case: free variables fix due to percolation
    if len(constants)>len(Trapspace):
        counterex = find_attractor_by_randomwalk_and_ctl( primes, Update )
        attractor_state = dict(list(counterex[-1].items()) + list(constants.items()))
        return (False, attractor_state)

    # faithfulness
    spec = 'CTLSPEC AG(%s)'%TemporalQueries.EF_unsteady_states(primes)
    init = 'INIT TRUE'
    answer, counterex = ModelChecking.check_primes_with_counterexample(primes, Update, init, spec)

    # success
    if answer:
        return True, None

    # failure
    else:
        attractor_state = dict(list(counterex[-1].items()) + list(constants.items()))
        return False, attractor_state
    

def completeness_naive( Primes, Update, Trapspaces ):
    """
    The naive approach to deciding whether *Trapspaces* is complete,
    i.e., whether there is no attractor outside of *Trapspaces*.
    The approach is described and discussed in :ref:`Klarner2015(a) <klarner2015trap>`.
    It is decided by a single CTL query of the :ref:`EF_oneof_subspaces <EF_oneof_subspaces>`.
    The state explosion problem limits this function to networks with around 40 variables.
    For networks with more variables (or a faster answer) use :ref:`completeness_iterative <completeness_iterative>`.

    .. note::
        Completeness depends on the update strategy, i.e.,
        a set of subspaces may be complete in the synchronous STG but not complete in the asynchronous STG or vice versa.

    .. note::
        A typical use case is to decide whether the minimal trap spaces of a network are complete.

    .. note::
        The subspaces of *Trapspaces* are in in fact not required to be a trap sets, i.e., it may contain arbitrary subspaces.
        If there are arbitrary subspaces then the semantics of the query is such that it checks whether each attractor *intersects* one of the subspaces.
    
    **arguments**:
        * *Primes*: prime implicants
        * *Update* (str): the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
        * *Trapspaces* (list): list of subspaces in string or dict representation

    **returns**:
        * *Answer* (bool): whether *Subspaces* is complete in the STG defined by *Primes* and *Update*,
        * *CounterExample* (dict): a state from which none of the *Subspaces* is reachable (if *Answer* is *False*)

    **example**::

        >>> mintspaces = TrapSpaces.trap_spaces(primes, "min")
        >>> answer, counterex = completeness_naive(primes, "asynchronous", mintspaces)
        >>> answer
        True
    """
    
    spec = "CTLSPEC " + TemporalQueries.EF_oneof_subspaces( Primes, Trapspaces )
    init = "INIT TRUE"
    answer, counterex = ModelChecking.check_primes_with_counterexample(Primes, Update, init, spec)

    if counterex:
        counterex = counterex[-1]
    
    return answer, counterex


def completeness_iterative( Primes, Update ):
    """
    The ASP and CTL model checking based algorithm for deciding whether the minimal trap spaces of a network are complete.
    The algorithm is discussed in :ref:`Klarner2015(a) <klarner2015trap>`.
    It splits the problem of deciding completeness into smaller subproblems by searching for so-called autonomous sets in the
    interaction graph of the network.
    If the minimal trap spaces of the corresponding restricted networks are complete
    then each of them defines a network reduction that is in turn subjected to a search for autonomous sets.
    The efficiency of the algorithm depends on the existence of small autonomous sets in the interaction graph, i.e.,
    the existence of "hierarchies" rather than a single connected component.

    .. note::
        Completeness depends on the update strategy, i.e.,
        the minimal trap spaces may be complete in the synchronous STG but not complete in the asynchronous STG or vice versa.

    .. note::
        The algorithm returns a counterexample, i.e., a state from which there is no path to one of the minimal trap spaces,
        if the minimal trap spaces are not complete.

    .. note::
        Each line that corresponds to a line of the pseudo code of Figure 3 in :ref:`Klarner2015(a) <klarner2015trap>` is marked by a comment. 
    
    **arguments**:
        * *Primes*: prime implicants
        * *Update* (str): the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
    
    **returns**:
        * *Answer* (bool): whether *Subspaces* is complete in the STG defined by *Primes* and *Update*,
        * *Counterexample* (dict): a state from which no subspace is reachable, if *Answer==False*

    **example**::

            >>> answer, counterex = completeness_iterative( primes, "asynchronous" )
            >>> answer
            False
            >>> STGs.state2str(counterex)
            10010111101010100001100001011011111111
    """

    primes = PrimeImplicants.copy(Primes)
    
    if PrimeImplicants.find_constants(primes):
        PrimeImplicants.percolate_and_remove_constants(primes)



    mintrapspaces = TrapSpaces.trap_spaces(primes, "min")   # line  1
    if mintrapspaces==[{}]:                                 # line  2
        return (True, None)                                 # line  3
    currentset = [({}, set([]))]                            # line  4
    while currentset:                                       # line  5
        p, W        = currentset.pop()                      # line  6

        ## line 7: primes_reduced = ReducedNetwork(V,F,p)
        primes_reduced = PrimeImplicants.copy(primes)
        PrimeImplicants.create_constants(primes_reduced, Constants=p)
        PrimeImplicants.percolate_and_remove_constants(primes_reduced)

        ## line 8: cgraph = CondensationGraph(V_p,F_p)
        igraph = InteractionGraphs.primes2igraph(primes_reduced)
        cgraph = Utility.DiGraphs.digraph2condensationgraph(igraph)

        ## line 9: cgraph_dash = RemoveComponents(Z,->,W)
        cgraph_dash = cgraph.copy()
        for U in cgraph.nodes():
            if set(U).issubset(set(W)):
                cgraph_dash.remove_node(U)

        ## line 10: W_dash = Copy(W)
        W_dash = W.copy()

        ## line 11
        refinement  = []                            

        ## line 12: toplayer = TopLayer(Z',->)
        toplayer = [U for U in cgraph_dash.nodes() if cgraph_dash.in_degree(U)==0]
        for U in toplayer: 

            ## line 13: U_dash = Above(V_p,F_p,U)
            U_dash = set(U)
            fringe = set(U)
            while fringe:
                name = fringe.pop()
                for pred in igraph.predecessors(name):
                    if not pred in U_dash:
                        U_dash.add(pred)
                        fringe.add(pred)

            ## line 14: primes_restricted = Restriction(V_p,F_p,U_dash)
            primes_restricted = PrimeImplicants.copy(primes_reduced)
            PrimeImplicants.remove_all_variables_except(primes_restricted, U_dash)
            
            ## line 15: Q = MinTrapSpaces(U',F|U')
            Q = TrapSpaces.trap_spaces(primes_restricted, "min")

            ## line 16: phi = CompletenessQuery(Q)
            phi = TemporalQueries.EF_oneof_subspaces(primes_restricted, Q)

            ## lines 17,18: answer = ModelChecking(S'_U, Update, phi)
            init = "INIT TRUE"
            spec = "CTLSPEC %s"%phi
            
            answer, counterex = ModelChecking.check_primes_with_counterexample(primes_restricted, Update, init, spec)
            if not answer:
                return (False, counterex)

            ## line 19: Refinement.append(Intersection(p,Q))
            ## Intersection(*args) is defined below
            refinement+= Intersection([p], Q)

            ## line 20: W_dash = SetUnion(W',U')
            W_dash.update(U_dash)

        ## line 21
        for q in Intersection(refinement):

            ## line 22: q_tilde = Percolation(V,F,q)
            dummy = PrimeImplicants.copy(primes)
            PrimeImplicants.create_constants(dummy, Constants=q)
            q_tilde = PrimeImplicants.percolate_and_keep_constants(dummy)

            ## lines 23, 24
            if q_tilde not in mintrapspaces:
                currentset.append( (q_tilde, W_dash) )

    return (True, None)


def create_attractor_report(Primes, FnameTXT=None):
    """
    Creates an attractor report for the network defined by *Primes*.
    
    **arguments**:
        * *Primes*: prime implicants
        * *FnameTXT* (str): the name of the report file or *None*
    
    **returns**:
        * *FnameTXT* (str): *FnameTXT=None* or *None* if *FnameTXT* is given

    **example**::
         >>> create_attractor_report(primes, "report.txt")
    """
    
    mints = TrapSpaces.trap_spaces(Primes, "min")
    steady = sorted([x for x in mints if len(x)==len(Primes)])
    cyclic = sorted([x for x in mints if len(x)<len(Primes)])

    lines = ["",""]
    lines+= ["### Attractor Report"]
    lines+= [" * created on %s using PyBoolNet, see https://github.com/hklarner/PyBoolNet"%datetime.date.today().strftime('%d. %b. %Y')]
    lines+= [""]

    lines+= ["### Steady States"]
    if not steady:
        lines+= [" * there are no steady states"]
    else:
        w = max([12,len(Primes)])
        lines+= ["| "+"steady state".ljust(w)+" |"]
        lines+= ["| "+ w*"-" +" | "]
        
    for x in steady:
        lines+= ["| "+StateTransitionGraphs.subspace2str(Primes, x).ljust(w)+" |"]
    lines+= [""]

    width = max([len(Primes), 14])
    spacer1 = lambda x: x.ljust(width)
    
    lines+= ["### Asynchronous STG"]
    answer, counterex = completeness_iterative( Primes, "asynchronous" )
    lines+= [" * completeness: %s"%answer]

    if not cyclic:
        lines+= [" * there are only steady states"]
    else:
        lines+= [""]
        line = "| "+"trapspace".ljust(width) + " | univocal  | faithful  |"
        lines+= [line]
        lines+= ["| "+ width*"-" +" | --------- | --------- |"]
    
    for x in cyclic:
        line =  "| "+ ("%s"%StateTransitionGraphs.subspace2str(Primes,x)).ljust(width)
        line+= " | "+ ("%s"%univocal(Primes, "asynchronous", x)[0]).ljust(9)
        line+= " | "+ ("%s"%faithful(Primes, "asynchronous", x)[0]).ljust(9)+" |"
        lines+= [line]
    lines+=[""]

    lines+= ["### Synchronous STG"]
    answer, counterex = completeness_iterative( Primes, "synchronous" )
    lines+= [" * completeness: %s"%answer]

    if not cyclic:
        lines+= [" * there are only steady states"]
    else:
        lines+= [""]
        line = "| "+"trapspace".ljust(width) + " | univocal  | faithful  |"
        lines+= [line]
        lines+= ["| "+ width*"-" +" | --------- | --------- |"]
    
    for x in cyclic:
        line =  "| "+ ("%s"%StateTransitionGraphs.subspace2str(Primes,x)).ljust(width)
        line+= " | "+ ("%s"%univocal(Primes, "synchronous", x)[0]).ljust(9)
        line+= " | "+ ("%s"%faithful(Primes, "synchronous", x)[0]).ljust(9)+" |"
        lines+= [line]
    lines+=[""]

    
    bnet = []
    for row in FileExchange.primes2bnet(Primes).split("\n"):
        t, f = row.split(",")
        bnet.append((t.strip(),f.strip()))

    t_width = max([7]+[len(x) for x,_ in bnet])    
    f_width = max([7]+[len(x) for _,x in bnet])
    lines+= ["### Network"]
    t,f = bnet.pop(0)
    lines+= ["| "+t.ljust(t_width)+" | "+f.ljust(f_width)+" |"]
    lines+= ["| "+t_width*"-"+" | "+f_width*"-"+" |"]
    for t,f in bnet:
        lines+= ["| "+t.ljust(t_width)+" | "+f.ljust(f_width)+" |"]
             
    lines+=["",""]

    if FnameTXT:
        with open(FnameTXT, "w") as f:
            f.writelines("\n".join(lines))
            print("created %s"%FnameTXT)
    else:
        return "\n".join(lines)


# auxillary functions
def Intersection( *args ):
    """
    each argument must be a list of subspaces (dicts)::

        >>> Intersection( [{"v1":1}], [{"v1":0}, {"v2":1, "v3":0}] )
    """

    # trivial case
    if len(args)==1:
        if args[0]==[]:
            return []
        else:
            return args[0]

    # non-trivial case
    result = []
    for product in itertools.product(*args):
        items = []
        for subspace in product:
            for item in subspace.items():
                items+= [item]
        subspace_new = dict(items)
        result+= [subspace_new]

    return result
    


    
