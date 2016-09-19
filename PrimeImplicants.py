

import PyBoolNet.FileExchange
import PyBoolNet.QuineMcCluskey
import PyBoolNet.InteractionGraphs
import PyBoolNet.Utility.DiGraphs
import PyBoolNet.Utility.Misc

import itertools


# constant values
CONSTANT_ON  = [[],[{}]]
CONSTANT_OFF = [[{}],[]]


def copy(Primes):
    """
    Creates a copy of *Primes*.

    **arguments**:
        * *Primes*: prime implicants

    **returns**:
        * *PrimesNew* (dict): a copy of *Primes*

    **example**::

        >>> primes_new = copy(primes)
    """
    
    primes_new = {}
    for name in Primes:
        primes_new[name]=[[],[]]

        for value in [0,1]:
            for prime in Primes[name][value]:
                primes_new[name][value].append(dict(prime))

    return primes_new

    
def are_equal(Primes1, Primes2):
    """
    Tests whether *Primes1* and *Primes2* are equal.
    The dictionary comparison *Primes1 == Primes2* does in general not work because the clauses of each may not be in the same order.

    **arguments**:
        * *Primes1*, *Primes2*: prime implicants

    **returns**:
        * *Answer* (bool): whether *Primes1=Primes2*

    **example**::

        >>> are_equal(primes1, primes2)
        True
    """
    
    if len(Primes1)!=len(Primes2):
        return False
    
    for name in Primes1:
        if not name in Primes2:
            return False
        
        for value in [0,1]:
            p1 = sorted([sorted(d.items()) for d in Primes1[name][value]])
            p2 = sorted([sorted(d.items()) for d in Primes2[name][value]])
            if not p1==p2:
                return False
            
    return True


def find_inputs(Primes):
    """
    Finds all inputs in the network defined by *Primes*.

    **arguments**:
        * *Primes*: prime implicants

    **returns**:
        * *Names* (list): the names of the inputs

    **example**::

        >>> find_inputs(primes)
        ['DNA_damage','EGFR','FGFR3']
    """

    inputs = []
    for name in Primes:
        if Primes[name][1]==[{name:1}]:
            inputs.append(name)

    return sorted(inputs)


def find_outputs(Primes):
    """
    Finds all outputs in the network defined by *Primes*. 

    **arguments**:
        * *Primes*: prime implicants

    **returns**:
        * *Names* (list): the names of the outputs

    **example**::

        >>> find_inputs(primes)
        ['Proliferation','Apoptosis','GrowthArrest']
    """

    igraph = PyBoolNet.InteractionGraphs.primes2igraph(Primes)
    outputs = [x for x in igraph if not igraph.successors(x)]

    return sorted(outputs)


def find_constants(Primes):
    """
    Finds all constants in the network defined by *Primes*.

    **arguments**:
        * *Primes*: prime implicants

    **returns**:
        * *Activities* (dict): the names and activities of constants

    **example**::

        >>> find_constants(primes)
        {'CGC':1,'IFNAR1':1,'IFNAR2':0,'IL4RA':1}
    """

    constants = {}
    for name in Primes:
        if Primes[name] == CONSTANT_ON:
            constants[name] = 1
        elif Primes[name] == CONSTANT_OFF:
            constants[name] = 0

    return constants

            
def create_constants(Primes, Constants):
    """
    Creates a constant in *Primes* for every name, value pair in *Constants*.
    Names that already exist in *Primes* are overwritten.

    **arguments**:
        * *Primes*: prime implicants
        * *Constants* (dict): names and values

    **example**::

        >>> create_constants(primes, {"p53":1, "p21":0})
    """

    for name, value in Constants.items():
        if value:
            Primes[name] = CONSTANT_ON
        else:
            Primes[name] = CONSTANT_OFF


def create_inputs(Primes, Names):
    """
    Creates an input for every member of *Names*.
    Variables that already exist in *Primes* are overwritten.

    .. note::
        Suppose that a given network has constants, e.g.::

            >>> len(find_constants(primes))>0
            True

        Too analyze how the network behaves under all possible values for these constants, turn them into inputs::

            >>> constants = find_constants(primes)
            >>> create_inputs(primes, constants)

    **arguments**:
        * *Primes*: prime implicants
        * *Names* (list): variables to become constants

    **example**::

        >>> names = ["p21", "p53"]
        >>> create_inputs(primes, names)
    """

    for name in Names:
        Primes[name][0]=[{name:1}]
        Primes[name][1]=[{name:0}]


def create_blinkers(Primes, Names):
    """
    Creates a blinker for every member of *Names*.
    Variables that alrerady exist in *Primes* are overwritten.
    A blinker is a variable with in-degree one and negative auto-regulation.
    Blinkers can therefore change their activity in every state of the transition system.

    .. note::
        Suppose that a given network has a lot of inputs, e.g.::

            >>> len(find_inputs(primes))
            20

        Since input combinations define trap spaces, see e.g. :ref:`Klarner2015(b) <klarner2015approx>` Sec. 5.1,
        all of which contain at least one minimal trap space,
        it follows that the network has at least 2^20 minimal trap spaces - too many to enumerate.
        To find out how non-input variables stabilize in minimal trap spaces turn the inputs into blinkers:: 

            >>> inputs = find_inputs(primes)
            >>> create_blinkers(primes, inputs)
            >>> tspaces = TS.trap_spaces(primes, "min")


    **arguments**:
        * *Primes*: prime implicants
        * *Names* (list): variables to become blinkers

    **example**::

        >>> names = ["p21", "p53"]
        >>> create_blinkers(primes, names)
    """

    for name in Names:
        Primes[name][0]=[{name:1}]
        Primes[name][1]=[{name:0}]


def create_variables(Primes, UpdateFunctions):
    """
    Creates the variables defined in *UpdateFunctions* and add them to *Primes*.
    Variables that already exist in *Primes* are overwritten.
    Raises an exception if the resulting primes contain undefined variables.
    The *UpdateFunctions* are given as a dictionary of names and functions that are either a bnet string or a Python function.

    **arguments**:
        * *Primes*: prime implicants
        * *UpdateFunctions* (dict): a dictionary of names and update functions

    **returns**:
        * *None*

    **example**::

        >>> primes = FileExchange.bnet2primes("A, A")
        >>> create_variables(primes, {"B": "A"})
        >>> create_variables(primes, {"C": lambda A, B: A and not B})
        >>> FileExchange.primes2bnet(primes)
        A, A
        B, A
        C, A&!B
    """

    newprimes = {}
    dependencies = set([])
    names = set(Primes)

    for name, function in UpdateFunctions.items():
        names.add(name)
        if type(function)==str:
            line = "%s, %s"%(name,function)
            newprimes[name] = PyBoolNet.FileExchange.bnet2primes(line)[name]
        else:
            newprimes[name] = PyBoolNet.QuineMcCluskey.functions2primes({name:function})[name]

        for x in newprimes[name][1]:
            dependencies.update(set(x))

    undefined = dependencies - names
    if undefined:
        print(" error: can not add variables that are dependent on undefined variables.")
        print("        these variables have undefined update functions: %s"%",".join(undefined))
        raise Exception

    Primes.update(newprimes)
    

def create_disjoint_union(Primes1, Primes2):
    """
    Creates a new primes dictionary that is the disjoint union of the networks represented by *Primes1* and *Primes2*.
    Here, "disjoint" means that the names of *Primes1* and *Primes2* do not intersect.

    **arguments**:
        * *Primes1*: prime implicants
        * *Primes2*: prime implicants

    **returns**:
        * *NewPrimes*: the disjoint union of *Primes1* and *Primes2*

    **example**::

        >>> primes1 = bnet2primes("A, B \\n B, A")
        >>> primes1 = bnet2primes("C, D \\n D, E")
        >>> newprimes = create_disjoint_union(primes1, primes2)
        >>> FileExchange.primes2bnet(newprimes)
        A, B
        B, A
        C, D
        D, E
    """

    assert(not set(Primes1).intersection(set(Primes2)))

    newprimes = {}
    newprimes.update(Primes1)
    newprimes.update(Primes2)

    return newprimes


def remove_variables(Primes, Names):
    """
    Removes all variables contained in *Names* from *Primes*.
    Members of *Names* that are not in *Primes* are ignored.
    Note that *Names* must be closed under the successors relation, i.e.,
    it must be a set of variables that contains all its successors.

    **arguments**:
        * *Primes*: prime implicants
        * *Names* (list): the names of variables to remove

    **example**::

        >>> names = ["PKC","GADD45","ELK1","FOS"]
        >>> remove_variables(primes, names)
    """

    igraph = PyBoolNet.InteractionGraphs.primes2igraph(Primes)
    hit = [x for x in PyBoolNet.Utility.DiGraphs.successors(igraph, Names) if x not in Names]
    if hit:
        print(" error: can not remove variables that are not closed under successor relation.")
        print("        these variables have successors outside the given set: %s"%", ".join(hit))
        raise Exception
    else:
        for name in Names:
            Primes.pop(name)


def remove_all_variables_except(Primes, Names):
    """
    Removes all variables except those in *Names* from *Primes*.
    Members of *Names* that are not in *Primes* are ignored.
    Note that *Names* must be closed under the predecessors relation, i.e.,
    it must be a set of variables that contains all its predecessors.

    **arguments**:
        * *Primes*: prime implicants
        * *Names* (list): the names of variables to keep

    **example**::

        >>> names = ["PKC","GADD45","ELK1","FOS"]
        >>> remove_all_variables_except(primes, names)
    """

    igraph = PyBoolNet.InteractionGraphs.primes2igraph(Primes)
    hit = [x for x in PyBoolNet.Utility.DiGraphs.predecessors(igraph, Names) if x not in Names]
    if hit:
        print(" error: can not remove variables that are not closed under predecessor relation.")
        print("        these variables have predecessors outside the given set: %s"%hit)
        raise Exception
        
    else:
        for name in list(Primes):
            if not name in Names:
                Primes.pop(name)


def rename_variable(Primes, OldName, NewName):
    """
    Renames a single component, i.e., replace every occurence of *OldName* with *NewName*.
    Throws an exception if *NewName* is already contained in *Primes*.

    **arguments**:
        * *Primes*: prime implicants
        * *OldName* (str): the old name of the component
        * *NewName* (str): the new name of the component

    **example**::

        
        >>> names = ["PKC","GADD45","ELK1","FOS"]
        >>> remove_all_variables_except(primes, names)
    """

    if OldName==NewName:
        return

    if NewName in Primes:
        print(" error: can not rename because %s already exists in primes."%NewName)
        raise Exception

    else:
        Primes[NewName] = Primes.pop(OldName)
        for name in Primes:
            for value in [0,1]:
                for prime in Primes[name][value]:
                    if OldName in prime:
                        prime[NewName] = prime.pop(OldName)
                


def _substitute(Primes, Name, Constants):
    """
    replaces the primes of *Name* by the ones obtained from substituting *Constants*.
    """
        
    for value in [0,1]:
        newprimes = []
        for prime in Primes[Name][value]:
            consistent, inconsistent = [], []
            for k in Constants:
                if k in prime:
                    if prime[k]==Constants[k]:
                        consistent.append(k)
                    else:
                        inconsistent.append(k)
                    
            if inconsistent:
                continue
            else:
                for k in consistent: prime.pop(k)
                if prime=={}:
                    newprimes = [{}]
                    break
                elif prime not in newprimes:
                    newprimes.append(prime)
                    
        Primes[Name][value] = newprimes
      

def _percolation( Primes, RemoveConstants ):
    """
    Percolates the values of constants, see :ref:`Klarner2015(b) <klarner2015approx>` Sec. 3.1 for a formal definition.
    Use *RemoveConstants* to determine whether constants should be kept in the remaining network or whether you want to remove them.
    
    **arguments**:
        * *Primes*: prime implicants
        * *RemoveConstants* (bool): whether constants should be kept

    **returns**:
        * *Activities* (dict): names and values of variables that became constants due to the percolation

    **example**::

        >>> percolate_constants(primes)
        >>> constants = percolate_constants(primes, True)
        >>> constants
        {'Erk':0, 'Mapk':0, 'Raf':1}
    """
    
    igraph = PyBoolNet.InteractionGraphs.primes2igraph(Primes)
    constants  = find_constants(Primes)
    fringe = PyBoolNet.Utility.DiGraphs.successors(igraph, constants)

    while fringe:
        newconstants = {}
        for name in fringe:
            _substitute(Primes, name, constants)
            if   Primes[name] == CONSTANT_ON:  newconstants[name] = 1
            elif Primes[name] == CONSTANT_OFF: newconstants[name] = 0

        constants.update(newconstants)
        fringe = set(PyBoolNet.Utility.DiGraphs.successors(igraph, newconstants)) - set(constants)

    if RemoveConstants:
        for name in constants: Primes.pop(name)

    return constants


def percolate_and_keep_constants( Primes ):
    """
    Percolates the values of constants, see :ref:`Klarner2015(b) <klarner2015approx>` Sec. 3.1 for a formal definition.
    Keeps constants in the *Primes*.

    **arguments**:
        * *Primes*: prime implicants

    **returns**:
        * *Constants* (dict): names and values of the constants

    **example**::

        >>> constants = percolate_and_keep_constants(primes)
        >>> constants
        {'Erk':0, 'Mapk':0, 'Raf':1}
    """

    return _percolation( Primes, RemoveConstants=False )

    
def percolate_and_remove_constants( Primes ):
    """
    Percolates the values of constants, see :ref:`Klarner2015(b) <klarner2015approx>` Sec. 3.1 for a formal definition.
    Removes constants from the *Primes*.

    **arguments**:
        * *Primes*: prime implicants

    **returns**:
        * *Constants* (dict): names and values of the constants

    **example**::

        >>> constants = percolate_and_remove_constants(primes)
        >>> constants
        {'Erk':0, 'Mapk':0, 'Raf':1}
    """

    return _percolation( Primes, RemoveConstants=True )
    

def input_combinations(Primes):
    """
    A generator for all possible input combinations of *Primes*.
    Returns the empty dictionary if there are no inputs.

    **arguments**:
        * *Primes*: prime implicants

    **returns**:
        * *Activities* (dict): generates all input combinations in dict representation

    **example**::

        >>> len(find_inputs(primes))
        >>> for x in input_combinations(primes):
        ...     print(STGs.subspace2str(primes,x))
        00
        01
        10
        11
    """
    
    inputs = find_inputs(Primes)
    if inputs:
        for x in itertools.product(*len(inputs)*[[0,1]]):
            yield dict(zip(inputs,x))
    else:
        yield {}











    

                
