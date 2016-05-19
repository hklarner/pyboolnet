

import InteractionGraphs

import itertools



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

            >>> inputs = find_inputs(primes)
            >>> print(inputs)
            ['DNA_damage','EGFR','FGFR3']
    """

    inputs = []
    for name in sorted(Primes):
        if Primes[name][1]==[{name:1}]:
            inputs.append( name )

    return inputs


def find_outputs(Primes):
    """
    Finds all outputs in the network defined by *Primes*. 

    **arguments**:
        * *Primes*: prime implicants

    **returns**:
        * *Names* (list): the names of the outputs

    **example**::

            >>> inputs = find_inputs(primes)
            >>> print(inputs)
            ['Proliferation','Apoptosis','GrowthArrest']
    """

    names = Primes.keys()
    outputs = []
    for source in names:
        hit = False
        for target in names:
            if hit: break
            for p in Primes[target][1]:
                if source in p:
                    hit=True
                    break

        if not hit:
            outputs+=[source]

    return outputs


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

    activities = {}
    for name in Primes:
        if Primes[name][1]==[{}]:
            activities[name] = 1
        elif Primes[name][0]==[{}]:
            activities[name] = 0

    return activities


            
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



def create_constants(Primes, Activities):
    """
    Overwrites *Primes* for every name, value pair in *Activities* such that name is constant at value.
    For safety it is required that the names of *Activities* exist in *Primes*.

    **arguments**:
        * *Primes*: prime implicants
        * *Activities* (dict): a subspace

    **example**::

            >>> activities = {"p53":1, "p21":0}
            >>> create_constants(primes, subspace)
    """

    assert(set(Activities.keys()).issubset(set(Primes.keys())))

    for name, value in Activities.items():
        Primes[name][value]   = [{}]
        Primes[name][1-value] = []


def create_blinkers(Primes, Names):
    """
    Overwrite *Primes* such that every name in *Names* becomes a so-called blinker, i.e.,
    a variable that is only regulated by itself, like an input, but the self-regulation is negative.
    Blinkers can therefore change their activity in every state of the transition system.
    For safety it is required that the names of *Activities* exist in *Primes*.

    .. note::
        Suppose that a given network has a lot of inputs, e.g.::

            >>> len(find_inputs(primes))
            20

        Since input combinations define trap spaces, see e.g. :ref:`Klarner2015(b) <klarner2015approx>` Sec. 5.1,
        all of which contain at least one minimal trap space,
        it follows that the network has at least 2^20 minimal trap spaces - usually too many to list.
        To find out how non-input variables stabilize in minimal trap spaces turn the inputs into blinkers:: 

            >>> inputs = find_inputs(primes)
            >>> create_blinkers(primes, inputs)
            >>> tspaces = TS.trap_spaces(primes, "min")


    **arguments**:
        * *Primes*: prime implicants
        * *Names* (list): variables to become blinkers

    **example**::

            >>> names = ["p21", "p53"]
            >>> variables_to_blinkers(primes, names)
    """

    assert(set(Names).issubset(set(Primes.keys())))

    for name in Names:
        if name in Primes:
            Primes[name][0]=[{name:1}]
            Primes[name][1]=[{name:0}]




def create_inputs(Primes, Names):
    """
    Overwrite *Primes* such that each name in *Names* becomes an input.
    For safety it is required that the names of *Activities* exist in *Primes*.

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
            >>> variables_to_blinkers(primes, names)
    """

    assert(set(Names).issubset(set(Primes.keys())))

    for name in Names:
        if name in Primes:
            Primes[name][0]=[{name:1}]
            Primes[name][1]=[{name:0}]



def remove_variables(Primes, Names):
    """
    Removes all variables contained in *Names* from *Primes*.
    For safety it is required that the names of *Activities* exist in *Primes*.

    **arguments**:
        * *Primes*: prime implicants
        * *Names* (list): the names of variables to remove


    **example**::

            >>> names = ["PKC","GADD45","ELK1","FOS"]
            >>> remove_variables(primes, names)
    """

    assert(set(Names).issubset(set(Primes.keys())))
    
    for name in Names:
        Primes.pop( name )
        
            

def percolate_constants( Primes, RemoveConstants=False ):
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
    
    igraph = InteractionGraphs.primes2igraph( Primes )
    constants  = find_constants( Primes )
    for name in constants:
        Primes.pop(name)


    # fringe = variables that may fix due to percolation
    fringe = set([])
    for name in constants:
        fringe.update( set([x for x in igraph.successors(name) if not x in constants]) )

    while fringe:
        name = fringe.pop()
        constant_predecessors = dict([x for x in constants.items() if x[0] in igraph.predecessors(name)])
        if not constant_predecessors:
            continue

        for value in [0,1]:
            
            expression_new = []
            for term in Primes[name][value]:
                
                term_new = {}
                for k,v in term.items():
                    
                    # term is affected
                    if k in constants:
                        
                        if v != constant_predecessors[k]:
                            # term is 0
                            term_new = 'remove'
                            break
                        else:
                            # literal is removed
                            pass
                            
                    else:
                        # literal is kept
                        term_new[k]=v

                if term_new != 'remove':
                    expression_new.append( term_new )

            # name is constant at value
            if expression_new==[{}]:
                constants[name] = value
                Primes.pop(name)
                fringe.update( set([x for x in igraph.successors(name) if not x in constants]) )
                break

            # name is constant at 1-value
            if expression_new==[]:
                constants[name] = 1-value
                Primes.pop(name)
                fringe.update( set([x for x in igraph.successors(name) if not x in constants]) )
                break

            # overwrite expression (may have simplified)
            Primes[name][value] = expression_new
                

    if not RemoveConstants:
        Primes.update( dict([(name,[[],[{}]]) if value==1 else (name,[[{}],[]]) for name,value in constants.items()]) )

    return constants



def input_combinations(Primes):
    """
    A generator for all possible input combinations of *Primes*.

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










                
