import datetime
import subprocess

import PyBoolNet.Utility.Misc

CMD_GRINGO = PyBoolNet.Utility.Misc.find_command("gringo")
CMD_CLASP = PyBoolNet.Utility.Misc.find_command("clasp")


def circuits(Primes, MaxOutput=1000, FnameASP=None, Representation="dict"):
    """
    Computes minimal trap spaces but also distinguishes between nodes that are fixed due to being part of a circuit
    and nodes that are fix due to percolation effects.

    **arguments**:
        * *Primes*: prime implicants
        * *MaxOutput*: maximum number of returned solutions
        * *FnameASP* (str): file name or *None*
        * *Representation* (str): either "str" or "dict", the representation of the trap spaces

    **returns**:
        * *Circuits* (list): of tuples consisting of circuit nodes and percolation nodes


    **example**::

        >>> circuits(primes)
        [({'Mek': 0, 'Erk': 0},{'Raf': 1}),..]
    """
    
    return potassco_handle(Primes, Type="circuits", Bounds=(0, "n"), Project=None, MaxOutput=MaxOutput,
                           FnameASP=FnameASP, Representation=Representation)


def percolate_trapspace(Primes, Trapspace):
    """
    Percolates the *Trapspace*.
    Does not check whether *Trapspace* is really a trap space.
    Instead, it creates constants from *Trapspace* and percolates the values.

    **arguments**:
        * *Primes*: prime implicants
        * *Trapspace*: a subspace

    **returns**:
        * *Trapspace* (dict): the percolated trap space

    **example**::

        >>> percolate_trapspace(primes, {'Mek': 0, 'Erk': 0})
        {'Raf': 1, 'Mek': 0, 'Erk': 0}
    """
    
    primes = PyBoolNet.PrimeImplicants.create_constants(Primes, Trapspace, Copy=True)
    constants = PyBoolNet.PrimeImplicants.percolate_and_keep_constants(primes)
    
    return constants


def trapspaces_that_contain_state(Primes, State, Type, FnameASP=None, Representation="dict", MaxOutput=1000):
    """
    Computes trap spaces that contain *State*.

    **arguments**:
        * *Primes*: prime implicants
        * *State* (dict): a state in dict format
        * *Type* (str): either "min", "max", "all" or "percolated"
        * *FnameASP* (str): file name or *None*
        * *Representation* (str): either "str" or "dict", the representation of the trap spaces
        * *MaxOutput*: maximum number of returned solutions

    **returns**:
        * *TrapSpaces* (list): the trap spaces that contain *State*

    **example**::

        >>> trapspaces_that_contain_state(primes, {"v1":1,"v2":0,"v3":0})
    """

    return trapspaces_that_intersect_subspace(Primes=Primes, Subspace=State, Type=Type, FnameASP=FnameASP, Representation=Representation, MaxOutput=MaxOutput)


def trapspaces_that_intersect_subspace(Primes, Subspace, Type, FnameASP=None, Representation="dict", MaxOutput=1000):
    """
    Computes trap spaces that have non-empty intersection with *Subspace*

    **arguments**:
        * *Primes*: prime implicants
        * *Subspace* (dict): a subspace in dict format
        * *Type* (str): either "min", "max", "all" or "percolated"
        * *FnameASP* (str): file name or *None*
        * *Representation* (str): either "str" or "dict", the representation of the trap spaces
        * *MaxOutput*: maximum number of returned solutions

    **returns**:
        * *TrapSpaces* (list): the trap spaces that have non-empty intersection with *Subspace*

    **example**::

        >>> trapspaces_that_intersect_subspace(primes, {"v1":1,"v2":0,"v3":0})
    """
    
    assert (len(Primes) >= len(Subspace))
    assert (type(Subspace) in [dict, str])
    
    if type(Subspace) == str:
        Subspace = PyBoolNet.StateTransitionGraphs.subspace2dict(Primes, Subspace)
    
    active_primes = PyBoolNet.PrimeImplicants.active_primes(Primes, Subspace)
    
    # exclude trivial trap space {} for search of maximal trap spaces
    Bounds = None
    if Type == "max":
        Bounds = (1, "n")

    tspaces = potassco_handle(active_primes, Type=Type, Bounds=Bounds, Project=[], MaxOutput=MaxOutput, FnameASP=FnameASP,
                              Representation=Representation)
    
    if not tspaces:
        # ASP program is unsatisfiable
        
        answer = {}
        
        if Representation == "str":
            answer = PyBoolNet.StateTransitionGraphs.subspace2str(Primes, answer)
        
        return [answer]
    
    if len(Subspace) == len(Primes) and Type == "min":
        if len(tspaces) > 1:
            print("the smallest trap space containing a state (or other space) must be unique!")
            print("found %i smallest tspaces." % len(tspaces))
            print(tspaces)
            raise Exception
        
        return [tspaces.pop()]
    
    return tspaces


def smallest_trapspace(Primes, State, Representation="dict"):
    """
    Returns the (unique) smallest trap space that contains *State*.
    Calls :ref:`trapspaces_that_contain_state`

    **arguments**:
        * *Primes*: prime implicants
        * *State* (dict): a state in dict format
        * *Representation* (str): either "str" or "dict", the representation of the trap spaces

    **returns**:
        * *TrapSpace* (dict): the unique minimal trap space that contains *State*

    **example**::

        >>> smallest_trapspace(primes, {"v1":1,"v2":0,"v3":0})
    """
    
    return trapspaces_that_contain_state(Primes, State, Type="min", FnameASP=None, Representation=Representation)


def trap_spaces(Primes, Type, MaxOutput=1000, FnameASP=None, Representation="dict"):
    """
    Returns a list of trap spaces using the :ref:`installation_potassco` ASP solver, see :ref:`Gebser2011 <Gebser2011>`.
    For a formal introcution to trap spaces and the ASP encoding that is used for their computation see :ref:`Klarner2015(a) <klarner2015trap>`.

    The parameter *Type* must be one of *"max"*, *"min"*, *"all"* or *"percolated"* and
    specifies whether subset minimal, subset maximal, all trap spaces or all percolated trap spaces should be returned.

    .. warning::
        The number of trap spaces is easily exponential in the number of components.
        Use the safety parameter *MaxOutput* to control the number of returned solutions.

    To create the *asp* file for inspection or manual editing, pass a file name to *FnameASP*.

    **arguments**:
        * *Primes*: prime implicants
        * *Type* (str): either *"max"*, *"min"*, *"all"* or *"percolated"*
        * *MaxOutput* (int): maximal number of trap spaces to return
        * *FnameASP* (str): name of *asp* file to create, or *None*
        * *Representation* (str): either "str" or "dict", the representation of the trap spaces

    **returns**:
        * *Subspaces* (list): the trap spaces

    **example**::

        >>> bnet = ["x, !x | y | z",
        ...         "y, !x&z | y&!z",
        ...         "z, x&y | z"]
        >>> bnet = "\\n".join(bnet)
        >>> primes = FEX.bnet2primes(bnet)
        >>> tspaces = TS.trap_spaces(primes, "all", Representation="str")
        ---, --1, 1-1, -00, 101
    """
    
    # exclude trivial trap space {} for search of maximal trap spaces
    Bounds = None
    if Type == "max":
        Bounds = (1, "n")
    
    return potassco_handle(Primes, Type, Bounds=Bounds, Project=None, MaxOutput=MaxOutput, FnameASP=FnameASP,
                           Representation=Representation)


def steady_states(Primes, MaxOutput=1000, FnameASP=None, Representation="dict"):
    """
    Returns steady states.

    **arguments**:
        * *Primes*: prime implicants
        * *MaxOutput* (int): maximal number of trap spaces to return
        * *FnameASP*: file name or *None*
        * *Representation* (str): either "str" or "dict", the representation of the trap spaces

    **returns**:
        * *States* (list): the steady states

    **example**::

        >>> steady = steady_states(primes)
        >>> len(steady)
        2
    """
    
    return potassco_handle(Primes, Type="all", Bounds=("n", "n"), Project=[], MaxOutput=MaxOutput, FnameASP=FnameASP,
                           Representation=Representation)


def trap_spaces_bounded(Primes, Type, Bounds, MaxOutput=1000, FnameASP=None):
    """
    Returns a list of bounded trap spaces using the Potassco_ ASP solver :ref:`[Gebser2011]<Gebser2011>`.
    See :ref:`trap_spaces <sec:trap_spaces>` for details of the parameters *Type*, *MaxOutput* and *FnameASP*.
    The parameter *Bounds* is used to restrict the set of trap spaces from which maximal, minimal or all solutions are drawn
    to those whose number of fixed variables are within the given range.
    Example: ``Bounds=(5,8)`` instructs Potassco_ to consider only trap spaces with 5 to 8 fixed variables as feasible.
    *Type* selects minimal, maximal or all trap spaces from the restricted set.
    .. warning::
        The *Bound* constraint is applied *before* selecting minimal or maximal trap spaces.
        A trap space may therefore be minimal w.r.t. to certain bounds but not minimal in the unbounded sense.

    Use ``"n"`` as a shortcut for "all variables", i.e., instead of ``len(Primes)``.
    Example: Use ``Bounds=("n","n")`` to compute steady states.
    Note that the parameter *Type* becomes irrelevant for ``Bounds=(x,y)`` with ``x=y``.

    **arguments**:
        * *Primes*: prime implicants
        * *Type* in ``["max","min","all"]``: subset minimal, subset maximal or all solutions
        * *Bounds* (tuple): the upper and lower bound for the number of fixed variables
        * *MaxOutput* (int): maximal number of trap spaces to return
        * *FnameASP*: file name or *None*
    **returns**:
        * list of trap spaces
    **example**::
        >>> tspaces = trap_spaces_bounded(primes, "min", (2,4))
        >>> len(tspaces)
        12
        >>> tspaces[0]
        {'TGFR':0,'FGFR':0}
    """
    
    return potassco_handle(Primes, Type, Bounds, Project=None, MaxOutput=MaxOutput, FnameASP=FnameASP,
                           Representation="dict")


def steady_states_projected(Primes, Project, MaxOutput=1000, FnameASP=None):
    """
    Returns a list of projected steady states using the Potassco_ ASP solver :ref:`[Gebser2011]<Gebser2011>`.

    **arguments**:
        * *Primes*: prime implicants
        * *Project*: list of names
        * *MaxOutput* (int): maximal number of trap spaces to return
        * *FnameASP*: file name or *None*

    **returns**:
        * *Activities* (list): projected steady states

    **example**::

        >>> psteady = steady_states_projected(primes, ["v1","v2"])
        >>> len(psteady)
        2
        >>> psteady
        [{"v1":1,"v2":0},{"v1":0,"v2":0}]
    """
    
    assert (set(Project).issubset(set(Primes.keys())))
    
    return potassco_handle(Primes, Type="all", Bounds=("n", "n"), Project=Project, MaxOutput=MaxOutput,
                           FnameASP=FnameASP, Representation="dict")


def primes2asp(Primes, FnameASP, Bounds, Project, Type):
    """
    Saves Primes as an *asp* file in the Potassco_ format intended for computing minimal and maximal trap spaces.
    The homepage of the Potassco_ solving collection is http://potassco.sourceforge.net.
    The *asp* file consists of data, the hyperarcs of the prime implicant graph,
    and a problem description that includes the consistency, stability and non-emptiness conditions.

    There are four additional parameters that modify the problem:

    *Bounds* must be either a tuple of integers *(a,b)* or *None*.
    A tuple *(a,b)* uses Potassco_'s cardinality constraints to enforce that the number of fixed variables *x* of a trap space satisfies *a<=x<=b*.
    *None* results in no bounds.

    *Project* must be either a list of names or *None*.
    A list of names projects the solutions onto these variables using the meta command "#show" and the clasp parameter "--project".
    Variables of *Project* that do not appear in *Primes* are ignored.
    *None* results in no projection.

    *Type* specifies whether additional constraints should be enforced.
    For example for computing circuits or percolated trap spaces.
    Recognized values are 'circuits' and 'percolated', everything else will be ignored.

    **arguments**:
       * *Primes*: prime implicants
       * *FnameASP*: name of *ASP* file or None
       * *Bounds* (tuple): cardinality constraint for the number of fixed variables
       * *Project* (list): names to project to or *None* for no projection
       * *Type* (str): one of 'max', 'min', 'all', 'percolated', 'circuits' or *None*

    **returns**:
       * *FileASP* (str): file as string if not *FnameASP is None* and *None* otherwise

    **example**::

          >>> primes2asp(primes, "mapk.asp", False, False)
          >>> primes2asp(primes, "mapk_bounded.asp", (20,30), False)
          >>> primes2asp(primes, "mapk_projected.asp", False, ['AKT','GADD45','FOS','SMAD'])
    """

    assert Type in [None, "max", "min", "all", "percolated", "circuits"]
    assert FnameASP is None or type(FnameASP) == str
    assert Bounds is None or type(Bounds) == tuple
    assert Project is None or type(Project) == list
    
    if Project:
        Project = [x for x in Project if x in Primes]
    
    lines = ['%% created on %s using PyBoolNet' % datetime.date.today().strftime('%d. %b. %Y'),
             '% PyBoolNet is available at https://github.com/hklarner/PyBoolNet',
             '',
             '% encoding of prime implicants as hyper-arcs that consist of a unique "target" and (possibly) several "sources".',
             '% "target" and "source" are triplets that consist of a variable name, an activity and a unique arc-identifier. ',
             '']
    
    ID = 0
    for name in sorted(Primes.keys()):
        for value in [0, 1]:
            for p in Primes[name][value]:
                ID += 1
                hyper = ['target("%s",%i,a%i).' % (name, value, ID)]
                for n2, v2 in p.items():
                    hyper.append('source("%s",%i,a%i).' % (n2, v2, ID))
                lines += [' '.join(hyper)]
    
    lines += ['']
    lines += [
        '% generator: "in_set(ID)" specifies which arcs are chosen for a trap set (ID is unique for target(_,_,_)).',
        '{in_set(ID) : target(V,S,ID)}.',
        '',
        '% consistency constraint',
        ':- in_set(ID1), in_set(ID2), target(V,1,ID1), target(V,0,ID2).',
        '',
        '% stability constraint',
        ':- in_set(ID1), source(V,S,ID1), not in_set(ID2) : target(V,S,ID2).',
        '']
    
    if Type in ['percolated', 'circuits']:
        lines += [
            '% percolation constraint.',
            '% ensure that if all sources of a prime are hit then it must belong to the solution.',
            'in_set(ID) :- target(V,S,ID), hit(V1,S1) : source(V1,S1,ID).']
    else:
        lines += [
            '% bijection constraint (between asp solutions and trap spaces)',
            '% to avoid the repetition of equivalent solutions we add all prime implicants',
            '% that agree with the current solution.',
            'in_set(ID) :- target(V,S,ID), hit(V,S), hit(V1,S1) : source(V1,S1,ID).']
    
    if Type == 'circuits':
        lines += ['',
                  '% circuits constraint, distinguishes between circuit nodes and percolated nodes',
                  'upstream(V1,V2) :- in_set(ID), target(V1,S1,ID), source(V2,S2,ID).',
                  'upstream(V1,V2) :- upstream(V1,V3), upstream(V3,V2).',
                  'percolated(V1) :- hit(V1,S), not upstream(V1,V1).']
    
    lines += ['',
              '% "hit" captures the stable variables and their activities.',
              'hit(V,S) :- in_set(ID), target(V,S,ID).']
    
    if Bounds:
        lines += ['',
                  '%% cardinality constraint (enforced by "Bounds=%s")' % repr(Bounds), ]
        if Bounds[0] > 0:
            lines += [':- {hit(V,S)} %i.' % (Bounds[0] - 1)]
        lines += [':- %i {hit(V,S)}.' % (Bounds[1] + 1)]
    
    if Project:
        lines += ['', '%% show projection (enforced by "Project=%s").' % (repr(sorted(Project)))]
        lines += ['#show.']
        lines += ['#show hit("{n}",S) : hit("{n}",S).'.format(n=name) for name in Project]
    
    elif Type == 'circuits':
        lines += ['',
                  '% show fixed nodes and distinguish between circuits and percolated',
                  '#show percolated/1.',
                  '#show hit/2.']
    
    else:
        lines += ['',
                  '% show fixed nodes',
                  '#show hit/2.']
    
    if FnameASP is None:
        return '\n'.join(lines)
    
    with open(FnameASP, 'w') as f:
        f.write('\n'.join(lines))

    print('created %s' % FnameASP)


def potassco_handle(Primes, Type, Bounds, Project, MaxOutput, FnameASP, Representation):
    """
    Returns a list of trap spaces using the Potassco_ ASP solver :ref:`[Gebser2011]<Gebser2011>`.
    """
    
    DEBUG = 0
    
    assert Type in ["max", "min", "all", "percolated", "circuits"]
    assert Representation in ["str", "dict"]
    
    if Bounds:
        Bounds = tuple([len(Primes) if x == "n" else x for x in Bounds])

    params_clasp = ["--project"]
    
    if Type == "max":
        params_clasp += ["--enum-mode=domRec", "--heuristic=Domain", "--dom-mod=5,16"]

    elif Type == "min":
        params_clasp += ["--enum-mode=domRec", "--heuristic=Domain", "--dom-mod=3,16"]
    
    aspfile = primes2asp(Primes, FnameASP, Bounds, Project, Type)
    
    try:
        # pipe ASP file
        if FnameASP is None:
            cmd_gringo = [CMD_GRINGO]
            proc_gringo = subprocess.Popen(cmd_gringo, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                           stderr=subprocess.PIPE)
            cmd_clasp = [CMD_CLASP, '--models=%i' % MaxOutput] + params_clasp
            proc_clasp = subprocess.Popen(cmd_clasp, stdin=proc_gringo.stdout, stdout=subprocess.PIPE,
                                          stderr=subprocess.PIPE)
            
            proc_gringo.stdin.write(aspfile.encode())
            proc_gringo.stdin.close()
            
            output, error = proc_clasp.communicate()
            error = error.decode()
            output = output.decode()
        
        # read ASP file
        else:
            cmd_gringo = [CMD_GRINGO, FnameASP]
            proc_gringo = subprocess.Popen(cmd_gringo, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                           stderr=subprocess.PIPE)
            cmd_clasp = [CMD_CLASP, '--models=%i' % MaxOutput] + params_clasp
            proc_clasp = subprocess.Popen(cmd_clasp, stdin=proc_gringo.stdout, stdout=subprocess.PIPE,
                                          stderr=subprocess.PIPE)
            
            output, error = proc_clasp.communicate()
            error = error.decode()
            output = output.decode()
    
    except Exception as Ex:
        print(aspfile)
        print(Ex)
        print("\nCall to gringo and / or clasp failed.")
        
        if FnameASP is not None:
            print('\ncommand: "%s"' % " ".join(cmd_gringo + ["|"] + cmd_clasp))
        
        raise Ex
    
    if "ERROR" in error:
        print("\nCall to gringo and / or clasp failed.")
        if FnameASP is not None:
            print('\nasp file: "%s"' % aspfile)
        print('\ncommand: "%s"' % " ".join(cmd_gringo + ["|"] + cmd_clasp))
        print('\nerror: "%s"' % error)
        raise Exception
    
    if DEBUG:
        print(aspfile)
        print("cmd_gringo: %s" % " ".join(cmd_gringo))
        print("cmd_clasp:  %s" % " ".join(cmd_clasp))
        print("error:")
        print(error)
        print("output:")
        print(output)
    
    lines = output.split("\n")
    result = []
    
    # parser
    # answers are assumed to be single lines after a line that
    # begins with 'Answer'
    
    if Type == "circuits":
        while lines and len(result) < MaxOutput:
            line = lines.pop(0)
            
            if line[:6] == "Answer":
                line = lines.pop(0)
                
                tspace = [x for x in line.split() if "hit" in x]
                tspace = [x[4:-1].split(",") for x in tspace]
                tspace = [(x[0][1:-1], int(x[1])) for x in tspace]
                
                perc = [x[12:-2] for x in line.split() if "perc" in x]
                perc = [x for x in tspace if x[0] in perc]
                perc = dict(perc)
                
                circ = [x for x in tspace if x[0] not in perc]
                circ = dict(circ)
                
                result.append((circ, perc))

    else:
        while lines and len(result) < MaxOutput:
            line = lines.pop(0)
            
            if line[:6] == "Answer":
                line = lines.pop(0)
                d = [x[4:-1].split(",") for x in line.split()]
                d = [(x[0][1:-1], int(x[1])) for x in d]
                result.append(dict(d))
    
    if len(result) == MaxOutput:
        print("There are possibly more than %i trap spaces." % MaxOutput)
        print("Increase MaxOutput to find out.")
    
    if Representation == "str":
        subspace2str = PyBoolNet.StateTransitionGraphs.subspace2str
        
        if Type == "circuits":
            result = [(subspace2str(Primes, x), subspace2str(Primes, y)) for x, y in result]
        else:
            result = [subspace2str(Primes, x) for x in result]
    
    return result


def Count(Spaces):
    """
    returns tuples *(space, count)* where *count* states how often *space* occurs in *Spaces*.
    """
    
    dummy = [tuple(sorted(x.items())) for x in Spaces]
    unique = set(dummy)
    result = []
    for x in unique:
        result.append((dict(x), dummy.count(x)))
    
    return result
