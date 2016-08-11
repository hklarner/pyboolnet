
import os
import subprocess
import datetime

import PyBoolNet.Utility.Misc

BASE = os.path.normpath(os.path.abspath(os.path.join(os.path.dirname(__file__))))
config = PyBoolNet.Utility.Misc.myconfigparser.SafeConfigParser()
config.read( os.path.join(BASE, "Dependencies", "settings.cfg") )

CMD_GRINGO = os.path.normpath(os.path.join( BASE, "Dependencies", config.get("Executables", "gringo") ))
CMD_CLASP  = os.path.normpath(os.path.join( BASE, "Dependencies", config.get("Executables", "clasp") ))



def trap_spaces(Primes, Type, MaxOutput=100, FnameASP=None):
    """
    Returns a list of trap spaces using the :ref:`installation_potassco` ASP solver, see :ref:`Gebser2011 <Gebser2011>`.
    For a formal introcution to trap spaces and the ASP encoding that is used for their computation see :ref:`Klarner2015(a) <klarner2015trap>`.

    The parameter *Type* must be one of *"max"*, *"min"* or *"all"* and
    specifies whether subset minimal, subset maximal or all trap spaces should be returned.
    
    .. warning::
        The number of trap spaces is easily exponential in the number of components.
        Use the safety parameter *MaxOutput* to control the number of returned solutions.

    To create the *asp* file for inspection or manual editing, pass a file name to *FnameASP*.
    
    **arguments**:
        * *Primes*: prime implicants
        * *Type* (str): either *"max"*, *"min"* or *"all"*
        * *MaxOutput* (int): maximal number of trap spaces to return
        * *FnameASP* (str): name of *asp* file to create, or *None*

    **returns**:
        * *Subspaces* (list): the trap spaces

    **example**::

        >>> bnet = ["x, !x | y | z",
        ...         "y, !x&z | y&!z",
        ...         "z, x&y | z"]
        >>> bnet = "\\n".join(bnet)
        >>> primes = FEX.bnet2primes(bnet)
        >>> tspaces = TS.trap_spaces(primes, "all")
        >>> ", ".join(STGs.subspace2str(primes, x) for x in tspaces)
        ---, --1, 1-1, -00, 101
    """

    # exclude trivial trap space {} for search of maximal trap spaces
    Bounds = None
    if Type=="max":
        Bounds=(1,"n")

    return potassco_handle(Primes, Type, Bounds=Bounds, Project=None, InsideOf=None, OutsideOf=None, MaxOutput=MaxOutput, Aggregate=False, FnameASP=FnameASP)




def steady_states(Primes, MaxOutput=100, FnameASP=None):
    """
    Wrapper function for :ref:`trap_spaces_bounded <sec:trap_spaces>` that sets the bounds to *n,n* to return steady states.

    **arguments**:
        * *Primes*: prime implicants
        * *MaxOutput* (int): maximal number of trap spaces to return
        * *FnameASP*: file name or *None*
        
    **returns**:
        * *States* (list): the steady states

    **example**::

        >>> steady = steady_states(primes)
        >>> len(steady)
        2
    """

    return potassco_handle(Primes, Type="all", Bounds=("n","n"), Project=[], InsideOf=None, OutsideOf=None, MaxOutput=MaxOutput, Aggregate=False, FnameASP=FnameASP)



def steady_states_projected(Primes, Project, Aggregate=False, MaxOutput=100, FnameASP=None):
    """
    Returns a list of projected steady states using the Potassco_ ASP solver :ref:`[Gebser2011]<Gebser2011>`.
    This function works like :ref:`trap_spaces_projected <sec:trap_spaces>` but enforces that the returned elements are steady states.

    **arguments**:
        * *Primes*: prime implicants
        * *Project*: list of names
        * *Aggregate*: count number of steady states per projection
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

    assert( set(Project).issubset(set(Primes.keys())) )

    return potassco_handle(Primes, Type="all", Bounds=("n","n"), Project=Project, InsideOf=None, OutsideOf=None, MaxOutput=MaxOutput, Aggregate=Aggregate, FnameASP=FnameASP)



def primes2asp(Primes, FnameASP, Bounds, Project, InsideOf, OutsideOf):
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

    *InsideOf* must be a subspace (dict) that specifies that only trap spaces that are contained in it are wanted.

    *OutsideOf* must be a subspace (dict) that specifies that only trap spaces that contain it are wanted.

    **arguments**:
       * *Primes*: prime implicants
       * *FnameASP*: name of *ASP* file or None
       * *Bounds* (tuple): cardinality constraint for the number of fixed variables
       * *Project* (list): names to project to or *None* for no projection
       * *InsideOf* (dict): a subspace or *None*
       * *OutsideOf* (dict): a subspace or *None*

    **returns**:
       * *FileASP* (str): file as string if not *FnameASP==None* and *None* otherwise

    **example**::

          >>> primes2asp(primes, "mapk.asp", False, False)
          >>> primes2asp(primes, "mapk_bounded.asp", (20,30), False)
          >>> primes2asp(primes, "mapk_projected.asp", False, ['AKT','GADD45','FOS','SMAD'])
    """

    assert( type(FnameASP)==type(None) or type(FnameASP)==str)
    assert( type(Bounds)==type(None) or type(Bounds)==tuple )
    assert( type(Project)==type(None) or type(Project)==list )
    
    if Project:
        Project = [x for x in Project if x in Primes]

    lines = ['%% created on %s using PyBoolNet'%datetime.date.today().strftime('%d. %b. %Y'),
             '% PyBoolNet is available at "sourceforge.net/projects/boolnetfixpoints"',
             '',
             '% encoding of prime implicants as hyper-arcs that consist of a unique "target" and (possibly) several "sources".',
             '% "target" and "source" are triplets that consist of a variable name, an activity and a unique arc-identifier. ','']

    ID = 0
    for name in sorted(Primes.keys()):
        for value in [0,1]:
            for p in Primes[name][value]:
                ID += 1
                hyper = [ 'target("%s",%i,a%i).'%(name,value,ID) ]
                for n2,v2 in p.items():
                    hyper.append( 'source("%s",%i,a%i).'%(n2,v2,ID) )
                lines+= [' '.join(hyper)]
                
    lines+= ['']
    lines+= ['% generator: "in_set(ID)" specifies which arcs are chosen for a trap set (ID is unique for target(_,_,_)).',
             '{in_set(ID) : target(V,S,ID)}.',
             '',
             '% consistency constraint',
             ':- in_set(ID1), in_set(ID2), target(V,1,ID1), target(V,0,ID2).',
             '',
             '% stability constraint',
             ':- in_set(ID1), source(V,S,ID1), not in_set(ID2) : target(V,S,ID2).',
             '',
             '% bijection constraint (bijection between solutions and trap spaces)',
             'in_set(ID) :- target(V,S,ID); hit(V1,S1) : source(V1,S1,ID); hit(V2,S2) : target(V2,S2,ID).',
             ]
    
    lines+= ['',
             '% "hit" captures the stable variables and their activities.',
             'hit(V,S) :- in_set(ID), target(V,S,ID).']

    if Bounds:
        lines+= ['',
                 '%% cardinality constraint (enforced by "Bounds=%s")'%repr(Bounds),]
        if Bounds[0]>0:
            lines+= [':- {hit(V,S)} %i.'%(Bounds[0]-1)]
        lines+= [':- %i {hit(V,S)}.'%(Bounds[1]+1)]


    if OutsideOf:
        lines+= ['',
                 '%% subspace constraint (enforced by "OutsideOf=%s")'%repr(OutsideOf)]
        lines+= ['hit("%s", %i) :- hit("%s", S).'%(v,s,v) for v,s in sorted(OutsideOf.items())]

    if InsideOf:
        lines+= ['',
                 '%% subspace constraint (enforced by "InsideOf=%s")'%repr(InsideOf)]
        lines+= [' :- not hit("%s",%i).'%x for x in sorted(InsideOf.items()) ]
    
    if Project:
        lines+= ['',
                 '%% show projection (enforced by "Project=%s").'%(repr(sorted(Project)))]
        lines+= ['#show.']
        lines+= ['#show hit("{n}",S) : hit("{n}",S).'.format(n=name) for name in Project]
    else:
        lines+= ['',
                 '% show all (default)',
                 '#show hit/2.']

    if FnameASP==None:
        return '\n'.join(lines)
    
    with open(FnameASP, 'w') as f:
        f.write('\n'.join(lines))
    print('created %s'%FnameASP)




def potassco_handle(Primes, Type, Bounds, Project, InsideOf, OutsideOf, MaxOutput, Aggregate, FnameASP):
    """
    Returns a list of trap spaces using the Potassco_ ASP solver :ref:`[Gebser2011]<Gebser2011>`.
    """

    DEBUG = 0
    
    assert( Type in ['max','min','all'] )

    # replaces shortcut "n" by len(Primes) in Bounds argument
    if Bounds:
        Bounds = tuple([len(Primes) if x=="n" else x for x in Bounds])
    
    # unique solutions w.r.t. show
    params_clasp = []

    if not Aggregate:
        params_clasp+= ['--project']

    if   Type=='max':
        params_clasp+= ['--enum-mode=domRec', '--heuristic=Domain', '--dom-mod=5,16']
    elif Type=='min':
        params_clasp+= ['--enum-mode=domRec', '--heuristic=Domain', '--dom-mod=3,16']

    
    aspfile = primes2asp( Primes, FnameASP, Bounds, Project, InsideOf, OutsideOf )

    try:
        # pipe ASP file
        if FnameASP==None:
            cmd_gringo = [CMD_GRINGO]
            proc_gringo = subprocess.Popen(cmd_gringo, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            cmd_clasp  = [CMD_CLASP, '--models=%i'%MaxOutput] + params_clasp
            proc_clasp  = subprocess.Popen(cmd_clasp,  stdin=proc_gringo.stdout, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

            proc_gringo.stdin.write( aspfile.encode() )
            proc_gringo.stdin.close()

            output, error = proc_clasp.communicate()
            output = output.decode()

        # read ASP file
        else:
            cmd_gringo = [CMD_GRINGO, FnameASP]
            proc_gringo = subprocess.Popen(cmd_gringo, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            cmd_clasp  = [CMD_CLASP, '--models=%i'%MaxOutput] + params_clasp
            proc_clasp  = subprocess.Popen(cmd_clasp, stdin=proc_gringo.stdout, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

            output, error = proc_clasp.communicate()
            output = output.decode()

    except Exception as Ex:
        print(Ex)
        msg = "\nCall to gringo and / or clasp failed."
        if FnameASP!=None:
            msg+= '\ncommand: "%s"'%' '.join(cmd_gringo+['|']+cmd_clasp)
        print(msg)
        raise Ex

    if error:
        print(error)
        msg = "\nCall to gringo and / or clasp failed."
        if FnameASP!=None:
            msg+= '\ncommand: "%s"'%' '.join(cmd_gringo+['|']+cmd_clasp)
        print(msg)
        raise Exception

    if DEBUG:
        print("cmd_gringo: %s"%' '.join(cmd_gringo))
        print("cmd_clasp:  %s"%' '.join(cmd_clasp))
        print("error %s"%error)
        print("output")
        print(output)


    lines = output.split("\n")
    tspaces = []
    
    while lines and len(tspaces)<MaxOutput:
        line = lines.pop(0)
        
        if line[:6]=='Answer':
            line = lines.pop(0)
            d = [l[4:-1].split(',') for l in line.split()]
            d = [(l[0][1:-1],int(l[1])) for l in d]
            tspaces.append( dict(d) )

    if len(tspaces)==MaxOutput:
        print("There are possibly more than %i trap space."%MaxOutput)
        print("Increase MaxOutput to find out.")
    
    if Aggregate:
        return Count(tspaces)
    else:
        return tspaces


################ Not Working at the Moment ################


def trap_spaces_outsideof(Primes, Type, OutsideOf, MaxOutput=100, FnameASP=None):
    """
    Similar to :ref:`trap_spaces <sec:trap_spaces>` but with an additional parameter *OutsideOf* that requires that all solutions must
    contain the given subspace.
    
    **arguments**:
        * *Primes*: prime implicants
        * *Type* in ``["max","min","all"]``: subset minimal, subset maximal or all solutions
        * *OutsideOf* (dict): a subspace
        * *MaxOutput* (int): maximal number of trap spaces to return
        * *FnameASP*: file name or *None*
        
    **returns**:
        * list of trap spaces

    **example**::

        >>> subspace = {"v1":1, "v3":0}
        >>> tspaces = trap_spaces_outsideof(primes, "min", subspace)
        >>> tspaces[0]
        {"v1":1}
    """

    return potassco_handle(Primes, Type=Type, Bounds=None, Project=[], InsideOf=None, OutsideOf=OutsideOf, MaxOutput=MaxOutput, Aggregate=False, FnameASP=FnameASP)


def trap_spaces_insideof(Primes, Type, InsideOf, MaxOutput=100, FnameASP=None):
    """
    Similar to :ref:`trap_spaces <sec:trap_spaces>` but with an additional parameter *InsideOf* that requires that all solutions must
    be contained in the given subspace.
    
    **arguments**:
        * *Primes*: prime implicants
        * *Type* in ``["max","min","all"]``: subset minimal, subset maximal or all solutions
        * *InsideOf* (dict): a subspace
        * *MaxOutput* (int): maximal number of trap spaces to return
        * *FnameASP*: file name or *None*
        
    **returns**:
        * list of trap spaces

    **example**::

        >>> subspace = {"v1":1, "v3":0}
        >>> tspaces = trap_spaces_insideof(primes, "min", subspace)
        >>> tspaces[0]
        {"v1":1, "v3":0, "v5":0, "v6":0}
    """

    return potassco_handle(Primes, Type=Type, Bounds=None, Project=[], InsideOf=InsideOf, OutsideOf=None, MaxOutput=MaxOutput, Aggregate=False, FnameASP=FnameASP)




def trap_spaces_bounded(Primes, Type, Bounds, MaxOutput=100, FnameASP=None):
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

    return potassco_handle(Primes, Type, Bounds, Project=None, InsideOf=None, OutsideOf=None, MaxOutput=MaxOutput, Aggregate=False, FnameASP=FnameASP)
    




def Count( Spaces ):
    """
    returns tuples *(space, count)* where *count* states how often *space* occurs in *Spaces*.
    """

    dummy  = [tuple(sorted(x.items())) for x in Spaces]
    unique = set(dummy)
    result = []
    for x in unique:
        result.append((dict(x), dummy.count(x)))

    return result
























    
