

import os, sys
import subprocess
import unittest
import ast
import datetime

import Utility

BASE = os.path.abspath(os.path.join(os.path.dirname(__file__)))
BASE = os.path.normpath(BASE)
config = Utility.myconfigparser.SafeConfigParser()
config.read( os.path.join(BASE, "Dependencies", "settings.cfg") )
CMD_NUSMV = os.path.normpath(os.path.join( BASE, "Dependencies", config.get("Executables", "nusmv") ))

fname_nusmvkeywords = os.path.join( BASE, "Dependencies", "nusmvkeywords.json" )
with open(fname_nusmvkeywords) as f:
            NUSMVKEYWORDS = f.read()
            NUSMVKEYWORDS = ast.literal_eval(NUSMVKEYWORDS)




def check_primes( Primes, Update, InitialStates, Specification, DisableCounterExamples=True,
                  DynamicReorder=True, DisableReachableStates=False, ConeOfInfluence=True, EnableAcceptingStates=False ):
    """
    Calls :ref:`installation_nusmv` to check whether the *Specification* is true or false in the transition system defined by *Primes*,
    the *InitialStates* and *Update*.
    The remaining arguments are :ref:`installation_nusmv` options, see the manual at http://nusmv.fbk.eu for details.

    See :ref:`primes2smv` and :ref:`Sec. 3.4 <sec:model_checking>` for details on model checking with |Software|.
        
    .. note::
        If *DisableCounterExamples* is *False* then *ConeOfInfluence* is forced to *False* because
        otherwise the counterexample output is incomplete.
    
    **arguments**:
        * *Primes*: prime implicants
        * *Update* (str): the update strategy, either *"synchronous"*, *"asynchronous"* or *"mixed"*
        * *InitialStates* (str): a :ref:`installation_nusmv` expression for the initial states, including the keyword *INIT*
        * *Specification* (str): a :ref:`installation_nusmv` formula, including the keyword *LTLSPEC* or *CTLSPEC*
        * *DisableCounterExamples* (bool): disables the computation of counterexamples using *-dcx*
        * *DynamicReorderBDDs* (bool): enables dynamic reordering of variables using *-dynamic*
        * *DisableReachableStates* (bool): disables the computation of reachable states using *-df*
        * *ConeOfInfluence* (bool): enables cone of influence reduction using *-coi*
        * *EnableAcceptingStates* (bool): enables the computation of accepting states (*-a*)

    **returns**:
        * *Answer* (bool): result of query, if *DisableCounterExamples==True*
        * *(Answer, Counterexample)* (bool, tuple/None): result of query and counterexample, if *DisableCounterExamples==False*. If *Answer==True* then *CounterExample* will be assigned *None*.

    **example**::

        >>> init = "INIT TRUE"
        >>> update = "asynchronous"
        >>> spec = "CTLSPEC AF(EG(v1&!v2))"
        >>> answer = check_primes(primes, update, init, spec)
        >>> answer
        False
        >>> answer, counterex = check_primes(primes, update, init, spec, False)
        >>> counterex
         ({'v1':0,'v2':0},{'v1':1,'v2':0},{'v1':1,'v2':1})
    """

    # trivial case: empty transition system
    if not Primes:
        return (True, None)

    cmd = [CMD_NUSMV]
    if DisableCounterExamples:
        cmd+= ['-dcx']
    if DynamicReorder:
        cmd+= ['-dynamic']
    if DisableReachableStates:
        cmd+= ['-df']
    if ConeOfInfluence and DisableCounterExamples:
        # coi messes with the output for the counterexamples printer of NuSMV
        cmd+= ['-coi']
    if EnableAcceptingStates:
        cmd+= ['-a', 'print']

    # needed, since NuSMV 2.6.0 doesn't accept stdin as input
    cmd+= ["/dev/stdin"]

    smvfile = primes2smv( Primes, Update, InitialStates, Specification, None )
    
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = proc.communicate( input=smvfile.encode() )
    out = out.decode()
    proc.stdin.close()

    return nusmv_handle( cmd, proc, out, err, DisableCounterExamples, EnableAcceptingStates )




def check_smv( FnameSMV, DisableCounterExamples=True, DynamicReorder=True, DisableReachableStates=False,
               ConeOfInfluence=True, EnableAcceptingStates=False ):
    """
    Calls :ref:`installation_nusmv` with the query defined in the *smv* file *FnameSMV*.
    The remaining arguments are :ref:`installation_nusmv` options, see the manual at http://nusmv.fbk.eu for details.

    See :ref:`primes2smv` and :ref:`Sec. 3.4 <sec:model_checking>` for details on model checking with |Software|.
    
    .. note::
        It is currently required that *FnameSMV* contains a single LTL or CTL formula.
        For future versions it is planned that :ref:`check_smv` returns a dictionary of answers.
    
    .. note::
        If *DisableCounterExamples* is *False* then *ConeOfInfluence* is forced to *False* because
        otherwise the counterexample output is incomplete.
        
    **arguments**:
        * *FnameSMV*: name of smv file
        * *DisableCounterExamples* (bool): disables computation of counterexamples (*-dcx*)
        * *DynamicReorderBDDs* (bool): enables dynamic reordering of variables (*-dynamic*)
        * *DisableReachableStates* (bool): disables the computation of reachable states (*-df*)
        * *ConeOfInfluence* (bool): enables cone of influence reduction (*-coi*)
        * *EnableAcceptingStates* (bool): disables the computation of accepting states (*-a*)

    **returns**:
        * *Answer* (bool): result of query, if *DisableCounterExamples==True*
        * *Counterexample* (tuple): result of query and counterexample, if *DisableCounterExamples==False*. If *Answer==True* then *CounterExample* will be assigned *None*.
        * *AcceptingStates* (dict): information about the accepting states, if *DisableAcceptingStates==False*.
        
    **example**::

        >>> check_smv("mapk.smv")
        False
        >>> answer, counterex = check_smv("mapk.smv", False)
        >>> counterex
        ({'Erk':0,'Mek':0},{'Erk':1,'Mek':0},{'Erk':1,'Mek':1})
    """

    cmd = [CMD_NUSMV]
    if DisableCounterExamples:
        cmd+= ['-dcx']
    if DynamicReorder:
        cmd+= ['-dynamic']
    if DisableReachableStates:
        cmd+= ['-df']
    if ConeOfInfluence:
        cmd+= ['-coi']
    if EnableAcceptingStates:
        cmd+= ['-a', 'print']
    
    cmd+= [FnameSMV]
    
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = proc.communicate()
    out = out.decode()

    return nusmv_handle( cmd, proc, out, err, DisableCounterExamples, EnableAcceptingStates )





def primes2smv(Primes, Update, InitialStates, Specification, FnameSMV=None):
    """
    Creates a NuSMV_ file from Primes and additional parameters that specify the update strategy, the initial states and the temporal logic specification.

    The initial states must be defined in :ref:`installation_nusmv` syntax, i.e.,
    starting with the keyword *INIT*.
    :ref:`installation_nusmv` uses *|* for disjunction, *&* for conjunction and *!* for negation.
    To set the initial states to the whole state space use *"INIT TRUE"*.
    CTL formulas must start with the keyword *CTLSPEC* and LTL formulas with the keyword *LTLSPEC*.

    .. note::
        The :ref:`installation_nusmv` language is case-sensitive and does not allow single character names for variables.
    
    In addition to variables that encode the activities of the components,
    auxillary variables are defined and available for use in CTL or LTL formulas,
    see :ref:`Sec. 3.4 <sec:model_checking>` for details:

    They are the Boolean *name_IMAGE* which is the value of the update function of the variable *name* in a state,
    the Boolean *name_STEADY* which is the value for whether the variable *name* is steady in a state,
    the integer *SUCCESSORS* which is the number of successors excluding itself (i.e., the number of variables that are changing in a state), and
    the Boolean *STEADYSTATE* which is the value for whether the current state is a steady state (which is equivalent to *SUCCESSORS=0*).
    
    **arguments**:
        * *Primes*: prime implicants
        * *Update* (str): the update strategy, either *"synchronous"*, *"asynchronous"* or *"mixed"*
        * *InitialStates* (str): a :ref:`installation_nusmv` expression for the initial states, including the keyword *INIT*
        * *Specification* (str): a :ref:`installation_nusmv` formula, including the keyword *LTLSPEC* or *CTLSPEC*
        * *FnameSMV* (str): name for *smv* file or *None*

    **returns**:
       * *FileSMV* (str): file as string or *None* if *FnameSMV==None*
       * raises *Exception* if *Primes* is the empty dictionary

    **example**::

        >>> ctlspec = "CTLSPEC EF(AG(!ERK) | AG(ERK))"
        >>> ltlspec = "LTLSPEC F(G(ERK))"
        >>> primes2smv(primes, "asynchronous", "INIT TRUE",  ctlspec, "mapk.smv")
        >>> primes2smv(primes, "synchronous",  "INIT ERK=1", ltlspec, "mapk.smv")
        >>> lines = primes2smv(primes, "synchronous",  "INIT ERK=1", ltlspec)
    """

    assert( type(FnameSMV)==type(None) or type(FnameSMV)==str )
    assert(Update in ['synchronous', 'asynchronous', 'mixed'])
    assert(InitialStates[:5] == "INIT ")
    assert(Specification[:8] in ["CTLSPEC ", "LTLSPEC "])

    if not Primes:
        print('You are trying to save the empty Boolean network as a SMV file.')
        print('Raising an exception to force you to decide what you want to do with empty Boolean networks (e.g. via a try-except block).')
        raise Exception

    names = [x for x in Primes if len(x)==1]
    if names:
        print('NuSMV requires variables names of at least two characters.')
        print('The network contains the following single character variables names: %s'%str(names))
        raise Exception

    critical = [x for x in Primes if x.lower()=='successors']
    if critical:
        print('Variable are not allowed to be called "SUCCESSORS".')
        print('Please change the name of the following variable: %s'%str(critical))
        raise Exception

    critical = [x for x in Primes if x.lower()=='steadystate']
    if critical:
        print('Variable are not allowed to be called "STEADYSTATE".')
        print('Please change the name of the following variable: %s'%str(critical))
        raise Exception

    critical = [x for x in Primes if '_image' in x.lower()]
    if critical:
        print('Variable names that include "_IMAGE" are not allowed.')
        print('Please change the name of the following variable: %s'%str(critical))
        raise Exception

    critical = [x for x in Primes if '_steady' in x.lower()]
    if critical:
        print('Variable names that include "_STEADY" are not allowed.')
        print('Please change the name of the following variable: %s'%str(critical))
        raise Exception

    keywords = [x for x in Primes if x in NUSMVKEYWORDS]
    if keywords:
        print('NuSMV keywords are not allowed as variable names.')
        print('The network contains the following variables names that are also NuSMVkeywords: %s'%str(keywords))
        raise Exception
              

    names_sorted = sorted(Primes)
    lines = ['-- created on %s using PyBoolNet'%datetime.date.today().strftime('%d. %b. %Y'),
             '-- available at "sourceforge.net/projects/boolnetfixpoints".',
             '',
             '',
             'MODULE main']

    lines+= ['','VAR']
    lines+= ['\t%s: boolean;'%name for name in names_sorted]

    lines+= ['']
    lines+= ['DEFINE']   
    for name in names_sorted:
        
        if Primes[name][1]==[{}]:
            expression = 'TRUE'
            
        elif Primes[name][1]==[]:
            expression = 'FALSE'
            
        else:
            expression = ' | '.join(['&'.join([x if term[x]==1 else '!'+x for x in term]) for term in Primes[name][1]  ])
            
        lines+= ['\t%s_IMAGE := %s;'%(name, expression)]

    lines+= ['']
    lines+= ['\t{n}_STEADY := ({n}_IMAGE = {n});'.format(n=name) for name in names_sorted]
    lines+= ['']
    x = ', '.join(['(!{n}_STEADY)'.format(n=name) for name in names_sorted])
    lines+= ['\tSUCCESSORS := count(%s);'%x]
    lines+= ['\tSTEADYSTATE := (SUCCESSORS = 0);']
        
    lines+= ['']
    lines+= ['ASSIGN']
    if Update=='synchronous':
        lines+= ['\tnext({n}) := {n}_IMAGE;'.format(n=name) for name in names_sorted]

    elif Update=='asynchronous':
        lines+= ['\tnext({n}) := {{{n}, {n}_IMAGE}};'.format(n=name) for name in names_sorted]
        lines+= ['','TRANS STEADYSTATE | count('+', '.join(['(next({n})!={n})'.format(n=name) for name in names_sorted])+')=1;']

    elif Update=='mixed':
        lines+= ['\tnext({n}) := {{{n}, {n}_IMAGE}};'.format(n=name) for name in names_sorted]
        lines+= ['','TRANS '+ ' | '.join(['STEADYSTATE']+['(next({n})!={n})'.format(n=name) for name in names_sorted])+';']

    
        
    lines+= ['','']
    lines+= [InitialStates]
    lines+= ['']
    lines+= [Specification]

    if FnameSMV==None:
        return '\n'.join(lines)
    
    with open(FnameSMV, 'w') as f:
        f.write('\n'.join(lines))
    print('created %s'%FnameSMV)







def output2counterexample( NuSMVOutput ):
    """
    Converts the output of a NuSMV call into a sequence of states that proves that the query is false.

    **arguments**:
        * *NuSMVOutput* (str): output of a call to NuSMV

    **returns**:
        * *CounterExample* (list): a sequence of states that disprove the query.
    """

    if 'Trace Type: Counterexample' not in NuSMVOutput:
        return None

    assert(NuSMVOutput.count('Trace Type: Counterexample')==1)
    counterexample = []
    last_state = False
    
    blocks = NuSMVOutput.split('Trace Type: Counterexample')[1]

    blocks = blocks.split('-> ')
    for block in blocks:
        lines = block.split('\n')
        lines = [x.strip() for x in lines]
        lines = [x for x in lines if '=' in x]
        lines = [x for x in lines if '_IMAGE' not in x]
        lines = [x for x in lines if '_STEADY' not in x]
        lines = [x for x in lines if not x.startswith('SUCCESSORS')]
        lines = [x for x in lines if not x.startswith('STEADYSTATE')]
        lines = [x for x in lines if x!=[]]

        if lines:
            
            if last_state:
                state = last_state.copy()
            else:
                state = {}
                
            for line in lines:
                name, value = line.split(' = ')
                assert(value in ['TRUE','FALSE'])
                state[name] = 1 if value== 'TRUE' else 0

            counterexample.append( state )
            last_state = state
    
    return tuple(counterexample)


def output2acceptingstates( NuSMVOutput ):
    """
    Converts the output of a NuSMV call into an accepting states dictionary that contains information about the initial states,
    accepting states and accepting and initial.

    **arguments**:
        * *NuSMVOutput* (str): output of a call to NuSMV

    **returns**:
        * *AcceptingStates* (dict): information about the accepting states with the following keys:
            * CTLSPEC: the CTL formula
            * INIT: the initial states
            * INIT_SIZE: number of initial states
            * ACCEPTING: factored formula of the accepting states
            * ACCEPTING_SIZE: number of accepting states
            * INITACCEPTING: factored formula of the initial and accepting states
            * INITACCEPTING_SIZE: number of initial and accepting states
            * ANSWER: whether the query is true
    """

    
    accepting = {}
    
    for line in NuSMVOutput.split("\n"):
        if line.startswith("initial states:"):
            accepting["INIT"] = str(line.split(":")[1].strip())
        elif line.startswith("number of initial states:"):
            accepting["INIT_SIZE"] = int(line.split(":")[1].strip())
        elif line.startswith("accepting states:"):
            accepting["ACCEPTING"] = str(line.split(":")[1].strip())
        elif line.startswith("number of accepting states:"):
            accepting["ACCEPTING_SIZE"] = int(line.split(":")[1].strip())
        elif line.startswith("initial and accepting States:"):
            accepting["INITACCEPTING"] = str(line.split(":")[1].strip())
        elif line.startswith("number of initial and accepting states:"):
            accepting["INITACCEPTING_SIZE"] = int(line.split(":")[1].strip())
    
    return accepting


def nusmv_handle( Command, Process, Output, Error, DisableCounterExamples, EnableAcceptingStates ):
    """
    The part of the code of "check_smv" and "check_primes" that is identical in both functions.
    
    **arguments**:
        * *Command* (list): list of commands that was used to call subprocess.Popen.
        It is only used for creating an error message if the process does not finish correctly.
        * *Process* (subprocess.Popen): the object returned by subprocess.Popen
        * *Output* (Popen.communicate): the object returned by Popen.communicate
        * *DisableCounterExamples* (bool): whether a counterexample should be returned if the query is false
        * *EnableAcceptingStates* (bool): whether information about the accepting states should be returned

    **returns**:
        * *Answer* (bool): whether NuSMV returns "is true"
        * *CounterExample* (list): a counterexample if NuSMV returns "is false" and DisableCounterExamples==False.
        * *AcceptingStates* (dict): information about the accepting states, if *DisableAcceptingStates==False*.
    """
    
    if Process.returncode == 0:

        if Output.count('specification')>1:
            print('SMV file contains more than one CTL or LTL specification.')
            raise Exception

        if 'is false' in Output:
            answer = False
        elif 'is true' in Output:
            answer = True
        else:
            print(Output)
            print(Error)
            print('NuSMV output does not respond with "is false" or "is true".')
            raise Exception
            
    else:
        print(Output)
        print(Error)
        print('NuSMV did not respond with return code 0')
        print('command: %s'%' '.join(Command))
        raise Exception

    if DisableCounterExamples and not EnableAcceptingStates:
        return answer

    result = [answer]
    
    if not DisableCounterExamples:
        counterex = output2counterexample( NuSMVOutput=Output )
        result.append(counterex)

    if EnableAcceptingStates:
        accepting = output2acceptingstates( NuSMVOutput=Output )
        result.append(accepting)

    return tuple(result)



    
