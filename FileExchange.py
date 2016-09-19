#!/usr/bin/env python
# -*- coding: utf-8 -*-

import subprocess
import os
import ast
import datetime

import PyBoolNet.PrimeImplicants
import PyBoolNet.InteractionGraphs
import PyBoolNet.QuineMcCluskey
import PyBoolNet.Utility.Misc

BASE = os.path.join(os.path.dirname(__file__))
config = PyBoolNet.Utility.Misc.myconfigparser.SafeConfigParser()
config.read( os.path.join(BASE, "Dependencies", "settings.cfg") )

CMD_BNET2PRIMES = os.path.normpath(os.path.join( BASE, "Dependencies", config.get("Executables", "bnet2prime") ))


def _bnet2primes_error(proc, out, err, cmd):
    """
    raises exception for bnet2primes
    """
    if not proc.returncode == 0:
        print(out)
        print(err)
        print('\nCall to "BNet2Prime" resulted in return code %i'%proc.returncode)
        print('Command: %s'%' '.join(cmd))
        raise Exception


def bnet2primes( BNET, FnamePRIMES=None ):
    """    
    Generates and returns the prime implicants of a Boolean network in :ref:`installation_boolnet` format.
    The primes are saved as a *json* file if *FnamePRIMES* is given.
    The argument *BNET* may be either the name of a *bnet* file or a string containing the file contents.
    Use the function :ref:`FileExchange.read_primes <read_primes>` to open a previously saved *json* file.

    .. note::
    
        Requires the program :ref:`BNetToPrime <installation_bnettoprime>`.

    **arguments**:
       * *BNET*: name of *bnet* file or string contents of file
       * *FnamePRIMES*: *None* or name of *json* file to save primes

    **returns**:    
       * *Primes*: prime implicants

    **example**::
    
          >>> primes = bnet2primes("mapk.bnet", "mapk.primes" )
          >>> primes = bnet2primes("mapk.bnet")
          >>> primes = bnet2primes("Erk, !Mek \\n Raf, Ras & Mek")
          >>> primes = bnet2primes("Erk, !Mek \\n Raf, Ras & Mek", "mapk.primes")
    """

    # input and output via filename
    if not ',' in BNET and not FnamePRIMES==None:
        FnameBNET = BNET

        
        if FnamePRIMES!=None:
            
            cmd = [CMD_BNET2PRIMES, FnameBNET, FnamePRIMES]
            proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            out, err = proc.communicate()
            out = out.decode()
            _bnet2primes_error(proc, out, err, cmd)
            print('created %s'%FnamePRIMES)
            
            with open(FnamePRIMES) as f:
                lines = f.read()
            primes = ast.literal_eval(lines)


    # input via filename / output to stdout
    elif not ',' in BNET and FnamePRIMES==None:
        FnameBNET = BNET
        
        cmd = [CMD_BNET2PRIMES, FnameBNET]
        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        out, err = proc.communicate()
        out = out.decode()
        _bnet2primes_error(proc, out, err, cmd)

        out = out.replace('\x08','') # remove backspaces
        out = out.replace(' ','') # remove whitespaces

        primes = ast.literal_eval(out)


    # input via stdin / output to filename
    elif ',' in BNET and not FnamePRIMES==None:
        
        print("This is the only combination that is currently not possible.")
        print("Need to specify either a bnet file name or a json file name.")
        raise Exception
            
        cmd = [CMD_BNET2PRIMES, ">", FnamePRIMES]
        proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        out, err = proc.communicate( input=BNET.encode() )
        out = out.decode()
        proc.stdin.close()
        
        _bnet2primes_error(proc, out, err, cmd)
        print('created %s'%FnamePRIMES)

        primes = ast.literal_eval(out)


    # input via stdin / output to stdout
    elif ',' in BNET and FnamePRIMES==None:

        cmd = [CMD_BNET2PRIMES]
        proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        out, err = proc.communicate( input=BNET.encode() )
        proc.stdin.close()
        _bnet2primes_error(proc, out, err, cmd)
        out = out.decode()
        
        out = out.replace('\x08','') # remove backspaces
        out = out.replace(' ','') # remove whitespaces

        primes = ast.literal_eval(out)
    
    return primes


def primes2bnet(Primes, FnameBNET=None, Minimize=False):
    """
    Saves *Primes* as a *bnet* file, including the header *"targets, factors"* for compatibility with :ref:`installation_boolnet`.
    Without minimization, the resuting formulas are disjunctions of all prime implicants and may therefore be very long.
    If *Minimize=True* then a Python version of the Quine-McCluskey algorithm,
    namely :ref:`Prekas2012 <Prekas2012>` which is implemented in :ref:`QuineMcCluskey.primes2mindnf <primes2mindnf>`,
    will be used to minimize the number of clauses for each update function.

    **arguments**:
       * *Primes*: prime implicants
       * *FnameBNET* (str): name of *bnet* file or *None* for the string of the file contents
       * *Minimize* (bool): whether the expressions should be minimized

    **returns**:
        * *BNET* (str) if *FnameBNET=None* or *None* otherwise

    **example**::
    
          >>> primes2bnet(primes, "mapk.bnet")
          >>> primes2bnet(primes, "mapk.bnet", True)
          >>> expr = primes2bnet(primes)
          >>> expr = primes2bnet(primes, True)
    """

    width = max([len(x) for x in Primes]) + 5
    names = sorted(Primes.keys())

    lines = ['targets, factors']
    if Minimize:
        expressions = PyBoolNet.QuineMcCluskey.primes2mindnf(Primes)
        for name in names:
            lines+= [(name+',').ljust(width)+expressions[name]]

    else:
        for name in names:
            if Primes[name] == PyBoolNet.PrimeImplicants.CONSTANT_ON:
                expression = '1'
            elif Primes[name] == PyBoolNet.PrimeImplicants.CONSTANT_OFF:
                expression = '0'
            else:
                expression = ' | '.join([' & '.join([x if term[x]==1 else '!'+x for x in term]) for term in Primes[name][1]  ])

            lines+= [(name+',').ljust(width)+expression]

    if FnameBNET==None:
        return "\n".join(lines)
    
    with open(FnameBNET, 'w') as f:
        f.writelines('\n'.join(lines))
    print('created %s'%FnameBNET)


def write_primes( Primes, FnamePRIMES ):
    """
    Saves *Primes* as a *json* file.

    **arguments**:
       * *Primes*: prime implicants
       * *FnamePRIMES* (str): name of *json* file

    **example**::
    
          >>> write_primes(primes, "mapk.primes")
    """
    
    with open(FnamePRIMES, 'w') as f:
        f.write(str(Primes))
    print('created %s'%FnamePRIMES)

    
def read_primes( FnamePRIMES ):        
    """
    Reads the prime implicants of a Boolean network that were previously stored as a *json* file.

    **arguments**:
       * *FnamePRIMES* (str): name of *json* file

    **returns**:
       * *Primes*: prime implicants

    **example**::
    
          >>> primes = read_primes("mapk.primes")
    """
        
    with open(FnamePRIMES, 'r') as f:
        lines = f.read()

    return ast.literal_eval(lines)


def primes2genysis(Primes, FnameGENYSIS):
    """
    Generates a GenYsis_ file from *Primes* for the computation of all attractors of the synchronous or asynchronous transition system.
    GenYsis_ was introduced in :ref:`Garg2008 <Garg2008>`.
    It is available at http://www.vital-it.ch/software/genYsis.
    

    **arguments**:
       * *Primes*: prime implicants
       * *FnameGENYSIS* (str): name of GenYsis_ file

    **example**::
    
          >>> primes2genysis(primes, "mapk.genysis")
    """

    lines = []
    for name in sorted(Primes):

        if Primes[name] == PyBoolNet.PrimeImplicants.CONSTANT_ON:  
            lines+= [name+' -> '+name]
            lines+= ['^'+name+' -> '+name]

        elif Primes[name] == PyBoolNet.PrimeImplicants.CONSTANT_OFF:
            lines+= [name+' -| '+name]
            lines+= ['^'+name+' -| '+name]

        else: 
            for prime in Primes[name][1]:
                
                seq = []
                for n,v in sorted(prime.items()):
                    if v==1:
                        seq.append(n)
                    else:
                        seq.append('^'+n)
                lines+= ['&'.join(seq)+' -> '+name]


    with open(FnameGENYSIS, 'w') as f:
        f.write('\n'.join(lines))

    print('created %s'%FnameGENYSIS)
    

def primes2bns(Primes, FnameBNS):
    """
    Saves Primes as a *bns* file for the computation of all attractors of the synchronous transition system.
    BNS_ is based on :ref:`Dubrova2011 <Dubrova2011>`.
    It is available at http://people.kth.se/~dubrova/bns.html.

    **arguments**:
       * *Primes*: prime implicants
       * *FnameBNS* (str): name of *bns* file

    **example**::
    
          >>> primes2bns(primes, "mapk.bns")
    """
    
    names_sorted = sorted(Primes)
    lines = ['# '+', '.join(names_sorted),'']
    lines+= ['.v %i'%len(names_sorted),'']
    
    ig = PyBoolNet.InteractionGraphs.primes2igraph(Primes)
    for i, name in enumerate(names_sorted):
        i=i+1
        lines+= ['# %s'%name]
        regulators = sorted(ig.predecessors(name))
        nregs = len(regulators)
        iregs = ' '.join([str(names_sorted.index(reg)+1) for reg in regulators])
        
        lines+= ['.n {index} {number_regs} {ids_regs}'.format(index=i, number_regs=nregs, ids_regs=iregs)]

        for v in [0,1]:
            for prime in Primes[name][v]:
                seq = []
                for reg in regulators:
                    if reg in prime:
                        if prime[reg]==1:
                            seq.append('1')
                        else:
                            seq.append('0')
                    else:
                        seq.append('-')
                seq.append(' %i'%v)

                lines+= [''.join(seq)]

        lines+= ['']

    with open(FnameBNS, 'w') as f:
        f.write('\n'.join(lines))
    print('created %s'%FnameBNS)
        

def primes2eqn(Primes, FnameEQN):
    """
    Generates a *eqn* file as specified in the manual for the model checking software Antelope_ from *Primes*.
    Antelope_ was introduced in :ref:`Arellano2011 <Arellano2011>`.

    **arguments**:
       * *Primes*: prime implicants
       * *FnameEQN* (str): name of *eqn* file

    **example**::
    
          >>> primes2eqn(primes, "mapk.eqn")
    """

    lines = []
    for name in sorted(Primes):

        if Primes[name] == PyBoolNet.PrimeImplicants.CONSTANT_ON:  
            lines+= [name+' := true;']

        elif Primes[name] == PyBoolNet.PrimeImplicants.CONSTANT_OFF:
            lines+= [name+' := false;']

        else:
            disj = []
            for prime in Primes[name][1]:
                
                conj = []
                for n,v in sorted(prime.items()):
                    if v==1:
                        conj.append(n)
                    else:
                        conj.append('~'+n)
                        
                disj+= ['&'.join(conj)]

            lines+=[name+' := '+' | '.join(disj)+';']

    with open(FnameEQN, 'w') as f:
        f.write('\n'.join(lines))
        
    print('created %s'%FnameEQN)





        
