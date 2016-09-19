#!/usr/bin/env python

import os
import ast
import inspect
import itertools

import PyBoolNet.FileExchange

BASE = os.path.join(os.path.dirname(__file__))
fname_nusmvkeywords = os.path.join(BASE, "Dependencies", "nusmvkeywords.json")
with open(fname_nusmvkeywords) as f:
            NUSMVKEYWORDS = f.read()
            NUSMVKEYWORDS = ast.literal_eval(NUSMVKEYWORDS)




def primes2mindnf(Primes):
    """
    Creates a minimal *disjunctive normal form* (DNF) expression for the Boolean network represented by *Primes*.
    The algorithm uses :ref:`Prekas2012 <Prekas2012>`, a Python implementation of the Quine-McCluskey algorithm.

    **arguments**:
        * *Primes*: prime implicants

    **returns**:
        * *MinDNF* (dict): keys are names and values are minimal DNF expressions

    **example**:

        >>> primes["v1"][1]
        [{'v1':1,'v2':0}]
        >>> mindnf = primes2mindnf(primes)
        >>> mindnf["v1"]
        ((! v2) | v1)
    """

    expressions = {}
    for name in Primes:

        # name is const
        if Primes[name][1]==[{}]:
            expressions[name] = "1"
            continue
        if Primes[name][0]==[{}]:
            expressions[name] = "0"
            continue

        inputs = sorted(set([x for p in Primes[name][1] for x in p]))
        prod = len(inputs)*[[0,1]]
        ones = []
        for i,values in enumerate(itertools.product(*prod)):
            state = dict(zip(inputs, values))

            for prime in Primes[name][1]:
                if all([state[x]==prime[x] for x in prime]):
                    ones+=[i]
                    
        primes_tuples = [ primedict2primetuple(x, inputs) for x in Primes[name][1] ]
        
        quine = QM(list(reversed(inputs)))
        complexity, minterms = quine.unate_cover(list(primes_tuples), ones)
        

        expressions[name] = quine.get_function(minterms)

    return expressions

    
def functions2primes(Functions):
    """
    Generates and returns the prime implicants of a Boolean network represented by *Functions*.

    **arguments**:
        * *Functions* (dict): keys are component names and values are Boolean functions

    **returns**:
        * *Primes*: primes implicants

    **example**:

        >>> funcs = {"v1": lambda v1,v2: v1 or not v2,
        ...          "v2": lambda v1,v2: v1+v2==1}
        >>> primes = functions2primes(funcs)
    """
    
    mindnf = functions2mindnf(Functions)
    lines = ["%s,\t\t%s"%x for x in mindnf.items()]

    return PyBoolNet.FileExchange.bnet2primes(BNET='\n'.join(lines))

    
def functions2mindnf(Functions):
    """
    Generates and returns a minimal *disjunctive normal form* (DNF) for the Boolean network represented by *Functions*.
    The algorithm uses :ref:`Prekas2012 <Prekas2012>`, a Python implementation of the Quine-McCluskey algorithm.

    **arguments**:
        * *Functions* (dict): keys are component names and values are Boolean functions

    **returns**:
        * *MinDNF* (dict): keys are component names and values are minimal DNF expressions

    **example**:

        >>> funcs = {"v1": lambda v1,v2: v1 or not v2,
        ...          "v2": lambda: 1}
        >>> mindnf = functions2primes(funcs)
        >>> mindnf["v1"]
        ((! v2) | v1)
    """

    assert(all([inspect.isfunction(f) for f in Functions.values()]))

    Names = Functions.keys()
    
    too_short = [x for x in Names if len(x)==1]
    if too_short:
        print('warning: variable names must be at least two characters if you want to you NuSMV.')
        print('Names that are too short: %s'%', '.join(too_short))

    keywords = [x for x in Names if x in fname_nusmvkeywords]
    if keywords:
        print('warning: variable names can not be NuSMV keywords.')
        print('Names that are keywords:', ', '.join(keywords))

    expressions = {}
    for name, func in Functions.items():
        inputs = inspect.getargspec(func).args

        # name is constant (no inputs)
        if not inputs:
            const = func()
            assert(const in [0,1,True,False])
            expressions[name] = '1' if func() else '0'
            continue

        if len(inputs)>10:
            print("warning: computation of prime implicants may take a very long time for %s."%name)

        ones, zeros = [], []
        prod = len(inputs)*[[0,1]]
        for i,values in enumerate(itertools.product(*prod)):
            if func(*values):
                ones +=[i]
            else:
                zeros+=[i]

        # name is constant (all combinations evaluate to same value)
        if ones==[]:
            expressions[name] = '0'
            continue
        if zeros==[]:
            expressions[name] = '1'
            continue

        quine = QM(list(reversed(inputs)))
        primes = quine.compute_primes(ones )
        complexity, minterms = quine.unate_cover(list(primes), ones)

        expressions[name] = quine.get_function(minterms)


    return expressions
        
        



#################################

"""
Copyright (c) 2012 George Prekas <prekgeo@yahoo.com>

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the "Software"), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
"""

"""
This class implements the Quine-McCluskey algorithm for minimization of boolean
functions.

Based on code from Robert Dick <dickrp@eecs.umich.edu> and Pat Maupin
<pmaupin@gmail.com>. Most of the original code was re-written for performance
reasons.

>>> qm = QM(['A','B'])

>>> qm.get_function(qm.solve([],[])[1])
'0'
>>> qm.get_function(qm.solve([1,3],[0,2])[1])
'1'
>>> qm.get_function(qm.solve([0,1,2,3],[])[1])
'1'
>>> qm.get_function(qm.solve([3],[])[1])
'(A AND B)'
>>> qm.get_function(qm.solve([0],[])[1])
'((NOT A) AND (NOT B))'
>>> qm.get_function(qm.solve([1,3],[])[1])
'A'
>>> qm.get_function(qm.solve([1],[3])[1])
'A'
>>> qm.get_function(qm.solve([2,3],[])[1])
'B'
>>> qm.get_function(qm.solve([0,2],[])[1])
'(NOT A)'
>>> qm.get_function(qm.solve([0,1],[])[1])
'(NOT B)'
>>> qm.get_function(qm.solve([1,2,3],[])[1])
'(A OR B)'
>>> qm.get_function(qm.solve([0,1,2],[])[1])
'((NOT B) OR (NOT A))'
"""

class QM:
  def __init__(self, variables):
    """
    Initialize the Quine-McCluskey solver.

    variables: a list of strings that are the names of the variables used in
    the boolean functions
    """

    self.variables = variables
    self.numvars = len(variables)

  def solve(self, ones, dc):
    """
    Executes the Quine-McCluskey algorithm and returns its results.

    ones: a list of indices for the minterms for which the function evaluates
    to 1
    dc: a list of indices for the minterms for which we do not care about the
    function evaluation

    returns: a tuple a,b; a is the complexity of the result and b is a list of
    minterms which is the minified boolean function expressed as a sum of
    products
    """

    # Handle special case for functions that always evaluate to True or False.
    if len(ones) == 0:
      return 0,'0'
    if len(ones) + len(dc) == 1<<self.numvars:
      return 0,'1'

    primes = self.compute_primes(ones + dc)
    return self.unate_cover(list(primes), ones)


  def compute_primes(self, cubes):
    """
    Find all prime implicants of the function.

    cubes: a list of indices for the minterms for which the function evaluates
    to 1 or don't-care.
    """

    sigma = []
    for i in range(self.numvars+1):
      sigma.append(set())
    for i in cubes:
      sigma[bitcount(i)].add((i,0))

    primes = set()
    while sigma:
      nsigma = []
      redundant = set()
      for c1, c2 in zip(sigma[:-1], sigma[1:]):
        nc = set()
        for a in c1:
          for b in c2:
            m = merge(a, b)
            if m != None:
              nc.add(m)
              redundant |= set([a, b])
        nsigma.append(nc)
      primes |= set(c for cubes in sigma for c in cubes) - redundant
      sigma = nsigma
      
    return primes

  def unate_cover(self, primes, ones):
    """
    Use the prime implicants to find the essential prime implicants of the
    function, as well as other prime implicants that are necessary to cover
    the function. This method uses the Petrick's method, which is a technique
    for determining all minimum sum-of-products solutions from a prime implicant
    chart.

    primes: the prime implicants that we want to minimize.
    ones: a list of indices for the minterms for which we want the function to
    evaluate to 1.
    """

    chart = []
    for one in ones:
      column = []
      for i in range(len(primes)):
        if (one & (~primes[i][1])) == primes[i][0]:
          column.append(i)
      chart.append(column)

    covers = []
    if len(chart) > 0:
      covers = [set([i]) for i in chart[0]]
    for i in range(1,len(chart)):
      new_covers = []
      for cover in covers:
        for prime_index in chart[i]:
          x = set(cover)
          x.add(prime_index)
          append = True
          for j in range(len(new_covers)-1,-1,-1):
            if x <= new_covers[j]:
              del new_covers[j]
            elif x > new_covers[j]:
              append = False
          if append:
            new_covers.append(x)
      covers = new_covers

    min_complexity = 99999999
    for cover in covers:
      primes_in_cover = [primes[prime_index] for prime_index in cover]
      complexity = self.calculate_complexity(primes_in_cover)
      if complexity < min_complexity:
        min_complexity = complexity
        result = primes_in_cover

    return min_complexity,result

  def calculate_complexity(self, minterms):
    """
    Calculate the complexity of the given function. The complexity is calculated
    based on the following rules:
      A NOT gate adds 1 to the complexity.
      A n-input AND or OR gate adds n to the complexity.

    minterms: a list of minterms that form the function

    returns: an integer that is the complexity of the function

    >>> qm = QM(['A','B','C'])

    >>> qm.calculate_complexity([(1,6)])
    0
    >>> qm.calculate_complexity([(0,6)])
    1
    >>> qm.calculate_complexity([(3,4)])
    2
    >>> qm.calculate_complexity([(7,0)])
    3
    >>> qm.calculate_complexity([(1,6),(2,5),(4,3)])
    3
    >>> qm.calculate_complexity([(0,6),(2,5),(4,3)])
    4
    >>> qm.calculate_complexity([(0,6),(0,5),(4,3)])
    5
    >>> qm.calculate_complexity([(0,6),(0,5),(0,3)])
    6
    >>> qm.calculate_complexity([(3,4),(7,0),(5,2)])
    10
    >>> qm.calculate_complexity([(1,4),(7,0),(5,2)])
    11
    >>> qm.calculate_complexity([(2,4),(7,0),(5,2)])
    11
    >>> qm.calculate_complexity([(0,4),(7,0),(5,2)])
    12
    >>> qm.calculate_complexity([(0,4),(0,0),(5,2)])
    15
    >>> qm.calculate_complexity([(0,4),(0,0),(0,2)])
    17
    """

    complexity = len(minterms)
    if complexity == 1:
      complexity = 0
    mask = (1<<self.numvars)-1
    for minterm in minterms:
      masked = ~minterm[1] & mask
      term_complexity = bitcount(masked)
      if term_complexity == 1:
        term_complexity = 0
      complexity += term_complexity
      complexity += bitcount(~minterm[0] & masked)

    return complexity


  def get_function(self, minterms):
    """
    Return in human readable form a sum of products function.

    minterms: a list of minterms that form the function

    returns: a string that represents the function using operators AND, OR and
    NOT.
    """

    if isinstance(minterms,str):
      return minterms

    def parentheses(glue, array):
      if len(array) > 1:
        return ''.join(['(',glue.join(array),')'])
      else:
        return glue.join(array)

    or_terms = []
    for minterm in minterms:
      and_terms = []
      for j in range(len(self.variables)):
        if minterm[0] & 1<<j:
          and_terms.append(self.variables[j])
        elif not minterm[1] & 1<<j:
          and_terms.append('(! %s)' % self.variables[j])
      or_terms.append(parentheses(' & ', and_terms))
    return parentheses(' | ', or_terms)

  def get_prime_dict(self, minterms):
    """
    Returns the prime implicants of a Boolean expression defined by the minterms.
    """

    if isinstance(minterms,str):
      return minterms

    def parentheses(glue, array):
      if len(array) > 1:
        return ''.join(['(',glue.join(array),')'])
      else:
        return glue.join(array)

    or_terms = []
    for minterm in minterms:
      and_terms = {}
      for j in range(len(self.variables)):
        if minterm[0] & 1<<j:
          and_terms[self.variables[j]]=1
        elif not minterm[1] & 1<<j:
          and_terms[self.variables[j]]=0
      or_terms.append(parentheses(' & ', and_terms))
      
    return and_terms
  

def bitcount(i):
  """ Count set bits of the input. """

  res = 0
  while i > 0:
    res += i&1
    i>>=1
  return res


def is_power_of_two_or_zero(x):
  """
  Determine if an input is zero or a power of two. Alternative, determine if an
  input has at most 1 bit set.
  """

  return (x & (~x + 1)) == x


def merge(i, j):
  """ Combine two minterms. """

  if i[1] != j[1]:
    return None
  y = i[0] ^ j[0]
  if not is_power_of_two_or_zero(y):
    return None
  return (i[0] & j[0],i[1]|y)


def primedict2primetuple(Primes, Names):
    atoms = ''.join(['1' if (x in Primes and Primes[x]==1) else '0' for x in Names])
    atoms = int(atoms,2)
    mask  = ''.join(['1' if x not in Primes else '0' for x in Names])
    mask  = int(mask,2)

    return (atoms,mask)





if __name__=="__main__":
    primes = {'A': [[{}], []], 'B': [[], [{}]], 'C': [[{'A': 1}, {'B': 0}], [{'A': 0, 'B': 1}]]}
    expressions = primes2mindnf(primes)
    print(expressions)












