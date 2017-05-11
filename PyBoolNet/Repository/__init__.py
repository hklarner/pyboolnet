
import os
BASE = os.path.abspath(os.path.join(os.path.dirname(__file__)))
BASE = os.path.normpath(BASE)

import PyBoolNet.FileExchange



def print_info(MarkDown=False):
    """
    prints repository info
    """

    MAXOUTPUT = 100000
    
    header = [('name','size','inputs','constants','steady states','cyclic attractors (mints)')]
    data   = []
    for name in get_all_names():
        primes = get_primes(name)
        tspaces = PyBoolNet.TrapSpaces.trap_spaces(primes, "min", MaxOutput=MAXOUTPUT)

        size      = str(len(primes))
        inputs    = str(len(PyBoolNet.PrimeImplicants.find_inputs(primes)))
        constants = str(len(PyBoolNet.PrimeImplicants.find_constants(primes)))
        steady    = len([x for x in tspaces if len(x)==len(primes)])
        steady    = str(steady) + '+'*(steady==MAXOUTPUT)
        cyclic    = len([x for x in tspaces if len(x)<len(primes)])
        cyclic    = str(cyclic) + '+'*(steady==MAXOUTPUT)
        
        data.append((name,size,inputs,constants,steady,cyclic))

    data.sort(key=lambda x: int(x[1]))
    data = header + data

    width = {}
    for i in range(len(data[0])):
        width[i] = max(len(x[i]) for x in data) + 2

    if MarkDown:
        header = '| ' + ' | '.join(x.ljust(width[i]) for i,x in enumerate(data[0])) + ' |'
        print(header)
        print('| ' + ' | '.join('-'*width[i] for i,x in enumerate(data[0])) + ' |')
        
        body   = data[1:]
        for row in body:
            print('| ' + ' | '.join(x.ljust(width[i]) for i,x in enumerate(row)) + ' |')

    else:
        for row in data:
            print(''.join(x.ljust(width[i]) for i,x in enumerate(row)))

    



def names_with_fast_basin_computation():
    result = ["arellano_rootstem","dahlhaus_neuroplastoma",
              "dinwoodie_life", "faure_cellcycle",
              "irons_yeast", "randomnet_n7k3", "randomnet_n15k3",
              "saadatpour_guardcell", "tournier_apoptosis", "xiao_wnt5a",
              "raf","n5s3","n3s1c1a","n3s1c1b","n6s1c2","n7s3"]
    
    return result


def get_all_names():
    """
    Returns the names of all models currently in the repository.

    **returns**:
        * *Fnames* (list): model names

    **example**::

        >>> get_all_names()
        ['arellano_rootstem', 'dahlhaus_neuroplastoma', ...]
    """

    result = sorted([os.path.basename(subdir) for subdir, _, _ in os.walk(BASE) if not subdir==BASE and not "__" in subdir])

    return result
        

def get_primes(Name):
    """
    Fetches the prime implicants of the network *Name* in the model repository.
    Run :ref:`get_all_names` to see all networks currently available. 
    
    **arguments**:
        * *Name* (str): name of network

    **returns**:
        * *Primes* (dict): the prime implicants

    **example**::

            >>> get_primes("raf")
            {'Raf': [[{'Raf': 1, 'Erk': 1}], [{'Raf': 0}, {'Erk': 0}]],...
    """

    path = os.path.join(BASE,Name,Name+".bnet")
    
    if os.path.isfile(path):
        return PyBoolNet.FileExchange.bnet2primes(path)
    
    print(" %s does not exist"%Name)
    raise Exception


def get_bnet(Fname):
    """
    Fetches the bnet file as a string of the network *Fname* in the model repository.
    Run :ref:`get_all_names` to see all networks currently available. 
    
    **arguments**:
        * *Fname* (str): name of network

    **returns**:
        * *BNET* (str): the bnet file

    **example**::

            >>> get_bnet("raf")
            {'Raf': [[{'Raf': 1, 'Erk': 1}], [{'Raf': 0}, {'Erk': 0}]],...
    """
        
    path = os.path.join(BASE,Fname,Fname+".bnet")
    with open(path) as f:
        bnet = f.read()

    return bnet
                     

if __name__=="__main__":
    print_info(MarkDown=True)

                     
