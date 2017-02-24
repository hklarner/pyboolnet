
import os
BASE = os.path.abspath(os.path.join(os.path.dirname(__file__)))
BASE = os.path.normpath(BASE)

import PyBoolNet.FileExchange


def names_with_fast_basin_computation():
    result = ["arellano_rootstem","dahlhaus_neuroplastoma",
              "davidich_yeast", "dinwoodie_life", "faure_cellcycle",
              "irons_yeast", "randomnet_n7k3", "randomnet_n15k3",
              "saadatpour_guardcell", "tournier_apoptosis", "xiao_wnt5a"]
    
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

    return sorted([os.path.basename(subdir) for subdir, _, _ in os.walk(BASE) if not subdir==BASE])
        

def get_primes(Fname):
    """
    Fetches the prime implicants of the network *Fname* in the model repository.
    Run :ref:`get_all_names` to see all networks currently available. 
    
    **arguments**:
        * *Fname* (str): name of network

    **returns**:
        * *Primes* (dict): the prime implicants

    **example**::

            >>> get_primes("raf")
            {'Raf': [[{'Raf': 1, 'Erk': 1}], [{'Raf': 0}, {'Erk': 0}]],...
    """
    
    path = os.path.join(BASE,Fname,Fname+".bnet")

    return PyBoolNet.FileExchange.bnet2primes(path)


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
