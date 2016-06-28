
import os
BASE = os.path.abspath(os.path.join(os.path.dirname(__file__)))
BASE = os.path.normpath(BASE)

import FileExchange
import generator



def get_primes(FnameBNET):
    assert("." not in FnameBNET)
    path = os.path.join(BASE,FnameBNET,FnameBNET+".bnet")

    return FileExchange.bnet2primes(path)


def get_bnet(FnameBNET):
    assert("." not in FnameBNET)
    path = os.path.join(BASE,FnameBNET,FnameBNET+".bnet")
    with open(path) as f:
        bnet = f.read()

    return bnet
