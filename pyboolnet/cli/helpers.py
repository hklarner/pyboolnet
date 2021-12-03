

import os
import sys

import click

from pyboolnet.file_exchange import bnet2primes, write_primes


def compute_primes_or_exit(fname_bnet: str, fname_primes: str) -> dict:
    if not os.path.isfile(fname_bnet):
        click.echo(f"file does not exist: fname_bnet={fname_bnet}")
        sys.exit()

    primes = bnet2primes(bnet=fname_bnet)
    if fname_primes:
        write_primes(primes=primes, fname_json=fname_primes)

    return bnet2primes(bnet=fname_bnet)
