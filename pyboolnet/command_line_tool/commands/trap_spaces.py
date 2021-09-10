

import click
from click import Command

from pyboolnet.command_line_tool.helpers import compute_primes_or_exit
from pyboolnet.trap_spaces import trap_spaces as compute_trap_spaces


@click.command("trap-spaces")
@click.option("-t", "--type", "type_", default="min", help="trap space type, 'min', 'max', 'all'")
@click.option("-m", "--max-output", default=10000, help="computes trap spaces")
@click.option("-r", "--representation", default="str", help="trap space representation, 'str' or 'dict'")
@click.option("-a", "--fname-asp", default="", help="file name to save asp text file")
@click.option("-p", "--fname-primes", default="", help="file name to save primes json")
@click.option("-o", "--fname-trap-spaces", default="", help="file name to save trap spaces")
@click.argument("fname-bnet")
def command_trap_spaces(type_: str, max_output: int, fname_asp: str, representation: str, fname_bnet: str, fname_primes: str, fname_trap_spaces: str):
    primes = compute_primes_or_exit(fname_bnet=fname_bnet, fname_primes=fname_primes)
    trap_spaces = compute_trap_spaces(primes=primes, type_=type_, max_output=max_output, representation=representation, fname_asp=fname_asp)
    lines = [str(x) for x in trap_spaces]
    for x in lines[:3]:
        click.echo(x)
    click.echo(f"found {len(lines)} trap spaces.")

    if fname_trap_spaces:
        with open(fname_trap_spaces, "r") as fp:
            fp.writelines(lines)
            click.echo(f"created {fname_trap_spaces}")


command_trap_spaces: Command


if __name__ == "__main__":
    command_trap_spaces.callback(
        type_="min",
        max_output=1000,
        fname_asp="",
        representation="str",
        fname_bnet="../../repository/grieco_mapk/grieco_mapk.bnet",
        fname_primes="",
        fname_trap_spaces="")
