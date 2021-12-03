

import click

from pyboolnet.cli.commands.check_dependencies import check_dependencies
from pyboolnet.cli.commands.trap_spaces import command_trap_spaces
from pyboolnet.version import read_version_txt


@click.group(chain=True, context_settings=dict(help_option_names=["-h", "--help"]), invoke_without_command=True)
def main():
    click.echo(f"pyboolnet version: {read_version_txt()}")


main.add_command(check_dependencies)
main.add_command(command_trap_spaces)
