

import click

from pyboolnet.version import read_version_txt
from pyboolnet.command_line_tool.commands.check_binaries import check_binaries


@click.group(chain=True, context_settings=dict(help_option_names=["-h", "--help"]), invoke_without_command=True)
def main():
    click.echo(f"pyboolnet version: {read_version_txt()}")


main.add_command(check_binaries)
