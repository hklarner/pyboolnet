

import click
from click import Command

from pyboolnet.command_line_tool.check_binaries import check_all_binaries


@click.command("check-binaries")
def check_binaries():
    check_all_binaries()


check_binaries: Command
