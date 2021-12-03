

import click
from click import Command

from pyboolnet.cli.check_dependencies import check_all_dependencies


@click.command("check-dependencies")
def check_dependencies():
    check_all_dependencies()


check_dependencies: Command
