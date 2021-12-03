

import pytest
from click.testing import CliRunner

from pyboolnet.cli.main import main


@pytest.mark.parametrize("args", [
    "trap-spaces -t min ../../pyboolnet/repository/grieco_mapk/grieco_mapk.bnet",
])
def test_trap_spaces(args):
    runner = CliRunner()
    result = runner.invoke(main, args)
    assert result.exit_code == 0
