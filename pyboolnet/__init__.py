

import logging
import os
import sys

from pyboolnet.helpers import read_executables
from pyboolnet.version import read_version_txt

VERSION = read_version_txt()
NUSMV_KEYWORDS = ['MODULE', 'DEFINE', 'MDEFINE', 'CONSTANTS', 'VAR', 'IVAR', 'FROZENVAR', 'INIT', 'TRANS', 'INVAR', 'SPEC', 'CTLSPEC', 'LTLSPEC', 'PSLSPEC', 'COMPUTE', 'NAME', 'INVARSPEC', 'FAIRNESS', 'JUSTICE', 'COMPASSION', 'ISA', 'ASSIGN', 'CONSTRAINT', 'SIMPWFF', 'CTLWFF', 'LTLWFF', 'PSLWFF', 'COMPWFF', 'IN', 'MIN', 'MAX', 'MIRROR', 'PRED', 'PREDICATES', 'process', 'array', 'of', 'boolean', 'integer', 'real', 'word', 'word1', 'bool', 'signed', 'unsigned', 'extend', 'resize', 'sizeof', 'uwconst', 'swconst', 'EX', 'AX', 'EF', 'AF', 'EG', 'AG', 'E', 'F', 'O', 'G', 'H', 'X', 'Y', 'Z', 'A', 'U', 'S', 'V', 'T', 'BU', 'EBF', 'ABF', 'EBG', 'ABG', 'case', 'esac', 'mod', 'next', 'init', 'union', 'in', 'xor', 'xnor', 'self', 'TRUE', 'FALSE', 'count']
COLOR_MAP = {"red1": "#df3e47", "green1": "#4bb93f", "blue1": "#7463b3", "yellow1": "#eecf1a", "pink1": "#db42a6", "green2": "#4cbd38", "red2": "#df3d47", "yellow2": "#efce1a"}
COLORS = ["dodgerblue3", "firebrick2", "chartreuse3", "gold1", "aquamarine2", "darkorchid2"]
UPDATES = ["synchronous", "asynchronous", "mixed"]
GRAPHVIZ_LAYOUT_ENGINES = ["dot", "neato", "fdp", "sfdp", "circo", "twopi"]
ROOT_DIR = os.path.join(os.path.dirname(__file__))
EXECUTABLES = read_executables()

logging.basicConfig(format="%(levelname)s %(message)s", stream=sys.stdout, level=logging.INFO)
log = logging.getLogger(__name__)


def find_command(name: str) -> str:
    """
    find the path to a command, in local binaries folder or in the shared execution PATH
    """

    if name in EXECUTABLES:
        cmd = EXECUTABLES[name]
        if cmd.startswith(":"):
            cmd = cmd[1:]
        else:
            cmd = os.path.normpath(os.path.join(ROOT_DIR, "binaries", cmd))
    else:
        cmd = name

    return cmd
