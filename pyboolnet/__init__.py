

import os
from typing import List
import logging

import pyboolnet.attractors
import pyboolnet.basins_of_attraction
import pyboolnet.commitment_diagrams
import pyboolnet.phenotypes
import pyboolnet.file_exchange
import pyboolnet.interaction_graphs
import pyboolnet.model_checking
import pyboolnet.prime_implicants
import pyboolnet.boolean_normal_forms
import pyboolnet.state_transition_graphs
import pyboolnet.temporal_logic
import pyboolnet.trap_spaces
import pyboolnet.repository
import pyboolnet.boolean_logic
import pyboolnet.tests
import pyboolnet.network_generators

from pyboolnet.misc import read_nusmv_keywords_or_exit

ROOT = os.path.abspath(os.path.dirname(__file__))
NUSMV_KEYWORDS = read_nusmv_keywords_or_exit()
COLOR_MAP = {"red1": "#df3e47", "green1": "#4bb93f", "blue1": "#7463b3", "yellow1": "#eecf1a", "pink1": "#db42a6", "green2": "#4cbd38", "red2": "#df3d47", "yellow2": "#efce1a"}
COLORS = ["dodgerblue3", "firebrick2", "chartreuse3", "gold1", "aquamarine2", "darkorchid2"]
UPDATES = ["synchronous", "asynchronous", "mixed"]
GRAPHVIZ_ENGINES = ["dot", "neato", "fdp", "sfdp", "circo", "twopi"]
ROOT_DIR = os.path.join(os.path.dirname(__file__))


if __name__ == '__main__':
    print(ROOT)
