

import logging
import sys
from typing import List
import configparser
import json
import math
import os
import ast

ROOT_DIR = os.path.join(os.path.dirname(__file__))
EXECUTABLES = _load_cfg()

log = logging.getLogger(__name__)


def read_txt_version() -> str:
    with open("version.txt") as fp:
        pass


def _load_cfg():
    config = configparser.SafeConfigParser()
    settings_file = os.path.join(ROOT_DIR, "Dependencies", "settings.cfg")

    if not os.path.exists(settings_file):
        execs = dict(
            nusmv="./NuSMV-2.6.0/bin/NuSMV",
            gringo="./gringo-4.4.0-x86-linux/gringo",
            clasp="./clasp-3.1.1/clasp-3.1.1-x86-linux",
            bnet2prime="./BNetToPrime/BNetToPrime")
    else:
        config.read(settings_file)
        execs = {n: config.get("Executables", n) for n in config.options("Executables")}

    return execs


def os_is_windows() -> bool:
    return os.name == 'nt'


def read_nusmv_keywords() -> List[str]:
    fname = os.path.join(ROOT_DIR, "dependencies", "nusmvkeywords.json")
    with open(fname) as fp:
        return ast.literal_eval(fp.read())


def read_nusmv_keywords_or_exit() -> List[str]:
    try:
        return read_nusmv_keywords()
    except Exception as e:
        log.error(f"could not read numsv keywords: exception={e}")
        sys.exit()


def find_command(name) -> str:
    """
    find the path to a command, in local dependencies or in the shared execution PATH
    """
    if name in EXECUTABLES:
        cmd = EXECUTABLES[name]
        if cmd.startswith(":"):
            cmd = cmd[1:]
        else:
            cmd = os.path.normpath(os.path.join(ROOT_DIR, "Dependencies", cmd))
    else:
        cmd = name
    return cmd


def dicts_are_consistent(dict1: dict, dict2: dict) -> bool:
    """
    checks if all items whose keys are in (d1 and d2) are equal.
    returns bool.
    """

    return all(dict1[k] == dict2[k] for k in set(dict1).intersection(set(dict2)))


def is_supdict(X, Y):
    """
    checks whether X contains Y, i.e., whether X is a "super-dictionary" of Y.
    returns bool.
    """
    
    return set(X.items()).issuperset(set(Y.items()))


def is_subdict(X, Y):
    """
        checks whether X is contained by Y, i.e., whether X is a "sub-dictionary" of Y.
        returns bool.
        """
    
    return set(X.items()).issubset(set(Y.items()))


def merge_dicts(dicts: List[dict]):
    """
        creates a new dictionary that is updated by all members of *Dict* (shallow copies).
        return newdict.
        """
    
    newdict = {}
    for dic in dicts:
        newdict.update(dic)
    
    return newdict


def remove_d1_from_d2(d1, d2):
    """
        removes all items from d1 that are also in d2 from d2.
        """
    
    d2items = d2.items()
    for x in d1.items():
        if x in d2items:
            d2.pop(x[0])


# auxillary to create graph labels that are as square as possible
# used by e.g. stg2sccgraph / stg2condensationgraph / basin diagram
def divide_list_into_similar_length_lists(List):
    """
        used for drawing pretty labels.
        """
    
    width = sum(len(x) for x in List)
    width = math.sqrt(width)
    
    stack = list(List)
    lists = []
    remaining = sum(map(len, stack))
    while remaining > width:
        new = stack.pop(0)
        size = len(new)
        line = [new]
        while size < width:
            new = stack.pop(0)
            size += len(new)
            line += [new]
        lists.append(line)
        remaining = sum(map(len, stack))
    if stack:
        lists.append(stack)
    
    return lists


def perc2str(Perc):
    """
    converts a number into a nice string.
    Used for plotting the labels of quotient graphs, e.g. Commitment.diagram2image(..)
    """
    
    res = "%.1f " % Perc
    i, d = res.split('.')
    remove = d[-1] == "0"
    while remove:
        if len(d) > 1:
            d = d[: -1]
            remove = d[-1] == " 0"
        else:
            d = ""
            remove = False
    
    if d:
        return i + '.' + d
    return i


def save_json_data(data: dict, fname: str):
    """
    saves a dictionary of data using json package

    todo: add unit tests
    """
    
    with open(fname, "w") as f:
        json.dump(obj=data, fp=f, indent=4)
    
    log.info(f"created {fname}")


def open_json_data(fname: str) -> dict:
    """
    opens a dictionary of data using json package
    """
    
    with open(fname, "r") as f:
        data = json.load(fp=f)
    
    return data


def copy_json_data(Data):
    """
        todo: finish code
        todo: add unit tests

        creates a copy of a json data structure by conversion to string and back.

        **arguments**:
                * *Data* (json): json data

        **returns**:
                * *DataCopy* (json): a copy of *Data*

        **example**::

                >>> data = Attractors.compute_attractor_json(primes, update)
                >>> data2 = copy_json_data(data)
        """
    
    return json.loads(json.dumps(Data))
