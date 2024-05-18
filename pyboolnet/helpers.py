

import ast
import configparser
import json
import logging
import math
import os
from typing import List


ROOT_DIR = os.path.join(os.path.dirname(__file__))


log = logging.getLogger(__name__)


def read_txt_version() -> str:
    with open(os.path.join(ROOT_DIR, "version.txt"), "r") as fp:
        return fp.read()


def read_executables() -> dict:
    config = configparser.SafeConfigParser()
    settings_file = os.path.join(ROOT_DIR, "binaries", "settings.cfg")

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
    return os.name == "nt"


def dicts_are_consistent(dict1: dict, dict2: dict) -> bool:
    """
    checks if all items whose keys are in (d1 and d2) are equal.
    """

    return all(dict1[k] == dict2[k] for k in set(dict1).intersection(set(dict2)))


def dict_contains(this: dict, other: dict) -> bool:
    """
    checks whether *this* dictionary contains the *other* dictionary.
    """

    return set(this.items()).issuperset(set(other.items()))


def dict_is_contained(this, other) -> bool:
    """
    checks whether X is contained by Y, i.e., whether X is a "sub-dictionary" of Y.
    """

    return set(this.items()).issubset(set(other.items()))


def merge_dicts(dicts: List[dict]) -> dict:
    """
    creates a new dictionary that is updated by all members of *dicts*.
    """

    new_dict = {}
    for dic in dicts:
        new_dict.update(dic)

    return new_dict


def remove_d1_from_d2(d1: dict, d2: dict):
    """
    removes all items from d1 that are also in d2 from d2.
    """

    d2items = d2.items()
    for x in d1.items():
        if x in d2items:
            d2.pop(x[0])


def divide_list_into_similar_length_lists(elements: list) -> List[list]:
    """
    used for drawing pretty labels.
    """

    width = sum(len(x) for x in elements)
    width = math.sqrt(width)

    stack = list(elements)
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


def perc2str(perc: float) -> str:
    """
    converts a number into a nice string.
    Used for plotting the labels of quotient graphs, e.g. Commitment.diagram2image(..)
    """

    res = f"{perc:.1f}"
    i, d = res.split(".")
    remove = d[-1] == "0"

    while remove:
        if len(d) > 1:
            d = d[: -1]
            remove = d[-1] == " 0"
        else:
            d = ""
            remove = False

    if d:
        return i + "." + d
    return i


def save_json_data(data: dict, fname: str):
    """
    Saves a dictionary of data using json package.
    """

    with open(fname, "w") as f:
        json.dump(obj=data, fp=f, indent=4)

    log.info(f"created {fname}")


def open_json_data(fname: str) -> dict:
    """
    Opens a dictionary of data using json package.
    """

    with open(fname, "r") as f:
        data = json.load(fp=f)

    return data


def copy_json_data(data: dict) -> dict:
    """
    Creates a copy of a json data structure by conversion to string and back.

    **arguments**:
        * *data*: json data

    **returns**:
        * *data_copy*: a copy of *data*

    **example**::

        >>> data = Attractors.compute_attractors(primes, update)
        >>> data2 = copy_json_data(data)
    """

    return json.loads(json.dumps(data))


def get_env_with_libreadline6_on_ld_library_path() -> dict:
    env = os.environ.copy()

    if "LD_LIBRARY_PATH" not in env:
        env["LD_LIBRARY_PATH"] = ""
    else:
        env["LD_LIBRARY_PATH"] += os.pathsep

    env["LD_LIBRARY_PATH"] += os.path.join(ROOT_DIR, "binaries", "NuSMV-a")

    return env


if __name__ == '__main__':
    x = get_env_with_libreadline6_on_ld_library_path()
    print(x)
