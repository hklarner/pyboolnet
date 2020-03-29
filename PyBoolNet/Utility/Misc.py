

import os

try:
    # Python 2.x
    import ConfigParser as configparser

except ImportError:
    # Python 3.x
    import configparser

myconfigparser = configparser

import math
import json

COLOR_MAP = {"red1": "#df3e47", "green1": "#4bb93f", "blue1": "#7463b3", "yellow1": "#eecf1a", "pink1": "#db42a6", "green2": "#4cbd38", "red2": "#df3d47", "yellow2": "#efce1a"}
COLORS = ["dodgerblue3", "firebrick2", "chartreuse3", "gold1", "aquamarine2", "darkorchid2"]
UPDATES = ["synchronous", "asynchronous", "mixed"]
GRAPHVIZ_ENGINES = ["dot", "neato", "fdp", "sfdp", "circo", "twopi"]


def os_is_windows() -> bool:
    return os.name == 'nt'


def dicts_are_consistent(d1: dict, d2: dict) -> bool:
    """
    checks if all items whose keys are in (d1 and d2) are equal.
    returns bool.
    """
    
    return all(d1[k] == d2[k] for k in set(d1).intersection(set(d2)))


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


def merge_dicts(Dicts):
    """
        creates a new dictionary that is updated by all members of *Dict* (shallow copies).
        return newdict.
        """
    
    newdict = {}
    for dic in Dicts:
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


def save_json_data(Data, Fname, Silent=False):
    """
    saves a dictionary of data using json package

    todo: add unit tests
    """
    
    with open(Fname, "w") as f:
        json.dump(obj=Data, fp=f, indent=4)
    
    if not Silent:
        print("created {x}".format(x=Fname))


def open_json_data(Fname):
    """
    opens a dictionary of data using json package

    todo: add unit tests
    """
    
    with open(Fname, "r") as f:
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

                >>> data = Attractors.compute_json(primes, update)
                >>> data2 = copy_json_data(data)
        """
    
    return json.loads(json.dumps(Data))
