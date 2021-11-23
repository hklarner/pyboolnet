

import logging
import sys
from typing import Union, Optional

import pyboolnet.state_space
import pyboolnet.state_space
from pyboolnet import find_command
from pyboolnet.boolean_logic import minimize_espresso
from pyboolnet.model_checking import model_checking
from pyboolnet.model_checking import subspace2proposition
from pyboolnet.state_space import size_state_space

CMD_DOT = find_command("dot")
BASIN_COLORS = ["#efedf5", "#bcbddc", "#756bb1"]
PIE_COLORS = ["#a6cee3", "#1f78b4", "#b2df8a", "#33a02c", "#fb9a99", "#e31a1c", "#fdbf6f", "#ff7f00", "#cab2d6", "#6a3d9a" "#ffff99"]

log = logging.getLogger(__name__)

try:
    import matplotlib.pyplot
except ImportError:
    log.warning(f"failed to import matplotlib: try to run 'pip3 install matplotlib>=3.3.3'.")


def weak_basin(primes: dict, update: str, subspace: Union[dict, str] = {}, minimize: bool = False):
    """
    Computes the weak basin of *subspace* via the CTL query AG(EF(Subspace)), for details see :ref:`Klarner2018 <klarner2018>`.

      **arguments**:
        * *primes*: prime implicants
        * *update*: the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
        * *minimize*: minimize the Boolean expressions
        * *subspace*: a subspace

      **returns**:
        * *basin*: with keys "size"=number of states, "formula"=state formula and "perc"=percentage of state space

      **example**::

        >>> weak_basin(primes, update, "0---1", True)
        {"size": 134,
        "formula": "Erk & !Raf | Mek",
        "perc": 12.89338}
    """

    return _basin_handle(primes=primes, update=update, subspace=subspace, minimize=minimize, ctl_pattern="CTLSPEC EF({x})")


def strong_basin(primes, update, subspace: Union[dict, str] = {}, minimize: bool = False):
    """
    Computes the strong basin of *subspace* via the CTL query AG(EF(Subspace)), for details see :ref:`Klarner2018 <klarner2018>`.

      **arguments**:
        * *primes*: prime implicants
        * *update*:  the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
        * *minimize*: minimize the Boolean expressions
        * *subspace*: a subspace

      **returns**:
        * *basin*: with keys "size"=number of states, "formula"=state formula and "perc"=percentage of state space

      **example**::

        >>> strong_basin(primes, update, True, "0---1")
        {"size":    134,
        "formula":    "Erk & !Raf | Mek",
        "perc":        12.89338}
    """

    return _basin_handle(primes, update, subspace, minimize, ctl_pattern="CTLSPEC AG(EF({x}))")


def cycle_free_basin(primes: dict, update: str, subspace: Union[dict, str] = {}, minimize: bool = False):
    """
    Computes the cycle-free basin of *subspace* via the CTL query AG(EF(Subspace)), for details see :ref:`Klarner2018 <klarner2018>`.

        **arguments**:
        * *primes*: prime implicants
        * *update*:  the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
        * *minimize*: minimize the Boolean expressions
        * *subspace*: a subspace
        
        **returns**:
        * *basin*: with keys "size"=number of states, "formula"=state formula and "perc"=percentage of state space
        
        **example**::

        >>> cycle_free_basin(primes, update, True, "0---1")
            {"size": 134,
            "formula": "Erk & !Raf | Mek",
            "perc": 12.89338}
    """

    return _basin_handle(primes, update, subspace, minimize, ctl_pattern="CTLSPEC AF({x})")


def compute_basins(attractors: dict, weak: bool = True, strong: bool = True, cycle_free: bool = True, fname_barplot: Optional[str] = None, fname_piechart: Optional[str] = None, minimize: bool = False) -> Optional[dict]:
    """
    Extends *attractors* with basin of attraction.
    Use *fname_barplot* and *FnamePiechart* to create plots of the basins, see :ref:`create_barplot` and :ref:`basins_create_piechart`.

    **arguments**:
        * *attractors*: json attractor data, see :ref:`attractors_compute_json`
        * *weak*: compute weak basins
        * *strong*: compute strong basins
        * *cycle_free*: compute cycle-free basins
        * *fname_barplot*: file name of bar plot
        * *fname_piechart*: file name of pie chart
        * *minimize*: minimize the Boolean expressions

    **example**::

        >>> primes = get_primes("raf")
        >>> attractors = compute_attractors(primes, update)
        >>> compute_basins(attractors)
    """

    primes = attractors["primes"]
    update = attractors["update"]

    if not any([weak, strong, cycle_free]):
        log.info("nothing to do. you should enable at least one of the parameters Weak, Strong, CycleFree.")
        return

    n = len(attractors["attractors"])
    for i, x in enumerate(attractors["attractors"]):
        log.info(f"working on attractor {i+1}/{n}: {x['state']['str']}")

        if weak:
            log.info("  weak_basin(..)")
            if n == 1:
                x["weak_basin"] = _default_basin(primes)
            else:
                x["weak_basin"] = weak_basin(primes, update, subspace=x["min_trap_space"]["dict"], minimize=minimize)

        if strong:
            log.info("  strong_basin(..)")
            if n == 1:
                x["strong_basin"] = _default_basin(primes)

            else:
                x["strong_basin"] = strong_basin(primes, update, subspace=x["min_trap_space"]["dict"], minimize=minimize)

        if cycle_free:
            log.info("cycle_free_basin(..)")
            x["cycle_free_basin"] = cycle_free_basin(primes, update, subspace=x["min_trap_space"]["dict"], minimize=minimize)

    if fname_barplot:
        create_basins_of_attraction_barplot(attractors, fname_barplot)

    if fname_piechart:
        create_basins_piechart(attractors, fname_piechart)


def create_basins_of_attraction_barplot(attractors: dict, fname_image: str, title: str = None, y_unit: Optional[str] = "perc", y_max: Optional[str] = None, labels_map: Optional[callable] = None):
    """
    Creates a bar plot of the basins of attraction specified in *attractors*.
    Requires that *attractors* has been extended with basins information by :ref:`compute_basins`.
    Requires https://matplotlib.org.

    **arguments**:
        * *attractors*: json attractor data, see :ref:`attractors_compute_json`
        * *fname_image*: create image for bar plot
        * *title*: optional title of plot
        * *Yunit*: "perc" for percentage of state space and "size" for number of states
        * *Ymax*: y axis limit
        * *LabelsMap* (function): a map from minimal trap space dictionary of attractor to label str

    **example**::

        >>> attractors = compute_attractors(primes, update)
        >>> compute_basins(attractors)
        >>> create_basins_of_attraction_barplot(attractors, "barplot.pdf")
        created barplot.pdf
    """

    import matplotlib.pyplot

    attractors_tuple = attractors["attractors"]
    primes = attractors["primes"]

    basins_available = all(basin in x for basin in ["weak_basin", "strong_basin", "cycle_free_basin"] for x in attractors_tuple)
    if not basins_available:
        log.error(f"attractors object does not have basin attributes: use compute_basins to add basins attributes.")
        sys.exit()

    if y_unit not in ["perc", "size"]:
        log.error(f"value error for y_unit: y_unit={y_unit}, admissible_values=['perc', 'size']")
        sys.exit()

    total = pyboolnet.state_space.size_state_space(primes)
    indices = list(range(len(attractors_tuple)))
    indices.sort(key=lambda i: attractors_tuple[i]["weak_basin"]["perc"], reverse=True)

    y1 = [attractors_tuple[i]["cycle_free_basin"][y_unit] for i in indices]
    y2 = [attractors_tuple[i]["strong_basin"][y_unit] - attractors_tuple[i]["cycle_free_basin"][y_unit] for i in indices]
    y3 = [attractors_tuple[i]["weak_basin"][y_unit] - attractors_tuple[i]["strong_basin"][y_unit] for i in indices]

    n = len(y1)
    x = list(range(n))
    width = 1 / 1.5

    if not labels_map:
        labels = [attractors_tuple[i]["min_trap_space"]["str"] for i in indices]
    else:
        labels = [labels_map(attractors_tuple[i]["min_trap_space"]["dict"]) for i in indices]

    figure = matplotlib.pyplot.figure()
    h3 = matplotlib.pyplot.bar(x, y1, width, color=BASIN_COLORS[2], align="center", label="cycle-free basin")
    h2 = matplotlib.pyplot.bar(x, y2, width, bottom=y1, color=BASIN_COLORS[1], align="center", label="strong basin")
    h1 = matplotlib.pyplot.bar(x, y3, width, bottom=[sum(x) for x in zip(y1, y2)], color=BASIN_COLORS[0], align="center", label="weak basin")
    matplotlib.pyplot.xticks(range(len(labels)), labels, rotation=40, ha="right")

    if not y_max:
        y_max = total if y_unit == "size" else 100

    y_lim = (0, y_max)
    matplotlib.pyplot.ylim(y_lim)

    matplotlib.pyplot.legend(handles=[h1, h2, h3], loc="upper right")

    if not title:
        title = "Basins of Attraction"

    matplotlib.pyplot.title(title, y=1.08)

    y_label = "number of states" if y_unit == "size" else "percent of state space"
    matplotlib.pyplot.ylabel(y_label)
    matplotlib.pyplot.xlabel("attractors")
    matplotlib.pyplot.tight_layout()

    figure.savefig(fname_image, bbox_inches="tight")
    matplotlib.pyplot.close(figure)

    log.info(f"created {fname_image}")


def create_basins_piechart(attractors: dict, fname_image: str, title: Optional[str] = None, y_unit: Optional[str] = "perc", labels_map: Optional[callable] = None):
    """
    Creates a pie chart of the basins of attraction specified in *attractors*.
    Requires that *attractors* has been extended with basins information by :ref:`compute_basins`.
    Requires https://matplotlib.org.

    **arguments**:
        * *attractors*: json attractor data, see :ref:`attractors_compute_json`
        * *fname_image*: create image for pie chart
        * *title*: optional title of plot
        * *y_unit*: "perc" for percentage of state space and "size" for number of states
        * *labels_map*: a map from minimal trap space dictionary of attractor to label str

    **example**::

        >>> attractors = compute_attractors(primes, update)
        >>> compute_basins(attractors)
        >>> create_basins_piechart(attractors, "piechart.pdf")
        created piechart.pdf
    """

    primes = attractors["primes"]
    attractors = attractors["attractors"]

    assert all(basin in x for basin in ["weak_basin", "strong_basin", "cycle_free_basin"] for x in attractors)
    assert y_unit in ["perc", "size"]

    total = pyboolnet.state_space.size_state_space(primes)
    strong = sum(x["strong_basin"]["size"] for x in attractors)
    outside = total - strong

    indices = list(range(len(attractors)))
    indices.sort(key=lambda i: attractors[i]["strong_basin"]["perc"], reverse=True)

    figure = matplotlib.pyplot.figure()
    sizes = [attractors[i]["strong_basin"]["size"] for i in indices] + [outside]

    if len(attractors) <= 9:
        colors = [PIE_COLORS[i] for i,x in enumerate(attractors)]
    else:
        colors = [matplotlib.pyplot.cm.rainbow(1.*x/(len(indices)+1)) for x in range(len(indices)+2)][1:-1]

    colors.append(BASIN_COLORS[0])  # for slice that represents "outside" states

    explode = [0.0] * len(indices) + [.08]

    if not labels_map:
        labels = [attractors[i]["min_trap_space"]["str"] for i in indices] + [""]
    else:
        labels = [labels_map(attractors[i]["min_trap_space"]["dict"]) for i in indices] + [""]

    auto_percent = (lambda p: '{:.0f}'.format(p * total / 100)) if y_unit == "size" else "%1.1f%%"
    stuff = matplotlib.pyplot.pie(sizes, explode=explode, labels=labels, colors=colors, autopct=auto_percent, shadow=True, startangle=140)
    patches = stuff[0]

    for i, patch in enumerate(patches):
        patch.set_ec("black")

    matplotlib.pyplot.axis("equal")

    if not title:
        title = "Strong Basins of Attraction"

    matplotlib.pyplot.title(title, y=1.08)
    matplotlib.pyplot.tight_layout()
    figure.savefig(fname_image, bbox_inches="tight")
    matplotlib.pyplot.close(figure)

    log.info(f"created {fname_image}")


def _basin_handle(primes: dict, update: str, subspace: Union[dict, str], minimize: bool, ctl_pattern: str) -> dict:
    """
    The handle for :ref:`weak_basin`, :ref:`strong_basin` and :ref:`cycle_free_basin`.

        **arguments**:
        * *primes*: prime implicants
        * *update*:  the update strategy, one of *"asynchronous"*, *"synchronous"*, *"mixed"*
        * *minimize*: minimize the Boolean expressions
        * *subspace*: a subspace
        * *CTLpattern*:

        **returns**:
        * *basin*: with keys "size"=number of states, "formula"=state formula and "perc"=percentage of state space

        **example**::

            >>> _basin_handle(primes, update, True, "0---1", "CTLSPEC EF({x})")
            {"size":134,
            "formula": "Erk & !Raf | Mek",
            "perc": 12.89338}
    """

    prop = subspace2proposition(primes, subspace)
    init = "INIT TRUE"
    spec = ctl_pattern.format(x=prop)
    answer, accepting_states = model_checking(primes, update, init, spec, enable_accepting_states=True)

    size = accepting_states["INITACCEPTING_SIZE"]
    formula = accepting_states["INITACCEPTING"]

    if minimize and formula not in ["TRUE", "FALSE"]:
        formula = minimize_espresso(formula)

    size_total = size_state_space(primes)

    return {"size": size,
            "formula": formula,
            "perc": 100. * size / size_total}


def _default_basin(primes: dict) -> dict:
    """
    <description>

      **arguments**:
        * *primes*: prime implicants

      **returns**:
        * *<arg>* (<type>): <description>

      **example**::

        >>> (..)
        <result>
    """

    size_total = pyboolnet.state_space.size_state_space(primes)

    return {"size": size_total,
            "formula": "TRUE",
            "perc": 100.}

