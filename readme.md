

### About PyBoolNet
PyBoolNet is a Python package for the generation, modification and analysis of Boolean networks.
The current version is available at [PyBoolNet/releases](http://github.com/hklarner/PyBoolNet/releases).

For the manual, a reference and tutorials see the [PyBoolNet manual](http://github.com/hklarner/PyBoolNet/releases).
For questions and suggestions do not hestitate to open issues or contact

 * hannes.klarner@fu-berlin.de (developer)
 * heike.siebert@fu-berlin.de

#### release notes for version 2.0 (August 2016)
- added functions `create_variables`, `create_disjoin_union` to module PIs
- split function `percolate_constants` from module PIs into `percolate_and_keep_constants` and `percolate_and_remove_constants` for clarity
- bugfix in `completeness_iterative` of module AD
- moved function `compute_attractors_tarjan` from module STGs to module AttractorDetection
- split functions `check_primes` and `check_smv` from module MC into three functions each for _counterexamples_, _acceptingstates_ and both of for clarity
- removed feature `add_style_condensationgraph` from module STGs
- bugfix for the computation of the condensation graph
- added the parameter `LayoutEngine` for drawing graphs. Possible engines: `dot,neato,fdp,sfdp,circo` and `twopi`
- added functions for the `sccgraph`, the `condensationgraph` and the `HTG` to module STGs
- now following the git model described in [nvie.com](http://nvie.com/posts/a-successful-git-branching-model/)
- refactored `Utility.py` in `Utility\DiGraphs.py` and `Utility\Misc.py`
- added documentation source to `Docs\Sphinx`
- added `AttractorBasins.py`, a library for visualizing basins of attraction
- added support for model checking with _accepting states_ via [NuSMV-a](https://github.com/hklarner/NuSMV-a)
- added `Repository/`, a folder with pre-defined networks
- added support for Python 2.x _and_ 3.x
- added function `input_combinations` to module `PrimeImplicants`

#### release notes for version 1.0 (February 2016)
- first official release
