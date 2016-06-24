

### About PyBoolNet
PyBoolNet is a Python package for the generation, modification and analysis of Boolean networks.
The current version is available at [PyBoolNet/releases](http://github.com/hklarner/PyBoolNet/releases).

For the manual, a reference and tutorials see the [PyBoolNet manual](http://github.com/hklarner/PyBoolNet/releases).
For questions and suggestions do not hestitate to open issues or contact

 * hannes.klarner@fu-berlin.de (developer)
 * heike.siebert@fu-berlin.de

#### release notes for next version

#### release notes for version 1.1 (June 2016)
- now following the git model described in [nvie.com](http://nvie.com/posts/a-successful-git-branching-model/)
- refactored `Utility.py` in `Utility\DiGraphs.py` and `Utility\Miscellaneous.py`
- added documentation source to `Docs\Sphins`
- added `AttractorBasins.py`, a library for visualizing basins of attraction
- added support for model checking with _accepting states_ via [NuSMV-a](https://github.com/hklarner/NuSMV-a)
- added `ExampleNetworks.py`, a library of pre-defined networks
- added support for Python 2.x _and_ 3.x
- added function "input_combinations(Primes)" to module "PrimeImplicants"
- fixed mistake in documentation of PrimeImplicants.percolate_constants

#### release notes for version 1.0 (Feb. 2016)
- first official release
