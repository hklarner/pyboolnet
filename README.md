

## About PyBoolNet
PyBoolNet is a Python package for the generation, modification and analysis of Boolean networks.
The current version is available at [PyBoolNet/releases](http://github.com/hklarner/PyBoolNet/releases).

For the manual, a reference and tutorials see the [PyBoolNet manual](http://github.com/hklarner/PyBoolNet/releases).
For bug reports and feedback do not hesitate to open issues at [PyBoolNet issues](http://github.com/hklarner/PyBoolNet/issues) or contact

 * hannes.klarner@fu-berlin.de (developer)
 * heike.siebert@fu-berlin.de


#### release notes for version
- improved formatting of `primes2bnet(..)` and `primes2mindnf(..)`
- added parameter `Representation` and option `percolated` to parameter `Type` of `trap_spaces(..)`
- implemented tempfile for functions `check_primes(..)`, `check_primes_with_counterexample(..)` and `check_primes_with_acceptingstates(..)` (bugfix for windows)
- bugfix in `subspace2proposition`
- renamed `subspace1_is_in_subspace2(..)` to `A_is_subspace_of_B(..)` for clarity


#### release notes for version 2.11 (February 2017)
- added section `For Developers` to manual
- refactored git repository so that all necessary files for building PyBoolNet are available on github
- added functions `state_is_in_subspace` and `subspace1_is_in_subspace2` to `StateTransitionGraphs`
- made the header _targets, factors_ in `FileExchange.primes2bnet(..)` optional (default without header)
- added argument `Copy` to `create_blinkers(..)`, `create_variables(..)`, `create_disjoint_union(..)`, `rename(..)`, `remove_variables(..)` and `remove_all_variables_except(..)` of module `PrimeImplicants`


#### release notes for version 2.1 (September 2016)
- support for windows and macos
- refactored `subspace2states` as `list_states_in_subspace` and `proposition2states` as `list_states_referenced_by_proposition`
- refactored function for state and subspace conversions to `state2str`, `state2dict`, `subspace2str`, `subspace2dict` and added basic asserts 
- added functions `univocality_with_counterexample`, `faithfulness_with_counterexample` and `completeness_with_counterexample`
- refactored the functions `univocal`, `faithful` and `completeness_iterative` to two `univocality`, `faithfulness` and `completeness`
- removed function `completeness_naive` from AD since it is always less efficient than `completeness_iterative`
- renamed module `TemporalQueries` to `QueryPatterns` for clarity
- bugfix absolute import for Python 3.x


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



