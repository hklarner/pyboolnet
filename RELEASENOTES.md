
## release notes for next version
 - bugfix in `input_combinations` of `PrimeImplicants`, typo: `primes` -> `Primes` (by @leonardogian)
 - modified `primes2stg` to return empty stg if primes are empty (by @nanls)
 - support for drawing multi-digraphs in `digraph2image`(by @nanls)


## release notes for version 2.2.9 (September 2020)
- adds Conda recipe [PR](https://github.com/hklarner/PyBoolNet/pull/38)
- support installation from github [PR](https://github.com/hklarner/PyBoolNet/pull/37)
- support for CoLoMoTo image [PR](https://github.com/hklarner/PyBoolNet/pull/35)


## release notes for version 2.2.8 (March 2020)
- bugfix binaries of eqntott for windows
- adds detection of os when calling eqntott 


## release notes for version 2.2.5 (June 2018)
- bugfix in create_piechart, affects python3
- bugfix in Commitment.create_diagram caused by moving to networkx2
- bugifx in Basins.create_barplot caused by range, affects python3
- bugfix in ModelChecking.primes2smv for van ham init constraints, caused by zip, affects python3
- bugfix in StateTransitionGraphs.random_walk
- bugfix in StateTransitionGraphs.create_image: adding styles anonymous and mintrapspaces
- bugfix in InteractionGraphs: drawing subgraphs, caused by moving to networkx2


## release notes for version 2.2.4 (February 2018)
- started to refactor the unittests (split into several files)
- PyBoolNet is now developed with Python3
- PyBoolNet is now compatible with networkx2
- continued work and tuning on Basins, Commitment and Phenotypes
- fixed encoding of mutli-valued variables in `remy_tumorigenesis.bnet` of the `Repository` (using GINsim)


## release notes for version 2.2.3 (February 2018)
- bugfixes for Python3: encoding / decoding and long / int


#### release notes for version 2.2.2 (February 2018)
- **new Module** `Commitment` for the computation of commitment diagrams
- **new Module** `Phenotypes` for the computation of phenotype diagrams
- **bugfix** of encoding of mutli-valued variables in `remy_tumorigenesis.bnet` of the `Repository`
- added function `Attractors.open_json(..)` to module `Attractors`
- added function `Attractors.save_json(..)` to module `Attractors`
- added function `Attractors.compute_json(..)` to module `Attractors`
- the PyBoolNet git repository is now in "hard tab" format (tab instead of whitespace)
- **refactored** `list_states_referenced_by_proposition(..)` as `enumerate_states(..)` for simplicity
- **refactored** the module `AttractorDetection` as `Attractors` for simplicity
- **refactored** the module `QueryPatterns` as `TemporalLogic` for clarity
- **refactored** the module `BooleanExpressions` as `BooleanLogic` for clarity
- adapted modules `Basins` and `ModelChecking` to handle Boolean variables that represent multi-valued variables (see van Ham encoding)
- added `StateTransitionGraphs.size_state_space` to determine size of state spaces, taking into account only the admissible states of Boolean variables that represent multi-valued variables (see van Ham encoding)
- added `StateTransitionGraphs.find_vanham_variables(..)` to detect variables that represent ternary variables


#### release notes for hotfix version 2.2.1 (January 2018)
- **bugfix**: removed slowdown that was introduced by unnecessarily computing counterexamples in `AttractorDetection.completeness(..)`, `AttractorDetection.univocality(..)` and `AttractorDetection.faithfulness(..)`


#### release notes for version 2.2.0 (November 2017)
- bugfix for linux dependencies, see [Issue17](https://github.com/hklarner/PyBoolNet/issues/17)
- removed support for linux 32 bit
- added module `BooleanExpressions` with `minimize_espresso(..)` (work by Sarah Nee)
- bugfix for `Utility.Diagraphs.subgraphs2tree(..)` that affected `StateTransitionGraphs.add_style_subspaces(..)`
- added functions `weak_basins(..)` `strong_basins(..)` with bar plot and pie chart visualizations to `Basins`. Plotting requires [matplotlib](https://matplotlib.org/).
- added `add_style_anonymous(..)` to `InteractionGraphs` which hides node labels
- added some toy networks to the `Repository`
- renamed module `TrapSpaces` to `AspSolver`
- renamed module `AttractorBasins` to `Basins`
- added energy function `energy(..)` to `StateTransitionGraphs`
- added pretty print function `pprint(..)` to `PyBoolNet`
- bugfix in NuSMV-a for dynamic reordering (currently compiled only in 32bit)
- bugfix in NuSMV-a for large numbers (currently compiled only in 32bit)
- removed parameter `Aggregate` from `TrapSpaces.trap_spaces(..)` and similar functions as it is rarely useful
- added warning for accepting states bug (see issue [#14](http://github.com/hklarner/PyBoolNet/issues/14))
- added T-Helper cell plasticity model of Wassim Abou-Jaoudé
- improved formatting of `primes2bnet(..)` and `primes2mindnf(..)`
- added parameter `Representation` and option `percolated` to parameter `Type` of `trap_spaces(..)`
- implemented tempfile for functions `check_primes(..)`, `check_primes_with_counterexample(..)` and `check_primes_with_acceptingstates(..)` (bugfix for windows)
- bugfix in `subspace2proposition`
- renamed `subspace1_is_in_subspace2(..)` to `A_is_subspace_of_B(..)` for clarity


#### release notes for version 2.1.1 (February 2017)
- added section `For Developers` to manual
- refactored git repository so that all necessary files for building PyBoolNet are available on github
- added functions `state_is_in_subspace` and `subspace1_is_in_subspace2` to `StateTransitionGraphs`
- made the header _targets, factors_ in `FileExchange.primes2bnet(..)` optional (default without header)
- added argument `Copy` to `create_blinkers(..)`, `create_variables(..)`, `create_disjoint_union(..)`, `rename(..)`, `remove_variables(..)` and `remove_all_variables_except(..)` of module `PrimeImplicants`


#### release notes for version 2.1 (September 2016)
- support for windows and macos
- refactored `subspace2states` as `list_states_in_subspace` and `proposition2states` as `enumerate_states`
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
