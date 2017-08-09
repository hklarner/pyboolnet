

## About PyBoolNet
PyBoolNet is a Python package for the generation, modification and analysis of Boolean networks.
The current version is available at [PyBoolNet/releases](http://github.com/hklarner/PyBoolNet/releases).

For the manual, a reference and tutorials see the [PyBoolNet manual](http://github.com/hklarner/PyBoolNet/releases).
For bug reports and feedback do not hesitate to open issues at [PyBoolNet issues](http://github.com/hklarner/PyBoolNet/issues) or contact

 * hannes.klarner@fu-berlin.de (developer)
 * heike.siebert@fu-berlin.de


#### release notes for version 2.2 (August 2017)
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

For older release notes, see [release_note.md](https://github.com/hklarner/PyBoolNet/blob/master/RELEASENOTES.md)





