

## About PyBoolNet
PyBoolNet is a Python package for the generation, modification and analysis of Boolean networks.
The accompanying paper was published with [Bioinformatics](https://academic.oup.com/bioinformatics) and is available at https://doi.org/10.1093/bioinformatics/btw682
The current version is available at [PyBoolNet/releases](http://github.com/hklarner/PyBoolNet/releases).

For the manual, a reference and tutorials see the [PyBoolNet manual](http://github.com/hklarner/PyBoolNet/releases).
For bug reports and feedback do not hesitate to open issues at [PyBoolNet issues](http://github.com/hklarner/PyBoolNet/issues) or contact

 * hannes.klarner@fu-berlin.de (developer)
 * heike.siebert@fu-berlin.de


#### release notes for version 2.2.1 (December 2017?)
- changed `Basins` functions to not count "meaningless states" of ternary variables
- changed `ModelChecking.primes2smv(..)` to remove "meaningless states" by adding INIT constraints
- added `PrimeImplicants.size_state_space` to count size of state spaces, excluding possibly "meaningless states" of ternary variables
- added `PrimeImplicants.find_ternary_variables(..)` to detect variables that represent ternary variables
- simplified Booleanization of variables that are originally ternary in the repository model `remi_tumorigenesis.bnet`
- bugfix for `commitment_diagram(..)` concerning the removal of nodes during model checking

For older release notes, see [RELEASENOTES.md](https://github.com/hklarner/PyBoolNet/blob/master/RELEASENOTES.md)





