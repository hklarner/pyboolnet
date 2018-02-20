

## About PyBoolNet
PyBoolNet is a Python package for the generation, modification and analysis of Boolean networks.
The accompanying paper was published with [Bioinformatics](https://academic.oup.com/bioinformatics) and is available at

 * https://doi.org/10.1093/bioinformatics/btw682

For the manual, a reference and tutorials see the [PyBoolNet manual](http://github.com/hklarner/PyBoolNet/releases).
For bug reports and feedback do not hesitate to open issues at [PyBoolNet issues](http://github.com/hklarner/PyBoolNet/issues) or contact

 * hannes.klarner@fu-berlin.de (developer)
 * heike.siebert@fu-berlin.de

 Please browse the PyBoolNet [model repository](https://github.com/hklarner/PyBoolNet/tree/master/PyBoolNet/Repository) for attractor, basin and phenotype information of example networks.


## Installation
Do not try to install this git repository directly, see [Issue #16](https://github.com/hklarner/PyBoolNet/issues/16). Instead download the latest release from https://github.com/hklarner/PyBoolNet/releases and use pip to install. For example:

```
sudo pip install PyBoolNet-2.2.2_linux64.tar.gz
```

PyBoolNet does not work with networkx 2.X. You need to install networkx 1.11:

```
sudo pip install networkx==1.11
```


## release notes for version 2.2.3
- bugfixes for Python3: encoding / decoding and long / int

#### release notes for version 2.2.2
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


For older release notes, see [RELEASENOTES.md](https://github.com/hklarner/PyBoolNet/blob/master/RELEASENOTES.md)
