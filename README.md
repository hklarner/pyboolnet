

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
sudo pip3 install PyBoolNet-2.2.5_linux64.tar.gz
```


## release notes for version 2.2.5 (June 2018)
- bugfix in create_piechart, affects python3
- bugfix in Commitment.create_diagram caused by moving to networkx2
- bugifx in Basins.create_barplot caused by range, affects python3
- bugfix in ModelChecking.primes2smv for van ham init constraints, caused by zip, affects python3
- bugfix in StateTransitionGraphs.random_walk
- bugfix in StateTransitionGraphs.create_image: adding styles anonymous and mintrapspaces
- bugfix in InteractionGraphs: drawing subgraphs, caused by moving to networkx2


For older release notes, see [RELEASENOTES.md](https://github.com/hklarner/PyBoolNet/blob/master/RELEASENOTES.md)
