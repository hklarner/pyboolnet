

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
sudo pip3 install PyBoolNet-2.2.4_linux64.tar.gz
```


## release notes for version 2.2.4 (February 2018)
- started to refactor the unittests (split into several files)
- PyBoolNet is now developed with Python3
- PyBoolNet is now compatible with networkx2
- continued work and tuning on Basins, Commitment and Phenotypes
- fixed encoding of mutli-valued variables in `remy_tumorigenesis.bnet` of the `Repository` (using GINsim)



For older release notes, see [RELEASENOTES.md](https://github.com/hklarner/PyBoolNet/blob/master/RELEASENOTES.md)
