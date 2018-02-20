

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

For older release notes, see [RELEASENOTES.md](https://github.com/hklarner/PyBoolNet/blob/master/RELEASENOTES.md)
