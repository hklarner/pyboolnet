

## About PyBoolNet
PyBoolNet is a Python package for the generation, modification and analysis of Boolean networks.
The accompanying paper was published with [Bioinformatics](https://academic.oup.com/bioinformatics) and is available at https://doi.org/10.1093/bioinformatics/btw682
The current version is available at [PyBoolNet/releases](http://github.com/hklarner/PyBoolNet/releases).

For the manual, a reference and tutorials see the [PyBoolNet manual](http://github.com/hklarner/PyBoolNet/releases).
For bug reports and feedback do not hesitate to open issues at [PyBoolNet issues](http://github.com/hklarner/PyBoolNet/issues) or contact

 * hannes.klarner@fu-berlin.de (developer)
 * heike.siebert@fu-berlin.de

 Please browse the PyBoolNet [model repository](https://github.com/hklarner/PyBoolNet/tree/master/PyBoolNet/Repository) for attractor, basin and phenotype information of example networks.

## Installation
Do not try to install this git repository directly, see [Issue #16](https://github.com/hklarner/PyBoolNet/issues/16). Instead download the latest release from https://github.com/hklarner/PyBoolNet/releases and use pip to install. For example:

```
sudo pip install PyBoolNet-2.2.1_linux64.tar.gz
```


#### release notes for hotfix version 2.2.1 (January 2018)
- **bugfix**: removed slowdown that was introduced by unnecessarily computing counterexamples in `AttractorDetection.completeness(..)`, `AttractorDetection.univocality(..)` and `AttractorDetection.faithfulness(..)`


For older release notes, see [RELEASENOTES.md](https://github.com/hklarner/PyBoolNet/blob/master/RELEASENOTES.md)
