

## About pyboolnet
pyboolnet is a Python package for the generation, modification and analysis of Boolean networks.
The accompanying paper was published with [Bioinformatics](https://academic.oup.com/bioinformatics) and is available at

 * https://doi.org/10.1093/bioinformatics/btw682

For report bugs, request features and give feedback at [issues](http://github.com/hklarner/pyboolnet/issues) or contact

 * hannes.klarner@fu-berlin.de (developer)
 * heike.siebert@fu-berlin.de

## Documentation
The documentation and tutorials are hosted here:

 * [https://pyboolnet.readthedocs.io/](https://pyboolnet.readthedocs.io/)

## Model repository
For examples of attractors, basins and phenotypes, browse the model repository here:

 * [pyboolnet/repository](https://github.com/hklarner/pyboolnet/tree/master/pyboolnet/repository)

## Installation
To install the pyboolnet master branch use:

``` 
pip3 install pip --upgrade
pip3 install git+https://github.com/hklarner/pyboolnet
```

To install a tagged version use the `@`: 

``` 
pip3 install pip --upgrade
pip3 install git+https://github.com/hklarner/pyboolnet@3.0.2
```

For release notes, see

 * [pyboolnet/releasenotes.md](https://github.com/hklarner/pyboolnet/blob/master/RELEASENOTES.md)
 
## Command line tool
```
$ pyboolnet -h
$ pyboolnet --trap-spaces --type min grieco_mapk.bnet
```


## Migration guide
The migration guide for PyBoolNet 2.x to pyboolnet 3.x is here:

 * [pyboolnet/MIGRATION_GUIDE.md](https://github.com/hklarner/pyboolnet/blob/master/MIGRATION_GUIDE.md)


## Contributions
- send pull requests to the `develop` branch
- add tests to `pyboolnet/tests/`

