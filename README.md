

### About PyBoolNet
PyBoolNet is a Python package for the generation, modification and analysis of Boolean networks.
The current version is available at [PyBoolNet/releases](http://github.com/hklarner/PyBoolNet/releases).

For the manual, a reference and tutorials see the [PyBoolNet manual](http://github.com/hklarner/PyBoolNet/releases).
For bug reports and feedback do not hesitate to open issues at [PyBoolNet issues](http://github.com/hklarner/PyBoolNet/issues) or contact

 * hannes.klarner@fu-berlin.de (developer)
 * heike.siebert@fu-berlin.de


#### release notes for version 2.2 (...)
- added functions `state_is_in_subspace` and `subspace1_is_in_subspace2` to `StateTransitionGraphs`
- made the header _targets, factors_ in `FileExchange.primes2bnet(..)` optional (default without header)
- added argument `Copy` to `create_blinkers(..)`, `create_variables(..)`, `create_disjoint_union(..)`, `rename(..)`, `remove_variables(..)` and `remove_all_variables_except(..)` of module `PrimeImplicants`

#### release notes for version 2.11 (February 2017)
- refactored git repository so that all necessary files for building PyBoolNet are available at github

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



### How to Clone, Develop and Release
### How to clone
You need to follow two branches: _master_ and _develop_.
To clone from github run `git clone git@github.com:hklarner/PyBoolNet.git`.
To get the development branch run `git checkout -b develop origin/develop`.


### How to develop
To develop you need to copy the dependencies that fit your system from `./Dependencies` into `./PyBoolNet/Dependencies`.
For example:
   $ cp -a Dependencies/linux32/. PyBoolNet/Dependencies

To test your local version of PyBoolNet either make a realse and install it.
Or add the path to your local version before importing PyBoolNet.
Assume you cloned into `/home/github/PyBoolNet`.
Use:
   import sys
   sys.path.insert(0,'/home/github/PyBoolNet/PyBoolNet')
   import PyBoolNet


### How to make a release
Update all references to the current version in:
   - ./Docs/Sphinx/source/conf.py
   - ./Docs/Sphinx/source/Substitutions.rst
   - ./Docs/Sphinx/source/Installation.rst
   - ./setup.py
   - ./PyBoolNet/__init__.version()
   - ./make_release.sh $VERSION

You should be on branch "develop".
Make final commits:
   $ git commit -a -m "last commit"
   $ git push

Merge with master:
   $ git checkout master
   $ git merge --no-ff develop
   
Add correct tag:
   $ git tag -a v3.0
 
Create Python packages:
   $ ./make_release
   
Packages will be created inside `./dist` 
   
Continue with branch develop:
   $ git checkout develop
