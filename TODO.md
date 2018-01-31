
### Release notes

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


### Source

- add safety feature to compute_attrs_obj and save_attrs_obj (a function "raise exception if fname exists")

- add function Repository.get_attr_obj(Name, Update)

- update Repository/jobs.py to use attractor objects

- refactor Utility -> Helpers and Misc -> ??

- refactor Representation="dict" -> Format="dict"

- refactor unit tests per module and add missing tests

- run with Python3, Windows and MacOS

- add controlled vocabulary to each module, docstrings, parameters and the documentation. See section below

- patch code to work with networkx >= 1.10 and 2.X, see the [migration guide](https://networkx.github.io/documentation/stable/release/migration_guide_from_1.x_to_2.0.html)

- In Commitment.compute_diagram(..) improve treatment of phenotype nodes that appear in outdag.
Remove all nodes from outdag that are above phenotype nodes.

- Create module PyBoolNet.Utility.Latex for Latex exports

- Create module PyBoolNet.Utility.Html for Html exports


### Documentation
- replace "2.1 Importing Boolean Networks" with "Creating Boolean networks", "Modifying Boolean Networks"

- add 2.1.6: Multi-Valued Variables


### Controlled Vocabulary
- **primes**:
- **igraph**:
- **successors**:
- **predeccessors**:
- **node(s)**: a node of the interaction graph $v\in V$. instead of "variable" and "component" and "Names"
- **stg**:
- **state(s)**:


### Controlled Docstrings
* *Silent* (bool): print infos to screen
* *Primes*: prime implicants




















end
