

### Attractor Report
 * created on 12. Jun. 2017 using PyBoolNet, see https://github.com/hklarner/PyBoolNet

### Steady States
| steady state            |
| ----------------------- | 
| 00010000000000011100010 |
| 00010000000000011110010 |
| 00010000000010011100010 |
| 00010000000010011110010 |
| 00010000010000011100010 |
| 00010000010000011110010 |
| 00010000010010011100010 |
| 00010000010010011110010 |
| 10010000000000011100010 |
| 10010000000000011110010 |
| 10010000000010011100010 |
| 10010000000010011110010 |
| 10010000010000011100010 |
| 10010000010000011110010 |
| 10010000010010011100010 |
| 10010000010010011110010 |

### Asynchronous STG
 * completeness: True

| trapspace               | univocal  | faithful  |
| ----------------------- | --------- | --------- |
| 011------0-10110000-101 | True      | True      |
| 011------0-10110001-101 | True      | True      |
| 011------0-11110000-101 | True      | True      |
| 011------0-11110001-101 | True      | True      |
| 011------1-10110000-101 | True      | True      |
| 011------1-10110001-101 | True      | True      |
| 011------1-11110000-101 | True      | True      |
| 011------1-11110001-101 | True      | True      |
| 111------0-10110000-101 | True      | True      |
| 111------0-10110001-101 | True      | True      |
| 111------0-11110000-101 | True      | True      |
| 111------0-11110001-101 | True      | True      |
| 111------1-10110000-101 | True      | True      |
| 111------1-10110001-101 | True      | True      |
| 111------1-11110000-101 | True      | True      |
| 111------1-11110001-101 | True      | True      |

### Synchronous STG
 * completeness: False

| trapspace               | univocal  | faithful  |
| ----------------------- | --------- | --------- |
| 011------0-10110000-101 | True      | True      |
| 011------0-10110001-101 | True      | True      |
| 011------0-11110000-101 | True      | True      |
| 011------0-11110001-101 | True      | True      |
| 011------1-10110000-101 | True      | True      |
| 011------1-10110001-101 | True      | True      |
| 011------1-11110000-101 | True      | True      |
| 011------1-11110001-101 | True      | True      |
| 111------0-10110000-101 | True      | True      |
| 111------0-10110001-101 | True      | True      |
| 111------0-11110000-101 | True      | True      |
| 111------0-11110001-101 | True      | True      |
| 111------1-10110000-101 | True      | True      |
| 111------1-10110001-101 | True      | True      |
| 111------1-11110000-101 | True      | True      |
| 111------1-11110001-101 | True      | True      |

### Network
| AJUBA           | AJUBA                                                                                                                                                                                                 |
| --------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| GSK3B           | GSK3B                                                                                                                                                                                                 |
| MTCanAct        | MTCanAct                                                                                                                                                                                              |
| STMNCanAct      | STMNCanAct                                                                                                                                                                                            |
| AURKAActive     | NEDD9&!PP1&AJUBA&AURKAPresent | !PP1&AJUBA&AURKAPresent&BORA | NEDD9&AJUBA&!AURKAActive&AURKAPresent | AJUBA&!AURKAActive&BORA&AURKAPresent | !PP1&TPX2&AURKAPresent | TPX2&!AURKAActive&AURKAPresent |
| AURKAPresent    | !PP2A                                                                                                                                                                                                 |
| BORA            | !PLK1&GSK3B | !Cytokinesis                                                                                                                                                                            |
| CDC25B          | PLK1&!Cytokinesis | !Cytokinesis&AURKAActive                                                                                                                                                          |
| CDK1CCNBComplex | !Cytokinesis&hCPEB | !WEE1&!Cytokinesis | CDC25B&!Cytokinesis                                                                                                                                         |
| CentrosomeMat   | !SpindleAssembly&CDK1CCNBComplex                                                                                                                                                                      |
| Cytokinesis     | !CentrosomeMat&SpindleAssembly                                                                                                                                                                        |
| ENSA            | GWL_MASTL                                                                                                                                                                                             |
| GWL_MASTL       | !PP2A&CDK1CCNBComplex                                                                                                                                                                                 |
| MT              | !STMN                                                                                                                                                                                                 |
| NEDD9           | AURKAActive                                                                                                                                                                                           |
| PLK1            | STMNCanAct&!STMN | MT&MTCanAct | AURKAActive                                                                                                                                                          |
| PP1             | !Cytokinesis&!AURKAActive&!CDK1CCNBComplex                                                                                                                                                            |
| PP2A            | PP1&!ENSA                                                                                                                                                                                             |
| STMN            | !AURKAActive                                                                                                                                                                                          |
| SpindleAssembly | CentrosomeMat&!Cytokinesis                                                                                                                                                                            |
| TPX2            | PLK1                                                                                                                                                                                                  |
| WEE1            | !PLK1                                                                                                                                                                                                 |
| hCPEB           | AURKAActive                                                                                                                                                                                           |

