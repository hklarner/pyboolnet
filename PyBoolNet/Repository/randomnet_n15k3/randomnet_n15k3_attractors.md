

### Attractor Report
 * created on 18. Oct. 2016 using PyBoolNet, see https://github.com/hklarner/PyBoolNet

### Steady States
| steady state    |
| --------------- | 
| 001010101110101 |
| 011110111011001 |
| 101111101110011 |

### Asynchronous STG
 * completeness: True
 * there are only steady states

### Synchronous STG
 * completeness: True
 * there are only steady states

### Network
| targets | factors                                                                                                 |
| ------- | ------------------------------------------------------------------------------------------------------- |
| Gene1   | !Gene12 & !Gene3 | Gene8                                                                                |
| Gene10  | !Gene1 & Gene10 & Gene3 | !Gene10 & !Gene3 | Gene1 & !Gene3                                             |
| Gene11  | !Gene14 | Gene13 | Gene12                                                                               |
| Gene12  | Gene8 & Gene4 | Gene8 & Gene3 | Gene3 & !Gene4                                                          |
| Gene13  | !Gene2 & !Gene11 & Gene6 | Gene2 & !Gene11 & !Gene6 | !Gene2 & Gene11 & !Gene6 | Gene2 & Gene11 & Gene6 |
| Gene14  | Gene8 & Gene9 | !Gene9 & !Gene5 | Gene8 & !Gene5                                                        |
| Gene15  | !Gene8 & Gene9 | Gene8 & !Gene9 | Gene9 & !Gene2 | Gene8 & !Gene2                                       |
| Gene2   | !Gene4 & !Gene14 | !Gene12 & !Gene4                                                                     |
| Gene3   | !Gene3 & Gene6 | Gene5                                                                                  |
| Gene4   | !Gene4 & !Gene6 | !Gene3 & !Gene4 | Gene3 & !Gene6                                                      |
| Gene5   | Gene6 & !Gene14 | !Gene6 & Gene14 | Gene9                                                               |
| Gene6   | !Gene8 & Gene10 | Gene10 & Gene14                                                                       |
| Gene7   | !Gene12 & Gene13 & !Gene10 | Gene12 & !Gene13 & !Gene10 | !Gene12 & !Gene13 & Gene10                    |
| Gene8   | !Gene8 & !Gene13 & Gene9 | !Gene8 & Gene13 & !Gene9 | Gene8 & Gene13 & Gene9                            |
| Gene9   | Gene7 | Gene12 | Gene11                                                                                 |

