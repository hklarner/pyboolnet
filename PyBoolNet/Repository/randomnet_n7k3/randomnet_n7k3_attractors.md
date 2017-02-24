

### Attractor Report
 * created on 18. Oct. 2016 using PyBoolNet, see https://github.com/hklarner/PyBoolNet

### Steady States
| steady state |
| ------------ | 
| 0001100      |
| 0001101      |
| 0001110      |
| 0101100      |
| 0101101      |
| 0101110      |
| 0110000      |
| 0110001      |
| 0110010      |
| 1011011      |

### Asynchronous STG
 * completeness: True
 * there are only steady states

### Synchronous STG
 * completeness: False
 * there are only steady states

### Network
| targets | factors                                                           |
| ------- | ----------------------------------------------------------------- |
| Gene1   | Gene3 & Gene4 & !Gene5 | !Gene4 & Gene5 | !Gene3 & !Gene4         |
| Gene2   | Gene2 & !Gene3 | !Gene1 & Gene2 | Gene1 & !Gene3                  |
| Gene3   | !Gene5 & Gene6 | !Gene1 & !Gene5 | Gene1 & Gene6 | Gene1 & Gene5  |
| Gene4   | !Gene3 & Gene5 | !Gene2 & Gene5 | !Gene2 & Gene3 | Gene2 & !Gene3 |
| Gene5   | !Gene3 & Gene4 | !Gene1 & Gene4 | Gene1 & !Gene3                  |
| Gene6   | !Gene1 & Gene6 & !Gene7 | Gene1 & Gene7 | Gene1 & !Gene6          |
| Gene7   | !Gene3 & Gene5 & Gene7 | Gene3 & !Gene5 & Gene7                   |

