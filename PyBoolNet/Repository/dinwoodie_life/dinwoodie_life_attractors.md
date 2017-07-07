

### Attractor Report
 * created on 12. Jun. 2017 using PyBoolNet, see https://github.com/hklarner/PyBoolNet

### Steady States
| steady state    |
| --------------- | 
| 001000000110010 |
| 001000010111010 |
| 001000100000010 |
| 001110000000010 |
| 001110000110010 |
| 001110010111010 |
| 010110010111000 |

### Asynchronous STG
 * completeness: True
 * there are only steady states

### Synchronous STG
 * completeness: False
 * there are only steady states

### Network
| compuse      | wssigma&!mci                                        |
| ------------ | --------------------------------------------------- |
| mci          | !wsq3&!compuse&waso | sleeplivroom&!compuse&!wsq3   |
| meanws       | wssigma&wsq3 | !wscv&wsq3                           |
| numfir       | !wsq3 | sleeplivroom | numtrans                     |
| numtrans     | numfir                                              |
| numwalks     | !wscv&wssigma                                       |
| sleeplatency | ttib&waso                                           |
| sleeplivroom | timeasleep&!ttib                                    |
| timeasleep   | ttib                                                |
| ttib         | timeasleep                                          |
| waso         | sleeplatency&ttib                                   |
| wscv         | wssigma&!meanws | wssigma&mci                       |
| wsq3         | !numwalks&!mci | meanws                             |
| wssigma      | wscv&meanws                                         |
| oohhours     | sleeplivroom&!ttib | numwalks&!ttib | !numfir&!ttib |

