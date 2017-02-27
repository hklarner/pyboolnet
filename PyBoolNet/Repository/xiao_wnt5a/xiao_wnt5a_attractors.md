

### Attractor Report
 * created on 18. Oct. 2016 using PyBoolNet, see https://github.com/hklarner/PyBoolNet

### Steady States
| steady state |
| ------------ | 
| 0101111      |
| 0110110      |
| 0111110      |
| 1000001      |

### Asynchronous STG
 * completeness: True
 * there are only steady states

### Synchronous STG
 * completeness: True
 * there are only steady states

### Network
| targets | factors                     |
| ------- | --------------------------- |
| x1      | !x6                         |
| x2      | x6 & x4 | x2 & x6 | x2 & x4 |
| x3      | !x7                         |
| x4      | x4                          |
| x5      | !x7 | x2                    |
| x6      | x4 | x3                     |
| x7      | x7 | !x2                    |

