

### Attractor Report
 * created on 12. Jun. 2017 using PyBoolNet, see https://github.com/hklarner/PyBoolNet

### Steady States
| steady state |
| ------------ | 
| 00000        |
| 00010        |
| 11110        |

### Asynchronous STG
 * completeness: True
 * there are only steady states

### Synchronous STG
 * completeness: True
 * there are only steady states

### Network
| v1      | v2&!v3&!v4&v5 | v2&v3&v4&!v5       |
| ------- | ---------------------------------- |
| v2      | v2&v3&v4&!v5                       |
| v3      | v1&!v2&!v4 | v1&v2&v4              |
| v4      | v2&!v3&!v4&v5 | v3&v4&!v5 | !v2&v4 |
| v5      | !v1&v2&v3                          |

