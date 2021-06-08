

### Attractor Report
 * created on 12. Jun. 2017 using PyBoolNet, see https://github.com/hklarner/PyBoolNet

### Steady States
| steady state |
| ------------ | 
| 110001000    |
| 110001010    |
| 110101111    |
| 110111110    |

### Asynchronous STG
 * completeness: True
 * there are only steady states

### Synchronous STG
 * completeness: True
 * there are only steady states

### Network
| AUXINS  | 1                                  |
| ------- | ---------------------------------- |
| SHR     | SHR                                |
| ARF     | !IAA                               |
| IAA     | !AUXINS                            |
| JKD     | SHR&SCR                            |
| MGP     | SHR&!WOX&SCR                       |
| SCR     | SHR&!MGP&SCR | JKD&SHR&SCR         |
| WOX     | SHR&WOX&ARF&SCR | SHR&!MGP&ARF&SCR |
| PLT     | ARF                                |

