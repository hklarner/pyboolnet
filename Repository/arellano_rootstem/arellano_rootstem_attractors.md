

### Attractor Report
 * created on 18. Oct. 2016 using PyBoolNet, see https://github.com/hklarner/PyBoolNet

### Steady States
| steady state |
| ------------ | 
| 001000000    |
| 001000010    |
| 001110110    |
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
| targets | factors                                        |
| ------- | ---------------------------------------------- |
| ARF     | !IAA                                           |
| AUXINS  | AUXINS                                         |
| IAA     | !AUXINS                                        |
| JKD     | SHR & SCR                                      |
| MGP     | SHR & !WOX & SCR                               |
| PLT     | ARF                                            |
| SCR     | SHR & !MGP & SCR | JKD & SHR & SCR             |
| SHR     | SHR                                            |
| WOX     | SHR & WOX & ARF & SCR | SHR & !MGP & ARF & SCR |

