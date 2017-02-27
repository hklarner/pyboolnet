

### Attractor Report
 * created on 18. Oct. 2016 using PyBoolNet, see https://github.com/hklarner/PyBoolNet

### Steady States
| steady state |
| ------------ | 
| 0000001011   |

### Asynchronous STG
 * completeness: True

| trapspace      | univocal  | faithful  |
| -------------- | --------- | --------- |
| ---1--0--0     | True      | True      |

### Synchronous STG
 * completeness: True

| trapspace      | univocal  | faithful  |
| -------------- | --------- | --------- |
| ---1--0--0     | True      | True      |

### Network
| targets | factors                                                                                                                 |
| ------- | ----------------------------------------------------------------------------------------------------------------------- |
| Cdc20   | CycB                                                                                                                    |
| CycA    | !cdh1 & E2F & !Rb & !Cdc20 | !UbcH10 & E2F & !Rb & !Cdc20 | !cdh1 & CycA & !Rb & !Cdc20 | !UbcH10 & CycA & !Rb & !Cdc20 |
| CycB    | !cdh1 & !Cdc20                                                                                                          |
| CycD    | CycD                                                                                                                    |
| CycE    | E2F & !Rb                                                                                                               |
| E2F     | p27 & !Rb & !CycB | !CycA & !Rb & !CycB                                                                                 |
| Rb      | !CycE & !CycD & !CycA & !CycB | !CycD & p27 & !CycB                                                                     |
| UbcH10  | UbcH10 & CycB | UbcH10 & CycA | UbcH10 & Cdc20 | !cdh1                                                                  |
| cdh1    | p27 & !CycB | !CycA & !CycB | Cdc20                                                                                     |
| p27     | !CycE & !CycD & p27 & !CycB | !CycD & p27 & !CycA & !CycB | !CycE & !CycD & !CycA & !CycB                               |

