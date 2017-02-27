

### Attractor Report
 * created on 18. Oct. 2016 using PyBoolNet, see https://github.com/hklarner/PyBoolNet

### Steady States
| steady state |
| ------------ | 
| 0000000010   |
| 0000000011   |
| 0000100000   |
| 0000100001   |
| 0000100010   |
| 0000100011   |
| 1000000010   |
| 1000000011   |
| 1000100000   |
| 1000100001   |
| 1000100010   |
| 1000100011   |

### Asynchronous STG
 * completeness: True
 * there are only steady states

### Synchronous STG
 * completeness: False
 * there are only steady states

### Network
| targets      | factors                                                                                                                                                                                       |
| ------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Cdc25        | Cdc2_Cdc13 & !PP | Cdc25 & !PP | Cdc2_Cdc13 & Cdc25                                                                                                                                           |
| Cdc2_Cdc13   | !Slp1 & !Rum1 & !Ste9                                                                                                                                                                         |
| Cdc2_Cdc13_A | !Slp1 & !Rum1 & Cdc25 & !Ste9 & !Wee1_Mik1                                                                                                                                                    |
| PP           | Slp1                                                                                                                                                                                          |
| Rum1         | !SK & Rum1 & PP & !Cdc2_Cdc13_A | !SK & !Cdc2_Cdc13 & PP & Rum1 | !SK & !Cdc2_Cdc13 & Rum1 & !Cdc2_Cdc13_A | !SK & !Cdc2_Cdc13 & PP & !Cdc2_Cdc13_A | !Cdc2_Cdc13 & PP & Rum1 & !Cdc2_Cdc13_A |
| SK           | Start                                                                                                                                                                                         |
| Slp1         | Cdc2_Cdc13_A                                                                                                                                                                                  |
| Start        | 0                                                                                                                                                                                             |
| Ste9         | !SK & PP & Ste9 & !Cdc2_Cdc13_A | !SK & !Cdc2_Cdc13 & PP & Ste9 | !SK & !Cdc2_Cdc13 & Ste9 & !Cdc2_Cdc13_A | !Cdc2_Cdc13 & PP & Ste9 & !Cdc2_Cdc13_A | !SK & !Cdc2_Cdc13 & PP & !Cdc2_Cdc13_A |
| Wee1_Mik1    | PP & Wee1_Mik1 | !Cdc2_Cdc13 & Wee1_Mik1 | !Cdc2_Cdc13 & PP                                                                                                                                   |

