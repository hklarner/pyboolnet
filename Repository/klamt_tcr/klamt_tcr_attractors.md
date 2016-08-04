

### Attractor Report
 * created on 01. Jul. 2016 using PyBoolNet, see https://github.com/hklarner/PyBoolNet

### Steady States
| steady state                             |
| ---------------------------------------- | 
| 0000000000000001000000000000000000011000 |
| 0000000000000001000000001000000000000000 |
| 0010000000000001000000000000000000011000 |
| 0010000000000001000000001000000000000000 |
| 0100000000000001000000001000000000000000 |
| 0100000000100001000000000000000000011100 |
| 0110000000000001000000001000000000000000 |

### Asynchronous STG
 * completeness: True

| trapspace                                | univocal  | faithful  |
| ---------------------------------------- | --------- | --------- |
| -11---------------------------------1--- | True      | True      |

### Synchronous STG
 * completeness: True

| trapspace                                | univocal  | faithful  |
| ---------------------------------------- | --------- | --------- |
| -11---------------------------------1--- | True      | False     |

### Network
| targets | factors                                                     |
| ------- | ----------------------------------------------------------- |
| AP1     | Jun & Fos                                                   |
| CD45    | CD45                                                        |
| CD8     | CD8                                                         |
| CRE     | CREB                                                        |
| CREB    | Rsk                                                         |
| Ca      | IP3                                                         |
| Calcin  | Ca                                                          |
| DAG     | PLCg_a                                                      |
| ERK     | MEK                                                         |
| Fos     | ERK                                                         |
| Fyn     | CD45 & TCRbind | CD45 & LCK                                 |
| Gads    | LAT                                                         |
| Grb2Sos | LAT                                                         |
| IKK     | PKCth                                                       |
| IP3     | PLCg_a                                                      |
| IkB     | !IKK                                                        |
| Itk     | Slp76 & ZAP70                                               |
| JNK     | SEK                                                         |
| Jun     | JNK                                                         |
| LAT     | ZAP70                                                       |
| LCK     | CD45 & CD8 & !PAGCsk                                        |
| MEK     | Raf                                                         |
| NFAT    | Calcin                                                      |
| NFkB    | !IkB                                                        |
| PAGCsk  | !TCRbind                                                    |
| PKCth   | DAG                                                         |
| PLCg_a  | ZAP70 & Slp76 & Rlk & PLCg_b | ZAP70 & Slp76 & Itk & PLCg_b |
| PLCg_b  | LAT                                                         |
| Raf     | Ras                                                         |
| Ras     | RasGRP1 & Grb2Sos                                           |
| RasGRP1 | PKCth & DAG                                                 |
| Rlk     | LCK                                                         |
| Rsk     | ERK                                                         |
| SEK     | PKCth                                                       |
| Slp76   | Gads                                                        |
| TCRbind | !cCbl & TCRlig                                              |
| TCRlig  | TCRlig                                                      |
| TCRphos | LCK & TCRbind | Fyn                                         |
| ZAP70   | TCRphos & !cCbl & LCK                                       |
| cCbl    | ZAP70                                                       |

