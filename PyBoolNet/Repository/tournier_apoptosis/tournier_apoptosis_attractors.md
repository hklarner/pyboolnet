

### Attractor Report
 * created on 18. Oct. 2016 using PyBoolNet, see https://github.com/hklarner/PyBoolNet

### Steady States
| steady state |
| ------------ | 
| 000101010000 |
| 011000010000 |

### Asynchronous STG
 * completeness: True

| trapspace      | univocal  | faithful  |
| -------------- | --------- | --------- |
| -110-00----1   | True      | True      |

### Synchronous STG
 * completeness: False

| trapspace      | univocal  | faithful  |
| -------------- | --------- | --------- |
| -110-00----1   | True      | True      |

### Network
| targets | factors                                         |
| ------- | ----------------------------------------------- |
| A20a    | NFkBnuc & TNF                                   |
| C3a     | C8a & !IAP                                      |
| C8a     | !CARP & T2 | !CARP & C3a                        |
| CARP    | NFkB & !TNF | !TNF & !C3a | NFkBnuc & !C3a      |
| FLIP    | NFkBnuc                                         |
| IAP     | NFkBnuc & !TNF | !TNF & !C3a | NFkBnuc & !C3a   |
| IKKa    | !C3a & TNF & !A20a                              |
| IkB     | NFkBnuc & !TNF | !TNF & !IKKa | NFkBnuc & !IKKa |
| NFkB    | !IkB                                            |
| NFkBnuc | !IkB & NFkB                                     |
| T2      | TNF & !FLIP                                     |
| TNF     | TNF                                             |

