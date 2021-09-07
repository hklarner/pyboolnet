

### Attractor Report
 * created on 12. Jun. 2017 using PyBoolNet, see https://github.com/hklarner/PyBoolNet

### Steady States
| steady state |
| ------------ | 
| 011111       |

### Asynchronous STG
 * completeness: True

| trapspace      | univocal  | faithful  |
| -------------- | --------- | --------- |
| -0-000         | True      | True      |
| 011-00         | True      | True      |

### Synchronous STG
 * completeness: True

| trapspace      | univocal  | faithful  |
| -------------- | --------- | --------- |
| -0-000         | True      | True      |
| 011-00         | True      | True      |

### Network
| v1      | !v1&!v3 | !v1&!v2               |
| ------- | ------------------------------- |
| v2      | !v1&v2                          |
| v3      | v2 | !v1                        |
| v4      | !v1&v2&v3&v5&v6 | !v1&v2&v3&!v4 |
| v5      | !v1&v2&v3&v6                    |
| v6      | !v1&v2&v3&v6 | !v1&v2&v3&v5     |

