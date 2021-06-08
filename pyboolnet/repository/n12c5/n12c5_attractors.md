

### Attractor Report
 * created on 02. May. 2017 using PyBoolNet, see https://github.com/hklarner/PyBoolNet

### Steady States
| steady state |
| ------------ | 
| 011111111011 |

### Asynchronous STG
 * completeness: True

| trapspace      | univocal  | faithful  |
| -------------- | --------- | --------- |
| 000011111-0-   | True      | True      |
| -0000-000000   | True      | True      |
| 000011-00000   | True      | True      |
| 0-0011111011   | True      | True      |

### Synchronous STG
 * completeness: True

| trapspace      | univocal  | faithful  |
| -------------- | --------- | --------- |
| 000011111-0-   | True      | True      |
| -0000-000000   | True      | True      |
| 000011-00000   | True      | True      |
| 0-0011111011   | True      | True      |

### Network
| v1      | !v1&!v3 | !v1&!v2                                                        |
| ------- | ------------------------------------------------------------------------ |
| v10     | v12&v11&!v1&v2&v3&v4&v5&v6&!v7&v8&v9 | !v10&!v1&v2&v3&v4&v5&v6&!v7&v8&v9 |
| v11     | v12&!v1&v2&v3&v4&v5&v6&!v7&v8&v9                                         |
| v12     | v12&!v1&v2&v3&v4&v5&v6&!v7&v8&v9 | v11&!v1&v2&v3&v4&v5&v6&!v7&v8&v9      |
| v2      | !v1&v2                                                                   |
| v3      | v2 | !v1                                                                 |
| v4      | !v1&v2&v3&v5&v6 | !v1&v2&v3&!v4                                          |
| v5      | !v1&v2&v3&v6                                                             |
| v6      | !v1&v2&v3&v6 | !v1&v2&v3&v5                                              |
| v7      | !v1&v2&v3&v4&v5&v6&!v7&!v9 | !v1&v2&v3&v4&v5&v6&!v7&!v8                  |
| v8      | !v1&v2&v3&v4&v5&v6&!v7&v8                                                |
| v9      | !v1&v2&v3&v4&v5&v6&v8 | !v1&v2&v3&v4&v5&v6&!v7                           |

