

### Attractor Report
 * created on 18. Oct. 2016 using PyBoolNet, see https://github.com/hklarner/PyBoolNet

### Steady States
 * there are no steady states

### Asynchronous STG
 * completeness: True

| trapspace          | univocal  | faithful  |
| ------------------ | --------- | --------- |
| ------------------ | True      | True      |

### Synchronous STG
 * completeness: True

| trapspace          | univocal  | faithful  |
| ------------------ | --------- | --------- |
| ------------------ | True      | True      |

### Network
| targets | factors                                                                                         |
| ------- | ----------------------------------------------------------------------------------------------- |
| CD      | FEAR & vM & Cdc14 & !CD                                                                         |
| CKI     | Swi5 & !Clb2 & !Cln2 & !Clb5 | !Clb2 & CKI & !Cln2 & !Clb5 | Swi5 & Cdc14                       |
| Cdc14   | FEAR & MEN                                                                                      |
| Cdc20   | SFF & Clb2 & vM                                                                                 |
| Cdh1    | !Clb2 & !Cln2 & !Clb5 | Cdc14                                                                   |
| Clb2    | !Cdh1 & Clb2 & SFF & !CKI | SFF & Clb2 & !CKI & !Cdc20 | !Cdh1 & vB & !CKI | vB & !CKI & !Cdc20 |
| Clb5    | SMBF & !Cdc20                                                                                   |
| Cln2    | SMBF                                                                                            |
| Cln3    | !Yhp1                                                                                           |
| FEAR    | Cdc20                                                                                           |
| MEN     | Clb2 & FEAR                                                                                     |
| SFF     | !Cdh1 & vB & !CKI | vB & !CKI & !Cdc20 | SFF & Clb2                                             |
| SMBF    | SMBF & !Clb2 | !Clb2 & Cln3 | !Clb2 & Cln2                                                      |
| Swi5    | SFF & !Clb2 | SFF & Cdc14                                                                       |
| Yhp1    | SMBF                                                                                            |
| vB      | vB & !CD | Cln2 & !CD | Clb5 & !CD                                                              |
| vM      | Clb2 & vS & !CD | vM & !CD                                                                      |
| vS      | vS & !CD | Clb5 & !CD | Clb2 & !CD                                                              |

