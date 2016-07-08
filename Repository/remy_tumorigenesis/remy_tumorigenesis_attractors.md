

### Attractor Report
 * created on 28. Jun. 2016 using PyBoolNet, see https://github.com/hklarner/PyBoolNet

### Steady States
| steady state                        |
| ----------------------------------- | 
| 00000000000000000000010000001100000 |
| 00000000000000000000011000000100011 |
| 00000000000000000000011000001100001 |
| 00000000000000000011011000011110001 |
| 00000000000000000111011000011110001 |
| 00000000000000010011011000010110011 |
| 00000000000000010111011000010110011 |
| 00000100101000010011001000110010010 |
| 00000100101000010111001000110010010 |
| 00000100101011010011001001110011110 |
| 00000100101011010111001001110011110 |
| 00000100101111010011001001110011110 |
| 00000100101111010111001001110011110 |
| 00000100111000010011000000110010000 |
| 00000100111000010111000000110010000 |
| 00000100111011010011000001110011100 |
| 00000100111011010111000001110011100 |
| 00000100111111010011000001110011100 |
| 00000100111111010111000001110011100 |
| 00011100101011010011001001110011110 |
| 00011100101011010111001001110011110 |
| 00011100101111010011001001110011110 |
| 00011100101111010111001001110011110 |
| 00011100111011010011000001110011100 |
| 00011100111011010111000001110011100 |
| 00011100111111010011000001110011100 |
| 00011100111111010111000001110011100 |
| 00101001000100000000010001001101001 |
| 00101001000100000000011001000101011 |
| 00101001000100000000011001001101001 |
| 00101001000100000011010001011111001 |
| 00101001000100000011011001011111001 |
| 00101001000100000111010001011111001 |
| 00101001000100000111011001011111001 |
| 00101001000100010011011001010111011 |
| 00101001000100010111011001010111011 |
| 01100100101111010011001001110011110 |
| 01100100101111010111001001110011110 |
| 01100100111111010011000001110011100 |
| 01100100111111010111000001110011100 |
| 01111100101111010011001001110011110 |
| 01111100101111010111001001110011110 |
| 01111100111111010011000001110011100 |
| 01111100111111010111000001110011100 |

### Asynchronous STG
 * completeness: True

| trapspace                           | univocal  | faithful  |
| ----------------------------------- | --------- | --------- |
| -0000-00---0000--100--0--0-----0000 | True      | True      |
| -00000000000000--100-11--00-01-001- | True      | True      |
| 001010010001000--100-110010-01-1011 | True      | True      |
| 0010100100010000-100-100010-11-1001 | True      | True      |
| 0010100100010000-100-110010-11-1001 | True      | True      |

### Synchronous STG
 * completeness: False

| trapspace                           | univocal  | faithful  |
| ----------------------------------- | --------- | --------- |
| -0000-00---0000--100--0--0-----0000 | True      | False     |
| -00000000000000--100-11--00-01-001- | True      | True      |
| 001010010001000--100-110010-01-1011 | True      | True      |
| 0010100100010000-100-100010-11-1001 | True      | True      |
| 0010100100010000-100-110010-11-1001 | True      | True      |

### Network
| targets           | factors                                                                                                                                                                                                                                                             |
| ----------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| AKT               | PI3K                                                                                                                                                                                                                                                                |
| ATM_high          | ATM_medium & DNA_damage & E2F1_medium                                                                                                                                                                                                                               |
| ATM_medium        | DNA_damage & !E2F1_medium | ATM_high                                                                                                                                                                                                                                |
| Apoptosis_high    | Apoptosis_medium & E2F1_high                                                                                                                                                                                                                                        |
| Apoptosis_medium  | TP53 & !E2F1_high | Apoptosis_high                                                                                                                                                                                                                                  |
| CDC25A            | E2F3_medium & !RBL2 & !CHEK1_2_medium | E2F1_medium & !RBL2 & !CHEK1_2_medium                                                                                                                                                                                       |
| CHEK1_2_high      | ATM_medium & E2F1_medium & CHEK1_2_medium                                                                                                                                                                                                                           |
| CHEK1_2_medium    | ATM_medium & !E2F1_medium | CHEK1_2_high                                                                                                                                                                                                                            |
| CyclinA           | E2F3_medium & CDC25A & !RBL2 & !p21CIP | CDC25A & !p21CIP & !RBL2 & E2F1_medium                                                                                                                                                                                     |
| CyclinD1          | !p16INK4a & RAS & !p21CIP | !p16INK4a & !p21CIP & AKT                                                                                                                                                                                                               |
| CyclinE1          | E2F3_medium & CDC25A & !RBL2 & !p21CIP | CDC25A & !p21CIP & !RBL2 & E2F1_medium                                                                                                                                                                                     |
| DNA_damage        | DNA_damage                                                                                                                                                                                                                                                          |
| E2F1_high         | E2F3_medium & !RBL2 & !RAS & !RB1 & E2F1_medium | !RBL2 & !CHEK1_2_high & RAS & !RB1 & E2F1_medium | E2F3_medium & !CHEK1_2_high & !RBL2 & !RB1 & E2F1_medium | E2F1_medium & !RBL2 & RAS & !RB1 & !ATM_high | E2F3_medium & E2F1_medium & !RBL2 & !RB1 & !ATM_high |
| E2F1_medium       | !RBL2 & CHEK1_2_high & RAS & !RB1 & ATM_high | !RBL2 & CHEK1_2_high & !RB1 & E2F3_high & ATM_high | E2F1_high                                                                                                                                                       |
| E2F3_high         | E2F3_medium & CHEK1_2_high & RAS & !RB1                                                                                                                                                                                                                             |
| E2F3_medium       | !CHEK1_2_high & RAS & !RB1 | E2F3_high                                                                                                                                                                                                                              |
| EGFR              | !GRB2 & !FGFR3 & SPRY | !GRB2 & !FGFR3 & EGFR_stimulus                                                                                                                                                                                                              |
| EGFR_stimulus     | EGFR_stimulus                                                                                                                                                                                                                                                       |
| FGFR3             | !GRB2 & !EGFR & FGFR3_stimulus                                                                                                                                                                                                                                      |
| FGFR3_stimulus    | FGFR3_stimulus                                                                                                                                                                                                                                                      |
| GRB2              | !GRB2 & FGFR3 & !SPRY | EGFR                                                                                                                                                                                                                                        |
| Growth_arrest     | p21CIP | RBL2 | RB1                                                                                                                                                                                                                                                 |
| Growth_inhibitors | Growth_inhibitors                                                                                                                                                                                                                                                   |
| MDM2              | !ATM_medium & !p14ARF & TP53 & !RB1 | !ATM_medium & !p14ARF & !RB1 & AKT                                                                                                                                                                                            |
| PI3K              | !PTEN & GRB2 & RAS                                                                                                                                                                                                                                                  |
| PTEN              | TP53                                                                                                                                                                                                                                                                |
| Proliferation     | CyclinE1 | CyclinA                                                                                                                                                                                                                                                  |
| RAS               | GRB2 | FGFR3 | EGFR                                                                                                                                                                                                                                                 |
| RB1               | !p16INK4a & !CyclinD1 & !CyclinA & !CyclinE1                                                                                                                                                                                                                        |
| RBL2              | !CyclinD1 & !CyclinE1                                                                                                                                                                                                                                               |
| SPRY              | RAS                                                                                                                                                                                                                                                                 |
| TP53              | ATM_medium & !MDM2 & CHEK1_2_medium | !MDM2 & E2F1_high                                                                                                                                                                                                             |
| p14ARF            | E2F1_medium                                                                                                                                                                                                                                                         |
| p16INK4a          | Growth_inhibitors & !RB1                                                                                                                                                                                                                                            |
| p21CIP            | !CyclinE1 & TP53 & !AKT | !CyclinE1 & Growth_inhibitors & !AKT                                                                                                                                                                                                      |

