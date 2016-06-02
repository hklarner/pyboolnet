

randomnet_n15k3 = """
# generated with BoolNet
# Mussel, Christoph, Martin Hopfensitz, and Hans A. Kestler. "BoolNet: an R package for generation, reconstruction and analysis of Boolean networks." Bioinformatics 26.10 (2010): 1378-1380.

Gene1, (!Gene3 & !Gene12) | (Gene8)
Gene2, (!Gene4 & !Gene14) | (!Gene12 & !Gene4)
Gene3, (Gene5) | (Gene6 & !Gene3)
Gene4, (!Gene3 & !Gene4) | (!Gene6 & !Gene4) | (!Gene6 & Gene3)
Gene5, (!Gene14 & Gene6) | (Gene14 & !Gene6) | (Gene9)
Gene6, (!Gene8 & Gene10) | (Gene10 & Gene14)
Gene7, (!Gene12 & !Gene13 & Gene10) | (!Gene12 & Gene13 & !Gene10) | (Gene12 & !Gene13 & !Gene10)
Gene8, (!Gene13 & !Gene8 & Gene9) | (Gene13 & !Gene8 & !Gene9) | (Gene13 & Gene8 & Gene9)
Gene9, (Gene12) | (Gene7) | (Gene11)
Gene10, (!Gene10 & !Gene3) | (!Gene3 & Gene1) | (Gene10 & Gene3 & !Gene1)
Gene11, (!Gene14) | (Gene12) | (Gene13)
Gene12, (!Gene4 & Gene3) | (Gene8 & Gene4)
Gene13, (!Gene6 & !Gene11 & Gene2) | (!Gene6 & Gene11 & !Gene2) | (Gene6 & !Gene11 & !Gene2) | (Gene6 & Gene11 & Gene2)
Gene14, (!Gene5 & !Gene9) | (Gene8 & Gene9)
Gene15, (!Gene8 & Gene9) | (Gene8 & !Gene9) | (!Gene2 & Gene9)
"""


dahlhaus_neuroplastoma = """
# taken from
# Dahlhaus, Meike, et al. "Boolean modeling identifies Greatwall/MASTL as an important regulator in the AURKA network of neuroblastoma." Cancer letters 371.1 (2016): 79-89.

CentrosomeMat,      CDK1CCNBComplex & ! SpindleAssembly
SpindleAssembly,    CentrosomeMat & !Cytokinesis
Cytokinesis,        SpindleAssembly & !CentrosomeMat
AURKAActive,        AURKAPresent & (( TPX2 | (AJUBA & BORA) | (AJUBA & NEDD9) ) & !(AURKAActive & (PP1)))
AURKAPresent,       !PP2A
GSK3B,              GSK3B
AJUBA,              AJUBA
MTCanAct,           MTCanAct
STMNCanAct,         STMNCanAct
CDK1CCNBComplex,    !Cytokinesis & (!WEE1 | hCPEB | CDC25B)
CDC25B,             (AURKAActive | PLK1) & !Cytokinesis
BORA,               GSK3B & Cytokinesis & !PLK1 | !Cytokinesis
GWL-MASTL,          CDK1CCNBComplex & !PP2A
HCPEB,              AURKAActive
MT,                 !STMN
NEDD9,              AURKAActive
ENSA,               GWL-MASTL
PLK1,               AURKAActive | !STMN & STMNCanAct | MT & MTCanAct
PP1,                !Cytokinesis & !(AURKAActive | CDK1CCNBComplex)
PP2A,               (PP1 & ( ! ENSA) )
STMN,               !AURKAActive
TPX2,               PLK1
WEE1,               !PLK1
"""


faure_cellcycle = """
# taken from
#Faure, Adrien, et al. "Dynamical analysis of a generic Boolean model for the control of the mammalian cell cycle." Bioinformatics 22.14 (2006): e124-e131.

Cdc20,               (CycB)
CycA,                (!cdh1 & CycA & !Rb & !Cdc20) | (!cdh1 & E2F & !Rb & !Cdc20) | (!UbcH10 & CycA & !Rb & !Cdc20) | (!UbcH10 & E2F & !Rb & !Cdc20)
CycB,                (!cdh1 & !Cdc20)
CycD,                (CycD)
CycE,                (E2F & !Rb)
E2F,                 (!CycA & !Rb & !CycB) | (p27 & !Rb & !CycB)
Rb,                  (!CycE & !CycD & !CycA & !CycB) | (!CycD & p27 & !CycB)
UbcH10,              (UbcH10 & CycA) | (UbcH10 & CycB) | (UbcH10 & Cdc20) | (!cdh1)
cdh1,                (p27 & !CycB) | (Cdc20) | (!CycA & !CycB)
p27,                 (!CycD & p27 & !CycA & !CycB) | (!CycE & !CycD & !CycA & !CycB) | (!CycE & !CycD & p27 & !CycB)
"""


irons_yeast = """
# taken from
# Irons, D. J. "Logical analysis of the budding yeast cell cycle." Journal of theoretical biology 257.4 (2009): 543-559.
# the variables B, M and S are replaced by vB, vM and vS because NuSMV requires two-letter names

vB,                  (Cln2 & !CD) | (vB & !CD) | (Clb5 & !CD)
CD,                  (FEAR & vM & Cdc14 & !CD)
CKI,                 (Swi5 & !Clb2 & !Cln2 & !Clb5) | (!Clb2 & CKI & !Cln2 & !Clb5) | (Swi5 & Cdc14)
Cdc14,               (FEAR & MEN)
Cdc20,               (SFF & Clb2 & vM)
Cdh1,                (!Clb2 & !Cln2 & !Clb5) | (Cdc14)
Clb2,                (!Cdh1 & SFF & !CKI & Clb2) | (vB & !CKI & !Cdc20) | (SFF & Clb2 & !CKI & !Cdc20) | (!Cdh1 & vB & !CKI)
Clb5,                (SMBF & !Cdc20)
Cln2,                (SMBF)
Cln3,                (!Yhp1)
FEAR,                (Cdc20)
vM,                  (Clb2 & vS & !CD) | (vM & !CD)
MEN,                 (Clb2 & FEAR)
vS,                  (Clb5 & !CD) | (vS & !CD) | (Clb2 & !CD)
SFF,                 (vB & !CKI & !Cdc20) | (!Cdh1 & vB & !CKI) | (SFF & Clb2)
SMBF,                (!Clb2 & Cln3) | (!Clb2 & Cln2) | (SMBF & !Clb2)
Swi5,                (SFF & Cdc14) | (SFF & !Clb2)
Yhp1,                (SMBF)
"""


davidich_yeast = """
# taken from
# Davidich, Maria I., and Stefan Bornholdt. "Boolean network model predicts cell cycle sequence of fission yeast." PloS one 3.2 (2008): e1672.

Cdc25,               (Cdc2_Cdc13 & !PP) | (Cdc2_Cdc13 & Cdc25) | (!PP & Cdc25)
Cdc2_Cdc13,          (!Slp1 & !Rum1 & !Ste9)
Cdc2_Cdc13_A,        (!Slp1 & !Rum1 & Cdc25 & !Ste9 & !Wee1_Mik1)
PP,                  (Slp1)
Rum1,                (!SK & Rum1 & PP & !Cdc2_Cdc13) | (!SK & Rum1 & !Cdc2_Cdc13 & !Cdc2_Cdc13_A) | (Rum1 & PP & !Cdc2_Cdc13 & !Cdc2_Cdc13_A) | (!SK & Rum1 & PP & !Cdc2_Cdc13_A) | (!SK & !Cdc2_Cdc13 & PP & !Cdc2_Cdc13_A)
SK,                  (Start)
Slp1,                (Cdc2_Cdc13_A)
Start,               0
Ste9,                (!SK & !Cdc2_Cdc13 & PP & Ste9) | (!SK & !Cdc2_Cdc13 & Ste9 & !Cdc2_Cdc13_A) | (!Cdc2_Cdc13 & PP & Ste9 & !Cdc2_Cdc13_A) | (!SK & PP & Ste9 & !Cdc2_Cdc13_A) | (!SK & !Cdc2_Cdc13 & PP & !Cdc2_Cdc13_A)
Wee1_Mik1,           (!Cdc2_Cdc13 & PP) | (PP & Wee1_Mik1) | (!Cdc2_Cdc13 & Wee1_Mik1)
"""

arellano_antelope = """
# taken from
# Arellano, Gustavo, et al. "Antelope: a hybrid-logic model checker for branching-time Boolean GRN analysis." BMC bioinformatics 12.1 (2011): 1.

PLT,  ARF
AUXINS,  AUXINS
IAA,  !AUXINS
ARF,  !IAA
SHR,  SHR
SCR,  SHR & SCR & (JKD | !MGP)
JKD,  SHR & SCR
MGP,  SHR & SCR & !WOX
WOX,  ARF & SHR & SCR & ( !MGP | WOX)
"""

klamt_tcr = """
# taken from
# Klamt S, Saez-Rodriguez J, Lindquist JA, Simeoni L, Gilles ED.  2006.  A methodology for the structural and functional analysis of signaling and regulatory networks. BMC Bioinformatics. 7(1):56.

AP1,                 Jun & Fos
CD45,                CD45
CD8,                 CD8
CRE,                 CREB
CREB,                Rsk
Ca,                  IP3
Calcin,              Ca
DAG,                 PLCg_a
ERK,                 MEK
Fos,                 ERK
Fyn,                 CD45 & TCRbind | CD45 & LCK
Gads,                LAT
Grb2Sos,             LAT
IKK,                 PKCth
IP3,                 PLCg_a
IkB,                 !IKK
Itk,                 Slp76 & ZAP70
JNK,                 SEK
Jun,                 JNK
LAT,                 ZAP70
LCK,                 CD45 & CD8 & !PAGCsk
MEK,                 Raf
NFAT,                Calcin
NFkB,                !IkB
PAGCsk,              !TCRbind
PKCth,               DAG
PLCg_a,              ZAP70 & Slp76 & Rlk & PLCg_b | ZAP70 & Itk & Slp76 & PLCg_b
PLCg_b,              LAT
Raf,                 Ras
Ras,                 RasGRP1 & Grb2Sos
RasGRP1,             PKCth & DAG
Rlk,                 LCK
Rsk,                 ERK
SEK,                 PKCth
Slp76,               Gads
TCRbind,             !cCbl & TCRlig
TCRlig,              TCRlig
TCRphos,             LCK & TCRbind | Fyn
ZAP70,               TCRphos & !cCbl & LCK
cCbl,                ZAP70
"""


grieco_mapk = """
# taken from "Integrative Modelling of the Influence of MAPK Network on Cancer Cell Fate Decision"
# by L. Grieco et. al, PLOS Computational Biology 2013

AKT,                 (PDK1 & !PTEN)
AP1,                 (JUN & ATF2) | (JUN & FOS)
ATF2,                (JNK) | (p38)
ATM,                 (DNA_damage)
Apoptosis,           (FOXO3 & p53 & !ERK & !BCL2)
BCL2,                (CREB & AKT)
CREB,                (MSK)
DNA_damage,          (DNA_damage)
DUSP1,               (CREB)
EGFR,                (!PKC & !GRB2 & EGFR_stimulus) | (!PKC & !GRB2 & SPRY)
EGFR_stimulus,       (EGFR_stimulus)
ELK1,                (p38) | (JNK) | (ERK)
ERK,                 (MEK1_2)
FGFR3,               (!PKC & !GRB2 & FGFR3_stimulus)
FGFR3_stimulus,      (FGFR3_stimulus)
FOS,                 (CREB & ERK & RSK) | (ELK1 & ERK & RSK)
FOXO3,               (JNK & !AKT)
FRS2,                (!GRB2 & FGFR3 & !SPRY)
GAB1,                (PI3K) | (GRB2)
GADD45,              (SMAD) | (p53)
GRB2,                (EGFR) | (FRS2) | (TGFBR)
Growth_Arrest,       (p21)
JNK,                 (TAK1 & TAOK) | (MAP3K1_3 & !DUSP1) | (MTK1 & !DUSP1) | (TAK1 & !DUSP1) | (MTK1 & TAOK) | (TAK1 & MTK1) | (MAP3K1_3 & MTK1) | (TAK1 & MAP3K1_3) | (MAP3K1_3 & TAOK) | (!DUSP1 & TAOK)
JUN,                 (JNK)
MAP3K1_3,            (RAS)
MAX1,                 (p38)
MDM2,                (!p14 & p53) | (!p14 & AKT)
MEK1_2,              (!PPP2CA & !AP1 & MAP3K1_3) | (RAF & !PPP2CA & !AP1)
MSK,                 (p38) | (ERK)
MTK1,                (GADD45)
MYC,                 (MSK & AKT) | (MAX1 & MSK)
PDK1,                (PI3K)
PI3K,                (SOS & RAS) | (GAB1)
PKC,                 (PLCG)
PLCG,                (FGFR3) | (EGFR)
PPP2CA,              (p38)
PTEN,                (p53)
Proliferation,       (MYC & !p21 & p70)
RAF,                 (!ERK & RAS & !AKT) | (PKC & !ERK & !AKT)
RAS,                 (SOS) | (PLCG)
RSK,                 (ERK)
SMAD,                (TGFBR)
SOS,                 (GRB2 & !RSK)
SPRY,                (ERK)
TAK1,                (TGFBR)
TAOK,                (ATM)
TGFBR,               (TGFBR_stimulus)
TGFBR_stimulus,      (TGFBR_stimulus)
p14,                 (MYC)
p21,                 (p53 & !AKT)
p38,                 (TAK1 & TAOK) | (MAP3K1_3 & !DUSP1) | (MTK1 & !DUSP1) | (TAK1 & !DUSP1) | (MTK1 & TAOK) | (TAK1 & MTK1) | (MAP3K1_3 & MTK1) | (TAK1 & MAP3K1_3) | (MAP3K1_3 & TAOK) | (!DUSP1 & TAOK)
p53,                 (!MDM2 & p38) | (p38 & ATM) | (!MDM2 & ATM)
p70,                 (PDK1 & ERK)
"""


raf = """
# made up to illustrate model checking

Erk,  Erk & Mek | Mek & Raf
Mek,  Erk | Mek & Raf
Raf,  !Erk | !Raf
"""


remy_tumorigenesis = """
# created from the *revised* PDF supplementary for the paper
# "A modelling approach to explain mutually exclusive and co-occurring genetic alterations in bladder tumorigenesis"
# E. Remy et al., Cancer Research, 2015
#
# Network originally contains 30 components, 5 of which are ternary
# hence, there are 35 components in this, booleanized, model
# Booleanization is done by the "bar graph encoding":
#    x_medium := x_high   | (condition for x_medium)
#    x_high   := x_medium & (condition for x_high)
# admissiable states satisfy "x_high -> x_medium"
#
# all expressions that involve "x" or "x:1" (for ternary x) are replaced by "x_medium"

# inputs
EGFR_stimulus,       EGFR_stimulus
FGFR3_stimulus,      FGFR3_stimulus
DNA_damage,          DNA_damage
Growth_inhibitors,   Growth_inhibitors

# intermediate
E2F1_medium,         E2F1_high   | (!RBL2 & !RB1  & ATM_high & CHEK1_2_high & (RAS | E2F3_high))
E2F1_high,           E2F1_medium & (!RB1  & !RBL2 & ((!(CHEK1_2_high & ATM_high) & (RAS | E2F3_medium)) | (CHEK1_2_high & ATM_high & !RAS & E2F3_medium)))
E2F3_medium,         E2F3_high   | (! RB1 & ! CHEK1_2_high & RAS )
E2F3_high,           E2F3_medium & (! RB1 &   CHEK1_2_high & RAS )
ATM_medium,          ATM_high   | ( DNA_damage & ! E2F1_medium )
ATM_high,            ATM_medium & ( DNA_damage &   E2F1_medium )
CHEK1_2_medium,      CHEK1_2_high   | ( ATM_medium & ! E2F1_medium )
CHEK1_2_high,        CHEK1_2_medium & ( ATM_medium &   E2F1_medium )
EGFR,                ( EGFR_stimulus | SPRY ) & ! FGFR3 & ! GRB2 
FGFR3,               ! EGFR & FGFR3_stimulus & ! GRB2 
RAS,                 EGFR | FGFR3 | GRB2 
PTEN,                TP53 
PI3K,                GRB2 & RAS & ! PTEN 
AKT,                 PI3K 
GRB2,                ( FGFR3 & ! GRB2 & ! SPRY ) | EGFR 
SPRY,                RAS 
CyclinD1,            ( RAS | AKT ) & ! p16INK4a & ! p21CIP 
CyclinE1,            ! RBL2 & ! p21CIP & CDC25A & ( E2F1_medium | E2F3_medium )
CyclinA,             ! RBL2 & ! p21CIP & CDC25A & ( E2F1_medium | E2F3_medium )
CDC25A,              ! CHEK1_2_medium & ! RBL2 &  ( E2F1_medium | E2F3_medium )
p16INK4a,            Growth_inhibitors & ! RB1 
p14ARF,              E2F1_medium 
RB1,                 ! CyclinD1 & ! CyclinE1 & ! p16INK4a & ! CyclinA 
RBL2,                ! CyclinD1 & ! CyclinE1 
p21CIP,              ! CyclinE1 & ( Growth_inhibitors | TP53 ) & ! AKT 
MDM2,                ( TP53 | AKT ) & ! p14ARF & ! ATM_medium & ! RB1 
TP53,                ! MDM2 & (( ATM_medium & CHEK1_2_medium ) | E2F1_high )

# outputs
Proliferation,       CyclinE1 | CyclinA 
Growth_arrest,       p21CIP | RB1 | RBL2
Apoptosis_medium,    Apoptosis_high   | (! E2F1_high & TP53 )
Apoptosis_high,      Apoptosis_medium & (  E2F1_high )
"""
