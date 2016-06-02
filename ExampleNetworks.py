

klamt_tcr = """
# based on 
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
