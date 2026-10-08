import Quartic.FiniteEndpointMetadata18Data
open Quartic.FiniteEndpointMetadata18Data Quartic.FiniteEndpointCheckerPolynomial
open Quartic.FiniteEndpointChunks
set_option maxRecDepth 1000000
set_option maxHeartbeats 32000000
set_option Elab.async false
noncomputable section
namespace Quartic.FiniteEndpointMetadata18

def quarticCondition (i : ℕ) : Prop :=
  let k : Fin 5985 := ⟨i%5985,Nat.mod_lt _ (by decide)⟩
  tupleRank 18 0 (vars4 k)=i ∧ (vars4 k).Pairwise (· ≤ ·) ∧
  selectedGenerator i < 40 ∧ selectedMultiplier i < 171 ∧
  (i < 5928 → selectedGenerator i < 39)

def productCondition (k : ℕ) : Prop :=
  let i : Fin 171 := ⟨k/171%171,Nat.mod_lt _ (by decide)⟩
  let j : Fin 171 := ⟨k%171,Nat.mod_lt _ (by decide)⟩
  naturalProduct i.val j.val < 5985 ∧
  vars4 (productIndex i j) = (vars2 i ++ vars2 j).insertionSort (· ≤ ·)

instance (i : ℕ) : Decidable (quarticCondition i) := inferInstanceAs (Decidable (_ ∧ _))
instance (i : ℕ) : Decidable (productCondition i) := inferInstanceAs (Decidable (_ ∧ _))

theorem quad_checked : ∀ i : Fin 171,tupleRank 18 0 (vars2 i)=i.val ∧
    (vars2 i).Pairwise (· ≤ ·) := by decide +kernel

theorem quartic_block_0 : ∀ j : Fin 256,0*256+j.val < 5985 → quarticCondition (0*256+j.val) := by decide +kernel

theorem quartic_block_1 : ∀ j : Fin 256,1*256+j.val < 5985 → quarticCondition (1*256+j.val) := by decide +kernel

theorem quartic_block_2 : ∀ j : Fin 256,2*256+j.val < 5985 → quarticCondition (2*256+j.val) := by decide +kernel

theorem quartic_block_3 : ∀ j : Fin 256,3*256+j.val < 5985 → quarticCondition (3*256+j.val) := by decide +kernel

theorem quartic_block_4 : ∀ j : Fin 256,4*256+j.val < 5985 → quarticCondition (4*256+j.val) := by decide +kernel

theorem quartic_block_5 : ∀ j : Fin 256,5*256+j.val < 5985 → quarticCondition (5*256+j.val) := by decide +kernel

theorem quartic_block_6 : ∀ j : Fin 256,6*256+j.val < 5985 → quarticCondition (6*256+j.val) := by decide +kernel

theorem quartic_block_7 : ∀ j : Fin 256,7*256+j.val < 5985 → quarticCondition (7*256+j.val) := by decide +kernel

theorem quartic_block_8 : ∀ j : Fin 256,8*256+j.val < 5985 → quarticCondition (8*256+j.val) := by decide +kernel

theorem quartic_block_9 : ∀ j : Fin 256,9*256+j.val < 5985 → quarticCondition (9*256+j.val) := by decide +kernel

theorem quartic_block_10 : ∀ j : Fin 256,10*256+j.val < 5985 → quarticCondition (10*256+j.val) := by decide +kernel

theorem quartic_block_11 : ∀ j : Fin 256,11*256+j.val < 5985 → quarticCondition (11*256+j.val) := by decide +kernel

theorem quartic_block_12 : ∀ j : Fin 256,12*256+j.val < 5985 → quarticCondition (12*256+j.val) := by decide +kernel

theorem quartic_block_13 : ∀ j : Fin 256,13*256+j.val < 5985 → quarticCondition (13*256+j.val) := by decide +kernel

theorem quartic_block_14 : ∀ j : Fin 256,14*256+j.val < 5985 → quarticCondition (14*256+j.val) := by decide +kernel

theorem quartic_block_15 : ∀ j : Fin 256,15*256+j.val < 5985 → quarticCondition (15*256+j.val) := by decide +kernel

theorem quartic_block_16 : ∀ j : Fin 256,16*256+j.val < 5985 → quarticCondition (16*256+j.val) := by decide +kernel

theorem quartic_block_17 : ∀ j : Fin 256,17*256+j.val < 5985 → quarticCondition (17*256+j.val) := by decide +kernel

theorem quartic_block_18 : ∀ j : Fin 256,18*256+j.val < 5985 → quarticCondition (18*256+j.val) := by decide +kernel

theorem quartic_block_19 : ∀ j : Fin 256,19*256+j.val < 5985 → quarticCondition (19*256+j.val) := by decide +kernel

theorem quartic_block_20 : ∀ j : Fin 256,20*256+j.val < 5985 → quarticCondition (20*256+j.val) := by decide +kernel

theorem quartic_block_21 : ∀ j : Fin 256,21*256+j.val < 5985 → quarticCondition (21*256+j.val) := by decide +kernel

theorem quartic_block_22 : ∀ j : Fin 256,22*256+j.val < 5985 → quarticCondition (22*256+j.val) := by decide +kernel

theorem quartic_block_23 : ∀ j : Fin 256,23*256+j.val < 5985 → quarticCondition (23*256+j.val) := by decide +kernel

theorem quartic_all : ∀ i,i < 5985 → quarticCondition i := by
  apply forall_lt_of_fin_chunks quarticCondition 5985 256 (by decide)
  intro k
  fin_cases k
  · exact quartic_block_0
  · exact quartic_block_1
  · exact quartic_block_2
  · exact quartic_block_3
  · exact quartic_block_4
  · exact quartic_block_5
  · exact quartic_block_6
  · exact quartic_block_7
  · exact quartic_block_8
  · exact quartic_block_9
  · exact quartic_block_10
  · exact quartic_block_11
  · exact quartic_block_12
  · exact quartic_block_13
  · exact quartic_block_14
  · exact quartic_block_15
  · exact quartic_block_16
  · exact quartic_block_17
  · exact quartic_block_18
  · exact quartic_block_19
  · exact quartic_block_20
  · exact quartic_block_21
  · exact quartic_block_22
  · exact quartic_block_23

theorem product_block_0 : ∀ j : Fin 256,0*256+j.val < 29241 → productCondition (0*256+j.val) := by decide +kernel

theorem product_block_1 : ∀ j : Fin 256,1*256+j.val < 29241 → productCondition (1*256+j.val) := by decide +kernel

theorem product_block_2 : ∀ j : Fin 256,2*256+j.val < 29241 → productCondition (2*256+j.val) := by decide +kernel

theorem product_block_3 : ∀ j : Fin 256,3*256+j.val < 29241 → productCondition (3*256+j.val) := by decide +kernel

theorem product_block_4 : ∀ j : Fin 256,4*256+j.val < 29241 → productCondition (4*256+j.val) := by decide +kernel

theorem product_block_5 : ∀ j : Fin 256,5*256+j.val < 29241 → productCondition (5*256+j.val) := by decide +kernel

theorem product_block_6 : ∀ j : Fin 256,6*256+j.val < 29241 → productCondition (6*256+j.val) := by decide +kernel

theorem product_block_7 : ∀ j : Fin 256,7*256+j.val < 29241 → productCondition (7*256+j.val) := by decide +kernel

theorem product_block_8 : ∀ j : Fin 256,8*256+j.val < 29241 → productCondition (8*256+j.val) := by decide +kernel

theorem product_block_9 : ∀ j : Fin 256,9*256+j.val < 29241 → productCondition (9*256+j.val) := by decide +kernel

theorem product_block_10 : ∀ j : Fin 256,10*256+j.val < 29241 → productCondition (10*256+j.val) := by decide +kernel

theorem product_block_11 : ∀ j : Fin 256,11*256+j.val < 29241 → productCondition (11*256+j.val) := by decide +kernel

theorem product_block_12 : ∀ j : Fin 256,12*256+j.val < 29241 → productCondition (12*256+j.val) := by decide +kernel

theorem product_block_13 : ∀ j : Fin 256,13*256+j.val < 29241 → productCondition (13*256+j.val) := by decide +kernel

theorem product_block_14 : ∀ j : Fin 256,14*256+j.val < 29241 → productCondition (14*256+j.val) := by decide +kernel

theorem product_block_15 : ∀ j : Fin 256,15*256+j.val < 29241 → productCondition (15*256+j.val) := by decide +kernel

theorem product_block_16 : ∀ j : Fin 256,16*256+j.val < 29241 → productCondition (16*256+j.val) := by decide +kernel

theorem product_block_17 : ∀ j : Fin 256,17*256+j.val < 29241 → productCondition (17*256+j.val) := by decide +kernel

theorem product_block_18 : ∀ j : Fin 256,18*256+j.val < 29241 → productCondition (18*256+j.val) := by decide +kernel

theorem product_block_19 : ∀ j : Fin 256,19*256+j.val < 29241 → productCondition (19*256+j.val) := by decide +kernel

theorem product_block_20 : ∀ j : Fin 256,20*256+j.val < 29241 → productCondition (20*256+j.val) := by decide +kernel

theorem product_block_21 : ∀ j : Fin 256,21*256+j.val < 29241 → productCondition (21*256+j.val) := by decide +kernel

theorem product_block_22 : ∀ j : Fin 256,22*256+j.val < 29241 → productCondition (22*256+j.val) := by decide +kernel

theorem product_block_23 : ∀ j : Fin 256,23*256+j.val < 29241 → productCondition (23*256+j.val) := by decide +kernel

theorem product_block_24 : ∀ j : Fin 256,24*256+j.val < 29241 → productCondition (24*256+j.val) := by decide +kernel

theorem product_block_25 : ∀ j : Fin 256,25*256+j.val < 29241 → productCondition (25*256+j.val) := by decide +kernel

theorem product_block_26 : ∀ j : Fin 256,26*256+j.val < 29241 → productCondition (26*256+j.val) := by decide +kernel

theorem product_block_27 : ∀ j : Fin 256,27*256+j.val < 29241 → productCondition (27*256+j.val) := by decide +kernel

theorem product_block_28 : ∀ j : Fin 256,28*256+j.val < 29241 → productCondition (28*256+j.val) := by decide +kernel

theorem product_block_29 : ∀ j : Fin 256,29*256+j.val < 29241 → productCondition (29*256+j.val) := by decide +kernel

theorem product_block_30 : ∀ j : Fin 256,30*256+j.val < 29241 → productCondition (30*256+j.val) := by decide +kernel

theorem product_block_31 : ∀ j : Fin 256,31*256+j.val < 29241 → productCondition (31*256+j.val) := by decide +kernel

theorem product_block_32 : ∀ j : Fin 256,32*256+j.val < 29241 → productCondition (32*256+j.val) := by decide +kernel

theorem product_block_33 : ∀ j : Fin 256,33*256+j.val < 29241 → productCondition (33*256+j.val) := by decide +kernel

theorem product_block_34 : ∀ j : Fin 256,34*256+j.val < 29241 → productCondition (34*256+j.val) := by decide +kernel

theorem product_block_35 : ∀ j : Fin 256,35*256+j.val < 29241 → productCondition (35*256+j.val) := by decide +kernel

theorem product_block_36 : ∀ j : Fin 256,36*256+j.val < 29241 → productCondition (36*256+j.val) := by decide +kernel

theorem product_block_37 : ∀ j : Fin 256,37*256+j.val < 29241 → productCondition (37*256+j.val) := by decide +kernel

theorem product_block_38 : ∀ j : Fin 256,38*256+j.val < 29241 → productCondition (38*256+j.val) := by decide +kernel

theorem product_block_39 : ∀ j : Fin 256,39*256+j.val < 29241 → productCondition (39*256+j.val) := by decide +kernel

theorem product_block_40 : ∀ j : Fin 256,40*256+j.val < 29241 → productCondition (40*256+j.val) := by decide +kernel

theorem product_block_41 : ∀ j : Fin 256,41*256+j.val < 29241 → productCondition (41*256+j.val) := by decide +kernel

theorem product_block_42 : ∀ j : Fin 256,42*256+j.val < 29241 → productCondition (42*256+j.val) := by decide +kernel

theorem product_block_43 : ∀ j : Fin 256,43*256+j.val < 29241 → productCondition (43*256+j.val) := by decide +kernel

theorem product_block_44 : ∀ j : Fin 256,44*256+j.val < 29241 → productCondition (44*256+j.val) := by decide +kernel

theorem product_block_45 : ∀ j : Fin 256,45*256+j.val < 29241 → productCondition (45*256+j.val) := by decide +kernel

theorem product_block_46 : ∀ j : Fin 256,46*256+j.val < 29241 → productCondition (46*256+j.val) := by decide +kernel

theorem product_block_47 : ∀ j : Fin 256,47*256+j.val < 29241 → productCondition (47*256+j.val) := by decide +kernel

theorem product_block_48 : ∀ j : Fin 256,48*256+j.val < 29241 → productCondition (48*256+j.val) := by decide +kernel

theorem product_block_49 : ∀ j : Fin 256,49*256+j.val < 29241 → productCondition (49*256+j.val) := by decide +kernel

theorem product_block_50 : ∀ j : Fin 256,50*256+j.val < 29241 → productCondition (50*256+j.val) := by decide +kernel

theorem product_block_51 : ∀ j : Fin 256,51*256+j.val < 29241 → productCondition (51*256+j.val) := by decide +kernel

theorem product_block_52 : ∀ j : Fin 256,52*256+j.val < 29241 → productCondition (52*256+j.val) := by decide +kernel

theorem product_block_53 : ∀ j : Fin 256,53*256+j.val < 29241 → productCondition (53*256+j.val) := by decide +kernel

theorem product_block_54 : ∀ j : Fin 256,54*256+j.val < 29241 → productCondition (54*256+j.val) := by decide +kernel

theorem product_block_55 : ∀ j : Fin 256,55*256+j.val < 29241 → productCondition (55*256+j.val) := by decide +kernel

theorem product_block_56 : ∀ j : Fin 256,56*256+j.val < 29241 → productCondition (56*256+j.val) := by decide +kernel

theorem product_block_57 : ∀ j : Fin 256,57*256+j.val < 29241 → productCondition (57*256+j.val) := by decide +kernel

theorem product_block_58 : ∀ j : Fin 256,58*256+j.val < 29241 → productCondition (58*256+j.val) := by decide +kernel

theorem product_block_59 : ∀ j : Fin 256,59*256+j.val < 29241 → productCondition (59*256+j.val) := by decide +kernel

theorem product_block_60 : ∀ j : Fin 256,60*256+j.val < 29241 → productCondition (60*256+j.val) := by decide +kernel

theorem product_block_61 : ∀ j : Fin 256,61*256+j.val < 29241 → productCondition (61*256+j.val) := by decide +kernel

theorem product_block_62 : ∀ j : Fin 256,62*256+j.val < 29241 → productCondition (62*256+j.val) := by decide +kernel

theorem product_block_63 : ∀ j : Fin 256,63*256+j.val < 29241 → productCondition (63*256+j.val) := by decide +kernel

theorem product_block_64 : ∀ j : Fin 256,64*256+j.val < 29241 → productCondition (64*256+j.val) := by decide +kernel

theorem product_block_65 : ∀ j : Fin 256,65*256+j.val < 29241 → productCondition (65*256+j.val) := by decide +kernel

theorem product_block_66 : ∀ j : Fin 256,66*256+j.val < 29241 → productCondition (66*256+j.val) := by decide +kernel

theorem product_block_67 : ∀ j : Fin 256,67*256+j.val < 29241 → productCondition (67*256+j.val) := by decide +kernel

theorem product_block_68 : ∀ j : Fin 256,68*256+j.val < 29241 → productCondition (68*256+j.val) := by decide +kernel

theorem product_block_69 : ∀ j : Fin 256,69*256+j.val < 29241 → productCondition (69*256+j.val) := by decide +kernel

theorem product_block_70 : ∀ j : Fin 256,70*256+j.val < 29241 → productCondition (70*256+j.val) := by decide +kernel

theorem product_block_71 : ∀ j : Fin 256,71*256+j.val < 29241 → productCondition (71*256+j.val) := by decide +kernel

theorem product_block_72 : ∀ j : Fin 256,72*256+j.val < 29241 → productCondition (72*256+j.val) := by decide +kernel

theorem product_block_73 : ∀ j : Fin 256,73*256+j.val < 29241 → productCondition (73*256+j.val) := by decide +kernel

theorem product_block_74 : ∀ j : Fin 256,74*256+j.val < 29241 → productCondition (74*256+j.val) := by decide +kernel

theorem product_block_75 : ∀ j : Fin 256,75*256+j.val < 29241 → productCondition (75*256+j.val) := by decide +kernel

theorem product_block_76 : ∀ j : Fin 256,76*256+j.val < 29241 → productCondition (76*256+j.val) := by decide +kernel

theorem product_block_77 : ∀ j : Fin 256,77*256+j.val < 29241 → productCondition (77*256+j.val) := by decide +kernel

theorem product_block_78 : ∀ j : Fin 256,78*256+j.val < 29241 → productCondition (78*256+j.val) := by decide +kernel

theorem product_block_79 : ∀ j : Fin 256,79*256+j.val < 29241 → productCondition (79*256+j.val) := by decide +kernel

theorem product_block_80 : ∀ j : Fin 256,80*256+j.val < 29241 → productCondition (80*256+j.val) := by decide +kernel

theorem product_block_81 : ∀ j : Fin 256,81*256+j.val < 29241 → productCondition (81*256+j.val) := by decide +kernel

theorem product_block_82 : ∀ j : Fin 256,82*256+j.val < 29241 → productCondition (82*256+j.val) := by decide +kernel

theorem product_block_83 : ∀ j : Fin 256,83*256+j.val < 29241 → productCondition (83*256+j.val) := by decide +kernel

theorem product_block_84 : ∀ j : Fin 256,84*256+j.val < 29241 → productCondition (84*256+j.val) := by decide +kernel

theorem product_block_85 : ∀ j : Fin 256,85*256+j.val < 29241 → productCondition (85*256+j.val) := by decide +kernel

theorem product_block_86 : ∀ j : Fin 256,86*256+j.val < 29241 → productCondition (86*256+j.val) := by decide +kernel

theorem product_block_87 : ∀ j : Fin 256,87*256+j.val < 29241 → productCondition (87*256+j.val) := by decide +kernel

theorem product_block_88 : ∀ j : Fin 256,88*256+j.val < 29241 → productCondition (88*256+j.val) := by decide +kernel

theorem product_block_89 : ∀ j : Fin 256,89*256+j.val < 29241 → productCondition (89*256+j.val) := by decide +kernel

theorem product_block_90 : ∀ j : Fin 256,90*256+j.val < 29241 → productCondition (90*256+j.val) := by decide +kernel

theorem product_block_91 : ∀ j : Fin 256,91*256+j.val < 29241 → productCondition (91*256+j.val) := by decide +kernel

theorem product_block_92 : ∀ j : Fin 256,92*256+j.val < 29241 → productCondition (92*256+j.val) := by decide +kernel

theorem product_block_93 : ∀ j : Fin 256,93*256+j.val < 29241 → productCondition (93*256+j.val) := by decide +kernel

theorem product_block_94 : ∀ j : Fin 256,94*256+j.val < 29241 → productCondition (94*256+j.val) := by decide +kernel

theorem product_block_95 : ∀ j : Fin 256,95*256+j.val < 29241 → productCondition (95*256+j.val) := by decide +kernel

theorem product_block_96 : ∀ j : Fin 256,96*256+j.val < 29241 → productCondition (96*256+j.val) := by decide +kernel

theorem product_block_97 : ∀ j : Fin 256,97*256+j.val < 29241 → productCondition (97*256+j.val) := by decide +kernel

theorem product_block_98 : ∀ j : Fin 256,98*256+j.val < 29241 → productCondition (98*256+j.val) := by decide +kernel

theorem product_block_99 : ∀ j : Fin 256,99*256+j.val < 29241 → productCondition (99*256+j.val) := by decide +kernel

theorem product_block_100 : ∀ j : Fin 256,100*256+j.val < 29241 → productCondition (100*256+j.val) := by decide +kernel

theorem product_block_101 : ∀ j : Fin 256,101*256+j.val < 29241 → productCondition (101*256+j.val) := by decide +kernel

theorem product_block_102 : ∀ j : Fin 256,102*256+j.val < 29241 → productCondition (102*256+j.val) := by decide +kernel

theorem product_block_103 : ∀ j : Fin 256,103*256+j.val < 29241 → productCondition (103*256+j.val) := by decide +kernel

theorem product_block_104 : ∀ j : Fin 256,104*256+j.val < 29241 → productCondition (104*256+j.val) := by decide +kernel

theorem product_block_105 : ∀ j : Fin 256,105*256+j.val < 29241 → productCondition (105*256+j.val) := by decide +kernel

theorem product_block_106 : ∀ j : Fin 256,106*256+j.val < 29241 → productCondition (106*256+j.val) := by decide +kernel

theorem product_block_107 : ∀ j : Fin 256,107*256+j.val < 29241 → productCondition (107*256+j.val) := by decide +kernel

theorem product_block_108 : ∀ j : Fin 256,108*256+j.val < 29241 → productCondition (108*256+j.val) := by decide +kernel

theorem product_block_109 : ∀ j : Fin 256,109*256+j.val < 29241 → productCondition (109*256+j.val) := by decide +kernel

theorem product_block_110 : ∀ j : Fin 256,110*256+j.val < 29241 → productCondition (110*256+j.val) := by decide +kernel

theorem product_block_111 : ∀ j : Fin 256,111*256+j.val < 29241 → productCondition (111*256+j.val) := by decide +kernel

theorem product_block_112 : ∀ j : Fin 256,112*256+j.val < 29241 → productCondition (112*256+j.val) := by decide +kernel

theorem product_block_113 : ∀ j : Fin 256,113*256+j.val < 29241 → productCondition (113*256+j.val) := by decide +kernel

theorem product_block_114 : ∀ j : Fin 256,114*256+j.val < 29241 → productCondition (114*256+j.val) := by decide +kernel

theorem product_all : ∀ i,i < 29241 → productCondition i := by
  apply forall_lt_of_fin_chunks productCondition 29241 256 (by decide)
  intro k
  fin_cases k
  · exact product_block_0
  · exact product_block_1
  · exact product_block_2
  · exact product_block_3
  · exact product_block_4
  · exact product_block_5
  · exact product_block_6
  · exact product_block_7
  · exact product_block_8
  · exact product_block_9
  · exact product_block_10
  · exact product_block_11
  · exact product_block_12
  · exact product_block_13
  · exact product_block_14
  · exact product_block_15
  · exact product_block_16
  · exact product_block_17
  · exact product_block_18
  · exact product_block_19
  · exact product_block_20
  · exact product_block_21
  · exact product_block_22
  · exact product_block_23
  · exact product_block_24
  · exact product_block_25
  · exact product_block_26
  · exact product_block_27
  · exact product_block_28
  · exact product_block_29
  · exact product_block_30
  · exact product_block_31
  · exact product_block_32
  · exact product_block_33
  · exact product_block_34
  · exact product_block_35
  · exact product_block_36
  · exact product_block_37
  · exact product_block_38
  · exact product_block_39
  · exact product_block_40
  · exact product_block_41
  · exact product_block_42
  · exact product_block_43
  · exact product_block_44
  · exact product_block_45
  · exact product_block_46
  · exact product_block_47
  · exact product_block_48
  · exact product_block_49
  · exact product_block_50
  · exact product_block_51
  · exact product_block_52
  · exact product_block_53
  · exact product_block_54
  · exact product_block_55
  · exact product_block_56
  · exact product_block_57
  · exact product_block_58
  · exact product_block_59
  · exact product_block_60
  · exact product_block_61
  · exact product_block_62
  · exact product_block_63
  · exact product_block_64
  · exact product_block_65
  · exact product_block_66
  · exact product_block_67
  · exact product_block_68
  · exact product_block_69
  · exact product_block_70
  · exact product_block_71
  · exact product_block_72
  · exact product_block_73
  · exact product_block_74
  · exact product_block_75
  · exact product_block_76
  · exact product_block_77
  · exact product_block_78
  · exact product_block_79
  · exact product_block_80
  · exact product_block_81
  · exact product_block_82
  · exact product_block_83
  · exact product_block_84
  · exact product_block_85
  · exact product_block_86
  · exact product_block_87
  · exact product_block_88
  · exact product_block_89
  · exact product_block_90
  · exact product_block_91
  · exact product_block_92
  · exact product_block_93
  · exact product_block_94
  · exact product_block_95
  · exact product_block_96
  · exact product_block_97
  · exact product_block_98
  · exact product_block_99
  · exact product_block_100
  · exact product_block_101
  · exact product_block_102
  · exact product_block_103
  · exact product_block_104
  · exact product_block_105
  · exact product_block_106
  · exact product_block_107
  · exact product_block_108
  · exact product_block_109
  · exact product_block_110
  · exact product_block_111
  · exact product_block_112
  · exact product_block_113
  · exact product_block_114

end Quartic.FiniteEndpointMetadata18
