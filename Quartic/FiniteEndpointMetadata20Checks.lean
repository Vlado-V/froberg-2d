import Quartic.FiniteEndpointMetadata20Data
open Quartic.FiniteEndpointMetadata20Data Quartic.FiniteEndpointCheckerPolynomial
open Quartic.FiniteEndpointChunks
set_option maxRecDepth 1000000
set_option maxHeartbeats 32000000
set_option Elab.async false
noncomputable section
namespace Quartic.FiniteEndpointMetadata20

def quarticCondition (i : ℕ) : Prop :=
  let k : Fin 8855 := ⟨i%8855,Nat.mod_lt _ (by decide)⟩
  tupleRank 20 0 (vars4 k)=i ∧ (vars4 k).Pairwise (· ≤ ·) ∧
  selectedGenerator i < 48 ∧ selectedMultiplier i < 210 ∧
  (i < 8789 → selectedGenerator i < 47)

def productCondition (k : ℕ) : Prop :=
  let i : Fin 210 := ⟨k/210%210,Nat.mod_lt _ (by decide)⟩
  let j : Fin 210 := ⟨k%210,Nat.mod_lt _ (by decide)⟩
  naturalProduct i.val j.val < 8855 ∧
  vars4 (productIndex i j) = (vars2 i ++ vars2 j).insertionSort (· ≤ ·)

instance (i : ℕ) : Decidable (quarticCondition i) := inferInstanceAs (Decidable (_ ∧ _))
instance (i : ℕ) : Decidable (productCondition i) := inferInstanceAs (Decidable (_ ∧ _))

theorem quad_checked : ∀ i : Fin 210,tupleRank 20 0 (vars2 i)=i.val ∧
    (vars2 i).Pairwise (· ≤ ·) := by decide +kernel

theorem quartic_block_0 : ∀ j : Fin 256,0*256+j.val < 8855 → quarticCondition (0*256+j.val) := by decide +kernel

theorem quartic_block_1 : ∀ j : Fin 256,1*256+j.val < 8855 → quarticCondition (1*256+j.val) := by decide +kernel

theorem quartic_block_2 : ∀ j : Fin 256,2*256+j.val < 8855 → quarticCondition (2*256+j.val) := by decide +kernel

theorem quartic_block_3 : ∀ j : Fin 256,3*256+j.val < 8855 → quarticCondition (3*256+j.val) := by decide +kernel

theorem quartic_block_4 : ∀ j : Fin 256,4*256+j.val < 8855 → quarticCondition (4*256+j.val) := by decide +kernel

theorem quartic_block_5 : ∀ j : Fin 256,5*256+j.val < 8855 → quarticCondition (5*256+j.val) := by decide +kernel

theorem quartic_block_6 : ∀ j : Fin 256,6*256+j.val < 8855 → quarticCondition (6*256+j.val) := by decide +kernel

theorem quartic_block_7 : ∀ j : Fin 256,7*256+j.val < 8855 → quarticCondition (7*256+j.val) := by decide +kernel

theorem quartic_block_8 : ∀ j : Fin 256,8*256+j.val < 8855 → quarticCondition (8*256+j.val) := by decide +kernel

theorem quartic_block_9 : ∀ j : Fin 256,9*256+j.val < 8855 → quarticCondition (9*256+j.val) := by decide +kernel

theorem quartic_block_10 : ∀ j : Fin 256,10*256+j.val < 8855 → quarticCondition (10*256+j.val) := by decide +kernel

theorem quartic_block_11 : ∀ j : Fin 256,11*256+j.val < 8855 → quarticCondition (11*256+j.val) := by decide +kernel

theorem quartic_block_12 : ∀ j : Fin 256,12*256+j.val < 8855 → quarticCondition (12*256+j.val) := by decide +kernel

theorem quartic_block_13 : ∀ j : Fin 256,13*256+j.val < 8855 → quarticCondition (13*256+j.val) := by decide +kernel

theorem quartic_block_14 : ∀ j : Fin 256,14*256+j.val < 8855 → quarticCondition (14*256+j.val) := by decide +kernel

theorem quartic_block_15 : ∀ j : Fin 256,15*256+j.val < 8855 → quarticCondition (15*256+j.val) := by decide +kernel

theorem quartic_block_16 : ∀ j : Fin 256,16*256+j.val < 8855 → quarticCondition (16*256+j.val) := by decide +kernel

theorem quartic_block_17 : ∀ j : Fin 256,17*256+j.val < 8855 → quarticCondition (17*256+j.val) := by decide +kernel

theorem quartic_block_18 : ∀ j : Fin 256,18*256+j.val < 8855 → quarticCondition (18*256+j.val) := by decide +kernel

theorem quartic_block_19 : ∀ j : Fin 256,19*256+j.val < 8855 → quarticCondition (19*256+j.val) := by decide +kernel

theorem quartic_block_20 : ∀ j : Fin 256,20*256+j.val < 8855 → quarticCondition (20*256+j.val) := by decide +kernel

theorem quartic_block_21 : ∀ j : Fin 256,21*256+j.val < 8855 → quarticCondition (21*256+j.val) := by decide +kernel

theorem quartic_block_22 : ∀ j : Fin 256,22*256+j.val < 8855 → quarticCondition (22*256+j.val) := by decide +kernel

theorem quartic_block_23 : ∀ j : Fin 256,23*256+j.val < 8855 → quarticCondition (23*256+j.val) := by decide +kernel

theorem quartic_block_24 : ∀ j : Fin 256,24*256+j.val < 8855 → quarticCondition (24*256+j.val) := by decide +kernel

theorem quartic_block_25 : ∀ j : Fin 256,25*256+j.val < 8855 → quarticCondition (25*256+j.val) := by decide +kernel

theorem quartic_block_26 : ∀ j : Fin 256,26*256+j.val < 8855 → quarticCondition (26*256+j.val) := by decide +kernel

theorem quartic_block_27 : ∀ j : Fin 256,27*256+j.val < 8855 → quarticCondition (27*256+j.val) := by decide +kernel

theorem quartic_block_28 : ∀ j : Fin 256,28*256+j.val < 8855 → quarticCondition (28*256+j.val) := by decide +kernel

theorem quartic_block_29 : ∀ j : Fin 256,29*256+j.val < 8855 → quarticCondition (29*256+j.val) := by decide +kernel

theorem quartic_block_30 : ∀ j : Fin 256,30*256+j.val < 8855 → quarticCondition (30*256+j.val) := by decide +kernel

theorem quartic_block_31 : ∀ j : Fin 256,31*256+j.val < 8855 → quarticCondition (31*256+j.val) := by decide +kernel

theorem quartic_block_32 : ∀ j : Fin 256,32*256+j.val < 8855 → quarticCondition (32*256+j.val) := by decide +kernel

theorem quartic_block_33 : ∀ j : Fin 256,33*256+j.val < 8855 → quarticCondition (33*256+j.val) := by decide +kernel

theorem quartic_block_34 : ∀ j : Fin 256,34*256+j.val < 8855 → quarticCondition (34*256+j.val) := by decide +kernel

theorem quartic_all : ∀ i,i < 8855 → quarticCondition i := by
  apply forall_lt_of_fin_chunks quarticCondition 8855 256 (by decide)
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
  · exact quartic_block_24
  · exact quartic_block_25
  · exact quartic_block_26
  · exact quartic_block_27
  · exact quartic_block_28
  · exact quartic_block_29
  · exact quartic_block_30
  · exact quartic_block_31
  · exact quartic_block_32
  · exact quartic_block_33
  · exact quartic_block_34

theorem product_block_0 : ∀ j : Fin 256,0*256+j.val < 44100 → productCondition (0*256+j.val) := by decide +kernel

theorem product_block_1 : ∀ j : Fin 256,1*256+j.val < 44100 → productCondition (1*256+j.val) := by decide +kernel

theorem product_block_2 : ∀ j : Fin 256,2*256+j.val < 44100 → productCondition (2*256+j.val) := by decide +kernel

theorem product_block_3 : ∀ j : Fin 256,3*256+j.val < 44100 → productCondition (3*256+j.val) := by decide +kernel

theorem product_block_4 : ∀ j : Fin 256,4*256+j.val < 44100 → productCondition (4*256+j.val) := by decide +kernel

theorem product_block_5 : ∀ j : Fin 256,5*256+j.val < 44100 → productCondition (5*256+j.val) := by decide +kernel

theorem product_block_6 : ∀ j : Fin 256,6*256+j.val < 44100 → productCondition (6*256+j.val) := by decide +kernel

theorem product_block_7 : ∀ j : Fin 256,7*256+j.val < 44100 → productCondition (7*256+j.val) := by decide +kernel

theorem product_block_8 : ∀ j : Fin 256,8*256+j.val < 44100 → productCondition (8*256+j.val) := by decide +kernel

theorem product_block_9 : ∀ j : Fin 256,9*256+j.val < 44100 → productCondition (9*256+j.val) := by decide +kernel

theorem product_block_10 : ∀ j : Fin 256,10*256+j.val < 44100 → productCondition (10*256+j.val) := by decide +kernel

theorem product_block_11 : ∀ j : Fin 256,11*256+j.val < 44100 → productCondition (11*256+j.val) := by decide +kernel

theorem product_block_12 : ∀ j : Fin 256,12*256+j.val < 44100 → productCondition (12*256+j.val) := by decide +kernel

theorem product_block_13 : ∀ j : Fin 256,13*256+j.val < 44100 → productCondition (13*256+j.val) := by decide +kernel

theorem product_block_14 : ∀ j : Fin 256,14*256+j.val < 44100 → productCondition (14*256+j.val) := by decide +kernel

theorem product_block_15 : ∀ j : Fin 256,15*256+j.val < 44100 → productCondition (15*256+j.val) := by decide +kernel

theorem product_block_16 : ∀ j : Fin 256,16*256+j.val < 44100 → productCondition (16*256+j.val) := by decide +kernel

theorem product_block_17 : ∀ j : Fin 256,17*256+j.val < 44100 → productCondition (17*256+j.val) := by decide +kernel

theorem product_block_18 : ∀ j : Fin 256,18*256+j.val < 44100 → productCondition (18*256+j.val) := by decide +kernel

theorem product_block_19 : ∀ j : Fin 256,19*256+j.val < 44100 → productCondition (19*256+j.val) := by decide +kernel

theorem product_block_20 : ∀ j : Fin 256,20*256+j.val < 44100 → productCondition (20*256+j.val) := by decide +kernel

theorem product_block_21 : ∀ j : Fin 256,21*256+j.val < 44100 → productCondition (21*256+j.val) := by decide +kernel

theorem product_block_22 : ∀ j : Fin 256,22*256+j.val < 44100 → productCondition (22*256+j.val) := by decide +kernel

theorem product_block_23 : ∀ j : Fin 256,23*256+j.val < 44100 → productCondition (23*256+j.val) := by decide +kernel

theorem product_block_24 : ∀ j : Fin 256,24*256+j.val < 44100 → productCondition (24*256+j.val) := by decide +kernel

theorem product_block_25 : ∀ j : Fin 256,25*256+j.val < 44100 → productCondition (25*256+j.val) := by decide +kernel

theorem product_block_26 : ∀ j : Fin 256,26*256+j.val < 44100 → productCondition (26*256+j.val) := by decide +kernel

theorem product_block_27 : ∀ j : Fin 256,27*256+j.val < 44100 → productCondition (27*256+j.val) := by decide +kernel

theorem product_block_28 : ∀ j : Fin 256,28*256+j.val < 44100 → productCondition (28*256+j.val) := by decide +kernel

theorem product_block_29 : ∀ j : Fin 256,29*256+j.val < 44100 → productCondition (29*256+j.val) := by decide +kernel

theorem product_block_30 : ∀ j : Fin 256,30*256+j.val < 44100 → productCondition (30*256+j.val) := by decide +kernel

theorem product_block_31 : ∀ j : Fin 256,31*256+j.val < 44100 → productCondition (31*256+j.val) := by decide +kernel

theorem product_block_32 : ∀ j : Fin 256,32*256+j.val < 44100 → productCondition (32*256+j.val) := by decide +kernel

theorem product_block_33 : ∀ j : Fin 256,33*256+j.val < 44100 → productCondition (33*256+j.val) := by decide +kernel

theorem product_block_34 : ∀ j : Fin 256,34*256+j.val < 44100 → productCondition (34*256+j.val) := by decide +kernel

theorem product_block_35 : ∀ j : Fin 256,35*256+j.val < 44100 → productCondition (35*256+j.val) := by decide +kernel

theorem product_block_36 : ∀ j : Fin 256,36*256+j.val < 44100 → productCondition (36*256+j.val) := by decide +kernel

theorem product_block_37 : ∀ j : Fin 256,37*256+j.val < 44100 → productCondition (37*256+j.val) := by decide +kernel

theorem product_block_38 : ∀ j : Fin 256,38*256+j.val < 44100 → productCondition (38*256+j.val) := by decide +kernel

theorem product_block_39 : ∀ j : Fin 256,39*256+j.val < 44100 → productCondition (39*256+j.val) := by decide +kernel

theorem product_block_40 : ∀ j : Fin 256,40*256+j.val < 44100 → productCondition (40*256+j.val) := by decide +kernel

theorem product_block_41 : ∀ j : Fin 256,41*256+j.val < 44100 → productCondition (41*256+j.val) := by decide +kernel

theorem product_block_42 : ∀ j : Fin 256,42*256+j.val < 44100 → productCondition (42*256+j.val) := by decide +kernel

theorem product_block_43 : ∀ j : Fin 256,43*256+j.val < 44100 → productCondition (43*256+j.val) := by decide +kernel

theorem product_block_44 : ∀ j : Fin 256,44*256+j.val < 44100 → productCondition (44*256+j.val) := by decide +kernel

theorem product_block_45 : ∀ j : Fin 256,45*256+j.val < 44100 → productCondition (45*256+j.val) := by decide +kernel

theorem product_block_46 : ∀ j : Fin 256,46*256+j.val < 44100 → productCondition (46*256+j.val) := by decide +kernel

theorem product_block_47 : ∀ j : Fin 256,47*256+j.val < 44100 → productCondition (47*256+j.val) := by decide +kernel

theorem product_block_48 : ∀ j : Fin 256,48*256+j.val < 44100 → productCondition (48*256+j.val) := by decide +kernel

theorem product_block_49 : ∀ j : Fin 256,49*256+j.val < 44100 → productCondition (49*256+j.val) := by decide +kernel

theorem product_block_50 : ∀ j : Fin 256,50*256+j.val < 44100 → productCondition (50*256+j.val) := by decide +kernel

theorem product_block_51 : ∀ j : Fin 256,51*256+j.val < 44100 → productCondition (51*256+j.val) := by decide +kernel

theorem product_block_52 : ∀ j : Fin 256,52*256+j.val < 44100 → productCondition (52*256+j.val) := by decide +kernel

theorem product_block_53 : ∀ j : Fin 256,53*256+j.val < 44100 → productCondition (53*256+j.val) := by decide +kernel

theorem product_block_54 : ∀ j : Fin 256,54*256+j.val < 44100 → productCondition (54*256+j.val) := by decide +kernel

theorem product_block_55 : ∀ j : Fin 256,55*256+j.val < 44100 → productCondition (55*256+j.val) := by decide +kernel

theorem product_block_56 : ∀ j : Fin 256,56*256+j.val < 44100 → productCondition (56*256+j.val) := by decide +kernel

theorem product_block_57 : ∀ j : Fin 256,57*256+j.val < 44100 → productCondition (57*256+j.val) := by decide +kernel

theorem product_block_58 : ∀ j : Fin 256,58*256+j.val < 44100 → productCondition (58*256+j.val) := by decide +kernel

theorem product_block_59 : ∀ j : Fin 256,59*256+j.val < 44100 → productCondition (59*256+j.val) := by decide +kernel

theorem product_block_60 : ∀ j : Fin 256,60*256+j.val < 44100 → productCondition (60*256+j.val) := by decide +kernel

theorem product_block_61 : ∀ j : Fin 256,61*256+j.val < 44100 → productCondition (61*256+j.val) := by decide +kernel

theorem product_block_62 : ∀ j : Fin 256,62*256+j.val < 44100 → productCondition (62*256+j.val) := by decide +kernel

theorem product_block_63 : ∀ j : Fin 256,63*256+j.val < 44100 → productCondition (63*256+j.val) := by decide +kernel

theorem product_block_64 : ∀ j : Fin 256,64*256+j.val < 44100 → productCondition (64*256+j.val) := by decide +kernel

theorem product_block_65 : ∀ j : Fin 256,65*256+j.val < 44100 → productCondition (65*256+j.val) := by decide +kernel

theorem product_block_66 : ∀ j : Fin 256,66*256+j.val < 44100 → productCondition (66*256+j.val) := by decide +kernel

theorem product_block_67 : ∀ j : Fin 256,67*256+j.val < 44100 → productCondition (67*256+j.val) := by decide +kernel

theorem product_block_68 : ∀ j : Fin 256,68*256+j.val < 44100 → productCondition (68*256+j.val) := by decide +kernel

theorem product_block_69 : ∀ j : Fin 256,69*256+j.val < 44100 → productCondition (69*256+j.val) := by decide +kernel

theorem product_block_70 : ∀ j : Fin 256,70*256+j.val < 44100 → productCondition (70*256+j.val) := by decide +kernel

theorem product_block_71 : ∀ j : Fin 256,71*256+j.val < 44100 → productCondition (71*256+j.val) := by decide +kernel

theorem product_block_72 : ∀ j : Fin 256,72*256+j.val < 44100 → productCondition (72*256+j.val) := by decide +kernel

theorem product_block_73 : ∀ j : Fin 256,73*256+j.val < 44100 → productCondition (73*256+j.val) := by decide +kernel

theorem product_block_74 : ∀ j : Fin 256,74*256+j.val < 44100 → productCondition (74*256+j.val) := by decide +kernel

theorem product_block_75 : ∀ j : Fin 256,75*256+j.val < 44100 → productCondition (75*256+j.val) := by decide +kernel

theorem product_block_76 : ∀ j : Fin 256,76*256+j.val < 44100 → productCondition (76*256+j.val) := by decide +kernel

theorem product_block_77 : ∀ j : Fin 256,77*256+j.val < 44100 → productCondition (77*256+j.val) := by decide +kernel

theorem product_block_78 : ∀ j : Fin 256,78*256+j.val < 44100 → productCondition (78*256+j.val) := by decide +kernel

theorem product_block_79 : ∀ j : Fin 256,79*256+j.val < 44100 → productCondition (79*256+j.val) := by decide +kernel

theorem product_block_80 : ∀ j : Fin 256,80*256+j.val < 44100 → productCondition (80*256+j.val) := by decide +kernel

theorem product_block_81 : ∀ j : Fin 256,81*256+j.val < 44100 → productCondition (81*256+j.val) := by decide +kernel

theorem product_block_82 : ∀ j : Fin 256,82*256+j.val < 44100 → productCondition (82*256+j.val) := by decide +kernel

theorem product_block_83 : ∀ j : Fin 256,83*256+j.val < 44100 → productCondition (83*256+j.val) := by decide +kernel

theorem product_block_84 : ∀ j : Fin 256,84*256+j.val < 44100 → productCondition (84*256+j.val) := by decide +kernel

theorem product_block_85 : ∀ j : Fin 256,85*256+j.val < 44100 → productCondition (85*256+j.val) := by decide +kernel

theorem product_block_86 : ∀ j : Fin 256,86*256+j.val < 44100 → productCondition (86*256+j.val) := by decide +kernel

theorem product_block_87 : ∀ j : Fin 256,87*256+j.val < 44100 → productCondition (87*256+j.val) := by decide +kernel

theorem product_block_88 : ∀ j : Fin 256,88*256+j.val < 44100 → productCondition (88*256+j.val) := by decide +kernel

theorem product_block_89 : ∀ j : Fin 256,89*256+j.val < 44100 → productCondition (89*256+j.val) := by decide +kernel

theorem product_block_90 : ∀ j : Fin 256,90*256+j.val < 44100 → productCondition (90*256+j.val) := by decide +kernel

theorem product_block_91 : ∀ j : Fin 256,91*256+j.val < 44100 → productCondition (91*256+j.val) := by decide +kernel

theorem product_block_92 : ∀ j : Fin 256,92*256+j.val < 44100 → productCondition (92*256+j.val) := by decide +kernel

theorem product_block_93 : ∀ j : Fin 256,93*256+j.val < 44100 → productCondition (93*256+j.val) := by decide +kernel

theorem product_block_94 : ∀ j : Fin 256,94*256+j.val < 44100 → productCondition (94*256+j.val) := by decide +kernel

theorem product_block_95 : ∀ j : Fin 256,95*256+j.val < 44100 → productCondition (95*256+j.val) := by decide +kernel

theorem product_block_96 : ∀ j : Fin 256,96*256+j.val < 44100 → productCondition (96*256+j.val) := by decide +kernel

theorem product_block_97 : ∀ j : Fin 256,97*256+j.val < 44100 → productCondition (97*256+j.val) := by decide +kernel

theorem product_block_98 : ∀ j : Fin 256,98*256+j.val < 44100 → productCondition (98*256+j.val) := by decide +kernel

theorem product_block_99 : ∀ j : Fin 256,99*256+j.val < 44100 → productCondition (99*256+j.val) := by decide +kernel

theorem product_block_100 : ∀ j : Fin 256,100*256+j.val < 44100 → productCondition (100*256+j.val) := by decide +kernel

theorem product_block_101 : ∀ j : Fin 256,101*256+j.val < 44100 → productCondition (101*256+j.val) := by decide +kernel

theorem product_block_102 : ∀ j : Fin 256,102*256+j.val < 44100 → productCondition (102*256+j.val) := by decide +kernel

theorem product_block_103 : ∀ j : Fin 256,103*256+j.val < 44100 → productCondition (103*256+j.val) := by decide +kernel

theorem product_block_104 : ∀ j : Fin 256,104*256+j.val < 44100 → productCondition (104*256+j.val) := by decide +kernel

theorem product_block_105 : ∀ j : Fin 256,105*256+j.val < 44100 → productCondition (105*256+j.val) := by decide +kernel

theorem product_block_106 : ∀ j : Fin 256,106*256+j.val < 44100 → productCondition (106*256+j.val) := by decide +kernel

theorem product_block_107 : ∀ j : Fin 256,107*256+j.val < 44100 → productCondition (107*256+j.val) := by decide +kernel

theorem product_block_108 : ∀ j : Fin 256,108*256+j.val < 44100 → productCondition (108*256+j.val) := by decide +kernel

theorem product_block_109 : ∀ j : Fin 256,109*256+j.val < 44100 → productCondition (109*256+j.val) := by decide +kernel

theorem product_block_110 : ∀ j : Fin 256,110*256+j.val < 44100 → productCondition (110*256+j.val) := by decide +kernel

theorem product_block_111 : ∀ j : Fin 256,111*256+j.val < 44100 → productCondition (111*256+j.val) := by decide +kernel

theorem product_block_112 : ∀ j : Fin 256,112*256+j.val < 44100 → productCondition (112*256+j.val) := by decide +kernel

theorem product_block_113 : ∀ j : Fin 256,113*256+j.val < 44100 → productCondition (113*256+j.val) := by decide +kernel

theorem product_block_114 : ∀ j : Fin 256,114*256+j.val < 44100 → productCondition (114*256+j.val) := by decide +kernel

theorem product_block_115 : ∀ j : Fin 256,115*256+j.val < 44100 → productCondition (115*256+j.val) := by decide +kernel

theorem product_block_116 : ∀ j : Fin 256,116*256+j.val < 44100 → productCondition (116*256+j.val) := by decide +kernel

theorem product_block_117 : ∀ j : Fin 256,117*256+j.val < 44100 → productCondition (117*256+j.val) := by decide +kernel

theorem product_block_118 : ∀ j : Fin 256,118*256+j.val < 44100 → productCondition (118*256+j.val) := by decide +kernel

theorem product_block_119 : ∀ j : Fin 256,119*256+j.val < 44100 → productCondition (119*256+j.val) := by decide +kernel

theorem product_block_120 : ∀ j : Fin 256,120*256+j.val < 44100 → productCondition (120*256+j.val) := by decide +kernel

theorem product_block_121 : ∀ j : Fin 256,121*256+j.val < 44100 → productCondition (121*256+j.val) := by decide +kernel

theorem product_block_122 : ∀ j : Fin 256,122*256+j.val < 44100 → productCondition (122*256+j.val) := by decide +kernel

theorem product_block_123 : ∀ j : Fin 256,123*256+j.val < 44100 → productCondition (123*256+j.val) := by decide +kernel

theorem product_block_124 : ∀ j : Fin 256,124*256+j.val < 44100 → productCondition (124*256+j.val) := by decide +kernel

theorem product_block_125 : ∀ j : Fin 256,125*256+j.val < 44100 → productCondition (125*256+j.val) := by decide +kernel

theorem product_block_126 : ∀ j : Fin 256,126*256+j.val < 44100 → productCondition (126*256+j.val) := by decide +kernel

theorem product_block_127 : ∀ j : Fin 256,127*256+j.val < 44100 → productCondition (127*256+j.val) := by decide +kernel

theorem product_block_128 : ∀ j : Fin 256,128*256+j.val < 44100 → productCondition (128*256+j.val) := by decide +kernel

theorem product_block_129 : ∀ j : Fin 256,129*256+j.val < 44100 → productCondition (129*256+j.val) := by decide +kernel

theorem product_block_130 : ∀ j : Fin 256,130*256+j.val < 44100 → productCondition (130*256+j.val) := by decide +kernel

theorem product_block_131 : ∀ j : Fin 256,131*256+j.val < 44100 → productCondition (131*256+j.val) := by decide +kernel

theorem product_block_132 : ∀ j : Fin 256,132*256+j.val < 44100 → productCondition (132*256+j.val) := by decide +kernel

theorem product_block_133 : ∀ j : Fin 256,133*256+j.val < 44100 → productCondition (133*256+j.val) := by decide +kernel

theorem product_block_134 : ∀ j : Fin 256,134*256+j.val < 44100 → productCondition (134*256+j.val) := by decide +kernel

theorem product_block_135 : ∀ j : Fin 256,135*256+j.val < 44100 → productCondition (135*256+j.val) := by decide +kernel

theorem product_block_136 : ∀ j : Fin 256,136*256+j.val < 44100 → productCondition (136*256+j.val) := by decide +kernel

theorem product_block_137 : ∀ j : Fin 256,137*256+j.val < 44100 → productCondition (137*256+j.val) := by decide +kernel

theorem product_block_138 : ∀ j : Fin 256,138*256+j.val < 44100 → productCondition (138*256+j.val) := by decide +kernel

theorem product_block_139 : ∀ j : Fin 256,139*256+j.val < 44100 → productCondition (139*256+j.val) := by decide +kernel

theorem product_block_140 : ∀ j : Fin 256,140*256+j.val < 44100 → productCondition (140*256+j.val) := by decide +kernel

theorem product_block_141 : ∀ j : Fin 256,141*256+j.val < 44100 → productCondition (141*256+j.val) := by decide +kernel

theorem product_block_142 : ∀ j : Fin 256,142*256+j.val < 44100 → productCondition (142*256+j.val) := by decide +kernel

theorem product_block_143 : ∀ j : Fin 256,143*256+j.val < 44100 → productCondition (143*256+j.val) := by decide +kernel

theorem product_block_144 : ∀ j : Fin 256,144*256+j.val < 44100 → productCondition (144*256+j.val) := by decide +kernel

theorem product_block_145 : ∀ j : Fin 256,145*256+j.val < 44100 → productCondition (145*256+j.val) := by decide +kernel

theorem product_block_146 : ∀ j : Fin 256,146*256+j.val < 44100 → productCondition (146*256+j.val) := by decide +kernel

theorem product_block_147 : ∀ j : Fin 256,147*256+j.val < 44100 → productCondition (147*256+j.val) := by decide +kernel

theorem product_block_148 : ∀ j : Fin 256,148*256+j.val < 44100 → productCondition (148*256+j.val) := by decide +kernel

theorem product_block_149 : ∀ j : Fin 256,149*256+j.val < 44100 → productCondition (149*256+j.val) := by decide +kernel

theorem product_block_150 : ∀ j : Fin 256,150*256+j.val < 44100 → productCondition (150*256+j.val) := by decide +kernel

theorem product_block_151 : ∀ j : Fin 256,151*256+j.val < 44100 → productCondition (151*256+j.val) := by decide +kernel

theorem product_block_152 : ∀ j : Fin 256,152*256+j.val < 44100 → productCondition (152*256+j.val) := by decide +kernel

theorem product_block_153 : ∀ j : Fin 256,153*256+j.val < 44100 → productCondition (153*256+j.val) := by decide +kernel

theorem product_block_154 : ∀ j : Fin 256,154*256+j.val < 44100 → productCondition (154*256+j.val) := by decide +kernel

theorem product_block_155 : ∀ j : Fin 256,155*256+j.val < 44100 → productCondition (155*256+j.val) := by decide +kernel

theorem product_block_156 : ∀ j : Fin 256,156*256+j.val < 44100 → productCondition (156*256+j.val) := by decide +kernel

theorem product_block_157 : ∀ j : Fin 256,157*256+j.val < 44100 → productCondition (157*256+j.val) := by decide +kernel

theorem product_block_158 : ∀ j : Fin 256,158*256+j.val < 44100 → productCondition (158*256+j.val) := by decide +kernel

theorem product_block_159 : ∀ j : Fin 256,159*256+j.val < 44100 → productCondition (159*256+j.val) := by decide +kernel

theorem product_block_160 : ∀ j : Fin 256,160*256+j.val < 44100 → productCondition (160*256+j.val) := by decide +kernel

theorem product_block_161 : ∀ j : Fin 256,161*256+j.val < 44100 → productCondition (161*256+j.val) := by decide +kernel

theorem product_block_162 : ∀ j : Fin 256,162*256+j.val < 44100 → productCondition (162*256+j.val) := by decide +kernel

theorem product_block_163 : ∀ j : Fin 256,163*256+j.val < 44100 → productCondition (163*256+j.val) := by decide +kernel

theorem product_block_164 : ∀ j : Fin 256,164*256+j.val < 44100 → productCondition (164*256+j.val) := by decide +kernel

theorem product_block_165 : ∀ j : Fin 256,165*256+j.val < 44100 → productCondition (165*256+j.val) := by decide +kernel

theorem product_block_166 : ∀ j : Fin 256,166*256+j.val < 44100 → productCondition (166*256+j.val) := by decide +kernel

theorem product_block_167 : ∀ j : Fin 256,167*256+j.val < 44100 → productCondition (167*256+j.val) := by decide +kernel

theorem product_block_168 : ∀ j : Fin 256,168*256+j.val < 44100 → productCondition (168*256+j.val) := by decide +kernel

theorem product_block_169 : ∀ j : Fin 256,169*256+j.val < 44100 → productCondition (169*256+j.val) := by decide +kernel

theorem product_block_170 : ∀ j : Fin 256,170*256+j.val < 44100 → productCondition (170*256+j.val) := by decide +kernel

theorem product_block_171 : ∀ j : Fin 256,171*256+j.val < 44100 → productCondition (171*256+j.val) := by decide +kernel

theorem product_block_172 : ∀ j : Fin 256,172*256+j.val < 44100 → productCondition (172*256+j.val) := by decide +kernel

theorem product_all : ∀ i,i < 44100 → productCondition i := by
  apply forall_lt_of_fin_chunks productCondition 44100 256 (by decide)
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
  · exact product_block_115
  · exact product_block_116
  · exact product_block_117
  · exact product_block_118
  · exact product_block_119
  · exact product_block_120
  · exact product_block_121
  · exact product_block_122
  · exact product_block_123
  · exact product_block_124
  · exact product_block_125
  · exact product_block_126
  · exact product_block_127
  · exact product_block_128
  · exact product_block_129
  · exact product_block_130
  · exact product_block_131
  · exact product_block_132
  · exact product_block_133
  · exact product_block_134
  · exact product_block_135
  · exact product_block_136
  · exact product_block_137
  · exact product_block_138
  · exact product_block_139
  · exact product_block_140
  · exact product_block_141
  · exact product_block_142
  · exact product_block_143
  · exact product_block_144
  · exact product_block_145
  · exact product_block_146
  · exact product_block_147
  · exact product_block_148
  · exact product_block_149
  · exact product_block_150
  · exact product_block_151
  · exact product_block_152
  · exact product_block_153
  · exact product_block_154
  · exact product_block_155
  · exact product_block_156
  · exact product_block_157
  · exact product_block_158
  · exact product_block_159
  · exact product_block_160
  · exact product_block_161
  · exact product_block_162
  · exact product_block_163
  · exact product_block_164
  · exact product_block_165
  · exact product_block_166
  · exact product_block_167
  · exact product_block_168
  · exact product_block_169
  · exact product_block_170
  · exact product_block_171
  · exact product_block_172

end Quartic.FiniteEndpointMetadata20
