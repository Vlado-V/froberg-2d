module

public import Quartic.MarkedIncidence
public import Quartic.SharpCertificate.Rational

@[expose] public section

/-!
# Marked sharp incidence certificates in core dimensions 41 through 129

The lower parent endpoint admits one additional marked scalar coefficient.
Each rational-edge inequality is certified by exact integer cubic arithmetic.
Core dimension 88, whose parent dimension 91 is an integral endpoint, is
excluded from this positive-surplus assertion.
-/

namespace Quartic.MarkedSharpCertificate

open Quartic.Counts Quartic.FiniteCounts Quartic.ProfileCertificate
open Quartic.HullCertificate Quartic.SharpCertificate

/-- The existing interval checker applied to the enlarged scalar block. -/
def checkEdge (m q c i : ℕ) (edge : Fin 6) : Bool :=
  let s := markedScalars (scalars m q c)
  let lo := edgeLower m c i edge
  let hi := edgeUpper m c i edge
  let xs := automaticIntervals s lo hi
  checkCover lo hi xs &&
    xs.all fun z => decide (ChunkValid s (edgeScale edge)
      (edgePolynomial (parameters m c i) edge) z)

def EdgeBounds (m q c i : ℕ) (edge : Fin 6) : Prop :=
  ∀ d : ℤ, SharpCertificate.Eligible m c i edge d →
    ImageBounds (markedScalars (scalars m q c))
      (sharpEdge (parameters m c i) edge d) d

/-- Soundness reuses the proved integer-to-rational cubic certificate. -/
theorem checkEdge_sound (m q c i : ℕ) (edge : Fin 6)
    (h : checkEdge m q c i edge = true) : EdgeBounds m q c i edge := by
  intro d hd
  have hr := hd.in_range
  rcases Bool.and_eq_true_iff.mp h with ⟨hcover, hvalid⟩
  obtain ⟨z, hz, hlo, hhi⟩ := checkCover_covers _
    (edgeLower m c i edge) (edgeUpper m c i edge) hcover d hr.1 hr.2
  have hzvalid : ChunkValid (markedScalars (scalars m q c)) (edgeScale edge)
      (edgePolynomial (parameters m c i) edge) z :=
    of_decide_eq_true ((List.all_eq_true.mp hvalid) z hz)
  have ho := hzvalid.1.nonnegative d hlo hhi
  have hn := hzvalid.2.nonnegative d hlo hhi
  rw [sharpEdge_eq_quotient]
  exact imageBounds_of_polynomials _ _ _ _ _ _ _ (edgeScale_pos edge) ho hn

def ConfigurationBounds (m q c : ℕ) : Prop :=
  ∀ i : Fin (coreA c + 1), ∀ edge : Fin 6, EdgeBounds m q c i edge

theorem configuration_of_checks (m q c : ℕ)
    (h : ∀ i : Fin (coreA c + 1), ∀ edge : Fin 6, checkEdge m q c i edge = true) :
    ConfigurationBounds m q c := by
  intro i edge
  exact checkEdge_sound m q c i edge (h i edge)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_41_lower : ConfigurationBounds 41 176 20 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_42_lower : ConfigurationBounds 42 184 21 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_43_lower : ConfigurationBounds 43 192 21 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_44_lower : ConfigurationBounds 44 201 21 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_45_lower : ConfigurationBounds 45 210 22 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_46_lower : ConfigurationBounds 46 218 23 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_47_lower : ConfigurationBounds 47 227 24 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_48_lower : ConfigurationBounds 48 237 23 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_49_lower : ConfigurationBounds 49 246 24 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_50_lower : ConfigurationBounds 50 256 24 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_51_lower : ConfigurationBounds 51 265 26 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_52_lower : ConfigurationBounds 52 275 26 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_53_lower : ConfigurationBounds 53 285 27 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_54_lower : ConfigurationBounds 54 296 27 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_55_lower : ConfigurationBounds 55 306 28 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_56_lower : ConfigurationBounds 56 317 28 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_57_lower : ConfigurationBounds 57 328 29 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_58_lower : ConfigurationBounds 58 339 29 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_59_lower : ConfigurationBounds 59 350 30 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_60_lower : ConfigurationBounds 60 362 30 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_61_lower : ConfigurationBounds 61 373 31 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_62_lower : ConfigurationBounds 62 385 31 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_63_lower : ConfigurationBounds 63 397 32 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_64_lower : ConfigurationBounds 64 409 33 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_65_lower : ConfigurationBounds 65 421 33 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_66_lower : ConfigurationBounds 66 434 34 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_67_lower : ConfigurationBounds 67 447 34 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_68_lower : ConfigurationBounds 68 459 35 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_69_lower : ConfigurationBounds 69 473 35 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_70_lower : ConfigurationBounds 70 486 36 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_71_lower : ConfigurationBounds 71 499 37 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_72_lower : ConfigurationBounds 72 513 37 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_73_lower : ConfigurationBounds 73 527 37 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_74_lower : ConfigurationBounds 74 541 38 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_75_lower : ConfigurationBounds 75 555 38 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_76_lower : ConfigurationBounds 76 569 39 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_77_lower : ConfigurationBounds 77 584 39 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_78_lower : ConfigurationBounds 78 598 41 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_79_lower : ConfigurationBounds 79 613 41 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_80_lower : ConfigurationBounds 80 628 42 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_81_lower : ConfigurationBounds 81 644 42 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_82_lower : ConfigurationBounds 82 659 43 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_83_lower : ConfigurationBounds 83 675 43 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_84_lower : ConfigurationBounds 84 691 43 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_85_lower : ConfigurationBounds 85 707 44 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_86_lower : ConfigurationBounds 86 723 44 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_87_lower : ConfigurationBounds 87 739 45 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_89_lower : ConfigurationBounds 89 772 47 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_90_lower : ConfigurationBounds 90 789 47 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_91_lower : ConfigurationBounds 91 806 48 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_92_lower : ConfigurationBounds 92 824 48 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_93_lower : ConfigurationBounds 93 841 49 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_94_lower : ConfigurationBounds 94 859 49 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_95_lower : ConfigurationBounds 95 877 49 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_96_lower : ConfigurationBounds 96 895 50 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_97_lower : ConfigurationBounds 97 913 51 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_98_lower : ConfigurationBounds 98 931 52 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_99_lower : ConfigurationBounds 99 950 52 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_100_lower : ConfigurationBounds 100 969 52 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_101_lower : ConfigurationBounds 101 988 53 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_102_lower : ConfigurationBounds 102 1007 53 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_103_lower : ConfigurationBounds 103 1026 54 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_104_lower : ConfigurationBounds 104 1046 54 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_105_lower : ConfigurationBounds 105 1065 55 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_106_lower : ConfigurationBounds 106 1085 56 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_107_lower : ConfigurationBounds 107 1105 56 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_108_lower : ConfigurationBounds 108 1125 57 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_109_lower : ConfigurationBounds 109 1146 57 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_110_lower : ConfigurationBounds 110 1166 58 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_111_lower : ConfigurationBounds 111 1187 59 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_112_lower : ConfigurationBounds 112 1208 59 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_113_lower : ConfigurationBounds 113 1229 60 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_114_lower : ConfigurationBounds 114 1251 60 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_115_lower : ConfigurationBounds 115 1272 61 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_116_lower : ConfigurationBounds 116 1294 61 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_117_lower : ConfigurationBounds 117 1316 61 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_118_lower : ConfigurationBounds 118 1338 62 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_119_lower : ConfigurationBounds 119 1360 63 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_120_lower : ConfigurationBounds 120 1382 64 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_121_lower : ConfigurationBounds 121 1405 64 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_122_lower : ConfigurationBounds 122 1428 64 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_123_lower : ConfigurationBounds 123 1451 65 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_124_lower : ConfigurationBounds 124 1474 66 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_125_lower : ConfigurationBounds 125 1497 66 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_126_lower : ConfigurationBounds 126 1521 67 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_127_lower : ConfigurationBounds 127 1545 67 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_128_lower : ConfigurationBounds 128 1568 68 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem configuration_129_lower : ConfigurationBounds 129 1593 68 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- All 88 nonintegral lower-parent configurations, using the verified count table. -/
theorem all_configurations_verified (index : Fin 89) (hne : (index : ℕ) + 41 ≠ 88) :
    let m := (index : ℕ) + 41
    ConfigurationBounds m (upperEndpoint m) (mixedCount m false) := by
  fin_cases index
  · exact configuration_41_lower
  · exact configuration_42_lower
  · exact configuration_43_lower
  · exact configuration_44_lower
  · exact configuration_45_lower
  · exact configuration_46_lower
  · exact configuration_47_lower
  · exact configuration_48_lower
  · exact configuration_49_lower
  · exact configuration_50_lower
  · exact configuration_51_lower
  · exact configuration_52_lower
  · exact configuration_53_lower
  · exact configuration_54_lower
  · exact configuration_55_lower
  · exact configuration_56_lower
  · exact configuration_57_lower
  · exact configuration_58_lower
  · exact configuration_59_lower
  · exact configuration_60_lower
  · exact configuration_61_lower
  · exact configuration_62_lower
  · exact configuration_63_lower
  · exact configuration_64_lower
  · exact configuration_65_lower
  · exact configuration_66_lower
  · exact configuration_67_lower
  · exact configuration_68_lower
  · exact configuration_69_lower
  · exact configuration_70_lower
  · exact configuration_71_lower
  · exact configuration_72_lower
  · exact configuration_73_lower
  · exact configuration_74_lower
  · exact configuration_75_lower
  · exact configuration_76_lower
  · exact configuration_77_lower
  · exact configuration_78_lower
  · exact configuration_79_lower
  · exact configuration_80_lower
  · exact configuration_81_lower
  · exact configuration_82_lower
  · exact configuration_83_lower
  · exact configuration_84_lower
  · exact configuration_85_lower
  · exact configuration_86_lower
  · exact configuration_87_lower
  · exact False.elim (hne rfl)
  · exact configuration_89_lower
  · exact configuration_90_lower
  · exact configuration_91_lower
  · exact configuration_92_lower
  · exact configuration_93_lower
  · exact configuration_94_lower
  · exact configuration_95_lower
  · exact configuration_96_lower
  · exact configuration_97_lower
  · exact configuration_98_lower
  · exact configuration_99_lower
  · exact configuration_100_lower
  · exact configuration_101_lower
  · exact configuration_102_lower
  · exact configuration_103_lower
  · exact configuration_104_lower
  · exact configuration_105_lower
  · exact configuration_106_lower
  · exact configuration_107_lower
  · exact configuration_108_lower
  · exact configuration_109_lower
  · exact configuration_110_lower
  · exact configuration_111_lower
  · exact configuration_112_lower
  · exact configuration_113_lower
  · exact configuration_114_lower
  · exact configuration_115_lower
  · exact configuration_116_lower
  · exact configuration_117_lower
  · exact configuration_118_lower
  · exact configuration_119_lower
  · exact configuration_120_lower
  · exact configuration_121_lower
  · exact configuration_122_lower
  · exact configuration_123_lower
  · exact configuration_124_lower
  · exact configuration_125_lower
  · exact configuration_126_lower
  · exact configuration_127_lower
  · exact configuration_128_lower
  · exact configuration_129_lower

/-- The marked scalar incidence bounds for all eligible sharp edge points. -/
theorem sharp_edge_inequalities (m : ℕ) (hmlo : 41 ≤ m) (hmhi : m ≤ 129)
    (hm88 : m ≠ 88) (i : ℕ) (hi : i ≤ coreA (mixedCount m false))
    (edge : Fin 6) (d : ℤ) (hd : SharpCertificate.Eligible m (mixedCount m false) i edge d) :
    ImageBounds (markedScalars (scalars m (upperEndpoint m) (mixedCount m false)))
      (sharpEdge (parameters m (mixedCount m false) i) edge d) d := by
  have hm : m - 41 + 41 = m := by omega
  have hconfig := all_configurations_verified ⟨m - 41, by omega⟩ (by simpa only [hm] using hm88)
  simp only [hm] at hconfig
  exact hconfig ⟨i, by omega⟩ edge d hd

theorem sharp_edge_feasible (m : ℕ) (hmlo : 41 ≤ m) (hmhi : m ≤ 129)
    (hm88 : m ≠ 88) (i : ℕ) (hi : i ≤ coreA (mixedCount m false))
    (edge : Fin 6) (d : ℤ) (hdlo : 1 ≤ d) (hdhi : d < (totalA m (mixedCount m false) : ℤ))
    (hzlo : 0 ≤ edgeIntermediate (parameters m (mixedCount m false) i) edge d)
    (hzhi : edgeIntermediate (parameters m (mixedCount m false) i) edge d ≤
      (freeW m (mixedCount m false) : ℚ)) :
    ImageBounds (markedScalars (scalars m (upperEndpoint m) (mixedCount m false)))
      (sharpEdge (parameters m (mixedCount m false) i) edge d) d := by
  apply sharp_edge_inequalities m hmlo hmhi hm88 i hi edge d
  exact (eligible_iff_intermediate _ _ _ _ _).2 ⟨hdlo, hdhi, hzlo, hzhi⟩

/-- Every rational prefix-edge point with integral source dimension satisfies
the marked bounds; this is the interface to concave profile minimization. -/
theorem sharp_prefix_edge_inequalities (m : ℕ) (hmlo : 41 ≤ m) (hmhi : m ≤ 129)
    (hm88 : m ≠ 88) (i : ℕ) (hi : i ≤ coreA (mixedCount m false))
    (u v : Fin 4) (huv : u < v) (z : ℚ) (hzlo : 0 ≤ z)
    (hzhi : z ≤ (freeW m (mixedCount m false) : ℚ))
    (d : ℤ) (hdlo : 1 ≤ d) (hdhi : d < (totalA m (mixedCount m false) : ℤ))
    (hsource : (i : ℚ) + (u.val : ℚ) * (freeW m (mixedCount m false) : ℚ) +
      ((v.val : ℚ) - (u.val : ℚ)) * z = (d : ℚ)) :
    let p := parameters m (mixedCount m false) i
    ImageBounds (markedScalars (scalars m (upperEndpoint m) (mixedCount m false)))
      (sharpProfile p (edgeLayer p.w z u v 1) (edgeLayer p.w z u v 2)
        (edgeLayer p.w z u v 3)) d := by
  obtain ⟨edge, hu, hv⟩ := edge_complete u v huv
  have hKq : (edgeWidth edge : ℚ) = (v.val : ℚ) - (u.val : ℚ) := by
    have h := edgeWidth_eq_difference edge
    rw [hu, hv] at h
    exact_mod_cast h
  have hKne : (edgeWidth edge : ℚ) ≠ 0 := by
    have h : (0 : ℚ) < edgeWidth edge := by exact_mod_cast edgeWidth_pos edge
    exact ne_of_gt h
  have hzeq : edgeIntermediate (parameters m (mixedCount m false) i) edge d = z := by
    unfold edgeIntermediate parameters
    apply (div_eq_iff hKne).2
    rw [hKq, hu]
    norm_num only [Int.cast_natCast]
    nlinarith only [hsource]
  have h := sharp_edge_feasible m hmlo hmhi hm88 i hi edge d hdlo hdhi
    (by rw [hzeq]; exact hzlo) (by rw [hzeq]; exact hzhi)
  simpa only [sharpEdge, hzeq, hu, hv] using h

end Quartic.MarkedSharpCertificate
