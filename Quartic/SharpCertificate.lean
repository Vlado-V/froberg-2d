import Quartic.SharpCertificate.Data
import Quartic.SharpCertificate.Full
import Quartic.SharpCertificate.Counting

/-!
# Verified sharp rational-edge inequalities, dimensions 41 through 129

For both parent endpoints, every core dimension and all six prefix edges satisfy
both scalar incidence inequalities at every feasible nontrivial integral source
dimension. The checked numerator is proved equal to the original rational sharp
profile expression. Geometric degeneration and concave minimization are separate
obligations, not assumptions hidden in this arithmetic certificate.
-/

namespace Quartic.SharpCertificate

open Quartic.Counts Quartic.FiniteCounts Quartic.ProfileCertificate Quartic.HullCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- All 178 configurations, linked to the sign-certified endpoint table. -/
theorem all_configurations_verified (index : Fin 89) (upper : Bool) :
    let m := (index : ℕ) + 41
    ConfigurationBounds m (upperEndpoint m) (mixedCount m upper) := by
  fin_cases index <;> cases upper
  · exact configuration_41_lower
  · exact configuration_41_upper
  · exact configuration_42_lower
  · exact configuration_42_upper
  · exact configuration_43_lower
  · exact configuration_43_upper
  · exact configuration_44_lower
  · exact configuration_44_upper
  · exact configuration_45_lower
  · exact configuration_45_upper
  · exact configuration_46_lower
  · exact configuration_46_upper
  · exact configuration_47_lower
  · exact configuration_47_upper
  · exact configuration_48_lower
  · exact configuration_48_upper
  · exact configuration_49_lower
  · exact configuration_49_upper
  · exact configuration_50_lower
  · exact configuration_50_upper
  · exact configuration_51_lower
  · exact configuration_51_upper
  · exact configuration_52_lower
  · exact configuration_52_upper
  · exact configuration_53_lower
  · exact configuration_53_upper
  · exact configuration_54_lower
  · exact configuration_54_upper
  · exact configuration_55_lower
  · exact configuration_55_upper
  · exact configuration_56_lower
  · exact configuration_56_upper
  · exact configuration_57_lower
  · exact configuration_57_upper
  · exact configuration_58_lower
  · exact configuration_58_upper
  · exact configuration_59_lower
  · exact configuration_59_upper
  · exact configuration_60_lower
  · exact configuration_60_upper
  · exact configuration_61_lower
  · exact configuration_61_upper
  · exact configuration_62_lower
  · exact configuration_62_upper
  · exact configuration_63_lower
  · exact configuration_63_upper
  · exact configuration_64_lower
  · exact configuration_64_upper
  · exact configuration_65_lower
  · exact configuration_65_upper
  · exact configuration_66_lower
  · exact configuration_66_upper
  · exact configuration_67_lower
  · exact configuration_67_upper
  · exact configuration_68_lower
  · exact configuration_68_upper
  · exact configuration_69_lower
  · exact configuration_69_upper
  · exact configuration_70_lower
  · exact configuration_70_upper
  · exact configuration_71_lower
  · exact configuration_71_upper
  · exact configuration_72_lower
  · exact configuration_72_upper
  · exact configuration_73_lower
  · exact configuration_73_upper
  · exact configuration_74_lower
  · exact configuration_74_upper
  · exact configuration_75_lower
  · exact configuration_75_upper
  · exact configuration_76_lower
  · exact configuration_76_upper
  · exact configuration_77_lower
  · exact configuration_77_upper
  · exact configuration_78_lower
  · exact configuration_78_upper
  · exact configuration_79_lower
  · exact configuration_79_upper
  · exact configuration_80_lower
  · exact configuration_80_upper
  · exact configuration_81_lower
  · exact configuration_81_upper
  · exact configuration_82_lower
  · exact configuration_82_upper
  · exact configuration_83_lower
  · exact configuration_83_upper
  · exact configuration_84_lower
  · exact configuration_84_upper
  · exact configuration_85_lower
  · exact configuration_85_upper
  · exact configuration_86_lower
  · exact configuration_86_upper
  · exact configuration_87_lower
  · exact configuration_87_upper
  · exact configuration_88_lower
  · exact configuration_88_upper
  · exact configuration_89_lower
  · exact configuration_89_upper
  · exact configuration_90_lower
  · exact configuration_90_upper
  · exact configuration_91_lower
  · exact configuration_91_upper
  · exact configuration_92_lower
  · exact configuration_92_upper
  · exact configuration_93_lower
  · exact configuration_93_upper
  · exact configuration_94_lower
  · exact configuration_94_upper
  · exact configuration_95_lower
  · exact configuration_95_upper
  · exact configuration_96_lower
  · exact configuration_96_upper
  · exact configuration_97_lower
  · exact configuration_97_upper
  · exact configuration_98_lower
  · exact configuration_98_upper
  · exact configuration_99_lower
  · exact configuration_99_upper
  · exact configuration_100_lower
  · exact configuration_100_upper
  · exact configuration_101_lower
  · exact configuration_101_upper
  · exact configuration_102_lower
  · exact configuration_102_upper
  · exact configuration_103_lower
  · exact configuration_103_upper
  · exact configuration_104_lower
  · exact configuration_104_upper
  · exact configuration_105_lower
  · exact configuration_105_upper
  · exact configuration_106_lower
  · exact configuration_106_upper
  · exact configuration_107_lower
  · exact configuration_107_upper
  · exact configuration_108_lower
  · exact configuration_108_upper
  · exact configuration_109_lower
  · exact configuration_109_upper
  · exact configuration_110_lower
  · exact configuration_110_upper
  · exact configuration_111_lower
  · exact configuration_111_upper
  · exact configuration_112_lower
  · exact configuration_112_upper
  · exact configuration_113_lower
  · exact configuration_113_upper
  · exact configuration_114_lower
  · exact configuration_114_upper
  · exact configuration_115_lower
  · exact configuration_115_upper
  · exact configuration_116_lower
  · exact configuration_116_upper
  · exact configuration_117_lower
  · exact configuration_117_upper
  · exact configuration_118_lower
  · exact configuration_118_upper
  · exact configuration_119_lower
  · exact configuration_119_upper
  · exact configuration_120_lower
  · exact configuration_120_upper
  · exact configuration_121_lower
  · exact configuration_121_upper
  · exact configuration_122_lower
  · exact configuration_122_upper
  · exact configuration_123_lower
  · exact configuration_123_upper
  · exact configuration_124_lower
  · exact configuration_124_upper
  · exact configuration_125_lower
  · exact configuration_125_upper
  · exact configuration_126_lower
  · exact configuration_126_upper
  · exact configuration_127_lower
  · exact configuration_127_upper
  · exact configuration_128_lower
  · exact configuration_128_upper
  · exact configuration_129_lower
  · exact configuration_129_upper

/-- Both original incidence inequalities for every sharp edge at every eligible
integer dimension throughout the finite sharp range. -/
theorem sharp_edge_inequalities (m : ℕ) (hmlo : 41 ≤ m) (hmhi : m ≤ 129)
    (upper : Bool) (i : ℕ) (hi : i ≤ coreA (mixedCount m upper))
    (edge : Fin 6) (d : ℤ) (hd : Eligible m (mixedCount m upper) i edge d) :
    ImageBounds (scalars m (upperEndpoint m) (mixedCount m upper))
      (sharpEdge (parameters m (mixedCount m upper) i) edge d) d := by
  have hconfig := all_configurations_verified ⟨m - 41, by omega⟩ upper
  have hm : m - 41 + 41 = m := by omega
  simp only [hm] at hconfig
  exact hconfig ⟨i, by omega⟩ edge d hd

/-- The same conclusion stated using the manuscript's rational intermediate
layer value rather than cleared integer source-range inequalities. -/
theorem sharp_edge_feasible (m : ℕ) (hmlo : 41 ≤ m) (hmhi : m ≤ 129)
    (upper : Bool) (i : ℕ) (hi : i ≤ coreA (mixedCount m upper))
    (edge : Fin 6) (d : ℤ) (hdlo : 1 ≤ d) (hdhi : d < (totalA m (mixedCount m upper) : ℤ))
    (hzlo : 0 ≤ edgeIntermediate (parameters m (mixedCount m upper) i) edge d)
    (hzhi : edgeIntermediate (parameters m (mixedCount m upper) i) edge d ≤
      (freeW m (mixedCount m upper) : ℚ)) :
    ImageBounds (scalars m (upperEndpoint m) (mixedCount m upper))
      (sharpEdge (parameters m (mixedCount m upper) i) edge d) d := by
  apply sharp_edge_inequalities m hmlo hmhi upper i hi edge d
  exact (eligible_iff_intermediate _ _ _ _ _).2 ⟨hdlo, hdhi, hzlo, hzhi⟩

/-- All rational prefix-edge points with an integral source dimension satisfy
the sharp incidence bounds, stated with arbitrary ranks `0 ≤ u < v ≤ 3`. -/
theorem sharp_prefix_edge_inequalities (m : ℕ) (hmlo : 41 ≤ m) (hmhi : m ≤ 129)
    (upper : Bool) (i : ℕ) (hi : i ≤ coreA (mixedCount m upper))
    (u v : Fin 4) (huv : u < v) (z : ℚ) (hzlo : 0 ≤ z)
    (hzhi : z ≤ (freeW m (mixedCount m upper) : ℚ))
    (d : ℤ) (hdlo : 1 ≤ d) (hdhi : d < (totalA m (mixedCount m upper) : ℤ))
    (hsource : (i : ℚ) + (u.val : ℚ) * (freeW m (mixedCount m upper) : ℚ) +
      ((v.val : ℚ) - (u.val : ℚ)) * z = (d : ℚ)) :
    let p := parameters m (mixedCount m upper) i
    ImageBounds (scalars m (upperEndpoint m) (mixedCount m upper))
      (sharpProfile p (edgeLayer p.w z u v 1) (edgeLayer p.w z u v 2) (edgeLayer p.w z u v 3)) d := by
  obtain ⟨edge, hu, hv⟩ := edge_complete u v huv
  have hKq : (edgeWidth edge : ℚ) = (v.val : ℚ) - (u.val : ℚ) := by
    have h := edgeWidth_eq_difference edge
    rw [hu, hv] at h
    exact_mod_cast h
  have hKne : (edgeWidth edge : ℚ) ≠ 0 := by
    have h : (0 : ℚ) < edgeWidth edge := by exact_mod_cast edgeWidth_pos edge
    exact ne_of_gt h
  have hzeq : edgeIntermediate (parameters m (mixedCount m upper) i) edge d = z := by
    unfold edgeIntermediate parameters
    apply (div_eq_iff hKne).2
    rw [hKq, hu]
    norm_num only [Int.cast_natCast]
    nlinarith only [hsource]
  have h := sharp_edge_feasible m hmlo hmhi upper i hi edge d hdlo hdhi
    (by rw [hzeq]; exact hzlo) (by rw [hzeq]; exact hzhi)
  simpa only [sharpEdge, hzeq, hu, hv] using h

end Quartic.SharpCertificate
