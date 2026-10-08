import Quartic.ProfileCertificate.Core

/-! Numerical kernel checks. Kept separate so wrapper edits reuse these proofs. -/

namespace Quartic.ProfileCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel check of all 23,938 nontrivial profiles in this configuration. -/
theorem configuration_28_lower : ConfigurationValid 28 87 13 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel check of all 22,285 nontrivial profiles in this configuration. -/
theorem configuration_28_upper : ConfigurationValid 28 87 14 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel check of all 27,928 nontrivial profiles in this configuration. -/
theorem configuration_29_lower : ConfigurationValid 29 93 13 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel check of all 26,218 nontrivial profiles in this configuration. -/
theorem configuration_29_upper : ConfigurationValid 29 93 14 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel check of all 30,588 nontrivial profiles in this configuration. -/
theorem configuration_30_lower : ConfigurationValid 30 99 14 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel check of all 28,498 nontrivial profiles in this configuration. -/
theorem configuration_30_upper : ConfigurationValid 30 99 15 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel check of all 35,418 nontrivial profiles in this configuration. -/
theorem configuration_31_lower : ConfigurationValid 31 105 14 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel check of all 33,248 nontrivial profiles in this configuration. -/
theorem configuration_31_upper : ConfigurationValid 31 105 15 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel check of all 38,498 nontrivial profiles in this configuration. -/
theorem configuration_32_lower : ConfigurationValid 32 111 15 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel check of all 35,908 nontrivial profiles in this configuration. -/
theorem configuration_32_upper : ConfigurationValid 32 111 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel check of all 44,273 nontrivial profiles in this configuration. -/
theorem configuration_33_lower : ConfigurationValid 33 118 15 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel check of all 41,578 nontrivial profiles in this configuration. -/
theorem configuration_33_upper : ConfigurationValid 33 118 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel check of all 47,815 nontrivial profiles in this configuration. -/
theorem configuration_34_lower : ConfigurationValid 34 124 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel check of all 44,658 nontrivial profiles in this configuration. -/
theorem configuration_34_upper : ConfigurationValid 34 124 17 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel check of all 51,357 nontrivial profiles in this configuration. -/
theorem configuration_35_lower : ConfigurationValid 35 131 17 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel check of all 47,738 nontrivial profiles in this configuration. -/
theorem configuration_35_upper : ConfigurationValid 35 131 18 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel check of all 58,694 nontrivial profiles in this configuration. -/
theorem configuration_36_lower : ConfigurationValid 36 138 17 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel check of all 54,899 nontrivial profiles in this configuration. -/
theorem configuration_36_upper : ConfigurationValid 36 138 18 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel check of all 62,742 nontrivial profiles in this configuration. -/
theorem configuration_37_lower : ConfigurationValid 37 145 18 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel check of all 58,441 nontrivial profiles in this configuration. -/
theorem configuration_37_upper : ConfigurationValid 37 145 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel check of all 71,298 nontrivial profiles in this configuration. -/
theorem configuration_38_lower : ConfigurationValid 38 153 18 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel check of all 66,790 nontrivial profiles in this configuration. -/
theorem configuration_38_upper : ConfigurationValid 38 153 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel check of all 75,898 nontrivial profiles in this configuration. -/
theorem configuration_39_lower : ConfigurationValid 39 160 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel check of all 70,838 nontrivial profiles in this configuration. -/
theorem configuration_39_upper : ConfigurationValid 39 160 20 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel check of all 85,798 nontrivial profiles in this configuration. -/
theorem configuration_40_lower : ConfigurationValid 40 168 19 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel check of all 80,498 nontrivial profiles in this configuration. -/
theorem configuration_40_upper : ConfigurationValid 40 168 20 := by
  decide +kernel

end Quartic.ProfileCertificate
