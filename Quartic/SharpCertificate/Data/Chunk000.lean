module

public import Quartic.SharpCertificate.Data.Initial

@[expose] public section

/-! Independent kernel-checked cubic certificates, round-robin chunk. -/

namespace Quartic.SharpCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_42_lower : ConfigurationBounds 42 184 21 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_42_upper : ConfigurationBounds 42 184 22 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_50_lower : ConfigurationBounds 50 256 24 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_50_upper : ConfigurationBounds 50 256 25 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_58_lower : ConfigurationBounds 58 339 29 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_58_upper : ConfigurationBounds 58 339 30 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_66_lower : ConfigurationBounds 66 434 34 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_66_upper : ConfigurationBounds 66 434 35 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_74_lower : ConfigurationBounds 74 541 38 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_74_upper : ConfigurationBounds 74 541 39 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_82_lower : ConfigurationBounds 82 659 43 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_82_upper : ConfigurationBounds 82 659 44 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_90_lower : ConfigurationBounds 90 789 47 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_90_upper : ConfigurationBounds 90 789 48 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_98_lower : ConfigurationBounds 98 931 52 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_98_upper : ConfigurationBounds 98 931 53 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_106_lower : ConfigurationBounds 106 1085 56 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_106_upper : ConfigurationBounds 106 1085 57 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_114_lower : ConfigurationBounds 114 1251 60 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_114_upper : ConfigurationBounds 114 1251 61 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_122_lower : ConfigurationBounds 122 1428 64 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_122_upper : ConfigurationBounds 122 1428 65 := by
  apply configuration_of_checks
  decide +kernel

end Quartic.SharpCertificate
