module

public import Quartic.SharpCertificate.Data.Initial

@[expose] public section

/-! Independent kernel-checked cubic certificates, round-robin chunk. -/

namespace Quartic.SharpCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_45_lower : ConfigurationBounds 45 210 22 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_45_upper : ConfigurationBounds 45 210 23 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_53_lower : ConfigurationBounds 53 285 27 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_53_upper : ConfigurationBounds 53 285 28 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_61_lower : ConfigurationBounds 61 373 31 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_61_upper : ConfigurationBounds 61 373 32 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_69_lower : ConfigurationBounds 69 473 35 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_69_upper : ConfigurationBounds 69 473 36 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_77_lower : ConfigurationBounds 77 584 39 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_77_upper : ConfigurationBounds 77 584 40 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_85_lower : ConfigurationBounds 85 707 44 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_85_upper : ConfigurationBounds 85 707 45 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_93_lower : ConfigurationBounds 93 841 49 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_93_upper : ConfigurationBounds 93 841 50 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_101_lower : ConfigurationBounds 101 988 53 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_101_upper : ConfigurationBounds 101 988 54 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_109_lower : ConfigurationBounds 109 1146 57 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_109_upper : ConfigurationBounds 109 1146 58 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_117_lower : ConfigurationBounds 117 1316 61 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_117_upper : ConfigurationBounds 117 1316 62 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_125_lower : ConfigurationBounds 125 1497 66 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_125_upper : ConfigurationBounds 125 1497 67 := by
  apply configuration_of_checks
  decide +kernel

end Quartic.SharpCertificate
