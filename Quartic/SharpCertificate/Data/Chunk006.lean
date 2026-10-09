module

public import Quartic.SharpCertificate.Data.Initial

@[expose] public section

/-! Independent kernel-checked cubic certificates, round-robin chunk. -/

namespace Quartic.SharpCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_48_lower : ConfigurationBounds 48 237 23 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_48_upper : ConfigurationBounds 48 237 24 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_56_lower : ConfigurationBounds 56 317 28 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_56_upper : ConfigurationBounds 56 317 29 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_64_lower : ConfigurationBounds 64 409 33 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_64_upper : ConfigurationBounds 64 409 34 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_72_lower : ConfigurationBounds 72 513 37 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_72_upper : ConfigurationBounds 72 513 38 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_80_lower : ConfigurationBounds 80 628 42 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_80_upper : ConfigurationBounds 80 628 43 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_88_lower : ConfigurationBounds 88 756 46 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_88_upper : ConfigurationBounds 88 756 46 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_96_lower : ConfigurationBounds 96 895 50 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_96_upper : ConfigurationBounds 96 895 51 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_104_lower : ConfigurationBounds 104 1046 54 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_104_upper : ConfigurationBounds 104 1046 55 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_112_lower : ConfigurationBounds 112 1208 59 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_112_upper : ConfigurationBounds 112 1208 60 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_120_lower : ConfigurationBounds 120 1382 64 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_120_upper : ConfigurationBounds 120 1382 65 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_128_lower : ConfigurationBounds 128 1568 68 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_128_upper : ConfigurationBounds 128 1568 69 := by
  apply configuration_of_checks
  decide +kernel

end Quartic.SharpCertificate
