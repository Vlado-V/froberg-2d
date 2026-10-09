module

public import Quartic.SharpCertificate.Data.Initial

@[expose] public section

/-! Independent kernel-checked cubic certificates, round-robin chunk. -/

namespace Quartic.SharpCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_43_lower : ConfigurationBounds 43 192 21 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_43_upper : ConfigurationBounds 43 192 22 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_51_lower : ConfigurationBounds 51 265 26 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_51_upper : ConfigurationBounds 51 265 27 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_59_lower : ConfigurationBounds 59 350 30 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_59_upper : ConfigurationBounds 59 350 31 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_67_lower : ConfigurationBounds 67 447 34 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_67_upper : ConfigurationBounds 67 447 35 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_75_lower : ConfigurationBounds 75 555 38 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_75_upper : ConfigurationBounds 75 555 39 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_83_lower : ConfigurationBounds 83 675 43 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_83_upper : ConfigurationBounds 83 675 44 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_91_lower : ConfigurationBounds 91 806 48 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_91_upper : ConfigurationBounds 91 806 49 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_99_lower : ConfigurationBounds 99 950 52 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_99_upper : ConfigurationBounds 99 950 53 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_107_lower : ConfigurationBounds 107 1105 56 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_107_upper : ConfigurationBounds 107 1105 57 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_115_lower : ConfigurationBounds 115 1272 61 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_115_upper : ConfigurationBounds 115 1272 62 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_123_lower : ConfigurationBounds 123 1451 65 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_123_upper : ConfigurationBounds 123 1451 66 := by
  apply configuration_of_checks
  decide +kernel

end Quartic.SharpCertificate
