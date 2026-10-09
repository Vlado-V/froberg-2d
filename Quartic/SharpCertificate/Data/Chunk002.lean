module

public import Quartic.SharpCertificate.Data.Initial

@[expose] public section

/-! Independent kernel-checked cubic certificates, round-robin chunk. -/

namespace Quartic.SharpCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_44_lower : ConfigurationBounds 44 201 21 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_44_upper : ConfigurationBounds 44 201 22 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_52_lower : ConfigurationBounds 52 275 26 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_52_upper : ConfigurationBounds 52 275 27 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_60_lower : ConfigurationBounds 60 362 30 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_60_upper : ConfigurationBounds 60 362 31 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_68_lower : ConfigurationBounds 68 459 35 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_68_upper : ConfigurationBounds 68 459 36 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_76_lower : ConfigurationBounds 76 569 39 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_76_upper : ConfigurationBounds 76 569 40 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_84_lower : ConfigurationBounds 84 691 43 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_84_upper : ConfigurationBounds 84 691 44 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_92_lower : ConfigurationBounds 92 824 48 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_92_upper : ConfigurationBounds 92 824 49 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_100_lower : ConfigurationBounds 100 969 52 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_100_upper : ConfigurationBounds 100 969 53 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_108_lower : ConfigurationBounds 108 1125 57 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_108_upper : ConfigurationBounds 108 1125 58 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_116_lower : ConfigurationBounds 116 1294 61 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_116_upper : ConfigurationBounds 116 1294 62 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_124_lower : ConfigurationBounds 124 1474 66 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_124_upper : ConfigurationBounds 124 1474 67 := by
  apply configuration_of_checks
  decide +kernel

end Quartic.SharpCertificate
