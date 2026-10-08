import Quartic.SharpCertificate.Certificate

/-! Kernel-checked cubic certificates for every core dimension and prefix edge. -/

namespace Quartic.SharpCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_41_lower : ConfigurationBounds 41 176 20 := by
  apply configuration_of_checks
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem configuration_41_upper : ConfigurationBounds 41 176 21 := by
  apply configuration_of_checks
  decide +kernel

end Quartic.SharpCertificate
